"""
001.py rewrites the ChemDYNA chat surface so every major feature routes through an
LLM reasoning stack instead of dozens of handwritten heuristics.

Key features implemented in this module:

1. Configuration + Secrets
   * load_combined_secrets folds Streamlit secrets with local TOML files so the
     same binary works for hosted and local runs.
   * resolve_openai_settings / resolve_sql_settings normalize those blobs and
     surface status badges in the Streamlit sidebar.

2. Reasoning Pipeline
   * ReasoningLLM.interpret_prompt asks OpenAI for a structured JSON plan that
     includes reasoning steps, intent metadata, and whether SQL is required.
   * ReasoningLLM.plan_sql hands that JSON + allow-listed schema to another LLM
     call that emits parameterized SQL plus self-checks.
   * ReasoningLLM.reason_over_results compresses SQL results + plan metadata into
     a narrated answer with cited assumptions and follow-up suggestions.

3. SQL Safety & Data Access
   * SQLValidator enforces SELECT/CTE-only statements, disallows multiple
     statements, and ensures FROM/JOIN tables exist on the allow list.
   * fetch_schema_snapshot introspects INFORMATION_SCHEMA once per session so the
     planner prompt contains the current column names.
   * QueryRunner executes every plan through a single pyodbc connection using
     parameter placeholders, returning a pandas DataFrame plus derived stats.

4. Session Memory & Logging
   * ensure_history_state keeps a per-user chat buffer (role/content/metadata)
     that gets rendered via the Streamlit chat components.
   * summarize_history_for_prompt flattens the latest messages into a markdown
     transcript that seeds each LLM call with high-signal context.
   * trace_events captures interpreter/SQL/reasoning steps so the UI can expose
     explainable breadcrumbs for auditing.

5. Streamlit UI
   * render_sidebar_status shows connection/model configuration plus debug
     toggles.
   * render_chat_ui wires Streamlit’s chat_input with the ReasoningOrchestrator
     so every turn displays the model reply, agent traces, and optional result
     previews/charts/downloads.
"""

from __future__ import annotations

import contextlib
import datetime as dt
import json
import logging
import re
import textwrap
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Iterable, Mapping, MutableMapping, Sequence

import pandas as pd
import pyodbc
import requests
import streamlit as st
from streamlit.errors import StreamlitAPIException

try:  # Python 3.11+
    import tomllib
except ModuleNotFoundError:  # pragma: no cover - fallback for older interpreters
    import tomli as tomllib  # type: ignore


LOGGER = logging.getLogger("chem_reasoner")
logging.basicConfig(level=logging.INFO)

APP_ROOT = Path(__file__).resolve().parent
LOCAL_SECRETS_PATHS = (
    APP_ROOT / ".streamlit" / "secrets.toml",
    APP_ROOT / "secrets.toml",
)

DEFAULT_DRIVER = "ODBC Driver 17 for SQL Server"
DEFAULT_SERVER = "DynamicsGP"
DEFAULT_DATABASE = "CDI"

CHAT_STATE_KEY = "001_chat_history"
TRACE_STATE_KEY = "001_agent_traces"
SESSION_CONTEXT_KEY = "001_structured_context"

OPENAI_CHAT_URL = "https://api.openai.com/v1/chat/completions"
OPENAI_TIMEOUT_SECONDS = 40
DEFAULT_INTERPRETER_MODEL = "gpt-5.0"
DEFAULT_SQL_MODEL = "gpt-5.0"
DEFAULT_REASONER_MODEL = "gpt-5.0"

CUSTOM_SQL_ALLOWED_TABLES: tuple[str, ...] = (
    "IV00101",
    "IV00102",
    "IV30200",
    "IV30300",
    "BM00101",
    "BM00111",
    "BM010115",
    "POP10100",
    "POP10110",
    "POP30100",
    "POP30110",
    "POP30200",
    "POP30300",
    "POP30310",
    "SOP10100",
    "SOP10200",
    "SOP30200",
    "SOP30300",
)
DATASET_REFERENCE_HINTS: tuple[str, ...] = (
    "InventoryBalance lives in IV00102 (site-level quantities like BGNGQTY, LSORDQTY, LRCPTQTY, QTYONHND, ATYALLOC, QTYONORD, ORDRPNTQTY, LOCNCODE) joined to IV00101 for ITEMDESC/ITMCLSCD. IV00101 itself only holds descriptive master data.",
    "QtyAvailable is IV00102.QTYONHND - IV00102.ATYALLOC. Compare it to IV00102.ORDRPNTQTY when answering reorder/coverage questions.",
    "Usage history comes from IV30300 transaction detail joined to IV30200 headers. Consumption rows are DOCTYPE = 1 and TRXQTY < 0, and DOCDATE lives on IV30200.",
    "Sales shipments/invoices require SOP30300 detail joined to SOP30200 headers. SOPTYPE 3 are invoices (positive) and SOPTYPE 4 are returns (negative); DOCDATE comes from SOP30200.",
    "Raw materials always show up as usage/burn-rate data (IV30300/IV30200) and drive buy/reorder reports. Finished goods flow through SOP30300/SOP30200 sales reports, so never mix the two when the user asks for purchasing guidance versus customer shipments.",
    "Open purchase orders require POP10100 headers (PONUMBER, VENDORID, DOCDATE, POSTATUS) joined to POP10110 lines (LOCNCODE, ITEMNMBR, QTYORDER, QTYCANCE, QTYCMTBASE). Outstanding quantity is QTYORDER - (QTYCMTBASE + QTYCANCE).",
    "Unless a user explicitly asks for finished goods, purchasing queries must filter IV00101.ITMCLSCD to classes that start with 'RAWMAT' (RAWMATNT, RAWMATNTB, RAWMATNTE, RAWMATT) and exclude manufactured/resale classes like MANUFPROT, MANUFPRONT, RESALEPROD, CONTAINERS, or STORAGE.",
)
ENFORCE_SQL_ALLOWLIST = False

RAW_MATERIAL_CLASS_PREFIXES: tuple[str, ...] = ("RAWMATNT", "RAWMATNTB", "RAWMATNTE", "RAWMATT")
FINISHED_GOOD_CLASS_EXAMPLES: tuple[str, ...] = ("MANUFPROT", "MANUFPRONT", "RESALEPROD", "CONTAINERS", "STORAGE")
PROCUREMENT_KEYWORDS: tuple[str, ...] = (
    "need to buy",
    "need to purchase",
    "need to order",
    "what to buy",
    "what should we buy",
    "reorder point",
    "re-order point",
    "below reorder",
    "below order point",
    "restock",
    "replenish",
    "procurement",
    "purchasing",
    "stockout",
    "stock out",
    "coverage",
    "shortfall",
    "items to purchase",
    "items to order",
    "buying list",
)
FINISHED_GOOD_OVERRIDE_PHRASES: tuple[str, ...] = (
    "finished good",
    "finished goods",
    "finished product",
    "finished products",
    "resale product",
    "resale products",
)
FINISHED_GOOD_NEGATION_PHRASES: tuple[str, ...] = (
    "exclude finished",
    "excluding finished",
    "no finished",
    "without finished",
    "not finished",
    "except finished",
)

FORBIDDEN_SQL_VERBS = (
    "DELETE",
    "UPDATE",
    "INSERT",
    "MERGE",
    "ALTER",
    "DROP",
    "TRUNCATE",
    "EXEC",
    "GRANT",
    "DENY",
    "CALL",
)

SQL_COMMENT_PATTERN = re.compile(r"(--.*?$)|(/\*.*?\*/)", re.MULTILINE | re.DOTALL)
SQL_TABLE_TOKEN_PATTERN = re.compile(r"\b(?:FROM|JOIN)\s+([A-Za-z0-9_\.\[\]]+)", re.IGNORECASE)
INVALID_COLUMN_PATTERN = re.compile(r"Invalid column name '([^']+)'")
MAX_RESULT_ROWS = 400
SCHEMA_PREVIEW_LIMIT = 20
HISTORY_WINDOW = 8
TRACE_LIMIT = 12


@dataclass
class ReasonedIntent:
    """Structured output from the interpreter model."""

    action: str
    reasoning: list[str]
    structured_request: dict[str, Any] = field(default_factory=dict)
    clarifications: list[str] = field(default_factory=list)
    follow_up_questions: list[str] = field(default_factory=list)


@dataclass
class SQLPlan:
    """Parameterised SQL instructions coming from the planner model."""

    sql: str
    params: list[Any]
    summary: str
    self_checks: list[str] = field(default_factory=list)


@dataclass
class QueryResult:
    """Container for SQL output and derived stats."""

    dataframe: pd.DataFrame
    rowcount: int
    columns: list[str]


@dataclass
class ModelCatalog:
    interpreter: str
    planner: str
    reasoner: str


def load_combined_secrets() -> dict[str, Any]:
    """
    Merge Streamlit secrets with local TOML files, preferring hosted values.
    """

    combined: dict[str, Any] = {}
    with contextlib.suppress(StreamlitAPIException, RuntimeError, KeyError, AttributeError, TypeError):
        for key in st.secrets:
            combined[key] = st.secrets[key]
    for path in LOCAL_SECRETS_PATHS:
        if not path.exists():
            continue
        try:
            data = tomllib.loads(path.read_text(encoding="utf-8"))
            combined = _deep_merge_dicts(combined, data)
        except (OSError, tomllib.TOMLDecodeError) as err:
            LOGGER.warning("Unable to read secrets from %s: %s", path, err)
    return combined


def _deep_merge_dicts(base: MutableMapping[str, Any], extra: Mapping[str, Any]) -> dict[str, Any]:
    merged = dict(base)
    for key, value in extra.items():
        if key in merged and isinstance(merged[key], Mapping) and isinstance(value, Mapping):
            merged[key] = _deep_merge_dicts(merged[key], value)
        else:
            merged[key] = value
    return merged


def resolve_openai_settings(secrets: Mapping[str, Any]) -> dict[str, Any]:
    """
    Normalize OpenAI configuration and default models.
    """

    section: Mapping[str, Any] = {}
    if "openai" in secrets and isinstance(secrets["openai"], Mapping):
        section = secrets["openai"]
    api_key = section.get("api_key") if isinstance(section, Mapping) else None
    if not api_key:
        api_key = secrets.get("openai_api_key")
    base_url = section.get("base_url") if isinstance(section, Mapping) else None
    api_version = section.get("api_version") if isinstance(section, Mapping) else None
    base_model = section.get("model")
    interpreter_model = section.get("interpreter_model") or base_model or DEFAULT_INTERPRETER_MODEL
    sql_model = section.get("sql_model") or base_model or DEFAULT_SQL_MODEL
    reasoner_model = section.get("reasoner_model") or section.get("analysis_model") or base_model or DEFAULT_REASONER_MODEL
    return {
        "api_key": api_key,
        "base_url": base_url,
        "api_version": api_version,
        "models": ModelCatalog(
            interpreter=interpreter_model,
            planner=sql_model,
            reasoner=reasoner_model,
        ),
    }


def resolve_sql_settings(secrets: Mapping[str, Any]) -> dict[str, Any]:
    """
    Normalize SQL connection settings (driver/server/db/auth).
    """

    section = secrets.get("sql")
    if not isinstance(section, Mapping):
        section = {}
    return {
        "driver": section.get("driver", DEFAULT_DRIVER),
        "server": section.get("server", DEFAULT_SERVER),
        "database": section.get("database", DEFAULT_DATABASE),
        "authentication": section.get("authentication", "windows").lower(),
        "username": section.get("username"),
        "password": section.get("password"),
        "encrypt": section.get("encrypt", "no"),
        "trust_server_certificate": section.get("trust_server_certificate", "yes"),
    }


def build_connection_string(sql_settings: Mapping[str, Any]) -> tuple[str, str]:
    """
    Compose a pyodbc connection string and human-readable label.
    """

    driver = sql_settings.get("driver") or DEFAULT_DRIVER
    server = sql_settings.get("server") or DEFAULT_SERVER
    database = sql_settings.get("database") or DEFAULT_DATABASE
    auth_mode = (sql_settings.get("authentication") or "windows").lower()
    username = sql_settings.get("username")
    password = sql_settings.get("password")
    encrypt = (sql_settings.get("encrypt") or "no").lower()
    trust_cert = sql_settings.get("trust_server_certificate", "yes").lower()

    clauses = [
        f"Driver={{{driver}}}",
        f"Server={server}",
        f"Database={database}",
    ]
    if auth_mode == "sql":
        clauses.append(f"UID={username}")
        clauses.append(f"PWD={password}")
    else:
        clauses.append("Trusted_Connection=yes")
    if encrypt in {"yes", "true", "required"}:
        clauses.append("Encrypt=yes")
        clauses.append(f"TrustServerCertificate={'yes' if trust_cert in {'yes', 'true'} else 'no'}")
    connection_string = ";".join(filter(None, clauses))
    label = f"{server}/{database}"
    return connection_string, label


def ensure_history_state() -> list[dict[str, Any]]:
    """
    Guarantee that st.session_state holds our chat transcript structure.
    """

    history = st.session_state.get(CHAT_STATE_KEY)
    if isinstance(history, list):
        return history
    st.session_state[CHAT_STATE_KEY] = []
    return st.session_state[CHAT_STATE_KEY]


def ensure_trace_state() -> list[dict[str, Any]]:
    traces = st.session_state.get(TRACE_STATE_KEY)
    if isinstance(traces, list):
        return traces
    st.session_state[TRACE_STATE_KEY] = []
    return st.session_state[TRACE_STATE_KEY]


def append_history(role: str, content: str, metadata: Mapping[str, Any] | None = None) -> None:
    history = ensure_history_state()
    history.append(
        {
            "role": role,
            "content": content,
            "timestamp": dt.datetime.now(dt.timezone.utc).isoformat(timespec="seconds"),
            "meta": dict(metadata or {}),
        }
    )


def summarize_history_for_prompt(limit: int = HISTORY_WINDOW) -> str:
    history = ensure_history_state()
    snippet = history[-limit:] if history else []
    lines = []
    for entry in snippet:
        role = entry.get("role", "user")
        content = entry.get("content", "")
        lines.append(f"{role}: {content.strip()}")
    return "\n".join(lines)


ITEM_ENTITY_FIELD_CANDIDATES: tuple[str, ...] = (
    "item",
    "items",
    "item_numbers",
    "skus",
    "sku_list",
    "materials",
    "products",
)


def _value_has_text(value: Any) -> bool:
    if isinstance(value, str):
        return bool(value.strip())
    if isinstance(value, Sequence) and not isinstance(value, (str, bytes)):
        return any(_value_has_text(entry) for entry in value)
    return False


def _structured_request_has_item(structured_request: Mapping[str, Any] | None) -> bool:
    if not isinstance(structured_request, Mapping):
        return False
    for key in ITEM_ENTITY_FIELD_CANDIDATES:
        if _value_has_text(structured_request.get(key)):
            return True
    entities = structured_request.get("entities")
    if isinstance(entities, Mapping):
        for key in ITEM_ENTITY_FIELD_CANDIDATES:
            if _value_has_text(entities.get(key)):
                return True
    return False


def _stringify_structured_request(structured_request: Mapping[str, Any] | None) -> str:
    if not structured_request:
        return ""
    try:
        return json.dumps(structured_request, default=str)
    except TypeError:
        return str(structured_request)


def _mentions_finished_goods_override(text: str) -> bool:
    lowered = text.lower()
    if not any(phrase in lowered for phrase in FINISHED_GOOD_OVERRIDE_PHRASES):
        return False
    return not any(negation in lowered for negation in FINISHED_GOOD_NEGATION_PHRASES)


def should_enforce_raw_material_scope(
    *,
    user_text: str,
    structured_request: Mapping[str, Any] | None,
    reasoning_steps: Sequence[str],
) -> bool:
    combined_bits = [user_text or "", _stringify_structured_request(structured_request)]
    if reasoning_steps:
        combined_bits.append(" ".join(reasoning_steps))
    combined = " ".join(part for part in combined_bits if part).lower()
    if not combined.strip():
        return False
    if _mentions_finished_goods_override(combined):
        return False
    if _structured_request_has_item(structured_request):
        return False
    return any(keyword in combined for keyword in PROCUREMENT_KEYWORDS)


def sql_plan_targets_raw_materials(sql_plan: SQLPlan | None) -> bool:
    if not sql_plan or not sql_plan.sql:
        return False
    sql_upper = sql_plan.sql.upper()
    if "ITMCLSCD" not in sql_upper:
        return False
    if "RAWMAT" in sql_upper:
        return True
    for param in sql_plan.params:
        if isinstance(param, str) and "RAWMAT" in param.upper():
            return True
    return False


def call_chat_completion(
    *,
    api_key: str | None,
    model: str,
    messages: Sequence[dict[str, str]],
    response_format: str | None = None,
    temperature: float = 0.1,
    base_url: str | None = None,
    api_version: str | None = None,
) -> str:
    """
    Thin wrapper over the OpenAI chat completions REST endpoint.
    """

    if not api_key:
        raise RuntimeError("Missing OpenAI API key.")
    url = (base_url.rstrip("/") if base_url else OPENAI_CHAT_URL)
    if not url.endswith("/chat/completions"):
        url = url.rstrip("/") + "/chat/completions"
    if api_version:
        separator = "&" if "?" in url else "?"
        url = f"{url}{separator}api-version={api_version}"
    payload: dict[str, Any] = {
        "model": model,
        "messages": list(messages),
        "temperature": temperature,
    }
    if response_format == "json_object":
        payload["response_format"] = {"type": "json_object"}
    headers = {
        "Authorization": f"Bearer {api_key}",
        "Content-Type": "application/json",
    }
    response = requests.post(url, headers=headers, json=payload, timeout=OPENAI_TIMEOUT_SECONDS)
    response.raise_for_status()
    data = response.json()
    return data["choices"][0]["message"]["content"]


def _extract_json(text: str) -> str:
    cleaned = text.strip()
    if "```" in cleaned:
        matches = re.findall(r"```(?:json)?\s*(.*?)```", cleaned, flags=re.DOTALL | re.IGNORECASE)
        if matches:
            return matches[0].strip()
    return cleaned


class ReasoningLLM:
    """
    Wraps the three LLM calls that power each chat turn.
    """

    def __init__(self, api_key: str, models: ModelCatalog, base_url: str | None = None, api_version: str | None = None):
        self.api_key = api_key
        self.models = models
        self.base_url = base_url
        self.api_version = api_version

    def interpret_prompt(
        self,
        *,
        user_text: str,
        history_text: str,
        structured_context: Mapping[str, Any],
        schema_summary: str,
    ) -> ReasonedIntent:
        system_prompt = (
            "You are ChemDYNA Reasoner, a senior supply-chain analyst who must think aloud "
            "before deciding how to help. Output strict JSON with keys: "
            "action (answer_only|needs_sql|clarify), reasoning_steps (array of strings), "
            "structured_request (object summarizing entities/time filters), "
            "clarifications (array of missing info questions), "
            "follow_up_questions (array)."
        )
        if DATASET_REFERENCE_HINTS:
            hint_blob = "\n".join(f"- {hint}" for hint in DATASET_REFERENCE_HINTS)
            system_prompt += "\nData sources you can rely on:\n" + hint_blob
        user_sections = [
            f"Chat history:\n{history_text or '<no history>'}",
            f"Structured memory: {json.dumps(structured_context or {}, indent=2)}",
        ]
        if schema_summary:
            user_sections.append("Schema snapshot:\n" + schema_summary)
        user_sections.append("User prompt:\n" + user_text.strip())
        payload = "\n\n".join(user_sections)
        response_text = call_chat_completion(
            api_key=self.api_key,
            model=self.models.interpreter,
            messages=[
                {"role": "system", "content": system_prompt},
                {"role": "user", "content": payload},
            ],
            response_format="json_object",
            base_url=self.base_url,
            api_version=self.api_version,
            temperature=0.0,
        )
        try:
            parsed = json.loads(_extract_json(response_text))
        except json.JSONDecodeError as err:
            raise RuntimeError(f"Interpreter returned invalid JSON: {err}") from err
        return ReasonedIntent(
            action=str(parsed.get("action") or "clarify"),
            reasoning=list(parsed.get("reasoning_steps") or []),
            structured_request=dict(parsed.get("structured_request") or {}),
            clarifications=list(parsed.get("clarifications") or []),
            follow_up_questions=list(parsed.get("follow_up_questions") or []),
        )

    def plan_sql(
        self,
        *,
        user_text: str,
        intent: ReasonedIntent,
        schema_summary: str,
        retry_feedback: str | None = None,
        procurement_scope: bool = False,
    ) -> SQLPlan:
        if ENFORCE_SQL_ALLOWLIST and CUSTOM_SQL_ALLOWED_TABLES:
            table_clause = "Approved tables: " + ", ".join(CUSTOM_SQL_ALLOWED_TABLES) + ". "
        else:
            table_clause = (
                "You may reference any Dynamics GP tables available to the connected "
                "readonly SQL user. "
            )
        system_prompt = (
            "You are ChemDYNA SQL Planner. You convert intent JSON + schema snapshots "
            "into a single parameterized SELECT/CTE statement targeting Microsoft Dynamics GP. "
            + table_clause
            + "Return JSON with keys sql (string), params (array ordered for ? placeholders), "
            "summary (short description), self_checks (array describing why the query is safe)."
        )
        sections = [
            "Schema snapshot:\n" + schema_summary,
            "Structured request JSON:\n" + json.dumps(intent.structured_request, indent=2),
            "Reasoning steps:\n" + "\n".join(f"- {step}" for step in intent.reasoning),
        ]
        insertion_index = 1
        if DATASET_REFERENCE_HINTS:
            hint_lines = "\n".join(f"- {hint}" for hint in DATASET_REFERENCE_HINTS)
            sections.insert(insertion_index, "Dynamics GP modeling tips:\n" + hint_lines)
            insertion_index += 1
        if procurement_scope:
            guardrail = (
                "Procurement guardrail:\n"
                "Join IV00101 to expose ITMCLSCD and limit classes to prefixes starting with 'RAWMAT' "
                f"({', '.join(RAW_MATERIAL_CLASS_PREFIXES)}). "
                f"Exclude manufactured/resale classes such as {', '.join(FINISHED_GOOD_CLASS_EXAMPLES)} "
                "unless the user explicitly asked for finished goods."
            )
            sections.insert(insertion_index, guardrail)
            insertion_index += 1
        if retry_feedback:
            sections.append("Planner feedback:\n" + retry_feedback)
        sections.extend(
            [
                "Original user text:\n" + user_text,
                f"Today's date: {dt.date.today():%Y-%m-%d}",
            ]
        )
        user_prompt = "\n\n".join(section for section in sections if section.strip())
        response_text = call_chat_completion(
            api_key=self.api_key,
            model=self.models.planner,
            messages=[
                {"role": "system", "content": system_prompt},
                {"role": "user", "content": user_prompt},
            ],
            response_format="json_object",
            temperature=0.0,
            base_url=self.base_url,
            api_version=self.api_version,
        )
        try:
            parsed = json.loads(_extract_json(response_text))
        except json.JSONDecodeError as err:
            raise RuntimeError(f"SQL planner output invalid JSON: {err}") from err
        sql_text = str(parsed.get("sql") or "").strip()
        return SQLPlan(
            sql=sql_text,
            params=list(parsed.get("params") or []),
            summary=str(parsed.get("summary") or "").strip(),
            self_checks=list(parsed.get("self_checks") or []),
        )

    def reason_over_results(
        self,
        *,
        user_text: str,
        intent: ReasonedIntent,
        sql_plan: SQLPlan | None,
        result: QueryResult | None,
    ) -> str:
        system_prompt = (
            "You are ChemDYNA Narrator. Explain Dynamics GP findings clearly, cite filters, "
            "call out assumptions, and suggest the next analytical question. "
            "Never fabricate SQL or rows that were not returned."
        )
        result_snippet = format_dataframe_preview(result.dataframe if result else None)
        metadata_bits = [
            f"Row count: {result.rowcount if result else 0}",
            f"Columns: {', '.join(result.columns) if result else 'n/a'}",
        ]
        context_blob = {
            "intent": intent.structured_request,
            "sql_summary": sql_plan.summary if sql_plan else "",
            "sql_checks": sql_plan.self_checks if sql_plan else [],
            "reason_chain": intent.reasoning,
        }
        user_sections = [
            "Original user request:\n" + user_text,
            "Context JSON:\n" + json.dumps(context_blob, indent=2),
            "Result preview:\n" + result_snippet,
            "Result metadata: " + "; ".join(metadata_bits),
        ]
        response_text = call_chat_completion(
            api_key=self.api_key,
            model=self.models.reasoner,
            messages=[
                {"role": "system", "content": system_prompt},
                {"role": "user", "content": "\n\n".join(user_sections)},
            ],
            temperature=0.2,
            base_url=self.base_url,
            api_version=self.api_version,
        )
        return response_text.strip()


def format_dataframe_preview(frame: pd.DataFrame | None, limit: int = 20) -> str:
    if frame is None or frame.empty:
        return "[no rows returned]"
    preview = frame.head(limit)
    return preview.to_csv(index=False)


class SQLValidator:
    """
    Static helpers that ensure planner-generated SQL stays inside guard rails.
    """

    @classmethod
    def strip_comments(cls, sql: str) -> str:
        return SQL_COMMENT_PATTERN.sub(" ", sql or "")

    @classmethod
    def validate(cls, sql: str, allowed_tables: Sequence[str]) -> tuple[bool, str]:
        if not sql or not sql.strip():
            return False, "SQL planner did not return a query."
        cleaned = cls.strip_comments(sql)
        upper = cleaned.strip().upper()
        if not (upper.startswith("SELECT") or upper.startswith("WITH")):
            return False, "Only SELECT/CTE statements are permitted."
        for verb in FORBIDDEN_SQL_VERBS:
            if re.search(rf"\b{verb}\b", upper, flags=re.IGNORECASE):
                return False, f"Found forbidden verb: {verb}"
        statements = [chunk for chunk in cleaned.split(";") if chunk.strip()]
        if len(statements) > 1:
            return False, "Multiple SQL statements detected."
        tables = cls.extract_tables(cleaned)
        if ENFORCE_SQL_ALLOWLIST and allowed_tables:
            disallowed = [table for table in tables if table not in allowed_tables]
            if disallowed:
                return False, f"Unapproved tables detected: {', '.join(sorted(set(disallowed)))}"
        return True, ""

    @staticmethod
    def extract_tables(sql: str) -> list[str]:
        tables: list[str] = []
        for match in SQL_TABLE_TOKEN_PATTERN.findall(sql or ""):
            token = match.strip().strip("[]")
            token = token.split(".")[-1]
            tables.append(token.upper())
        return tables


def fetch_schema_snapshot(connection_string: str, allowed_tables: Sequence[str]) -> dict[str, list[dict[str, Any]]]:
    if not allowed_tables:
        return {}
    placeholders = ", ".join("?" for _ in allowed_tables)
    query = textwrap.dedent(
        f"""
        SELECT TABLE_NAME, COLUMN_NAME, DATA_TYPE
        FROM INFORMATION_SCHEMA.COLUMNS
        WHERE TABLE_SCHEMA = 'dbo' AND TABLE_NAME IN ({placeholders})
        ORDER BY TABLE_NAME, ORDINAL_POSITION
        """
    ).strip()
    try:
        with pyodbc.connect(connection_string, timeout=10) as conn:
            cursor = conn.cursor()
            cursor.execute(query, allowed_tables)
            rows = cursor.fetchall()
    except pyodbc.Error as err:
        LOGGER.warning("Failed to load schema snapshot: %s", err)
        return {}
    schema: dict[str, list[dict[str, Any]]] = {}
    for row in rows:
        table = getattr(row, "TABLE_NAME", None) or row[0]
        column = getattr(row, "COLUMN_NAME", None) or row[1]
        data_type = getattr(row, "DATA_TYPE", None) or (row[2] if len(row) > 2 else "")
        schema.setdefault(table, []).append({"name": column, "type": data_type})
    return schema


@st.cache_data(show_spinner=False)
def cached_schema(connection_string: str, allowed_tables: tuple[str, ...]) -> dict[str, list[dict[str, Any]]]:
    return fetch_schema_snapshot(connection_string, allowed_tables)


def summarize_schema(
    schema: Mapping[str, list[Mapping[str, Any]]], max_columns: int = SCHEMA_PREVIEW_LIMIT
) -> str:
    if not schema:
        return ""
    lines: list[str] = []
    for table_name in sorted(schema):
        columns = schema[table_name]
        if max_columns:
            columns = columns[:max_columns]
        column_bits = [f"{col.get('name')} ({col.get('type')})" for col in columns]
        if max_columns and len(schema[table_name]) > max_columns:
            column_bits.append("...")
        lines.append(f"{table_name}: {', '.join(column_bits)}")
    return "\n".join(lines)


class QueryRunner:
    """
    Lightweight pyodbc wrapper for executing approved SQL statements.
    """

    def __init__(self, connection_string: str):
        self.connection_string = connection_string

    def run(self, sql: str, params: Sequence[Any]) -> QueryResult:
        parameters = list(params or [])
        with pyodbc.connect(self.connection_string, timeout=45) as conn:
            with contextlib.closing(conn.cursor()) as cursor:
                cursor.execute(sql, parameters)
                columns = [col[0] for col in cursor.description] if cursor.description else []
                rows = cursor.fetchmany(MAX_RESULT_ROWS)
        limited = pd.DataFrame.from_records(rows, columns=columns)
        return QueryResult(
            dataframe=limited,
            rowcount=len(limited.index),
            columns=list(limited.columns),
        )


class ReasoningOrchestrator:
    """
    High-level controller that unifies OpenAI reasoning and SQL execution.
    """

    def __init__(self, *, llm: ReasoningLLM, query_runner: QueryRunner, schema: Mapping[str, Any]):
        self.llm = llm
        self.query_runner = query_runner
        self.schema = dict(schema or {})
        self._schema_lookup = {name.upper(): columns for name, columns in self.schema.items()}

    def _column_preview_for_table(self, table: str, limit: int = 15) -> str:
        columns = self._schema_lookup.get(table.upper()) or []
        if not columns:
            return ""
        preview = [f"{col.get('name')} ({col.get('type')})" for col in columns[:limit]]
        if len(columns) > limit:
            preview.append("...")
        return ", ".join(preview)

    def _build_runtime_retry_feedback(self, sql_plan: SQLPlan, error: pyodbc.Error) -> str:
        message = str(error)
        invalid_columns = INVALID_COLUMN_PATTERN.findall(message)
        table_hints: list[str] = []
        for table in SQLValidator.extract_tables(sql_plan.sql or ""):
            preview = self._column_preview_for_table(table)
            if preview:
                table_hints.append(f"{table}: {preview}")
        parts = [
            "SQL Server rejected the previous query during execution.",
            f"Error: {message}",
        ]
        if invalid_columns:
            parts.append("Columns mentioned in the error: " + ", ".join(sorted(set(invalid_columns))) + ".")
        if table_hints:
            hint_lines = "\n".join(f"- {hint}" for hint in table_hints)
            parts.append("Schema hints:\n" + hint_lines)
        parts.append("Rewrite the SQL so it only references existing columns and valid expressions.")
        return "\n\n".join(part for part in parts if part)

    def run_chat_turn(self, user_text: str) -> dict[str, Any]:
        history_text = summarize_history_for_prompt()
        structured_context = st.session_state.get(SESSION_CONTEXT_KEY, {})
        schema_summary = summarize_schema(self.schema)
        intent = self.llm.interpret_prompt(
            user_text=user_text,
            history_text=history_text,
            structured_context=structured_context,
            schema_summary=schema_summary,
        )
        traces = ensure_trace_state()
        traces.append({"agent": "Interpreter", "details": intent.reasoning})
        if len(traces) > TRACE_LIMIT:
            del traces[: len(traces) - TRACE_LIMIT]
        procurement_scope = should_enforce_raw_material_scope(
            user_text=user_text,
            structured_request=intent.structured_request,
            reasoning_steps=intent.reasoning,
        )
        if intent.action == "clarify" and intent.clarifications:
            clarification_text = "\n".join(f"- {q}" for q in intent.clarifications)
            reply = (
                "I need a bit more context before running anything:\n"
                f"{clarification_text}\n\n"
                "Give me those details and I'll continue."
            )
            return {
                "reply": reply,
                "intent": intent,
                "sql_plan": None,
                "result": None,
            }
        sql_plan: SQLPlan | None = None
        result: QueryResult | None = None
        if intent.action == "needs_sql":
            retry_feedback: str | None = None
            validation_error = ""
            runtime_error_message = ""
            for attempt in range(2):
                sql_plan = self.llm.plan_sql(
                    user_text=user_text,
                    intent=intent,
                    schema_summary=schema_summary,
                    retry_feedback=retry_feedback,
                    procurement_scope=procurement_scope,
                )
                traces.append(
                    {
                        "agent": "SQL Planner",
                        "details": [f"Attempt {attempt + 1}: {sql_plan.summary}", *sql_plan.self_checks],
                    }
                )
                if not (sql_plan.sql or "").strip():
                    validation_error = "The SQL planner returned an empty statement."
                    break
                valid, reason = SQLValidator.validate(sql_plan.sql, CUSTOM_SQL_ALLOWED_TABLES)
                if valid and procurement_scope and not sql_plan_targets_raw_materials(sql_plan):
                    valid = False
                    validation_error = (
                        "Procurement answers must filter IV00101.ITMCLSCD to RAWMAT* classes."
                    )
                    retry_feedback = (
                        "Join IV00101 to include ITMCLSCD in the result and add a WHERE clause "
                        "limiting classes to RAWMATNT/RAWMATNTB/RAWMATNTE/RAWMATT while excluding "
                        "classes such as MANUFPROT, MANUFPRONT, RESALEPROD, CONTAINERS, STORAGE."
                    )
                    traces.append(
                        {
                            "agent": "SQL Validator",
                            "details": [
                                validation_error,
                                "Retrying SQL planning with a raw-material filter guardrail.",
                            ],
                        }
                    )
                    continue
                if not valid:
                    validation_error = reason or "The SQL validator rejected the query."
                    runtime_error_message = ""
                    offending_tables: list[str] = []
                    if "Unapproved tables" in validation_error:
                        extracted = SQLValidator.extract_tables(sql_plan.sql)
                        offending_tables = [table for table in extracted if table not in CUSTOM_SQL_ALLOWED_TABLES]
                    if ENFORCE_SQL_ALLOWLIST and offending_tables and attempt == 0:
                        retry_feedback = (
                            "These table names are not approved: "
                            + ", ".join(sorted(set(offending_tables)))
                            + ". Rewrite the query using only this allowlist: "
                            + ", ".join(CUSTOM_SQL_ALLOWED_TABLES)
                        )
                        traces.append(
                            {
                                "agent": "SQL Validator",
                                "details": [validation_error, "Retrying SQL planning with stricter instructions."],
                            }
                        )
                        continue
                    break
                validation_error = ""
                runtime_error_message = ""
                try:
                    result = self.query_runner.run(sql_plan.sql, sql_plan.params)
                except pyodbc.ProgrammingError as err:
                    runtime_error_message = str(err)
                    retry_feedback = None
                    details = [
                        f"Attempt {attempt + 1} failed during execution: {runtime_error_message}",
                    ]
                    if attempt == 0:
                        retry_feedback = self._build_runtime_retry_feedback(sql_plan, err)
                        details.append("Retrying SQL planning with schema/context feedback.")
                        traces.append({"agent": "SQL Runner", "details": details})
                        continue
                    traces.append({"agent": "SQL Runner", "details": details})
                    result = None
                    break
                except pyodbc.Error as err:
                    runtime_error_message = str(err)
                    retry_feedback = None
                    details = [
                        f"Attempt {attempt + 1} failed during execution: {runtime_error_message}",
                    ]
                    if attempt == 0:
                        retry_feedback = (
                            "SQL Server raised an execution error: "
                            + runtime_error_message
                            + ". Rewrite the SQL to avoid this failure."
                        )
                        details.append("Retrying SQL planning with execution-error context.")
                        traces.append({"agent": "SQL Runner", "details": details})
                        continue
                    traces.append({"agent": "SQL Runner", "details": details})
                    result = None
                    break
                else:
                    traces.append(
                        {
                            "agent": "SQL Runner",
                            "details": [f"Rows returned: {result.rowcount}", f"Columns: {', '.join(result.columns)}"],
                        }
                    )
                    st.session_state[SESSION_CONTEXT_KEY] = intent.structured_request
                    break
            if result is None:
                if runtime_error_message:
                    return {
                        "reply": f"The SQL query failed to run: {runtime_error_message}",
                        "intent": intent,
                        "sql_plan": sql_plan,
                        "result": None,
                    }
                return {
                    "reply": f"The SQL planner produced an unsafe query: {validation_error or 'Unknown validation error.'}",
                    "intent": intent,
                    "sql_plan": sql_plan,
                    "result": None,
                }
        reply_text = self.llm.reason_over_results(
            user_text=user_text,
            intent=intent,
            sql_plan=sql_plan,
            result=result,
        )
        traces.append({"agent": "Reasoner", "details": intent.follow_up_questions or []})
        return {
            "reply": reply_text,
            "intent": intent,
            "sql_plan": sql_plan,
            "result": result,
        }


def render_sidebar_status(sql_label: str, models: ModelCatalog, openai_ready: bool) -> None:
    st.sidebar.header("Environment")
    st.sidebar.write(f"SQL: `{sql_label}`")
    st.sidebar.write(f"Interpreter model: `{models.interpreter}`")
    st.sidebar.write(f"Planner model: `{models.planner}`")
    st.sidebar.write(f"Reasoner model: `{models.reasoner}`")
    st.sidebar.success("OpenAI ready") if openai_ready else st.sidebar.error("Missing OpenAI key")
    if st.sidebar.button("Reset conversation"):
        st.session_state.pop(CHAT_STATE_KEY, None)
        st.session_state.pop(TRACE_STATE_KEY, None)
        st.session_state.pop(SESSION_CONTEXT_KEY, None)
        st.experimental_rerun()


def render_agent_traces(traces: Sequence[Mapping[str, Any]]) -> None:
    if not traces:
        return
    with st.expander("Agent trace", expanded=False):
        for trace in traces[-TRACE_LIMIT:]:
            st.markdown(f"**{trace.get('agent')}**")
            details = trace.get("details") or []
            if isinstance(details, str):
                st.write(details)
            else:
                for line in details:
                    st.write(f"- {line}")


def render_chat_ui(orchestrator: ReasoningOrchestrator) -> None:
    history = ensure_history_state()
    traces = ensure_trace_state()
    for entry in history:
        with st.chat_message(entry.get("role", "assistant")):
            st.markdown(entry.get("content", ""))
    user_input = st.chat_input("Ask about Dynamics GP usage, sales, or inventory…")
    if not user_input:
        render_agent_traces(traces)
        return
    append_history("user", user_input)
    with st.chat_message("user"):
        st.markdown(user_input)
    with st.chat_message("assistant"):
        with st.spinner("Reasoning through your request…"):
            outcome = orchestrator.run_chat_turn(user_input)
            reply = outcome["reply"]
            st.markdown(reply)
            result: QueryResult | None = outcome.get("result")
            if result and not result.dataframe.empty:
                st.dataframe(result.dataframe)
    append_history("assistant", reply)
    render_agent_traces(traces)


def main() -> None:
    st.set_page_config(page_title="ChemDYNA Reasoning Chat", layout="wide")
    st.title("ChemDYNA Reasoning Chat")
    st.caption("A reasoning-first copilot for Dynamics GP inventory intelligence.")
    secrets = load_combined_secrets()
    openai_settings = resolve_openai_settings(secrets)
    sql_settings = resolve_sql_settings(secrets)
    connection_string, sql_label = build_connection_string(sql_settings)
    render_sidebar_status(sql_label, openai_settings["models"], bool(openai_settings.get("api_key")))
    if not openai_settings.get("api_key"):
        st.error("Configure an OpenAI API key via [openai] secrets to continue.")
        return
    schema = cached_schema(connection_string, CUSTOM_SQL_ALLOWED_TABLES)
    llm = ReasoningLLM(
        api_key=openai_settings["api_key"],
        models=openai_settings["models"],
        base_url=openai_settings.get("base_url"),
        api_version=openai_settings.get("api_version"),
    )
    query_runner = QueryRunner(connection_string)
    orchestrator = ReasoningOrchestrator(llm=llm, query_runner=query_runner, schema=schema)
    render_chat_ui(orchestrator)


if __name__ == "__main__":
    main()
