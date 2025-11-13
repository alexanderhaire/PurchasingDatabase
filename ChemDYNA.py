import calendar
import copy
import csv
import datetime
import hashlib
import hmac
import io
import json
import logging
import math
import re
import uuid
from collections.abc import Iterable, Mapping, Sequence
from decimal import Decimal
from functools import lru_cache
from numbers import Number
from pathlib import Path
from typing import Any, Callable, TypedDict

import pyodbc
import requests
import pandas as pd
import streamlit as st
from dateutil import parser as date_parser
from streamlit.errors import StreamlitAPIException, StreamlitSecretNotFoundError

try:  # Python 3.11+ includes tomllib; fall back to tomli when available.
    import tomllib
except ModuleNotFoundError:  # pragma: no cover - only triggered on older interpreters.
    try:
        import tomli as tomllib  # type: ignore
    except ModuleNotFoundError:  # pragma: no cover - tomli not installed.
        tomllib = None

# Defaults for local Windows-auth runs. Override via Streamlit secrets when hosting remotely.
APP_ROOT = Path(__file__).resolve().parent
DEFAULT_DRIVER = "ODBC Driver 17 for SQL Server"
DEFAULT_SERVER = "DynamicsGP"
DEFAULT_DATABASE = "CDI"
CHAT_HISTORY_KEY = "sql_chat_history"
CHAT_FEEDBACK_KEY = "sql_chat_feedback"
CHAT_FEEDBACK_LOG_KEY = "sql_chat_feedback_log"
CHAT_FEEDBACK_PROMPT_KEY = "sql_chat_feedback_prompt"
CHAT_SESSIONS_KEY = "sql_chat_sessions"
CHAT_ACTIVE_SESSION_KEY = "sql_chat_active_session"
CHAT_SESSION_CONTEXT_KEY = "context"
SEMANTIC_MEMORY_KEY = "sql_chat_memory"
SEMANTIC_MEMORY_MAX = 200
SEMANTIC_MEMORY_RESULTS = 3
LLM_HISTORY_WINDOW = 8  # number of literal turns to keep verbatim
HISTORY_SUMMARY_LOOKBACK = 24  # max older turns to scan when summarizing
HISTORY_SUMMARY_MAX_CONTEXT_LINES = 6
HISTORY_SUMMARY_MAX_SQL_LINES = 6
HISTORY_SUMMARY_CONTENT_LIMIT = 220
HISTORY_SUMMARY_SQL_LIMIT = 320
ITEM_TOKEN_PATTERN = re.compile(r"\b[A-Z0-9]{3,}\b")
CHAT_ITEM_STOPWORDS = {
    "SHOW",
    "COMPARE",
    "SALES",
    "SALE",
    "USAGE",
    "USAGES",
    "HEY",
    "DID",
    "FOR",
    "IN",
    "OF",
    "THE",
    "PLEASE",
    "DATA",
    "SQL",
    "ITEM",
    "ITEMS",
    "ROWS",
    "ROW",
    "AND",
    "BY",
    "WHAT",
    "WHO",
    "WHEN",
    "WHERE",
    "WHY",
    "HOW",
    "DOES",
    "DO",
    "SHOULD",
    "COULD",
    "WOULD",
    "MEAN",
    "MEANS",
    "HAS",
    "HAVE",
    "HAVING",
    "HAD",
    "WAS",
    "WERE",
    "OUR",
    "YOUR",
    "YOURS",
    "PAST",
    "OVER",
    "AVERAGE",
    "NEED",
    "NEEDS",
    "NEEDED",
    "BUY",
    "BUYS",
    "BUYING",
    "PURCHASE",
    "PURCHASES",
    "PURCHASING",
    "PURCHASED",
    "THANK",
    "THANKS",
    "ALSO",
    "CAN",
    "CANT",
    "YOU",
    "YOURSELF",
    "TURN",
    "THIS",
    "THAT",
    "THESE",
    "THOSE",
    "MAKE",
    "MAKES",
    "MAKING",
    "GRAPH",
    "GRAPHS",
    "CHART",
    "CHARTS",
    "PLOT",
    "PLOTS",
    "DRAW",
    "DRAWING",
    "CREATE",
    "CREATES",
    "CREATING",
    "BUILD",
    "BUILDING",
    "BUILT",
    "INTO",
    "AGAIN",
    "ANOTHER",
}
ITEM_PRECEDING_KEYWORDS = {
    "FOR",
    "OF",
    "ON",
    "ABOUT",
    "REGARDING",
    "REGARD",
    "WITH",
    "VERSUS",
    "VS",
    "AGAINST",
    "NEED",
    "NEEDS",
    "NEEDED",
    "ITEM",
    "ITEMS",
    "ITEMNUMBER",
    "ITEMNUMBR",
    "NUMBER",
    "CODE",
    "SKU",
    "PRODUCT",
    "MATERIAL",
    "ALSO",
    "ADD",
    "INCLUDE",
    "USING",
    "USE",
}
ITEM_FOLLOWING_KEYWORDS = {
    "USAGE",
    "USAGES",
    "DEMAND",
    "DEMANDS",
    "DATA",
    "DETAIL",
    "DETAILS",
    "REPORT",
    "REPORTS",
    "HISTORY",
    "HISTORICAL",
    "TREND",
    "AVERAGE",
    "SHORTFALL",
    "SUMMARY",
}

GRAPH_SINGLE_TOKENS: set[str] = {
    "graph",
    "graphs",
    "chart",
    "charts",
    "plot",
    "plots",
    "visual",
    "visuals",
    "visualize",
    "visualise",
    "visualized",
    "visualised",
    "visualization",
    "visualisation",
}
GRAPH_MULTI_PHRASES: tuple[str, ...] = (
    "line graph",
    "line chart",
    "bar graph",
    "bar chart",
    "trend graph",
    "trend chart",
    "graph it",
    "chart it",
    "make a graph",
    "make a chart",
    "show a graph",
    "show the graph",
)

CUSTOM_SQL_CHART_DIMENSION_KEYWORDS: tuple[str, ...] = (
    "period",
    "month",
    "date",
    "year",
    "week",
    "day",
)
CUSTOM_SQL_CHART_METRIC_KEYWORDS: tuple[str, ...] = (
    "total",
    "amount",
    "qty",
    "quantity",
    "usage",
    "units",
    "value",
    "sales",
    "revenue",
    "count",
    "cost",
    "sum",
)

MONTH_KEYWORD_TOKENS = {
    name.upper()
    for name in list(calendar.month_name)[1:]
    if name
}
MONTH_KEYWORD_TOKENS.update(
    name.upper()
    for name in list(calendar.month_abbr)[1:]
    if name
)
# Accept both SEP and SEPT spellings so month references are filtered consistently.
MONTH_KEYWORD_TOKENS.add("SEPT")

YEAR_TOKEN_SUFFIXES: tuple[str, ...] = ("S", "ST", "ND", "RD", "TH")

REORDER_ACTION_KEYWORDS: tuple[str, ...] = (
    "need to order",
    "need order",
    "need another order",
    "do we order",
    "do i order",
    "do we need to order",
    "do i need to order",
    "have to order",
    "should we order",
    "should i order",
    "order more",
    "order another",
    "order again",
    "buy more",
    "buy again",
    "need to buy",
    "need buy",
    "should we buy",
    "should i buy",
    "purchase more",
    "need to purchase",
    "restock",
    "restocking",
    "re-stock",
    "re order",
    "reorder",
    "reordering",
    "reorder list",
    "reorder report",
    "replenish",
    "replenishment",
    "stock up",
    "stockup",
    "what should we buy",
    "what should i buy",
    "what to buy",
    "what to reorder",
    "what should we reorder",
    "what should i reorder",
)

REORDER_SHORTAGE_KEYWORDS: tuple[str, ...] = (
    "running low",
    "inventory low",
    "low inventory",
    "low on",
    "low stock",
    "stock is low",
    "stock low",
    "stock getting low",
    "getting low on",
    "almost out",
    "nearly out",
    "out of stock",
    "stock out",
    "stockout",
    "shortfall",
    "shortfalls",
    "short on",
    "shortage",
    "shortages",
    "order point",
    "order-point",
    "reorder point",
    "re-order point",
    "below order point",
    "under order point",
    "below min",
    "below minimum",
    "min qty",
    "minimum qty",
    "safety stock",
    "backorder",
    "back order",
    "back-ordered",
    "need more on hand",
    "need more inventory",
)

BURN_RATE_KEYWORDS: tuple[str, ...] = (
    "burn rate",
    "burn-rate",
    "burnrate",
    "burning rate",
    "usage rate",
    "consumption rate",
)

RESET_COMMANDS = {"reset", "clear", "clear chat", "restart"}
CORRECTION_PREFIXES = ("correction:", "fix:")
CORRECTION_PROMPT_FOOTER = "If this isn’t what you meant, tell me what to fix (e.g., 'use December too' or 'wrong intent')."
OPENAI_CHAT_URL = "https://api.openai.com/v1/chat/completions"
OPENAI_DEFAULT_MODEL = "gpt-5.0"
OPENAI_TIMEOUT_SECONDS = 15
OPENAI_EMBEDDING_URL = "https://api.openai.com/v1/embeddings"
OPENAI_EMBEDDING_MODEL = "text-embedding-3-small"
REASONING_PREVIEW_ROWS = 24
REASONING_VALUE_CHAR_LIMIT = 160
REASONING_MAX_NESTING = 4
REASONING_STEP_LIMIT = 6
TRAINING_FEEDBACK_DIR = APP_ROOT / "training_feedback"
LOCAL_SECRETS_PATHS = (
    APP_ROOT / ".streamlit" / "secrets.toml",
    APP_ROOT / "secrets.toml",
)
RECENT_CORRECTION_LIMIT = 5
CHAT_EVENT_LOG_FILENAME = "chat_events.jsonl"
SELF_SIGNUP_STORE_PATH = APP_ROOT / ".streamlit" / "self_signup_users.json"
AUTH_USER_STATE_KEY = "auth_user"
AUTH_ERROR_STATE_KEY = "auth_error"
AUTH_TIMESTAMP_STATE_KEY = "auth_last_authenticated"
SELF_SIGNUP_SUCCESS_STATE_KEY = "self_signup_success"
USER_STATE_SUFFIX_DELIMITER = "__"
USER_SCOPED_STATE_BASE_KEYS = [
    CHAT_HISTORY_KEY,
    CHAT_FEEDBACK_KEY,
    CHAT_FEEDBACK_LOG_KEY,
    CHAT_FEEDBACK_PROMPT_KEY,
    CHAT_SESSIONS_KEY,
    CHAT_ACTIVE_SESSION_KEY,
    SEMANTIC_MEMORY_KEY,
]
CUSTOM_SQL_INTENT = "custom_sql"
MULTI_ITEM_INTENT = "multi_report"
ALL_ITEMS_INTENT = "all_items"
CUSTOM_SQL_MAX_ROWS = 200
CUSTOM_SQL_ALLOWED_TABLES: tuple[str, ...] = (
    "IV00101",
    "IV00102",
    "IV30200",
    "IV30300",
    "BM00101",
    "BM00111",
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
CUSTOM_SQL_HINTS: tuple[str, ...] = (
    "Inventory adjustments: IV30300 transaction detail holds TRXQTY but not DOCDATE; join IV30200 header (DOCNUMBR + DOCTYPE) to filter by DOCDATE or other header fields.",
    "Sales shipments: SOP30300 line detail holds QUANTITY/EXTDCOST but not DOCDATE; join SOP30200 header (SOPNUMBE + SOPTYPE) whenever you need DOCDATE or posting metadata.",
)
SQL_SCHEMA_CACHE_KEY = "default"
SQL_SCHEMA_CACHE: dict[str, dict[str, list[dict]]] = {}
SQL_TABLE_TOKEN_PATTERN = re.compile(r"\b(?:FROM|JOIN)\s+([A-Za-z0-9_\.\[\]]+)", re.IGNORECASE)

def _sanitize_user_fragment(value: str | None) -> str:
    if not value:
        return ""
    return re.sub(r"[^0-9a-zA-Z_-]", "_", str(value))


def _user_state_suffix(user_id: str | None) -> str:
    if not user_id:
        return ""
    return f"{USER_STATE_SUFFIX_DELIMITER}{_sanitize_user_fragment(user_id)}"


def build_user_state_key(base_key: str, user_id: str | None) -> str:
    """
    Return a Streamlit session state key uniquely namespaced per user.
    """

    return f"{base_key}{_user_state_suffix(user_id)}"


def get_authenticated_user(default: dict | None = None) -> dict | None:
    user = st.session_state.get(AUTH_USER_STATE_KEY)
    if isinstance(user, dict):
        return user
    return default


class AuthContext(TypedDict):
    registry: dict[str, dict]
    required: bool


def resolve_auth_context() -> AuthContext:
    """
    Return registry information and whether authentication must be enforced.
    """

    config = load_auth_config()
    signup_users = load_self_signup_users()
    registry = build_auth_registry(config, signup_users)
    return {
        "registry": registry,
        "required": is_authentication_required(config, registry),
    }


def get_authenticated_user_id() -> str | None:
    auth_context = resolve_auth_context()
    if auth_context["required"] and not auth_context["registry"]:
        st.title("Chemical Dynamics")
        st.error("Authentication is enabled but no users are configured. Add entries under [auth.users] in secrets.toml.")
        st.stop()

    user = get_authenticated_user()
    if not user:
        return None
    return user.get("id") or user.get("username") or user.get("email")


LOGGER = logging.getLogger(__name__)


@lru_cache(maxsize=1)
def load_project_secrets() -> dict:
    """
    Return secrets parsed from a local secrets.toml when Streamlit secrets are unavailable.
    """

    if tomllib is None:
        return {}
    for candidate in LOCAL_SECRETS_PATHS:
        try:
            with candidate.open("rb") as handle:
                parsed = tomllib.load(handle)
        except FileNotFoundError:
            continue
        except (OSError, ValueError) as err:
            LOGGER.warning("Unable to read secrets file %s: %s", candidate, err)
            continue
        if isinstance(parsed, Mapping):
            return dict(parsed)
        try:
            return {key: parsed[key] for key in parsed}
        except (KeyError, TypeError, AttributeError) as err:  # pragma: no cover - defensive guard.
            LOGGER.warning("Unexpected secrets structure in %s: %s", candidate, err)
            return {}
    return {}


def ensure_semantic_memory() -> list[dict]:
    """
    Return the semantic memory list stored in Streamlit session state.
    """

    user_id = get_authenticated_user_id()
    key = build_user_state_key(SEMANTIC_MEMORY_KEY, user_id)
    return st.session_state.setdefault(key, [])


def cosine_similarity(vec_a: Iterable[float], vec_b: Iterable[float]) -> float:
    """
    Basic cosine similarity for two equal-length vectors.
    """

    try:
        dot = sum(a * b for a, b in zip(vec_a, vec_b))
        norm_a = math.sqrt(sum(a * a for a in vec_a))
        norm_b = math.sqrt(sum(b * b for b in vec_b))
    except TypeError:
        return 0.0
    if not norm_a or not norm_b:
        return 0.0
    return dot / (norm_a * norm_b)


def get_text_embedding(text: str) -> list[float] | None:
    """
    Fetch an embedding vector for the supplied text via the OpenAI embeddings API.
    """

    if not text:
        return None
    settings = load_openai_settings()
    api_key = settings.get("api_key") if settings else None
    if not api_key:
        return None

    headers = {
        "Authorization": f"Bearer {api_key}",
        "Content-Type": "application/json",
    }
    payload = {"input": text, "model": OPENAI_EMBEDDING_MODEL}
    try:
        response = requests.post(
            OPENAI_EMBEDDING_URL,
            headers=headers,
            json=payload,
            timeout=OPENAI_TIMEOUT_SECONDS,
        )
        response.raise_for_status()
        data = response.json()
        embedding = data["data"][0]["embedding"]
        if isinstance(embedding, list):
            return embedding
    except (requests.RequestException, KeyError, json.JSONDecodeError) as err:
        LOGGER.warning("Embedding lookup failed: %s", err)
    return None


def store_semantic_memory(text: str, metadata: dict | None = None, embedding: list[float] | None = None) -> None:
    """
    Persist text + metadata into the semantic memory store.
    """

    if not text:
        return
    memory = ensure_semantic_memory()
    vector = embedding or get_text_embedding(text)
    if not vector:
        return
    entry = {
        "id": uuid.uuid4().hex,
        "text": text.strip(),
        "metadata": metadata or {},
        "embedding": vector,
        "timestamp": datetime.datetime.now(datetime.UTC).isoformat(timespec="seconds"),
    }
    memory.append(entry)
    if len(memory) > SEMANTIC_MEMORY_MAX:
        del memory[: len(memory) - SEMANTIC_MEMORY_MAX]


def retrieve_semantic_context(prompt: str, seed_entities: dict | None = None, limit: int = SEMANTIC_MEMORY_RESULTS) -> list[dict]:
    """
    Return up to `limit` prior memory entries most similar to the prompt.
    seed_entities helps filter by item/entity overlap for higher precision.
    """

    memory = ensure_semantic_memory()
    if not memory:
        return []
    embedding = get_text_embedding(prompt)
    if not embedding:
        return []

    seed_item = (seed_entities or {}).get("item")
    matches: list[tuple[float, dict]] = []
    for entry in memory:
        metadata = entry.get("metadata") or {}
        if seed_item and metadata.get("item") and metadata.get("item") != seed_item:
            continue
        entry_embedding = entry.get("embedding")
        if not isinstance(entry_embedding, list):
            continue
        score = cosine_similarity(embedding, entry_embedding)
        if score <= 0:
            continue
        matches.append((score, entry))

    matches.sort(key=lambda pair: pair[0], reverse=True)
    return [entry for _, entry in matches[:limit]]


def record_memory_entry(
    prompt: str,
    response_payload: dict,
    session_id: str | None,
    message_id: str | None,
    user_id: str | None = None,
) -> None:
    """
    Store a question/answer pair plus metadata so future prompts can recall it while preserving user attribution.
    """

    if not response_payload:
        return
    parts: list[str] = []
    if prompt:
        parts.append(f"User prompt: {prompt.strip()}")
    answer = response_payload.get("content")
    if isinstance(answer, str):
        parts.append(f"Assistant reply: {answer.strip()}")
    sql_text = response_payload.get("sql")
    if isinstance(sql_text, str):
        parts.append(f"SQL preview: {sql_text.strip()}")
    if not parts:
        return
    context = response_payload.get("context") or {}
    context = response_payload.get("context") or {}
    metadata = {
        "user_id": user_id,
        "session_id": session_id,
        "message_id": message_id,
        "intent": context.get("intent"),
        "item": context.get("item"),
        "month": context.get("month"),
        "year": context.get("year"),
        "context_type": response_payload.get("context_type"),
        "entities": context.get("entities"),
    }
    insights = context.get("insights")
    if isinstance(insights, dict) and insights:
        metadata["insights"] = insights
    row_aggregates = context.get("row_aggregates")
    if isinstance(row_aggregates, dict) and row_aggregates:
        metadata["row_aggregates"] = row_aggregates
    store_semantic_memory("\n".join(parts), metadata)


def ensure_training_feedback_dir() -> Path:
    directory = TRAINING_FEEDBACK_DIR
    directory.mkdir(parents=True, exist_ok=True)
    return directory


def _json_log_default(value: object) -> object:
    if isinstance(value, Decimal):
        return str(value)
    if isinstance(value, (datetime.datetime, datetime.date, datetime.time)):
        return value.isoformat()
    if isinstance(value, Path):
        return str(value)
    if isinstance(value, set):
        return list(value)
    if isinstance(value, bytes):
        return value.decode("utf-8", errors="replace")
    return str(value)


def _append_jsonl(filename: Path, payload: object) -> None:
    with filename.open("a", encoding="utf-8") as handle:
        handle.write(json.dumps(payload, default=_json_log_default) + "\n")


def record_correction(example: dict | None, user_id: str | None = None) -> None:
    if not isinstance(example, dict) or not example:
        return
    directory = ensure_training_feedback_dir()
    filename = directory / f"{datetime.date.today().isoformat()}.jsonl"
    payload = example.copy()
    if user_id:
        payload.setdefault("user_id", user_id)
    payload.setdefault("timestamp", datetime.datetime.now(datetime.UTC).isoformat(timespec="seconds"))
    try:
        _append_jsonl(filename, payload)
    except OSError as err:
        LOGGER.warning("Failed to record correction: %s", err)


def log_chat_event(event: dict | None) -> None:
    """
    Persist chat turns for centralized training regardless of who is signed in.
    """

    if not isinstance(event, dict) or not event:
        return
    directory = ensure_training_feedback_dir()
    filename = directory / CHAT_EVENT_LOG_FILENAME
    payload = event.copy()
    payload.setdefault("timestamp", datetime.datetime.now(datetime.UTC).isoformat(timespec="seconds"))
    try:
        _append_jsonl(filename, payload)
    except OSError as err:
        LOGGER.warning("Failed to log chat event: %s", err)


def load_recent_corrections(limit: int = RECENT_CORRECTION_LIMIT) -> list[dict]:
    if limit <= 0:
        return []
    directory = TRAINING_FEEDBACK_DIR
    if not directory.exists():
        return []
    entries: list[dict] = []
    for path in sorted(directory.glob("*.jsonl"), reverse=True):
        try:
            with path.open("r", encoding="utf-8") as handle:
                lines = handle.readlines()
        except OSError:
            continue
        for line in reversed(lines):
            cleaned = line.strip()
            if not cleaned:
                continue
            try:
                payload = json.loads(cleaned)
            except json.JSONDecodeError:
                continue
            entries.append(payload)
            if len(entries) >= limit:
                return entries
    return entries


def build_session_snapshot_from_context(context: dict | None) -> dict:
    if not isinstance(context, dict):
        return {}
    entities = context.get("entities") or {}
    snapshot = {
        "intent": context.get("intent"),
        "item": context.get("item") or entities.get("item"),
        "month": context.get("month"),
        "year": context.get("year"),
    }
    return {key: value for key, value in snapshot.items() if value is not None}


def summarize_correction_action(context: dict | None, correction_text: str | None = None) -> str:
    if not isinstance(context, dict):
        return correction_text or ""
    parts: list[str] = []
    intent = context.get("intent")
    if intent:
        parts.append(f"intent={intent}")
    item = context.get("item") or (context.get("entities") or {}).get("item")
    if item:
        parts.append(f"item={item}")
    month_val = context.get("month")
    year_val = context.get("year")
    if month_val and year_val:
        parts.append(f"month={month_val}/{year_val}")
    entities = context.get("entities") or {}
    periods = normalize_periods_list(entities.get("periods"))
    if periods:
        labels = [f"{month:02d}/{year}" for month, year in periods]
        parts.append("periods=[" + ", ".join(labels) + "]")
    comparison = normalize_periods_list(entities.get("comparison_periods"))
    if comparison:
        labels = [f"{month:02d}/{year}" for month, year in comparison]
        parts.append("comparison_periods=[" + ", ".join(labels) + "]")
    multiplier = context.get("multiplier")
    if multiplier is not None:
        parts.append(f"multiplier={multiplier}")
    if correction_text:
        parts.append(f"notes={correction_text}")
    return "; ".join(parts) if parts else (correction_text or "")


def format_correction_examples(entries: list[dict]) -> str:
    if not entries:
        return ""

    examples: list[str] = []
    for entry in entries:
        user_prompt = entry.get("user_prompt") or ""
        correct_intent = entry.get("correct_intent") or entry.get("session_snapshot", {}).get("intent") or "report"
        notes = entry.get("corrective_action") or ""
        snippet = [
            "Past correction:",
            f'User: "{user_prompt}"' if user_prompt else "User: (not captured)",
            f'Correct intent: "{correct_intent}"',
        ]
        if notes:
            snippet.append(f'Notes: "{notes}"')
        examples.append("\n".join(snippet))
    return "Recent corrections to honor:\n" + "\n\n".join(examples)


def apply_feedback_to_memory(message_id: str, direction: str, comment: str | None = None) -> None:
    """
    Update the semantic memory entry that produced the answer with user feedback.
    """

    if not message_id:
        return
    memory = ensure_semantic_memory()
    for entry in reversed(memory):
        metadata = entry.setdefault("metadata", {})
        if metadata.get("message_id") != message_id:
            continue
        metadata["feedback"] = direction
        if comment:
            metadata["feedback_comment"] = comment
        metadata["feedback_timestamp"] = datetime.datetime.now(datetime.UTC).isoformat(timespec="seconds")
        break


def ensure_chat_sessions(user_id: str | None = None) -> tuple[list[dict], dict]:
    """
    Return (all_sessions, active_session) initializing defaults if needed.
    """

    sessions_key = build_user_state_key(CHAT_SESSIONS_KEY, user_id)
    sessions = st.session_state.setdefault(sessions_key, [])
    if not sessions:
        sessions.append(
            {
                "id": uuid.uuid4().hex,
                "name": "Chat 1",
                "history": [],
                CHAT_SESSION_CONTEXT_KEY: {},
            }
        )

    active_key = build_user_state_key(CHAT_ACTIVE_SESSION_KEY, user_id)
    active_id = st.session_state.get(active_key)
    if not active_id or not any(session["id"] == active_id for session in sessions):
        active_id = sessions[0]["id"]
        st.session_state[active_key] = active_id

    active_session = next(session for session in sessions if session["id"] == active_id)
    active_session.setdefault("history", [])
    active_session.setdefault(CHAT_SESSION_CONTEXT_KEY, {})
    return sessions, active_session


def find_last_history_entry(history: list[dict], role: str) -> dict | None:
    for entry in reversed(history or []):
        if entry.get("role") == role:
            return entry
    return None


def find_prior_user_prompt(history: list[dict], anchor_id: str | None) -> str | None:
    if not history:
        return None
    anchor_index = None
    if anchor_id:
        for idx, entry in enumerate(history):
            if entry.get("id") == anchor_id:
                anchor_index = idx
                break
    if anchor_index is None:
        anchor_index = len(history)
    for idx in range(anchor_index - 1, -1, -1):
        entry = history[idx]
        if entry.get("role") == "user":
            content = entry.get("content")
            if isinstance(content, str):
                return content
    return None


def _shorten_history_text(value: str | None, limit: int) -> str:
    if not isinstance(value, str):
        return ""
    cleaned = " ".join(value.strip().split())
    if len(cleaned) <= limit:
        return cleaned
    return cleaned[: limit - 3].rstrip() + "..."


def _summarize_sql_snippet(entry: dict) -> str | None:
    sql_text = entry.get("sql")
    if not isinstance(sql_text, str) or not sql_text.strip():
        return None
    normalized_sql = " ".join(sql_text.split())
    sql_summary = _shorten_history_text(normalized_sql, HISTORY_SUMMARY_SQL_LIMIT)
    context = entry.get("context") if isinstance(entry.get("context"), dict) else {}
    context_label_parts: list[str] = []
    intent = context.get("intent")
    if isinstance(intent, str):
        context_label_parts.append(intent)
    entities = context.get("entities") if isinstance(context.get("entities"), dict) else {}
    item = context.get("item") or entities.get("item")
    if isinstance(item, str):
        context_label_parts.append(item)
    month = context.get("month")
    year = context.get("year")
    if isinstance(month, int) and isinstance(year, int) and 1 <= month <= 12:
        context_label_parts.append(f"{calendar.month_abbr[month]} {year}")
    context_label = " ".join(part for part in context_label_parts if part)
    if context_label:
        return f"{context_label}: {sql_summary}"
    return sql_summary


def _summarize_conversation_line(entry: dict) -> str | None:
    role = entry.get("role")
    if role not in {"user", "assistant"}:
        return None
    snippet = _shorten_history_text(entry.get("content"), HISTORY_SUMMARY_CONTENT_LIMIT)
    if not snippet:
        return None
    role_label = "User" if role == "user" else "Assistant"
    return f"{role_label}: {snippet}"


def summarize_older_history_entries(history: list[dict], window: int | None = None) -> dict | None:
    if window is None:
        window = LLM_HISTORY_WINDOW
    if not history or len(history) <= window:
        return None
    older_entries = history[:-window]
    if len(older_entries) > HISTORY_SUMMARY_LOOKBACK:
        older_entries = older_entries[-HISTORY_SUMMARY_LOOKBACK:]
    conversation_lines: list[str] = []
    sql_lines: list[str] = []
    for entry in older_entries:
        convo_line = _summarize_conversation_line(entry)
        if convo_line:
            conversation_lines.append(convo_line)
        sql_line = _summarize_sql_snippet(entry)
        if sql_line:
            sql_lines.append(sql_line)
    summary_parts: list[str] = []
    if conversation_lines:
        summary_parts.append(
            "Older conversation recap:\n"
            + "\n".join(f"- {line}" for line in conversation_lines[-HISTORY_SUMMARY_MAX_CONTEXT_LINES:])
        )
    if sql_lines:
        summary_parts.append(
            "Earlier SQL outputs to reuse if helpful:\n"
            + "\n".join(f"- {line}" for line in sql_lines[-HISTORY_SUMMARY_MAX_SQL_LINES:])
        )
    if not summary_parts:
        return None
    summary_text = (
        f"Context older than the most recent {window} turns has been condensed below.\n"
        + "\n\n".join(summary_parts)
    )
    return {"role": "system", "content": summary_text}


def build_history_messages_for_llm(history: list[dict], window: int | None = None) -> list[dict]:
    if window is None:
        window = LLM_HISTORY_WINDOW
    if not history:
        return []
    summary_entry = summarize_older_history_entries(history, window)
    recent_entries: list[dict] = []
    for entry in history[-window:]:
        role = entry.get("role")
        content = entry.get("content")
        if role in {"user", "assistant", "system"} and isinstance(content, str):
            combined_content = content
            if role == "assistant":
                snapshot = entry.get("llm_data_snapshot")
                if isinstance(snapshot, str):
                    snapshot_text = snapshot.strip()
                    if snapshot_text:
                        combined_content = f"{combined_content}\n\n[Data Snapshot]\n{snapshot_text}"
            recent_entries.append({"role": role, "content": combined_content})
    if summary_entry:
        return [summary_entry, *recent_entries]
    return recent_entries


def load_sql_secrets() -> dict:
    """
    Return the SQL section from Streamlit secrets, or {} when not provided.
    Missing secrets should not crash the app so local defaults remain usable.
    """

    try:
        return load_auth_feedback(st.secrets["sql"])
    except (KeyError, AttributeError, StreamlitSecretNotFoundError, TypeError):
        pass
    except (StreamlitAPIException, RuntimeError) as err:
        LOGGER.warning("Unable to load [sql] secrets: %s", err)
    return load_local_secret_section("sql")


def load_openai_settings() -> dict:
    """
    Return {'api_key': str, 'model': str} if an OpenAI key is configured.
    Accepts either [openai] blocks or top-level openai_api_key entries.
    """

    def normalize_section(section) -> dict:
        if isinstance(section, Mapping):
            return dict(section)
        try:
            return {key: section[key] for key in section}
        except (TypeError, AttributeError, KeyError):
            return {}

    openai_section: dict = {}
    try:
        openai_section = normalize_section(st.secrets["openai"])
    except (KeyError, StreamlitSecretNotFoundError, AttributeError, TypeError):
        openai_section = {}
    except (StreamlitAPIException, RuntimeError) as err:
        LOGGER.warning("Unable to load [openai] secrets: %s", err)
        openai_section = {}
    if not openai_section:
        openai_section = load_local_secret_section("openai")

    api_key = openai_section.get("api_key")
    if not api_key:
        try:
            api_key = st.secrets["openai_api_key"]
        except (KeyError, StreamlitSecretNotFoundError, AttributeError, TypeError):
            api_key = None
        except (StreamlitAPIException, RuntimeError) as err:
            LOGGER.warning("Unable to read openai_api_key secret: %s", err)
            api_key = None
        if not api_key:
            api_key = load_project_secrets().get("openai_api_key")

    if not api_key:
        return {}

    model = openai_section.get("model", OPENAI_DEFAULT_MODEL)
    sql_model = openai_section.get("sql_model") or openai_section.get("query_model")
    reasoning_model = (
        openai_section.get("reasoning_model")
        or openai_section.get("analysis_model")
        or openai_section.get("insight_model")
    )
    settings = {"api_key": api_key, "model": model}
    if sql_model:
        settings["sql_model"] = sql_model
    if reasoning_model:
        settings["reasoning_model"] = reasoning_model
    return settings


def build_connection_string() -> tuple[str, str, str, str]:
    """
    Return (connection_string, server, database, mode_description) using Streamlit secrets when provided.
    Expected secrets keys (example):
        [sql]
        server = tcp:my-sql-host,1433
        database = CDI
        authentication = sql
        username = readonly_user
        password = supersecret
    """

    secrets_config = load_sql_secrets()
    using_local_defaults = not secrets_config
    driver = secrets_config.get("driver", DEFAULT_DRIVER)
    server = secrets_config.get("server", DEFAULT_SERVER)
    database = secrets_config.get("database", DEFAULT_DATABASE)
    auth_mode = secrets_config.get("authentication", "windows").lower()

    driver_label = str(driver).lower()

    def security_clause() -> str:
        """
        Driver 18 enables encryption by default; allow local runs to disable verification unless secrets override.
        """

        encrypt_setting = secrets_config.get("encrypt")
        trust_setting = secrets_config.get("trust_server_certificate")
        if "driver 18" in driver_label:
            encrypt_setting = encrypt_setting if encrypt_setting is not None else "no"
            trust_setting = trust_setting if trust_setting is not None else "yes"
        parts: list[str] = []
        if encrypt_setting is not None:
            parts.append(f"Encrypt={encrypt_setting};")
        if trust_setting is not None:
            parts.append(f"TrustServerCertificate={trust_setting};")
        return "".join(parts)

    if auth_mode == "sql":
        username = secrets_config.get("username") or secrets_config.get("uid")
        password = secrets_config.get("password") or secrets_config.get("pwd")
        if not username or not password:
            raise RuntimeError(
                "SQL authentication requires sql.username (or sql.uid) and sql.password (or sql.pwd) secrets."
            )
        conn_str = (
            f"Driver={{{driver}}};"
            f"Server={server};"
            f"Database={database};"
            f"UID={username};PWD={password};"
            f"{security_clause()}"
        )
        return conn_str, server, database, "SQL user credentials"

    trusted_flag = secrets_config.get("trusted_connection", "yes")
    conn_str = (
        f"Driver={{{driver}}};"
        f"Server={server};"
        f"Database={database};"
        f"Trusted_Connection={trusted_flag};"
        f"{security_clause()}"
    )
    label = "Windows authentication"
    if using_local_defaults:
        label += " (local defaults)"
    return conn_str, server, database, label


def clear_user_scoped_state(user_id: str | None = None) -> None:
    """
    Remove chat-related state for the supplied user (and legacy global keys).
    """

    suffix = _user_state_suffix(user_id)
    keys_to_delete: set[str] = set()
    for base_key in USER_SCOPED_STATE_BASE_KEYS:
        if base_key in st.session_state:
            keys_to_delete.add(base_key)
        if suffix:
            namespaced_key = f"{base_key}{suffix}"
            if namespaced_key in st.session_state:
                keys_to_delete.add(namespaced_key)
    for key in keys_to_delete:
        try:
            del st.session_state[key]
        except KeyError:
            continue


def load_auth_feedback(section) -> dict:
    """
    Best-effort to convert Streamlit secrets sections into plain dictionaries.
    """

    if isinstance(section, Mapping):
        try:
            return {key: section[key] for key in section}
        except (TypeError, KeyError, AttributeError):
            return dict(section)
    try:
        return dict(section)
    except (TypeError, ValueError, AttributeError):
        return {}


def load_local_secret_section(section_name: str) -> dict:
    """
    Return a normalized dictionary for the requested section inside local secrets.toml files.
    """

    secrets_blob = load_project_secrets()
    if not secrets_blob:
        return {}
    section = secrets_blob.get(section_name)
    if not section:
        return {}
    return load_auth_feedback(section)


def load_auth_config() -> dict:
    """
    Return the [auth] section from Streamlit secrets, or {} when missing.
    """

    try:
        raw = st.secrets["auth"]
    except (KeyError, StreamlitSecretNotFoundError, AttributeError, TypeError):
        return load_local_secret_section("auth")
    except (StreamlitAPIException, RuntimeError) as err:
        LOGGER.warning("Unable to load [auth] secrets: %s", err)
        return load_local_secret_section("auth")
    return load_auth_feedback(raw)


def normalize_auth_users(config: dict) -> list[dict]:
    """
    Accept both [[auth.users]] array-of-table and [auth.users.<id>] mappings.
    """

    users_section = config.get("users")
    entries: list[dict] = []
    if isinstance(users_section, dict):
        for key, value in users_section.items():
            if not isinstance(value, dict):
                continue
            normalized = load_auth_feedback(value)
            normalized.setdefault("id", normalized.get("id") or key)
            entries.append(normalized)
    elif isinstance(users_section, list):
        for value in users_section:
            if not isinstance(value, dict):
                continue
            normalized = load_auth_feedback(value)
            if not normalized.get("id"):
                fallback = normalized.get("username") or normalized.get("email")
                if fallback:
                    normalized["id"] = fallback
            entries.append(normalized)
    elif not users_section and isinstance(config, dict):
        # Allow bare [auth.<user>] without a nested "users" key.
        for key, value in config.items():
            if key in {"enabled", "require_login"}:
                continue
            if not isinstance(value, dict):
                continue
            normalized = load_auth_feedback(value)
            normalized.setdefault("id", normalized.get("id") or key)
            entries.append(normalized)
    return entries


def build_auth_registry(config: dict, extra_users: list[dict] | None = None) -> dict[str, dict]:
    """
    Return {login_identifier: user_entry} with passwords retained for verification.
    """

    registry: dict[str, dict] = {}
    entries = normalize_auth_users(config)
    if extra_users:
        entries.extend(entry for entry in extra_users if isinstance(entry, dict))
    for entry in entries:
        password_marker = entry.get("password") or entry.get("password_hash")
        if not password_marker:
            continue
        canonical_id = entry.get("id") or entry.get("username") or entry.get("email")
        if not canonical_id:
            continue
        normalized = load_auth_feedback(entry)
        normalized["id"] = str(canonical_id)
        normalized.setdefault("name", normalized.get("username") or normalized.get("email") or normalized["id"])
        login_handles = {normalized["id"].lower()}
        username = normalized.get("username")
        if username:
            login_handles.add(str(username).lower())
        email = normalized.get("email")
        if email:
            login_handles.add(str(email).lower())
        for handle in login_handles:
            registry[handle] = normalized
    return registry


def is_authentication_required(config: dict, registry: dict[str, dict]) -> bool:
    """
    Return True when authentication must be enforced for the provided configuration.
    """

    return bool(config.get("enabled", False) or registry)


def verify_user_password(entry: dict, candidate: str) -> bool:
    if not isinstance(candidate, str) or not candidate:
        return False
    hashed = entry.get("password_hash")
    if hashed:
        digest = hashlib.sha256(candidate.encode("utf-8")).hexdigest()
        return hmac.compare_digest(str(hashed), digest)
    stored = entry.get("password")
    if stored is None:
        return False
    return hmac.compare_digest(str(stored), candidate)


def redact_user_payload(entry: dict) -> dict:
    public = {key: value for key, value in entry.items() if key not in {"password", "password_hash"}}
    public.setdefault("id", entry.get("id"))
    public.setdefault("name", entry.get("name") or entry.get("username") or entry.get("email") or entry.get("id"))
    return public


def load_self_signup_users() -> list[dict]:
    """
    Return self-service accounts stored on disk. Missing/invalid files return [].
    """

    path = SELF_SIGNUP_STORE_PATH
    if not path.exists():
        return []
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as err:
        LOGGER.warning("Unable to read self-signup users: %s", err)
        return []
    if not isinstance(data, list):
        return []
    normalized: list[dict] = []
    for entry in data:
        if isinstance(entry, dict):
            normalized.append(entry)
    return normalized


def save_self_signup_users(users: list[dict]) -> None:
    """
    Persist the provided users to disk as JSON.
    """

    try:
        SELF_SIGNUP_STORE_PATH.parent.mkdir(parents=True, exist_ok=True)
        SELF_SIGNUP_STORE_PATH.write_text(json.dumps(users, indent=2), encoding="utf-8")
    except OSError as err:
        LOGGER.warning("Unable to save self-signup users: %s", err)
        raise


def register_self_signup_user(
    work_email: str, password: str, existing_handles: set[str] | None = None
) -> dict:
    """
    Create a new credentialed user sourced from self-service signup.
    """

    email = (work_email or "").strip()
    password = (password or "").strip()
    if not email or "@" not in email:
        raise ValueError("Enter a valid work email.")
    if not password or len(password) < 8:
        raise ValueError("Password must be at least 8 characters long.")

    canonical_email = email.lower()
    username = canonical_email
    if existing_handles and canonical_email in existing_handles:
        raise ValueError("An account already exists for that email.")

    users = load_self_signup_users()
    for entry in users:
        entry_email = str(entry.get("email") or "").lower()
        if entry_email == canonical_email:
            raise ValueError("An account already exists for that email.")

    timestamp = datetime.datetime.now(datetime.UTC).isoformat(timespec="seconds")
    hashed = hashlib.sha256(password.encode("utf-8")).hexdigest()
    new_entry = {
        "id": canonical_email,
        "email": email,
        "username": username,
        "name": email,
        "password_hash": hashed,
        "created_at": timestamp,
        "created_via": "self_signup",
    }
    users.append(new_entry)
    save_self_signup_users(users)
    return new_entry


def render_self_signup_form(registry_handles: set[str], login_prefill: str | None = None) -> None:
    """
    Render an inline form that lets new users create an account with only email + password.
    """

    st.divider()
    st.caption("Need an account? Create one with your work email.")

    success_message = st.session_state.pop(SELF_SIGNUP_SUCCESS_STATE_KEY, None)
    if success_message:
        st.success(success_message)

    default_email = login_prefill if login_prefill and "@" in login_prefill else ""
    with st.form("self_signup_form"):
        signup_email = st.text_input("Work email", value=default_email)
        signup_password = st.text_input("Create a password", type="password")
        submitted = st.form_submit_button("Create account", use_container_width=True)

    if not submitted:
        return

    errors: list[str] = []
    if not signup_email.strip():
        errors.append("Work email is required.")
    elif "@" not in signup_email:
        errors.append("Enter a valid work email.")
    if not signup_password.strip():
        errors.append("Password is required.")

    if errors:
        for err in errors:
            st.error(err)
        return

    try:
        new_entry = register_self_signup_user(signup_email, signup_password, registry_handles)
    except ValueError as err:
        st.error(str(err))
        return
    except OSError:
        st.error("Unable to save your account right now. Please try again shortly.")
        return

    public_user = redact_user_payload(new_entry)
    st.session_state[AUTH_USER_STATE_KEY] = public_user
    st.session_state[AUTH_TIMESTAMP_STATE_KEY] = datetime.datetime.now(datetime.UTC).isoformat(timespec="seconds")
    st.session_state.pop(AUTH_ERROR_STATE_KEY, None)
    st.session_state[SELF_SIGNUP_SUCCESS_STATE_KEY] = "Account created! You're now signed in."
    st.rerun()


def ensure_authenticated_user() -> dict:
    """
    Return the signed-in user, prompting for credentials when required.
    """

    auth_context = resolve_auth_context()
    registry = auth_context["registry"]
    if not auth_context["required"]:
        user = get_authenticated_user()
        if user:
            return user
        guest = {"id": "anonymous", "name": "Guest"}
        st.session_state[AUTH_USER_STATE_KEY] = guest
        return guest

    user = get_authenticated_user()
    if user:
        return user

    auth_error = st.session_state.pop(AUTH_ERROR_STATE_KEY, None)
    registry_handles = set(registry.keys())
    st.title("Chemical Dynamics")
    st.subheader("Sign in to continue")
    login_value = st.text_input("Work email or username")
    password_value = st.text_input("Password", type="password")
    submit = st.button("Sign in", use_container_width=True)

    if submit:
        lookup = (login_value or "").strip().lower()
        record = registry.get(lookup)
        if record and verify_user_password(record, password_value or ""):
            public_user = redact_user_payload(record)
            previous_user = get_authenticated_user()
            previous_id = previous_user.get("id") if isinstance(previous_user, dict) else None
            if previous_id and previous_id != public_user.get("id"):
                clear_user_scoped_state(previous_id)
            st.session_state[AUTH_USER_STATE_KEY] = public_user
            st.session_state[AUTH_TIMESTAMP_STATE_KEY] = datetime.datetime.now(datetime.UTC).isoformat(timespec="seconds")
            st.session_state.pop(AUTH_ERROR_STATE_KEY, None)
            st.session_state.pop(SELF_SIGNUP_SUCCESS_STATE_KEY, None)
            st.rerun()
        else:
            st.session_state[AUTH_ERROR_STATE_KEY] = "Invalid username or password."
            st.rerun()

    if auth_error:
        st.error(auth_error)
    render_self_signup_form(registry_handles, login_value)
    st.stop()


def logout_current_user() -> None:
    user = get_authenticated_user()
    if user:
        clear_user_scoped_state(user.get("id"))
    st.session_state.pop(AUTH_USER_STATE_KEY, None)
    st.session_state.pop(AUTH_TIMESTAMP_STATE_KEY, None)
    st.session_state.pop(AUTH_ERROR_STATE_KEY, None)
    st.rerun()


def extract_item_candidates(prompt: str, limit: int = 5) -> list[str]:
    """
    Return up to limit candidate item tokens using the same priority as extract_item_code.
    """

    upper_prompt = prompt.upper()
    raw_tokens = ITEM_TOKEN_PATTERN.findall(upper_prompt)
    if not raw_tokens:
        return []

    def looks_like_month_reference(token: str) -> bool:
        return token in MONTH_KEYWORD_TOKENS

    def year_digits(token: str) -> str | None:
        if token.isdigit():
            return token
        for suffix in YEAR_TOKEN_SUFFIXES:
            if token.endswith(suffix) and token[: -len(suffix)].isdigit():
                return token[: -len(suffix)]
        return None

    def looks_like_year_reference(token: str) -> bool:
        digits = year_digits(token)
        if not digits or len(digits) != 4:
            return False
        value = int(digits)
        return 1900 <= value <= 2100

    keyword_candidates: list[str] = []
    digit_candidates: list[str] = []
    leading_candidates: list[str] = []

    def has_digit(token: str) -> bool:
        return any(char.isdigit() for char in token)

    def keyword_nearby(index: int) -> bool:
        start = max(0, index - 2)
        prev_tokens = raw_tokens[start:index]
        next_tokens = raw_tokens[index + 1 : index + 3]
        if any(token in ITEM_PRECEDING_KEYWORDS for token in prev_tokens):
            return True
        if any(token in ITEM_FOLLOWING_KEYWORDS for token in next_tokens):
            return True
        return False

    for idx, token in enumerate(raw_tokens):
        if token in CHAT_ITEM_STOPWORDS:
            continue
        if looks_like_month_reference(token):
            continue
        if looks_like_year_reference(token):
            continue
        if has_digit(token):
            digit_candidates.append(token)
            continue
        if keyword_nearby(idx):
            keyword_candidates.append(token)
            continue
        if idx == 0:
            leading_candidates.append(token)

    ordered = digit_candidates + keyword_candidates + leading_candidates
    candidates: list[str] = []
    for token in ordered:
        if token in candidates:
            continue
        candidates.append(token)
        if len(candidates) >= limit:
            break
    return candidates


def extract_item_code(prompt: str) -> str | None:
    """
    Return the first uppercase token that looks like an item number.
    """

    candidates = extract_item_candidates(prompt, limit=1)
    return candidates[0] if candidates else None


def extract_description_keywords(text: str, max_terms: int = 3) -> list[str]:
    """
    Return up to max_terms keywords from a free-form description.
    """

    tokens = re.findall(r"[A-Za-z0-9]+", text.upper())
    keywords: list[str] = []
    for token in tokens:
        if len(token) < 3:
            continue
        if token in CHAT_ITEM_STOPWORDS:
            continue
        keywords.append(token)
        if len(keywords) >= max_terms:
            break
    return keywords


def extract_multiplier(prompt: str) -> float | None:
    """
    Look for instructions such as 'multiply by 3' or 'times 1.5'.
    """

    lowered = prompt.lower()
    multiplier_pattern = re.compile(r"(?:multiply|times|x)\s*(?:by\s*)?(-?\d+(?:\.\d+)?)")
    match = multiplier_pattern.search(lowered)
    if match:
        try:
            return float(match.group(1))
        except ValueError:
            return None
    return None


CLASS_FILTER_REGEX = re.compile(
    r"\bclass(?:\s+code|\s+is|[:=])?\s*(['\"])?([A-Za-z0-9][A-Za-z0-9._-]{1,})\1?",
    flags=re.IGNORECASE,
)
BELOW_ORDER_POINT_REGEX = re.compile(
    r"(below|under|less than)\s+(?:their\s+|the\s+)?(?:re)?order\s*-?\s*points?",
    flags=re.IGNORECASE,
)
BELOW_ORDER_POINT_EXTRA_PHRASES = (
    "below reorder point",
    "below their reorder",
    "below reorder",
    "under reorder point",
    "under their reorder point",
    "under order point",
    "under the order point",
    "below order point",
    "below orderpoint",
    "under orderpoint",
)


def _clean_class_token(token: str | None) -> str | None:
    if not token:
        return None
    cleaned = token.strip().strip("\"'.,)")
    if len(cleaned) < 2:
        return None
    return cleaned.upper()


def extract_item_class_from_text(text: str | None) -> str | None:
    if not text:
        return None
    match = CLASS_FILTER_REGEX.search(text)
    if match:
        candidate = match.group(2) or match.group(1)
        cleaned = _clean_class_token(candidate)
        if cleaned:
            return cleaned
    return None


def references_below_order_point(text: str | None) -> bool:
    if not text:
        return False
    lowered = text.lower()
    if any(phrase in lowered for phrase in BELOW_ORDER_POINT_EXTRA_PHRASES):
        return True
    if BELOW_ORDER_POINT_REGEX.search(text):
        return True
    return False


def extract_inventory_filters(prompt: str, context: dict | None = None) -> dict:
    """
    Determine optional filters (class, below order point) inferred from the prompt/context.
    """

    context = context or {}
    entities = context.get("entities")
    if not isinstance(entities, dict):
        entities = {}
    entity_filters = entities.get("filters")
    if not isinstance(entity_filters, dict):
        entity_filters = {}

    class_candidate = None
    for source in (entity_filters, entities):
        for key in CLASS_ENTITY_KEYS:
            value = source.get(key)
            if isinstance(value, str) and value.strip():
                class_candidate = value.strip().upper()
                break
        if class_candidate:
            break

    text_sources: list[str] = []
    for candidate in (prompt, context.get("notes"), context.get("reply")):
        if isinstance(candidate, str) and candidate.strip():
            text_sources.append(candidate)
    for chunk in text_sources:
        if not class_candidate:
            class_candidate = extract_item_class_from_text(chunk)
        if class_candidate:
            break

    below_order_point = any(references_below_order_point(chunk) for chunk in text_sources)
    if not below_order_point:
        for key in ("below_order_point", "below_reorder_point", "below_reorder"):
            if entity_filters.get(key):
                below_order_point = True
                break
        if not below_order_point:
            order_point_state = entity_filters.get("order_point")
            if isinstance(order_point_state, str) and order_point_state.lower() in {"below", "under", "less"}:
                below_order_point = True

    return {"item_class": class_candidate, "below_order_point": below_order_point}


def resolve_item_from_context(prompt: str, context: dict | None) -> str | None:
    """
    Prefer explicit context/entity values, then fall back to token extraction.
    """

    if not context:
        return extract_item_code(prompt)
    entities = context.get("entities") or {}
    candidate = context.get("item") or entities.get("item")
    return candidate or extract_item_code(prompt)


def resolve_item_with_fallbacks(
    cursor: pyodbc.Cursor,
    prompt: str,
    context: dict | None,
    *,
    auto_select_single: bool = True,
) -> tuple[str | None, list[dict], str | None]:
    """
    Return (item_code, suggestions, assumption_note). When no explicit item is present but a single
    description match exists, optionally auto-select it so downstream SQL can proceed.
    """

    context = context or {}
    item_code = resolve_item_from_context(prompt, context)
    if item_code:
        return item_code, [], None

    suggestions = suggest_items_by_description(cursor, prompt)
    assumption_note = None
    if auto_select_single and len(suggestions) == 1:
        assumed = suggestions[0].get("Item")
        if assumed:
            item_code = assumed
            description = suggestions[0].get("Description")
            if description:
                assumption_note = f"Assuming you meant {assumed} ({description}) based on your description."
            else:
                assumption_note = f"Assuming you meant {assumed} based on your description."
            context["item"] = assumed
            existing_notes = context.get("notes")
            context["notes"] = (
                f"{existing_notes} {assumption_note}".strip() if existing_notes else assumption_note
            )
    return item_code, suggestions, assumption_note


SITE_ENTITY_KEYS = (
    "site",
    "sites",
    "location",
    "locations",
    "warehouse",
    "warehouses",
    "plant",
    "plants",
    "facility",
    "facilities",
    "loc",
    "locs",
)
SITE_VALUE_KEYS = ("code", "value", "name", "label", "site", "location", "warehouse", "plant", "facility", "id")
SITE_ALL_TOKENS = {
    "ALL",
    "ANY",
    "ALL LOCATIONS",
    "ALL SITES",
    "ALL WAREHOUSES",
    "COMPANY",
    "COMPANY WIDE",
    "COMPANYWIDE",
}
ITEM_LIST_ENTITY_KEYS = (
    "items",
    "item_list",
    "item_numbers",
    "skus",
    "sku_list",
    "materials",
    "products",
)
ITEM_VALUE_KEYS = ("item", "items", "code", "value", "number", "sku", "material", "product", "label", "id")
KEYWORD_VALUE_KEYS = ("keywords", "keyword", "value", "label", "description", "text")
CLASS_ENTITY_KEYS = (
    "item_class",
    "item_classes",
    "class_code",
    "class_codes",
    "class",
    "classes",
    "itmclscd",
    "category",
    "categories",
    "group",
    "groups",
)
CLASS_VALUE_KEYS = ("code", "value", "name", "label", "class", "item_class", "itmclscd", "category", "group")
CLASS_ALL_TOKENS = {
    "ALL",
    "ANY",
    "ALL CLASSES",
    "ALL ITEMS",
    "ALL PRODUCTS",
}


def _collect_contextual_filters(context: dict | None, candidate_keys: tuple[str, ...]) -> list:
    context = context or {}
    collected: list = []
    for key in candidate_keys:
        value = context.get(key)
        if value is not None:
            collected.append(value)
    entities = context.get("entities")
    if isinstance(entities, Mapping):
        for key in candidate_keys:
            value = entities.get(key)
            if value is not None:
                collected.append(value)
        filters_section = entities.get("filters")
        if isinstance(filters_section, Mapping):
            for key in candidate_keys:
                value = filters_section.get(key)
                if value is not None:
                    collected.append(value)
    return collected


def _flatten_filter_values(value, allowed_nested_keys: tuple[str, ...]) -> list[str]:
    if value is None:
        return []
    if isinstance(value, str):
        cleaned = value.strip()
        return [cleaned] if cleaned else []
    if isinstance(value, (list, tuple, set)):
        flattened: list[str] = []
        for entry in value:
            flattened.extend(_flatten_filter_values(entry, allowed_nested_keys))
        return flattened
    if isinstance(value, Mapping):
        flattened: list[str] = []
        matched_key = False
        for key in allowed_nested_keys:
            if key in value:
                flattened.extend(_flatten_filter_values(value[key], allowed_nested_keys))
                matched_key = True
        if not matched_key:
            for entry in value.values():
                flattened.extend(_flatten_filter_values(entry, allowed_nested_keys))
        return flattened
    return []


def _normalize_filter_tokens(values: list[str]) -> list[str]:
    normalized: list[str] = []
    seen: set[str] = set()
    for value in values:
        cleaned = value.strip()
        if not cleaned:
            continue
        token = cleaned.upper()
        if token not in seen:
            normalized.append(token)
            seen.add(token)
    return normalized


def _matches_all_token(token: str, token_set: set[str]) -> bool:
    simplified = re.sub(r"[\s_-]+", " ", token).strip()
    return simplified in token_set


def _wildcard_value(value: str) -> str:
    return value if any(char in value for char in ("%","_")) else f"%{value}%"


def resolve_site_filters(context: dict | None) -> tuple[list[str], bool, bool]:
    raw_values = _collect_contextual_filters(context, SITE_ENTITY_KEYS)
    flattened: list[str] = []
    for entry in raw_values:
        flattened.extend(_flatten_filter_values(entry, SITE_VALUE_KEYS))
    normalized = _normalize_filter_tokens(flattened)
    if not normalized:
        return ["MAIN"], False, False
    if any(_matches_all_token(token, SITE_ALL_TOKENS) for token in normalized):
        return [], True, True
    return normalized, True, False


def resolve_class_filters(context: dict | None) -> tuple[list[str], bool, bool]:
    raw_values = _collect_contextual_filters(context, CLASS_ENTITY_KEYS)
    flattened: list[str] = []
    for entry in raw_values:
        flattened.extend(_flatten_filter_values(entry, CLASS_VALUE_KEYS))
    normalized = _normalize_filter_tokens(flattened)
    if not normalized:
        return [], False, False
    if any(_matches_all_token(token, CLASS_ALL_TOKENS) for token in normalized):
        return [], True, True
    return normalized, True, False


def resolve_item_list_filters(context: dict | None) -> list[str]:
    raw_values = _collect_contextual_filters(context, ITEM_LIST_ENTITY_KEYS)
    flattened: list[str] = []
    for entry in raw_values:
        flattened.extend(_flatten_filter_values(entry, ITEM_VALUE_KEYS))
    normalized = _normalize_filter_tokens(flattened)
    return normalized


def gather_scope_keywords(prompt: str, context: dict | None, max_terms: int = 3) -> list[str]:
    keywords = extract_description_keywords(prompt, max_terms)
    entities = (context or {}).get("entities")
    if isinstance(entities, Mapping):
        for key in ("keywords", "keyword", "item_description", "description"):
            keywords.extend(_flatten_filter_values(entities.get(key), KEYWORD_VALUE_KEYS))
        filters = entities.get("filters")
        if isinstance(filters, Mapping):
            for key in ("keywords", "keyword", "description"):
                keywords.extend(_flatten_filter_values(filters.get(key), KEYWORD_VALUE_KEYS))
    seen: set[str] = set()
    normalized: list[str] = []
    for token in keywords:
        if not token:
            continue
        cleaned = str(token).strip().upper()
        if len(cleaned) < 3:
            continue
        if cleaned in seen:
            continue
        normalized.append(cleaned)
        seen.add(cleaned)
        if len(normalized) >= max_terms:
            break
    return normalized


def human_join(values: list[str]) -> str:
    cleaned = [value.strip() for value in values if isinstance(value, str) and value.strip()]
    if not cleaned:
        return ""
    if len(cleaned) == 1:
        return cleaned[0]
    if len(cleaned) == 2:
        return f"{cleaned[0]} and {cleaned[1]}"
    return ", ".join(cleaned[:-1]) + f", and {cleaned[-1]}"


def describe_site_scope(site_codes: list[str], covers_all: bool) -> str:
    if covers_all:
        return "all locations"
    if not site_codes:
        return ""
    return site_codes[0] if len(site_codes) == 1 else human_join(site_codes)


def site_error_clause(site_codes: list[str], covers_all: bool) -> str:
    label = describe_site_scope(site_codes, covers_all)
    if not label:
        return ""
    if covers_all:
        return f"across {label}"
    if len(site_codes) == 1:
        return f"at {label}"
    return f"across {label}"


def describe_class_scope(class_filters: list[str], covers_all: bool) -> str:
    if covers_all:
        return "all classes"
    if not class_filters:
        return ""
    return human_join(class_filters)


def build_scope_note(
    site_codes: list[str],
    site_explicit: bool,
    site_covers_all: bool,
    class_filters: list[str],
    class_explicit: bool,
    class_covers_all: bool,
) -> str:
    parts: list[str] = []
    site_label = describe_site_scope(site_codes, site_covers_all)
    if site_covers_all:
        parts.append("Scope spans all locations.")
    elif site_label:
        if site_explicit:
            parts.append(f"Scope limited to {site_label}.")
        else:
            parts.append(f"No site mentioned, so I defaulted to {site_label}.")
    if class_explicit:
        class_label = describe_class_scope(class_filters, class_covers_all)
        if class_label:
            if class_covers_all:
                parts.append("Included all classes per your request.")
            else:
                parts.append(f"Class filter: {class_label}.")
    return " ".join(parts).strip()


def update_session_context(session_context: dict, context: dict | None) -> None:
    """
    Persist the latest interpreted context so follow-up questions inherit it.
    """

    if not isinstance(session_context, dict) or not isinstance(context, dict):
        return
    tracked_keys = ("intent", "item", "month", "year", "multiplier", "needs_item_for_intent")
    for key in tracked_keys:
        if key not in context:
            continue
        value = context.get(key)
        if value is None:
            session_context.pop(key, None)
        else:
            session_context[key] = value
    entities = context.get("entities")
    if isinstance(entities, dict) and entities:
        session_context.setdefault("entities", {})
        session_context["entities"].update(entities)
    if "insights" in context:
        insights_value = context.get("insights")
        if isinstance(insights_value, Mapping) and insights_value:
            session_context["insights"] = insights_value
        else:
            session_context.pop("insights", None)
    if "row_aggregates" in context:
        aggregate_value = context.get("row_aggregates")
        if isinstance(aggregate_value, Mapping) and aggregate_value:
            session_context["row_aggregates"] = aggregate_value
        else:
            session_context.pop("row_aggregates", None)


SESSION_CONTEXT_SANITIZE_DEPTH = 3
SESSION_CONTEXT_MAX_COLLECTION_ITEMS = 10
SESSION_CONTEXT_MAX_MAPPING_ITEMS = 20
SESSION_CONTEXT_SAMPLE_ROWS = 5
SESSION_CONTEXT_NUMERIC_TOTAL_LIMIT = 6


def _coerce_real_number(value: Any) -> float | None:
    if isinstance(value, bool):
        return None
    if isinstance(value, Number):
        try:
            number = float(value)
        except (TypeError, ValueError, OverflowError):
            return None
        if math.isnan(number) or math.isinf(number):
            return None
        return number
    return None


def _sanitize_session_value(value: Any, depth: int = SESSION_CONTEXT_SANITIZE_DEPTH) -> Any:
    if value is None:
        return None
    if isinstance(value, (str, bool)):
        return value
    if isinstance(value, Number):
        number = _coerce_real_number(value)
        if number is None:
            return None
        if number.is_integer():
            return int(number)
        return number
    if isinstance(value, datetime.datetime):
        return value.isoformat(timespec="seconds")
    if isinstance(value, datetime.date):
        return value.isoformat()
    if depth <= 0:
        return str(value)
    if isinstance(value, Mapping):
        cleaned: dict[str, Any] = {}
        for idx, (key, entry) in enumerate(value.items()):
            if idx >= SESSION_CONTEXT_MAX_MAPPING_ITEMS:
                break
            sanitized = _sanitize_session_value(entry, depth - 1)
            if sanitized is not None:
                cleaned[str(key)] = sanitized
        return cleaned
    if isinstance(value, Iterable) and not isinstance(value, (str, bytes, bytearray)):
        cleaned_list: list[Any] = []
        for idx, entry in enumerate(value):
            if idx >= SESSION_CONTEXT_MAX_COLLECTION_ITEMS:
                break
            sanitized = _sanitize_session_value(entry, depth - 1)
            if sanitized is not None:
                cleaned_list.append(sanitized)
        return cleaned_list
    return str(value)


def sanitize_insights_for_session(insights: Mapping | None) -> dict | None:
    if not isinstance(insights, Mapping):
        return None
    cleaned = _sanitize_session_value(insights)
    if isinstance(cleaned, dict) and cleaned:
        return cleaned
    return None


def build_row_aggregates(rows: Sequence[Mapping] | None) -> dict | None:
    if rows is None or isinstance(rows, (str, bytes, bytearray)):
        return None
    if not isinstance(rows, Sequence):
        if isinstance(rows, Iterable):
            rows = list(rows)
        else:
            return None
    row_list = [row for row in rows if isinstance(row, Mapping)]
    row_count = len(rows)
    summary: dict[str, Any] = {"row_count": row_count}
    numeric_totals: dict[str, float] = {}
    for row in row_list:
        for key, value in row.items():
            number = _coerce_real_number(value)
            if number is None:
                continue
            numeric_totals[key] = numeric_totals.get(key, 0.0) + number
    if numeric_totals:
        sorted_totals = sorted(numeric_totals.items(), key=lambda pair: abs(pair[1]), reverse=True)
        summary["numeric_totals"] = {
            key: value for key, value in sorted_totals[:SESSION_CONTEXT_NUMERIC_TOTAL_LIMIT]
        }
    samples: list[dict] = []
    for row in row_list[:SESSION_CONTEXT_SAMPLE_ROWS]:
        sanitized = _sanitize_session_value(row)
        if isinstance(sanitized, dict) and sanitized:
            samples.append(sanitized)
    if samples:
        summary["sample_rows"] = samples
    if summary.get("row_count") is None and not summary.get("numeric_totals") and not summary.get("sample_rows"):
        return None
    return summary


def month_key(month: int, year: int) -> str:
    return f"{year:04d}-{month:02d}"


def normalize_periods_list(raw_periods: Iterable | None) -> list[tuple[int, int]]:
    normalized: list[tuple[int, int]] = []
    if not raw_periods:
        return normalized
    for entry in raw_periods:
        month_val = None
        year_val = None
        if isinstance(entry, dict):
            month_val = entry.get("month") or entry.get("Month")
            year_val = entry.get("year") or entry.get("Year")
        elif isinstance(entry, (list, tuple)) and len(entry) == 2:
            month_val, year_val = entry
        if month_val is None or year_val is None:
            continue
        try:
            month_int = int(month_val)
            year_int = int(year_val)
        except (TypeError, ValueError):
            continue
        if 1 <= month_int <= 12 and 1900 <= year_int <= 2100:
            normalized.append((month_int, year_int))
    return normalized


NUMBER_WORDS = {
    "one": 1,
    "two": 2,
    "three": 3,
    "four": 4,
    "five": 5,
    "six": 6,
    "seven": 7,
    "eight": 8,
    "nine": 9,
    "ten": 10,
    "eleven": 11,
    "twelve": 12,
}
ZERO_USAGE_EPSILON = 1e-4

MAX_USAGE_PERIODS = 6
GRAPH_MAX_USAGE_PERIODS = 12
DEFAULT_USAGE_HISTORY_MONTHS = 3


class UsagePeriod(TypedDict):
    label: str
    start_date: datetime.date
    end_date: datetime.date
    granularity: str
    month: int | None
    year: int


def extract_recent_month_count(text: str, max_months: int = MAX_USAGE_PERIODS) -> int | None:
    """
    Return the number of trailing months referenced by phrases such as 'past 3 months'.
    """

    if not text:
        return None
    lowered = text.lower()
    digit_match = re.search(r"(?:past|last)\s+(\d{1,2})(?:\s+months?|\s+mos?\b)", lowered)
    if digit_match:
        try:
            value = int(digit_match.group(1))
            if 1 <= value <= max_months:
                return value
        except ValueError:
            pass

    word_pattern = r"(?:past|last)\s+(" + "|".join(NUMBER_WORDS.keys()) + r")(?:\s+months?)?"
    word_match = re.search(word_pattern, lowered)
    if word_match:
        value = NUMBER_WORDS.get(word_match.group(1))
        if value and 1 <= value <= max_months:
            return value
    return None


def deduplicate_periods(periods: Iterable[tuple[int, int]] | None, limit: int = MAX_USAGE_PERIODS) -> list[tuple[int, int]]:
    """
    Preserve order while dropping invalid duplicates. Hard-cap to avoid overly broad pulls.
    """

    normalized: list[tuple[int, int]] = []
    if not periods:
        return normalized
    seen: set[str] = set()
    for entry in periods:
        if not isinstance(entry, (list, tuple)) or len(entry) != 2:
            continue
        month_val, year_val = entry
        try:
            month_int = int(month_val)
            year_int = int(year_val)
        except (TypeError, ValueError):
            continue
        if not (1 <= month_int <= 12 and 1900 <= year_int <= 2100):
            continue
        key = month_key(month_int, year_int)
        if key in seen:
            continue
        normalized.append((month_int, year_int))
        seen.add(key)
        if len(normalized) >= limit:
            break
    return normalized


def previous_month(month: int, year: int) -> tuple[int, int]:
    if month == 1:
        return 12, year - 1
    return month - 1, year


def default_comparison_periods(month: int, year: int) -> list[tuple[int, int]]:
    prev_month, prev_year = previous_month(month, year)
    return [(month, year), (prev_month, prev_year)]


def normalize_year_token(token: str, default_year: int) -> int | None:
    try:
        value = int(token)
    except (TypeError, ValueError):
        return None
    if value < 100:
        century = (default_year // 100) * 100
        value += century
        if value > default_year + 50:
            value -= 100
    if 1900 <= value <= 2100:
        return value
    return None


def extract_periods_from_prompt(prompt: str, default_year: int) -> list[tuple[int, int]]:
    """
    Return ordered month/year tuples mentioned explicitly in the prompt (e.g., "March vs April").
    """

    periods: list[tuple[int, int]] = []
    for match in MONTH_NAME_REGEX.finditer(prompt):
        name = match.group(1) or ""
        month_token = name[:3].lower()
        month_num = MONTH_NAME_LOOKUP.get(month_token)
        if not month_num:
            continue
        year_token = match.group(2)
        if year_token:
            year_val = normalize_year_token(year_token, default_year)
            if not year_val:
                continue
        else:
            year_val = default_year
        periods.append((month_num, year_val))
        if len(periods) >= 4:
            break
    return periods


def extract_year_mentions(prompt: str) -> list[int]:
    if not prompt:
        return []
    years: list[int] = []
    for match in YEAR_TOKEN_REGEX.finditer(prompt):
        token = match.group(0)
        try:
            value = int(token)
        except (TypeError, ValueError):
            continue
        if 1900 <= value <= 2100 and value not in years:
            years.append(value)
    return years


def build_month_usage_period(month: int, year: int) -> UsagePeriod:
    start_date, end_date = month_date_range(month, year)
    label = start_date.strftime("%B %Y")
    return {
        "label": label,
        "start_date": start_date,
        "end_date": end_date,
        "granularity": "month",
        "month": month,
        "year": year,
    }


def build_year_usage_period(year: int) -> UsagePeriod:
    start_date = datetime.date(year, 1, 1)
    end_date = datetime.date(year, 12, 31)
    label = f"{year} (Jan-Dec)"
    return {
        "label": label,
        "start_date": start_date,
        "end_date": end_date,
        "granularity": "year",
        "month": None,
        "year": year,
    }


def resolve_year_span_periods(prompt: str, context: dict | None, today: datetime.date) -> list[UsagePeriod]:
    years = extract_year_mentions(prompt)
    if isinstance(context, dict):
        entities = context.get("entities") or {}
        for bucket_key in ("periods", "comparison_periods"):
            bucket = entities.get(bucket_key)
            if not isinstance(bucket, Iterable) or isinstance(bucket, (str, bytes)):
                continue
            for entry in bucket:
                if not isinstance(entry, Mapping):
                    continue
                month_val = entry.get("month") or entry.get("Month")
                year_val = entry.get("year") or entry.get("Year")
                if month_val:
                    continue
                if year_val is None:
                    continue
                try:
                    year_int = int(year_val)
                except (TypeError, ValueError):
                    continue
                years.append(year_int)
        if context.get("mentions_last_year"):
            years.append(today.year - 1)
        if context.get("mentions_this_year"):
            years.append(today.year)
    normalized: list[int] = []
    for year in years:
        try:
            year_int = int(year)
        except (TypeError, ValueError):
            continue
        if not (1900 <= year_int <= 2100):
            continue
        if year_int in normalized:
            continue
        normalized.append(year_int)
        if len(normalized) >= MAX_USAGE_PERIODS:
            break
    return [build_year_usage_period(year) for year in normalized]


def determine_usage_periods(prompt: str, context: dict | None, today: datetime.date) -> list[UsagePeriod]:
    """
    Combine LLM entities, explicit prompt months, and fallbacks (including whole-year spans) to decide which periods to query.
    """

    if not isinstance(context, dict):
        month_guess, year_guess = infer_period_from_text(prompt, today)
        return [build_month_usage_period(month_guess, year_guess)]

    entities = context.get("entities") or {}
    graph_requested = bool(context.get("graph_requested"))
    period_limit = GRAPH_MAX_USAGE_PERIODS if graph_requested else MAX_USAGE_PERIODS
    entity_periods = normalize_periods_list(entities.get("periods")) or normalize_periods_list(
        entities.get("comparison_periods")
    )
    prompt_periods = context.get("prompt_periods") or []
    candidate_pairs = deduplicate_periods(entity_periods or prompt_periods, limit=period_limit)
    if candidate_pairs:
        return [build_month_usage_period(month_val, year_val) for month_val, year_val in candidate_pairs]

    year_span_periods = resolve_year_span_periods(prompt, context, today)
    if year_span_periods:
        if graph_requested:
            expanded: list[UsagePeriod] = []
            for year_period in year_span_periods:
                year_val = year_period.get("year")
                try:
                    year_int = int(year_val) if year_val is not None else None
                except (TypeError, ValueError):
                    year_int = None
                if year_int is None:
                    continue
                for month in range(1, 13):
                    expanded.append(build_month_usage_period(month, year_int))
                    if len(expanded) >= period_limit:
                        break
                if len(expanded) >= period_limit:
                    break
            if expanded:
                return expanded
        return year_span_periods[:period_limit]

    month_val = context.get("month")
    year_val = context.get("year")
    try:
        month_int = int(month_val) if month_val is not None else None
        year_int = int(year_val) if year_val is not None else None
    except (TypeError, ValueError):
        month_int = None
        year_int = None
    if not month_int or not year_int:
        month_int, year_int = infer_period_from_text(prompt, today)
    return [build_month_usage_period(month_int, year_int)]


def determine_scope_period(
    prompt: str,
    context: dict | None,
    today: datetime.date,
) -> tuple[datetime.date, datetime.date, str, list[UsagePeriod]]:
    periods = determine_usage_periods(prompt, context, today) or []
    if not periods:
        month_guess, year_guess = infer_period_from_text(prompt, today)
        periods = [build_month_usage_period(month_guess, year_guess)]
    valid_periods = [
        period
        for period in periods
        if isinstance(period.get("start_date"), datetime.date) and isinstance(period.get("end_date"), datetime.date)
    ]
    if not valid_periods:
        month_guess, year_guess = infer_period_from_text(prompt, today)
        fallback = build_month_usage_period(month_guess, year_guess)
        valid_periods = [fallback]
    start_date = min(period["start_date"] for period in valid_periods if isinstance(period["start_date"], datetime.date))
    end_date = max(period["end_date"] for period in valid_periods if isinstance(period["end_date"], datetime.date))
    if len(valid_periods) == 1:
        period_label = valid_periods[0].get("label") or start_date.strftime("%B %Y")
    else:
        first_label = valid_periods[0].get("label") or valid_periods[0]["start_date"].strftime("%B %Y")
        last_label = valid_periods[-1].get("label") or valid_periods[-1]["end_date"].strftime("%B %Y")
        period_label = f"{first_label} - {last_label}"
    return start_date, end_date, period_label, valid_periods


def suggest_items_by_description(
    cursor: pyodbc.Cursor,
    description_text: str,
    limit: int = 5,
) -> list[dict]:
    """
    Attempt to locate likely item numbers based on description keywords.
    """

    keywords = extract_description_keywords(description_text)
    if not keywords:
        return []

    conditions = " AND ".join("m.ITEMDESC LIKE ?" for _ in keywords)
    query = (
        f"SELECT TOP {limit} i.ITEMNMBR, m.ITEMDESC "
        "FROM IV00101 m "
        "JOIN IV00102 i ON i.ITEMNMBR = m.ITEMNMBR "
        f"WHERE {conditions} "
        "ORDER BY m.ITEMDESC"
    )
    params = [f"%{keyword}%" for keyword in keywords]
    cursor.execute(query, params)
    rows = cursor.fetchall()
    suggestions: list[dict] = []
    for row in rows:
        item = getattr(row, "ITEMNMBR", None)
        desc = getattr(row, "ITEMDESC", None)
        if not item:
            continue
        suggestions.append({"Item": item, "Description": desc})
    return suggestions


def format_item_suggestions(suggestions: list[dict]) -> str:
    if not suggestions:
        return ""
    formatted = []
    for entry in suggestions:
        item = entry.get("Item")
        desc = entry.get("Description")
        if item and desc:
            formatted.append(f"{item} ({desc})")
        elif item:
            formatted.append(item)
    if not formatted:
        return ""
    return "Did you mean: " + ", ".join(formatted) + "?"


def contains_word_boundary_keyword(text: str, keywords: Iterable[str]) -> bool:
    """Return True if text includes any keyword as an isolated word or phrase."""
    for keyword in keywords:
        if re.search(rf"\b{re.escape(keyword)}\b", text):
            return True
    return False


def looks_like_reorder_prompt(prompt: str, lowered: str | None = None) -> bool:
    haystack = lowered if lowered is not None else prompt.lower()
    if any(keyword in haystack for keyword in REORDER_ACTION_KEYWORDS):
        return True
    if any(keyword in haystack for keyword in REORDER_SHORTAGE_KEYWORDS):
        return True
    return False


def classify_chat_intent(prompt: str) -> str:
    lowered = prompt.lower()
    if contains_compare_language(prompt):
        if looks_like_inventory_vs_usage_prompt(prompt):
            return "inventory_usage"
        return "compare"

    drop_keywords = ("drop", "decline", "decrease", "fall", "slump", "down", "lower")
    if ("why" in lowered or "reason" in lowered) and any(keyword in lowered for keyword in drop_keywords):
        return "why_drop"

    custom_sql_keywords = (
        "purchase order",
        "purchase orders",
        "purchase history",
        "purchase quantity",
        "purchased",
        "vendor spend",
        "vendor invoice",
        "vendor history",
        "receipts",
        "receipt history",
        "po#",
        "p.o.",
    )
    if any(keyword in lowered for keyword in custom_sql_keywords):
        return CUSTOM_SQL_INTENT

    if looks_like_reorder_prompt(prompt, lowered):
        return "reorder"
    explanation_keywords = ("mean", "explain", "why", "how", "what does", "difference", "clarify", "tell me more")
    if contains_word_boundary_keyword(lowered, explanation_keywords):
        return "chitchat"

    has_item_code = bool(extract_item_code(prompt))
    data_request = contains_data_request_keywords(prompt)
    if data_request and looks_like_all_items_prompt(prompt) and not has_item_code:
        return ALL_ITEMS_INTENT
    if data_request and looks_like_multi_item_prompt(prompt):
        return MULTI_ITEM_INTENT

    if contains_sales_intent(prompt):
        return "sales"

    if contains_usage_intent(prompt):
        return "report"
    if contains_inventory_intent(prompt):
        return "inventory"
    match = ITEM_TOKEN_PATTERN.search(prompt.upper())
    if match:
        token = match.group(0)
        if token not in CHAT_ITEM_STOPWORDS:
            return "inventory"
    return "chitchat"


DATA_REQUEST_KEYWORDS: tuple[str, ...] = (
    "usage",
    "consumption",
    "consume",
    "consumed",
    "report",
    "summary",
    "table",
    "data",
    "history",
    "trend",
    "pull",
    "show",
    "display",
    "list",
    "numbers",
    "figures",
    "sales",
    "invoice",
    "invoices",
    "sold",
    "selling",
    "ship",
    "shipped",
    "shipment",
    "shipments",
    "customer order",
    "customer orders",
    "revenue",
    "use",
    "using",
    "demand",
    "forecast",
    "how much",
) + BURN_RATE_KEYWORDS

USAGE_HISTORY_KEYWORDS: tuple[str, ...] = (
    "usage",
    "usage report",
    "usage history",
    "usage summary",
    "usage trend",
    "historical usage",
    "past usage",
    "no usage",
    "zero usage",
    "not used",
    "haven't used",
    "consumption",
    "consumed",
    "consumption history",
    "consumption report",
    "demand history",
    "sales",
    "sales report",
    "sales history",
    "invoice history",
    "invoiced sales",
    "shipped",
    "shipments",
) + BURN_RATE_KEYWORDS

INVENTORY_INTENT_KEYWORDS: tuple[str, ...] = (
    "inventory",
    "on hand",
    "stock",
    "available",
    "available stock",
    "availability",
    "avail",
    "qty available",
    "order point",
    "reorder point",
    "below reorder point",
    "under reorder point",
    "safety stock",
    "qty on hand",
    "qoh",
)

USAGE_INTENT_KEYWORDS: tuple[str, ...] = (
    "usage",
    "adjust",
    "consumption",
    "report",
    "summary",
    "use",
    "using",
) + BURN_RATE_KEYWORDS

USAGE_METRIC_KEYWORDS: tuple[str, ...] = (
    "usage",
    "use",
    "using",
    "consume",
    "consumed",
    "consumption",
) + BURN_RATE_KEYWORDS

SALES_INTENT_KEYWORDS: tuple[str, ...] = (
    "sale",
    "sales",
    "sold",
    "selling",
    "invoice",
    "invoices",
    "invoiced",
    "ship",
    "shipped",
    "shipment",
    "shipments",
    "customer order",
    "customer orders",
    "customer shipment",
    "customer shipments",
)

BOM_PROMPT_KEYWORDS: tuple[str, ...] = (
    "bill of materials",
    "bill-of-materials",
    "bom",
    "bom explosion",
    "component list",
    "components of",
    "parts list",
    "what goes into",
    "what go into",
    "goes into",
    "go into",
    "made of",
    "made up of",
    "ingredients for",
    "ingredients in",
)

MULTI_ITEM_SCOPE_KEYWORDS: tuple[str, ...] = (
    "which items",
    "any items",
    "items with",
    "items that",
    "items showing",
    "item class",
    "item classes",
    "classes of items",
    "per class",
    "by class",
    "item groups",
    "product group",
    "product family",
    "material group",
    "skus with",
    "sku group",
)

ALL_ITEMS_SCOPE_KEYWORDS: tuple[str, ...] = (
    "all items",
    "every item",
    "overall items",
    "overall inventory",
    "entire catalog",
    "entire list",
    "whole catalog",
    "whole list",
    "across the board",
    "across all items",
)

ZERO_USAGE_PHRASES: tuple[str, ...] = (
    "no usage",
    "zero usage",
    "not used",
    "did not move",
    "no one used",
    "nobody used",
    "unused",
    "no consumption",
    "zero consumption",
)

PLURAL_ITEM_TOKENS: tuple[str, ...] = (
    "items",
    "skus",
    "products",
    "materials",
    "chemicals",
    "ingredients",
    "components",
)

TOTAL_SCOPE_KEYWORDS: tuple[str, ...] = (
    "total",
    "overall",
    "grand total",
    "combined",
    "all in",
    "all-in",
    "entire period",
    "whole period",
    "cumulative",
)

AVAILABLE_FIELD_KEYWORDS: tuple[str, ...] = (
    "available",
    "availability",
    "available stock",
    "avail",
    "available to promise",
    "atp",
)

ON_HAND_FIELD_KEYWORDS: tuple[str, ...] = (
    "on hand",
    "on-hand",
    "onhand",
    "physical stock",
    "physically on hand",
    "stock on hand",
)

COMPARE_KEYWORDS: tuple[str, ...] = (
    "compare",
    "compared to",
    "compared with",
    "comparing",
    "versus",
    "vs ",
    "vs.",
    "difference between",
    "diff between",
    "relative to",
    "against",
)

SMALL_TALK_PHRASES: tuple[str, ...] = (
    "hi",
    "hello",
    "hey",
    "good morning",
    "good afternoon",
    "good evening",
    "how are you",
    "how's it going",
    "how are things",
    "what's up",
    "nice to meet you",
    "pleased to meet you",
    "thank you",
    "thanks",
    "appreciate it",
)

CAPABILITY_QUESTION_PHRASES: tuple[str, ...] = (
    "what can you do",
    "what do you do",
    "what can you help with",
    "how can you help",
    "how do you help",
    "what do you support",
    "what are you able to do",
    "what are some things you can do",
    "what are some things i can ask",
    "what questions can i ask",
    "what should i ask",
)

CONCEPTUAL_QUESTION_KEYWORDS: tuple[str, ...] = (
    "what is",
    "what's",
    "what does",
    "mean",
    "meaning of",
    "definition of",
    "define",
    "explain",
    "explanation of",
    "tell me about",
    "talk me through",
    "how does",
    "why do we",
    "what do you mean by",
)

GP_CONCEPT_KNOWLEDGE: dict[str, dict[str, Any]] = {
    "reorder point": {
        "aliases": ("reorder point", "order point"),
        "definition": (
            "The stocking target for an item. It covers expected demand during supplier lead time "
            "plus whatever safety stock buffer you set."
        ),
        "context": "When Available quantity drops below the reorder point, the GP reorder report flags the shortfall.",
    },
    "reorder gap": {
        "aliases": ("reorder gap", "gap", "shortfall"),
        "definition": "The difference between the reorder point and the available quantity (Order Point - Available).",
        "context": "A positive gap is how many units you still need to buy to get back to the target level.",
    },
    "lead time": {
        "aliases": ("lead time", "lead-time", "leadtime"),
        "definition": "The number of calendar days between placing a purchase order and receiving usable stock.",
        "context": "Lead time feeds the reorder point calculation because longer lead times require covering more usage.",
    },
    "safety stock": {
        "aliases": ("safety stock", "safety inventory", "buffer stock"),
        "definition": "The extra quantity you keep on top of lead-time demand to absorb forecast or supply variability.",
        "context": "In GP it's often modeled as additional days of usage so the reorder point isn't exhausted by normal swings.",
    },
    "available quantity": {
        "aliases": ("available quantity", "qty available", "available qty", "avail"),
        "definition": "GP's Available field equals On Hand + On Order - Allocations.",
        "context": "It's the snapshot of what you can ship right now, and it's compared to the reorder point to find gaps.",
    },
}

SAMPLE_ITEM_SUGGESTIONS: tuple[str, ...] = (
    "NO3MN",
    "NO3CA12",
    "AO4ADD",
)
ITEM_FOLLOWUP_IGNORE_KEYWORDS: tuple[str, ...] = (
    "usage",
    "report",
    "summary",
    "compare",
    "comparison",
    "inventory",
    "reorder",
    "why",
    "drop",
    "decline",
    "order",
    "buy",
    "sales",
    "trend",
    "history",
    "table",
    "data",
    "show",
    "display",
)
ITEM_FOLLOWUP_WORDS: set[str] = {
    "use",
    "using",
    "its",
    "it's",
    "item",
    "sku",
    "code",
    "number",
    "same",
    "this",
    "that",
}
ITEM_FOLLOWUP_PHRASES: tuple[str, ...] = (
    "that one",
    "this one",
    "same item",
    "same one",
    "go with",
)
PENDING_ITEM_RESET_KEYWORDS: tuple[str, ...] = (
    "usage",
    "report",
    "summary",
    "compare",
    "comparison",
    "inventory",
    "reorder",
    "why",
    "drop",
    "decline",
    "order",
    "buy",
    "restock",
    "stock",
    "sales",
    "trend",
    "history",
    "table",
    "data",
)


def contains_reorder_intent(prompt: str) -> bool:
    return looks_like_reorder_prompt(prompt)


def contains_inventory_intent(prompt: str) -> bool:
    lowered = prompt.lower()
    return any(keyword in lowered for keyword in INVENTORY_INTENT_KEYWORDS)


def contains_sales_intent(prompt: str) -> bool:
    lowered = prompt.lower()
    return any(keyword in lowered for keyword in SALES_INTENT_KEYWORDS)


def contains_usage_intent(prompt: str) -> bool:
    lowered = prompt.lower()
    return any(keyword in lowered for keyword in USAGE_INTENT_KEYWORDS)


def looks_like_bom_prompt(prompt: str) -> bool:
    lowered = prompt.lower()
    return any(keyword in lowered for keyword in BOM_PROMPT_KEYWORDS)


def contains_compare_language(prompt: str) -> bool:
    lowered = prompt.lower()
    return any(keyword in lowered for keyword in COMPARE_KEYWORDS)


def looks_like_inventory_vs_usage_prompt(prompt: str) -> bool:
    """
    Identify prompts that explicitly compare availability/stock metrics to usage.
    """

    return (
        contains_compare_language(prompt)
        and contains_inventory_intent(prompt)
        and contains_usage_intent(prompt)
    )


def mentions_usage_history(prompt: str) -> bool:
    lowered = prompt.lower()
    return any(keyword in lowered for keyword in USAGE_HISTORY_KEYWORDS)


def contains_data_request_keywords(prompt: str) -> bool:
    lowered = prompt.lower()
    return any(keyword in lowered for keyword in DATA_REQUEST_KEYWORDS)


def wants_graph(prompt: str) -> bool:
    normalized = " ".join(prompt.lower().split())
    if not normalized:
        return False
    if any(phrase in normalized for phrase in GRAPH_MULTI_PHRASES):
        return True
    tokens = re.findall(r"[a-z]+", normalized)
    return any(token in GRAPH_SINGLE_TOKENS for token in tokens)


def mentions_plural_item_language(prompt: str) -> bool:
    lowered = prompt.lower()
    return any(re.search(rf"\b{re.escape(token)}\b", lowered) for token in PLURAL_ITEM_TOKENS)


def looks_like_all_items_prompt(prompt: str) -> bool:
    lowered = prompt.lower()
    if any(phrase in lowered for phrase in ALL_ITEMS_SCOPE_KEYWORDS):
        return True
    if mentions_plural_item_language(prompt) and any(phrase in lowered for phrase in ZERO_USAGE_PHRASES):
        return True
    return False


def looks_like_multi_item_prompt(prompt: str) -> bool:
    lowered = prompt.lower()
    if any(phrase in lowered for phrase in MULTI_ITEM_SCOPE_KEYWORDS):
        return True
    if mentions_plural_item_language(prompt) and any(
        trigger in lowered for trigger in ("which", "any", "list", "show", "had", "have")
    ):
        return True
    if len(extract_item_candidates(prompt, limit=3)) >= 2:
        return True
    return False


def wants_zero_usage_only(prompt: str) -> bool:
    lowered = prompt.lower()
    return any(phrase in lowered for phrase in ZERO_USAGE_PHRASES)


def looks_like_item_followup(prompt: str) -> bool:
    normalized = " ".join(prompt.lower().split())
    if not normalized:
        return False
    tokens = ITEM_TOKEN_PATTERN.findall(prompt.upper())
    valid_items = [token for token in tokens if token not in CHAT_ITEM_STOPWORDS]
    if not valid_items:
        return False
    if any(keyword in normalized for keyword in ITEM_FOLLOWUP_IGNORE_KEYWORDS):
        return False
    stripped = normalized.replace("'", " ")
    words = stripped.split()
    if len(words) <= 6:
        return True
    if ITEM_FOLLOWUP_WORDS.intersection(words):
        return True
    return any(phrase in normalized for phrase in ITEM_FOLLOWUP_PHRASES)


def looks_like_small_talk(prompt: str) -> bool:
    normalized = " ".join(prompt.lower().split())
    if not normalized:
        return False
    if contains_data_request_keywords(normalized):
        return False
    if len(normalized) > 80:
        return False
    stripped = normalized.strip(" !,.?")
    if not stripped:
        return False
    for phrase in SMALL_TALK_PHRASES:
        if stripped == phrase or stripped.startswith(f"{phrase} "):
            return True
    if len(stripped.split()) <= 6 and any(phrase in stripped for phrase in SMALL_TALK_PHRASES):
        return True
    return False


def looks_like_conceptual_question(prompt: str) -> bool:
    normalized = " ".join(prompt.lower().split())
    if not normalized:
        return False
    if any(keyword in normalized for keyword in CONCEPTUAL_QUESTION_KEYWORDS):
        return True
    # Short direct questions like "Order point?" should also be treated as conceptual.
    if normalized.endswith("?") and len(normalized.split()) <= 4:
        return True
    return False


def lookup_gp_concept(prompt: str) -> dict[str, str] | None:
    lowered = prompt.lower()
    for key, details in GP_CONCEPT_KNOWLEDGE.items():
        aliases = details.get("aliases") or (key,)
        for alias in aliases:
            if not alias:
                continue
            pattern = r"\b" + re.escape(alias.lower()) + r"\b"
            if re.search(pattern, lowered):
                definition = details.get("definition")
                if not definition:
                    continue
                label = details.get("label") or key.title()
                context = details.get("context")
                return {
                    "label": label,
                    "definition": definition,
                    "context": context or "",
                }
    return None


def describe_gp_concept(prompt: str) -> str | None:
    concept = lookup_gp_concept(prompt)
    if not concept:
        return None
    parts = [f"{concept['label']}: {concept['definition']}"]
    context = concept.get("context")
    if context:
        parts.append(context)
    return " ".join(parts).strip()


def detect_multi_intent_usage_conflict(prompt: str) -> str | None:
    """
    Return a warning message when a single prompt mixes usage/report logic with
    reorder or inventory filters that require separate SQL templates.
    """

    if not prompt:
        return None
    wants_usage = mentions_usage_history(prompt)
    if not wants_usage:
        return None
    reorder_needed = contains_reorder_intent(prompt)
    inventory_needed = contains_inventory_intent(prompt)
    if not (reorder_needed or inventory_needed):
        return None

    conflict_labels: list[str] = []
    if reorder_needed:
        conflict_labels.append("reorder")
    if inventory_needed:
        conflict_labels.append("inventory")
    conflict_text = " and ".join(conflict_labels)
    primary_view = "reorder" if reorder_needed else "inventory"
    return (
        f"You mentioned historical usage or sales along with {conflict_text} criteria, so I focused on the {primary_view} view first. "
        "Run a separate usage or sales question if you also need the historical detail table."
    )


INVENTORY_ZERO_KEY_PHRASES: tuple[str, ...] = (
    "zero on hand",
    "0 on hand",
    "no on hand",
    "zero qty on hand",
    "zero quantity on hand",
    "no inventory on hand",
    "no stock on hand",
    "zero inventory",
    "zero stock",
    "out of stock",
    "stocked out",
    "stock out",
    "stockout",
    "without stock",
    "nothing on hand",
)

INVENTORY_FILTER_ALIASES: dict[str, set[str]] = {
    "zero_on_hand": {
        "zero_on_hand",
        "zero",
        "zero_stock",
        "zero_inventory",
        "zeroonhand",
        "0_on_hand",
        "0_stock",
        "0_inventory",
        "no_on_hand",
        "no_onhand",
        "no_stock",
        "no_inventory",
        "none_on_hand",
        "none_onhand",
        "out_of_stock",
        "outofstock",
        "stockout",
        "stock_out",
        "stocked_out",
        "without_stock",
        "without_inventory",
        "empty_stock",
    }
}


def normalize_inventory_filter_value(value) -> str | None:
    """
    Normalize a free-form filter label (from entities, notes, etc.) into a canonical tag.
    """

    if value is None:
        return None
    text = str(value).strip().lower()
    if not text:
        return None
    normalized = re.sub(r"[^0-9a-z]+", "_", text).strip("_")
    for canonical, aliases in INVENTORY_FILTER_ALIASES.items():
        if normalized in aliases:
            return canonical
    return None


def _inventory_filter_from_entities(entities: Mapping | None) -> str | None:
    if not isinstance(entities, Mapping):
        return None
    filters = entities.get("filters")
    if isinstance(filters, Mapping):
        for key in ("inventory_status", "status", "inventory", "stock"):
            candidate = normalize_inventory_filter_value(filters.get(key))
            if candidate:
                return candidate
        for entry in filters.values():
            candidate = normalize_inventory_filter_value(entry)
            if candidate:
                return candidate
    for key in ("inventory_status", "inventory_filter", "stock_status", "status"):
        candidate = normalize_inventory_filter_value(entities.get(key))
        if candidate:
            return candidate
    return None


def _inventory_filter_from_text(prompt: str) -> str | None:
    normalized = " ".join(prompt.lower().split())
    if not normalized:
        return None
    if any(phrase in normalized for phrase in INVENTORY_ZERO_KEY_PHRASES):
        return "zero_on_hand"
    zero_patterns = (
        r"\b(?:zero|0|no)\s+(?:inventory|stock)\b",
        r"\b(?:zero|0|no)\s+(?:qty|quantity)\s+on\s+hand\b",
        r"\bout\s+of\s+stock\b",
        r"\bstock\s*out\b",
        r"\bstocked\s*out\b",
    )
    for pattern in zero_patterns:
        if re.search(pattern, normalized):
            return "zero_on_hand"
    return None


def detect_inventory_filter(prompt: str, context: dict | None = None) -> str | None:
    """
    Infer whether the user asked for a specific inventory filter (e.g., zero on hand).
    """

    if context and context.get("inventory_filter"):
        existing = normalize_inventory_filter_value(context["inventory_filter"])
        if existing:
            return existing
    entities = (context or {}).get("entities")
    candidate = _inventory_filter_from_entities(entities)
    if candidate:
        return candidate
    if context:
        candidate = normalize_inventory_filter_value(context.get("notes"))
        if candidate:
            return candidate
    return _inventory_filter_from_text(prompt)


def asks_about_capabilities(prompt: str) -> bool:
    normalized = " ".join(prompt.lower().split())
    if not normalized:
        return False
    return any(phrase in normalized for phrase in CAPABILITY_QUESTION_PHRASES)


def deduce_usage_report_or_sales_intent(prompt: str) -> str:
    if contains_sales_intent(prompt):
        return "sales"

    if contains_usage_intent(prompt):
        return "usage"
    return "report"


LAST_YEAR_KEYWORDS: tuple[str, ...] = (
    "last year",
    "previous year",
    "prior year",
    "same time last year",
    "year over year",
    "yoy",
    "y/y",
)

THIS_YEAR_KEYWORDS: tuple[str, ...] = ("this year", "current year", "this fiscal year")

RANGE_KEYWORDS: tuple[str, ...] = ("between", "range", "from", "through", "thru", "span")


def contains_last_year_reference(prompt: str) -> bool:
    lowered = prompt.lower()
    return any(keyword in lowered for keyword in LAST_YEAR_KEYWORDS)


def contains_this_year_reference(prompt: str) -> bool:
    lowered = prompt.lower()
    return any(keyword in lowered for keyword in THIS_YEAR_KEYWORDS)


def mentions_month_range(prompt: str) -> bool:
    if not prompt:
        return False

    lowered = prompt.lower()
    current_year = datetime.date.today().year
    month_mentions = extract_periods_from_prompt(prompt, current_year)
    month_count = len(month_mentions)
    year_mentions = extract_year_mentions(prompt)
    year_count = len(year_mentions)

    def has_multiple_time_refs() -> bool:
        if month_count >= 2:
            return True
        if month_count >= 1 and year_count >= 1:
            return True
        if year_count >= 2:
            return True
        return False

    if not has_multiple_time_refs():
        return False

    core_range_keywords = ("between", "range", "through", "thru", "span")
    if any(keyword in lowered for keyword in core_range_keywords):
        return True

    if "from" in lowered:
        return bool(re.search(r"\bfrom\b.*?(?:\bto\b|\bthrough\b|\bthru\b|-)", lowered))

    return False


def describe_month_year(month: int | None, year: int | None, fallback_year: int) -> str:
    if not month:
        return "that month"
    safe_year = year if year else fallback_year
    safe_year = max(1900, min(2100, safe_year))
    return datetime.date(safe_year, month, 1).strftime("%B %Y")


def find_recent_data_context(history: list[dict]) -> dict | None:
    """
    Return the most recent assistant context that referenced an actual data pull.
    """

    for entry in reversed(history or []):
        if entry.get("role") != "assistant":
            continue
        if entry.get("context_type") == "chitchat":
            continue
        context = entry.get("context")
        if isinstance(context, dict):
            item = context.get("item") or (context.get("entities") or {}).get("item")
            if item:
                return context
    return None


def build_question_suggestions(history: list[dict], limit: int = 3) -> list[str]:
    """
    Generate context-aware starter questions so capability prompts feel actionable.
    """

    suggestions: list[str] = []
    today = datetime.date.today()
    context = find_recent_data_context(history)
    if context:
        entities = context.get("entities") or {}
        item = context.get("item") or entities.get("item")
        if item:
            base_month = context.get("month") or entities.get("month") or today.month
            base_year = context.get("year") or entities.get("year") or today.year
            base_label = describe_month_year(base_month, base_year, today.year)
            suggestions.append(f"What was {item} usage for {base_label}?")
            prev_month, prev_year = previous_month(base_month, base_year)
            suggestions.append(
                f"Compare {item} between {base_label} and {describe_month_year(prev_month, prev_year, today.year)}."
            )
            suggestions.append(f"Why did {item} usage change after {base_label}?")
    if not suggestions:
        sample_item = SAMPLE_ITEM_SUGGESTIONS[0]
        current_label = describe_month_year(today.month, today.year, today.year)
        suggestions = [
            f"What was {sample_item} usage for {current_label}?",
            f"Compare {sample_item} with the prior month.",
            "Which items are below their reorder point right now?",
        ]
    return suggestions[:limit]


FOLLOWUP_DATA_PHRASES: tuple[str, ...] = (
    "same data",
    "that data",
    "same info",
    "that info",
    "same report",
    "that report",
    "pull that data",
    "pull the same",
    "same numbers",
    "same table",
)

THAT_VISUAL_WINDOW = 3


def _mentions_that_visualization(prompt: str, window: int = THAT_VISUAL_WINDOW) -> bool:
    tokens = re.findall(r"[a-z]+", prompt.lower())
    if not tokens or "that" not in tokens:
        return False
    for idx, token in enumerate(tokens):
        if token != "that":
            continue
        start = max(0, idx - window)
        end = min(len(tokens), idx + window + 1)
        for neighbor_index in range(start, end):
            if neighbor_index == idx:
                continue
            if tokens[neighbor_index] in GRAPH_SINGLE_TOKENS:
                return True
    return False


def references_previous_data(prompt: str) -> bool:
    lowered = prompt.lower()
    if any(phrase in lowered for phrase in FOLLOWUP_DATA_PHRASES):
        return True
    return _mentions_that_visualization(prompt)


def _format_metric_snippet(field: str, value: Any) -> str | None:
    number = _coerce_real_number(value)
    if number is None:
        return None
    lower_field = (field or "").lower()
    if "percent" in lower_field or lower_field.endswith("_pct"):
        pct_value = number * 100 if abs(number) <= 1 else number
        return f"{pct_value:+.1f}%"
    if float(number).is_integer():
        return f"{int(round(number)):,}"
    if abs(number) >= 10:
        return f"{number:,.1f}"
    return f"{number:,.2f}"


def summarize_insight_metrics(insights: Mapping | None, limit: int = 3) -> list[str]:
    if not isinstance(insights, Mapping):
        return []
    summaries: list[str] = []
    seen: set[str] = set()

    def add_field(field_name: str | None) -> None:
        if not field_name or field_name in seen:
            return
        snippet = _format_metric_snippet(field_name, insights.get(field_name))
        if snippet:
            summaries.append(f"{field_name}={snippet}")
            seen.add(field_name)

    metric_key = insights.get("metric_key")
    if isinstance(metric_key, str):
        add_field(metric_key)
    total_key = insights.get("total_metric_key")
    if isinstance(total_key, str):
        add_field(total_key)

    priority_fields = (
        "usage",
        "sales",
        "row_count",
        "zero_item_count",
        "active_item_count",
        "difference",
        "percent_change",
        "drop_amount",
        "drop_percent",
        "coverage_months",
        "multiplier",
        "scaled",
    )
    for field in priority_fields:
        add_field(field)
        if len(summaries) >= limit:
            break

    if len(summaries) < limit:
        for field in insights:
            add_field(str(field))
            if len(summaries) >= limit:
                break

    return summaries[:limit]


def summarize_row_aggregate_snapshot(aggregate: Mapping | None, limit: int = 3) -> list[str]:
    if not isinstance(aggregate, Mapping):
        return []
    parts: list[str] = []
    row_count = aggregate.get("row_count")
    row_snippet = _format_metric_snippet("rows", row_count)
    if row_snippet:
        parts.append(f"rows={row_snippet}")
    numeric_totals = aggregate.get("numeric_totals")
    if isinstance(numeric_totals, Mapping):
        for key, value in numeric_totals.items():
            snippet = _format_metric_snippet(key, value)
            if snippet:
                parts.append(f"{key}_sum={snippet}")
            if len(parts) >= limit:
                break
    return parts[:limit]


def summarize_session_context(session_context: dict | None, today: datetime.date) -> str:
    if not isinstance(session_context, dict) or not session_context:
        return ""

    pieces: list[str] = []
    intent = session_context.get("intent")
    if intent:
        pieces.append(f"intent={intent}")

    item_code = session_context.get("item")
    if item_code:
        desc = (session_context.get("entities") or {}).get("item_description")
        if desc:
            pieces.append(f"item={item_code} ({desc})")
        else:
            pieces.append(f"item={item_code}")

    month_val = session_context.get("month")
    year_val = session_context.get("year")
    if month_val and year_val:
        pieces.append(f"month={describe_month_year(month_val, year_val, today.year)}")

    multiplier = session_context.get("multiplier")
    if multiplier is not None:
        pieces.append(f"multiplier={multiplier}")

    entities = session_context.get("entities") or {}
    if entities:
        extra_bits = []
        entity_item = entities.get("item")
        if entity_item and entity_item != item_code:
            extra_bits.append(f"entity_item={entity_item}")
        entity_sites = entities.get("sites")
        if entity_sites:
            extra_bits.append(f"sites={entity_sites}")
        periods = entities.get("periods")
        if periods:
            labels = []
            for entry in normalize_periods_list(periods)[:3]:
                labels.append(describe_month_year(entry[0], entry[1], today.year))
            if labels:
                extra_bits.append("periods=" + ", ".join(labels))
        if extra_bits:
            pieces.append("entities[" + "; ".join(extra_bits) + "]")

    insight_bits = summarize_insight_metrics(session_context.get("insights"))
    if insight_bits:
        pieces.append("insights[" + "; ".join(insight_bits) + "]")
    aggregate_bits = summarize_row_aggregate_snapshot(session_context.get("row_aggregates"))
    if aggregate_bits:
        pieces.append("rows[" + "; ".join(aggregate_bits) + "]")

    return "; ".join(pieces)


INTENT_ITEM_ACTIONS: dict[str, str] = {
    "usage": "usage report",
    "report": "usage report",
    "sales": "sales report",
    "inventory": "inventory check",
    "inventory_usage": "inventory vs usage snapshot",
    "compare": "usage comparison",
    "why_drop": "drop analysis",
    MULTI_ITEM_INTENT: "multi-item summary",
    ALL_ITEMS_INTENT: "all-items summary",
}


def build_clarification_question(intent: str, context: dict, today: datetime.date) -> str | None:
    """
    Decide whether we should ask the user clarifying questions before running SQL.
    """

    action = INTENT_ITEM_ACTIONS.get(intent)
    if not action:
        return None

    prompt_has_item = bool(context.get("prompt_has_item"))
    followup_same_data = bool(context.get("followup_same_data"))
    entities = context.get("entities") or {}
    candidate_item = context.get("item") or entities.get("item")
    inventory_filter_present = intent == "inventory" and bool(context.get("inventory_filter"))
    prompt_candidates = context.get("prompt_item_candidates") or []
    unique_prompt_candidates: list[str] = []
    for token in prompt_candidates:
        if token not in unique_prompt_candidates:
            unique_prompt_candidates.append(token)

    single_item_intents = {"usage", "report", "sales", "compare", "why_drop"}
    if (
        intent in single_item_intents
        and len(unique_prompt_candidates) >= 2
        and not inventory_filter_present
    ):
        context["needs_item_for_intent"] = intent
        listed = ", ".join(unique_prompt_candidates[:3])
        if len(unique_prompt_candidates) > 3:
            listed += ", ..."
        return (
            f"I noticed multiple item numbers ({listed}). "
            f"I'm only able to run one {action} at a time, so which item should I use?"
        )

    if not candidate_item and not inventory_filter_present:
        context["needs_item_for_intent"] = intent
        return f"I'm not sure which item you mean. Before I run that {action}, which item number should I use?"
    if not prompt_has_item and candidate_item and not inventory_filter_present:
        if not followup_same_data:
            return (
                f"I'm not sure if you're still asking about {candidate_item}. "
                f"Should I keep using it for this {action}, or is there another item you have in mind?"
            )

    period_intents = {"usage", "report", "sales", "compare", MULTI_ITEM_INTENT, ALL_ITEMS_INTENT}
    if intent not in period_intents:
        return None

    period_question = build_period_clarification_question(context, today)
    if period_question:
        return period_question
    return None


def build_period_clarification_question(context: dict, today: datetime.date) -> str | None:
    period_count = context.get("prompt_period_count") or 0
    mentions_between = bool(context.get("mentions_between_months"))
    mentions_last_year = bool(context.get("mentions_last_year"))
    mentions_this_year = bool(context.get("mentions_this_year"))
    month_val = context.get("month")
    year_val = context.get("year") or today.year

    if mentions_between and period_count < 2:
        return "You mentioned a range of months. Tell me the exact start and end months you'd like me to use."

    if mentions_last_year:
        if month_val:
            current_label = describe_month_year(month_val, year_val, today.year)
            prior_label = describe_month_year(month_val, year_val - 1, today.year - 1)
            if mentions_this_year:
                return (
                    f"You mentioned both this year and last year. "
                    f"Should I compare {current_label} against {prior_label}, "
                    "or just pull last year's month as the basis? "
                    "Let me know by restating the option you want."
                )
            return (
                f"Should I pull last year's {prior_label} usage for reference, "
                f"or compare it directly with {current_label}? "
                "Please clarify which result you need."
            )
        return "You mentioned last year's usage. Which month should I use for that comparison?"

    return None


def infer_period_from_text(prompt: str, today: datetime.date) -> tuple[int, int]:
    """
    Attempt to parse a month/year from the prompt; fall back to the current month.
    """

    normalized = prompt.replace(" of ", " ")
    if isinstance(today, datetime.datetime):
        default_dt = today.replace(day=1, hour=0, minute=0, second=0, microsecond=0)
    else:
        default_dt = datetime.datetime(today.year, today.month, 1)
    try:
        parsed = date_parser.parse(normalized, fuzzy=True, default=default_dt)
        return parsed.month, parsed.year
    except (ValueError, OverflowError, TypeError):
        return today.month, today.year


def month_date_range(month: int, year: int) -> tuple[datetime.date, datetime.date]:
    _, last_day = calendar.monthrange(year, month)
    start = datetime.date(year, month, 1)
    end = datetime.date(year, month, last_day)
    return start, end


def format_sql_preview(sql: str, params: Iterable) -> str:
    """
    Render the parameterized SQL with literal values for display only.
    """

    sql_single_line = " ".join(line.strip() for line in sql.strip().splitlines())
    preview = sql_single_line
    for param in params:
        if isinstance(param, datetime.date):
            value = param.isoformat()
        else:
            value = param
        literal = f"'{value}'" if isinstance(value, str) else str(value)
        preview = preview.replace("?", literal, 1)
    return preview


def load_allowed_sql_schema(cursor: pyodbc.Cursor) -> dict[str, list[dict]]:
    """
    Fetch column metadata for whitelisted tables so the SQL generator has context.
    Results are cached for the lifetime of the process.
    """

    cached = SQL_SCHEMA_CACHE.get(SQL_SCHEMA_CACHE_KEY)
    if cached is not None:
        return cached
    if not CUSTOM_SQL_ALLOWED_TABLES:
        SQL_SCHEMA_CACHE[SQL_SCHEMA_CACHE_KEY] = {}
        return {}
    placeholders = ", ".join("?" for _ in CUSTOM_SQL_ALLOWED_TABLES)
    schema_query = (
        "SELECT TABLE_NAME, COLUMN_NAME, DATA_TYPE "
        "FROM INFORMATION_SCHEMA.COLUMNS "
        "WHERE TABLE_SCHEMA = 'dbo' AND TABLE_NAME IN (" + placeholders + ") "
        "ORDER BY TABLE_NAME, ORDINAL_POSITION"
    )
    try:
        cursor.execute(schema_query, CUSTOM_SQL_ALLOWED_TABLES)
        rows = cursor.fetchall()
    except pyodbc.Error as err:
        LOGGER.warning("Failed to load schema metadata for custom SQL: %s", err)
        SQL_SCHEMA_CACHE[SQL_SCHEMA_CACHE_KEY] = {}
        return {}

    schema: dict[str, list[dict]] = {}
    for row in rows:
        table_name = getattr(row, "TABLE_NAME", None) or (row[0] if len(row) > 0 else None)
        column_name = getattr(row, "COLUMN_NAME", None) or (row[1] if len(row) > 1 else None)
        data_type = getattr(row, "DATA_TYPE", None) or (row[2] if len(row) > 2 else None)
        if not table_name or not column_name:
            continue
        entry = {"name": column_name, "type": data_type}
        schema.setdefault(table_name, []).append(entry)
    SQL_SCHEMA_CACHE[SQL_SCHEMA_CACHE_KEY] = schema
    return schema


def summarize_schema_for_prompt(schema: dict[str, list[dict]], max_columns: int = 12) -> str:
    """
    Convert schema metadata into a compact, LLM-friendly reference block.
    """

    if not schema:
        return ""
    lines: list[str] = []
    for table_name in sorted(schema):
        columns = schema[table_name]
        preview = columns[:max_columns]
        column_bits = []
        for column in preview:
            col_name = column.get("name") or "UNKNOWN"
            data_type = column.get("type") or "unknown"
            column_bits.append(f"{col_name} ({data_type})")
        if len(columns) > max_columns:
            column_bits.append("…")
        lines.append(f"{table_name}: {', '.join(column_bits)}")
    return "\n".join(lines)


def summarize_sql_context(context: dict | None) -> str:
    """
    Build a short description of the structured intent so the SQL generator honors it.
    """

    if not isinstance(context, dict):
        return ""
    pieces: list[str] = []
    intent = context.get("intent")
    if intent:
        pieces.append(f"intent={intent}")
    item = context.get("item")
    if item:
        pieces.append(f"item={item}")
    month_val = context.get("month")
    year_val = context.get("year")
    if month_val and year_val:
        pieces.append(f"month={month_val}, year={year_val}")
    multiplier = context.get("multiplier")
    if multiplier is not None:
        pieces.append(f"multiplier={multiplier}")
    notes = context.get("notes")
    if notes:
        pieces.append(f"notes={notes}")
    entities = context.get("entities") or {}
    filters = entities.get("filters")
    if isinstance(filters, Mapping) and filters:
        pieces.append("filters=" + ", ".join(f"{key}={filters[key]}" for key in filters))
    sites = entities.get("sites")
    if sites:
        pieces.append(f"sites={sites}")
    periods = entities.get("periods")
    if periods:
        pieces.append(f"periods={periods}")
    return "; ".join(pieces)


def normalize_sql_params(raw_params) -> list:
    """
    Ensure parameters are returned as a concrete list suitable for pyodbc.
    """

    if raw_params is None:
        return []
    if isinstance(raw_params, (str, bytes)):
        return [raw_params]
    if isinstance(raw_params, Mapping):
        return [raw_params.get("value")]
    if isinstance(raw_params, Iterable):
        normalized: list = []
        for value in raw_params:
            if isinstance(value, (str, bytes, int, float)):
                normalized.append(value)
            elif isinstance(value, bool):
                normalized.append(int(value))
            elif value is None:
                normalized.append(None)
            elif isinstance(value, Mapping):
                normalized.append(value.get("value"))
            else:
                normalized.append(str(value))
        return normalized
    return [raw_params]


def _sanitize_table_token(token: str) -> str:
    cleaned = token.strip()
    if cleaned.startswith("[") and cleaned.endswith("]"):
        cleaned = cleaned[1:-1]
    if "." in cleaned:
        cleaned = cleaned.split(".")[-1]
    return cleaned.upper()


def validate_custom_sql(sql: str, allowed_tables: Iterable[str]) -> tuple[bool, str | None]:
    if not isinstance(sql, str):
        return False, "SQL plan did not return a string."
    cleaned = sql.strip()
    if not cleaned:
        return False, "SQL plan was empty."
    lowered = cleaned.lstrip().lower()
    if not (lowered.startswith("select") or lowered.startswith("with")):
        return False, "Only SELECT statements are allowed."
    upper_sql = cleaned.upper()
    forbidden = ("INSERT ", "UPDATE ", "DELETE ", "DROP ", "ALTER ", "TRUNCATE ", "MERGE ", "EXEC ", "EXECUTE ")
    for keyword in forbidden:
        if keyword in upper_sql:
            return False, f"Disallowed keyword detected ({keyword.strip()})."
    if ";" in cleaned[:-1]:
        return False, "Multiple SQL statements are not allowed."

    allowed = {name.upper() for name in allowed_tables}
    referenced: set[str] = set()
    for match in SQL_TABLE_TOKEN_PATTERN.finditer(cleaned):
        table_token = _sanitize_table_token(match.group(1))
        if not table_token:
            continue
        referenced.add(table_token)
        if allowed and table_token not in allowed:
            return False, f"Table '{table_token}' is not allowed."
    if allowed and referenced and not referenced.intersection(allowed):
        return False, "SQL must reference at least one approved table."
    return True, None


def call_openai_sql_generator(
    prompt: str,
    today: datetime.date,
    schema_summary: str,
    context_hint: str | None = None,
) -> dict | None:
    """
    Ask OpenAI to translate a free-form question into a safe, parameterized SQL query.
    """

    settings = load_openai_settings()
    api_key = settings.get("api_key")
    if not api_key:
        return None
    model = settings.get("sql_model") or settings.get("model", OPENAI_DEFAULT_MODEL)
    system_prompt = (
        "You convert natural-language supply-chain questions into safe, read-only T-SQL for Microsoft Dynamics GP. "
        "Always return JSON with keys: sql (string), params (array), summary (string). "
        "Rules: only SELECT/CTE statements, no DDL/DML, no temp tables, no multiple statements, "
        "only reference the provided tables, and prefer parameter placeholders (?) over literal user values. "
        f"Limit results to at most {CUSTOM_SQL_MAX_ROWS} rows using TOP or FILTER logic when reasonable."
    )
    user_sections = [
        f"Current date: {today.isoformat()}",
        "Approved tables: " + ", ".join(CUSTOM_SQL_ALLOWED_TABLES),
    ]
    if schema_summary:
        user_sections.append("Schema reference:\n" + schema_summary)
    if CUSTOM_SQL_HINTS:
        hint_lines = "\n".join(f"- {hint}" for hint in CUSTOM_SQL_HINTS)
        user_sections.append("Dynamics GP modeling tips:\n" + hint_lines)
    if context_hint:
        user_sections.append(f"Structured context: {context_hint}")
    user_sections.append("User question:\n" + prompt.strip())
    user_sections.append(
        "Respond with JSON only. Params must align with each ? placeholder. "
        "Set summary to a short human-readable description of what the SQL returns."
    )
    user_prompt = "\n\n".join(section for section in user_sections if section)
    payload = {
        "model": model,
        "temperature": 0.0,
        "messages": [
            {"role": "system", "content": system_prompt},
            {"role": "user", "content": user_prompt},
        ],
        "response_format": {"type": "json_object"},
    }
    headers = {"Authorization": f"Bearer {api_key}", "Content-Type": "application/json"}
    try:
        response = requests.post(
            OPENAI_CHAT_URL,
            headers=headers,
            json=payload,
            timeout=OPENAI_TIMEOUT_SECONDS,
        )
        response.raise_for_status()
        data = response.json()
        content = data["choices"][0]["message"]["content"]
        json_text = _extract_json_block(content)
        return json.loads(json_text)
    except (requests.RequestException, KeyError, json.JSONDecodeError) as err:
        LOGGER.warning("OpenAI SQL generation failed: %s", err)
        return None


def _extract_json_block(text: str) -> str:
    cleaned = text.strip()
    if "```" in cleaned:
        fence_match = re.findall(r"```(?:json)?\s*(.*?)```", cleaned, flags=re.DOTALL | re.IGNORECASE)
        if fence_match:
            return fence_match[0].strip()
    return cleaned


def _truncate_reasoner_text(value: str) -> str:
    trimmed = value.strip()
    if len(trimmed) <= REASONING_VALUE_CHAR_LIMIT:
        return trimmed
    return trimmed[: REASONING_VALUE_CHAR_LIMIT - 3].rstrip() + "..."


def _reasoner_safe_value(value, depth: int = 0):
    if value is None or depth > REASONING_MAX_NESTING:
        return None
    if isinstance(value, Mapping):
        safe: dict[str, object] = {}
        for key, inner in value.items():
            safe_inner = _reasoner_safe_value(inner, depth + 1)
            if safe_inner is not None:
                safe[str(key)] = safe_inner
        return safe or None
    if isinstance(value, Sequence) and not isinstance(value, (str, bytes, bytearray)):
        safe_items: list[object] = []
        for index, inner in enumerate(value):
            if index >= REASONING_PREVIEW_ROWS:
                break
            safe_inner = _reasoner_safe_value(inner, depth + 1)
            if safe_inner is not None:
                safe_items.append(safe_inner)
        return safe_items or None
    coerced = _coerce_snapshot_value(value)
    if isinstance(coerced, str):
        trimmed = coerced.strip()
        if not trimmed:
            return None
        return _truncate_reasoner_text(trimmed)
    return coerced


def _reasoner_preview_rows(rows: object) -> list[object]:
    if not isinstance(rows, Sequence) or isinstance(rows, (str, bytes, bytearray)):
        return []
    preview: list[object] = []
    for row in rows:
        if len(preview) >= REASONING_PREVIEW_ROWS:
            break
        safe_row = _reasoner_safe_value(row)
        if safe_row is not None:
            preview.append(safe_row)
    return preview


def call_openai_reasoner(
    prompt: str,
    today: datetime.date,
    context: Mapping | None,
    sql_payload: Mapping | None,
) -> dict | None:
    if not sql_payload:
        return None
    settings = load_openai_settings()
    api_key = settings.get("api_key") if settings else None
    if not api_key:
        return None
    data_preview = _reasoner_preview_rows(sql_payload.get("data"))
    insights_snapshot = _reasoner_safe_value(sql_payload.get("insights"))
    row_snapshot = _reasoner_safe_value((context or {}).get("row_aggregates"))
    if not any([data_preview, insights_snapshot, row_snapshot]):
        return None
    entity_snapshot = _reasoner_safe_value((context or {}).get("entities"))
    question_text = prompt.strip() if isinstance(prompt, str) else ""
    reasoner_payload = {
        "question": question_text,
        "intent": (context or {}).get("intent"),
        "item": (context or {}).get("item"),
        "notes": (context or {}).get("notes"),
        "entities": entity_snapshot,
        "insights": insights_snapshot,
        "row_aggregates": row_snapshot,
        "data_preview": data_preview,
        "sql": sql_payload.get("sql"),
        "chart_caption": sql_payload.get("chart_caption"),
        "chart_warning": sql_payload.get("chart_warning"),
        "today": today.isoformat(),
    }
    structured_blob = _snapshot_json(reasoner_payload)
    model = settings.get("reasoning_model") or settings.get("model", OPENAI_DEFAULT_MODEL)
    system_prompt = (
        "You are an expert supply-planning analyst. "
        "Use the provided SQL findings to think through the problem in multiple steps before responding. "
        "Cite the evidence in each step and keep conclusions grounded in the supplied data."
    )
    user_prompt = (
        "Original user question:\n"
        f"{question_text}\n\n"
        "Structured findings:\n"
        f"{structured_blob}\n\n"
        "Return JSON with keys: steps (array), conclusion (string), confidence (string)."
    )
    payload = {
        "model": model,
        "temperature": 0.1,
        "messages": [
            {"role": "system", "content": system_prompt},
            {"role": "user", "content": user_prompt},
        ],
        "response_format": {"type": "json_object"},
    }
    headers = {
        "Authorization": f"Bearer {api_key}",
        "Content-Type": "application/json",
    }
    try:
        response = requests.post(
            OPENAI_CHAT_URL,
            headers=headers,
            json=payload,
            timeout=OPENAI_TIMEOUT_SECONDS,
        )
        response.raise_for_status()
        data = response.json()
        content = data["choices"][0]["message"]["content"]
        json_text = _extract_json_block(content)
        parsed = json.loads(json_text)
    except (requests.RequestException, KeyError, json.JSONDecodeError) as err:
        LOGGER.warning("OpenAI reasoning failed: %s", err)
        return None
    result: dict[str, object] = {}
    steps_value = parsed.get("steps")
    if isinstance(steps_value, Sequence) and not isinstance(steps_value, (str, bytes, bytearray)):
        clean_steps: list[str] = []
        for idx, step in enumerate(steps_value[:REASONING_STEP_LIMIT]):
            if isinstance(step, str):
                step_text = step.strip()
            else:
                step_text = str(step).strip()
            if step_text:
                clean_steps.append(step_text)
        if clean_steps:
            result["steps"] = clean_steps
    conclusion = parsed.get("conclusion")
    if isinstance(conclusion, str):
        conclusion_text = conclusion.strip()
        if conclusion_text:
            result["conclusion"] = conclusion_text
    confidence = parsed.get("confidence")
    if isinstance(confidence, str):
        confidence_text = confidence.strip()
        if confidence_text:
            result["confidence"] = confidence_text
    return result or None


def call_openai_interpreter(
    prompt: str,
    today: datetime.date,
    history: list[dict] | None = None,
    feedback: str | None = None,
    memory_snippets: list[str] | None = None,
    session_snapshot: dict | None = None,
) -> dict | None:
    settings = load_openai_settings()
    api_key = settings.get("api_key") if settings else None
    if not api_key:
        return None

    model = settings.get("model", OPENAI_DEFAULT_MODEL)
    system_prompt = (
        "You are a friendly supply-planning copilot for a chemical manufacturer. "
        "Hold natural conversations, but always convert each request into structured intents so downstream SQL templates know what to run. "
        "Supported intents: 'report' (single-period usage summary), 'sales' (customer invoice/shipment quantities), "
        "'compare' (contrast two or more periods), 'why_drop' (explain a decline), 'inventory', "
        "'inventory_usage' (availability vs usage snapshot), 'multi_report' (multiple items/classes or keyword-driven usage summaries), "
        "'all_items' (catalog-wide or zero-usage summaries when no item is given), 'reorder', "
        "'usage' (legacy synonym for report), 'custom_sql' (bespoke SQL needed for purchases/vendors/custom aggregates), "
        "and 'chitchat' when no data is needed. "
        "When unsure but data is requested, default to 'report' only for historical usage/lookback questions; "
        "if the user explicitly mentions sales, invoices, shipments, or customer orders, choose 'sales'. "
        "If the user hints at ordering, stocking, or what to buy, choose 'reorder' even if details are fuzzy. "
        "If their request cannot be satisfied by usage/sales/inventory/reorder templates (for example purchase orders, vendor spend, multi-table joins), choose 'custom_sql'. "
        "Always emit strict JSON with keys: intent, item, month, year, multiplier, notes, reply, entities. "
        "entities must be an object capturing structured details such as item, metric, month/year, "
        "periods (list of {\"month\": int, \"year\": int}), comparison_periods, sites, items (list of item numbers), "
        "item_classes (for class/category filters), and any filters you inferred. "
        "If you infer an item from a description, note that assumption in notes/reply so downstream SQL can auto-select it. "
        "For out-of-stock or zero on-hand list requests, set entities.filters.inventory_status to 'zero_on_hand' and keep item null unless the user names one so downstream SQL can pull all matching items. "
        "Use uppercase item codes. reply must be a concise conversational response that references what you plan to run or clarifies missing info. "
        "If the user asks what to buy or restock, choose intent 'reorder'. "
        "If they ask for items/classes without naming a specific item (e.g., 'which items had no usage' or 'show the emulsifier class'), prefer 'all_items' or 'multi_report' as appropriate and leave item null. "
        "If they omit the item, leave item null and explain assumptions in notes. "
        "Treat any mention of burn rate (burn-rate, burnrate, usage rate, consumption rate) as a usage/report intent: highlight the historical consumption window and include the per-period average so downstream tools can reuse that burn rate. "
        "When the user pivots from burn rate or usage questions into 'how much should we buy', stay on intent 'reorder' so the SQL agent compares order-point gaps versus the recent burn rate coverage. "
        "Honor any Relevant past context that appears before the latest input. "
        "Data entities you can reference: "
        "InventoryBalance from IV00102 joined to IV00101 with columns ITEMNMBR, ITEMDESC, ITMCLSCD, QTYONHND, ATYALLOC, QTYONORD, ORDRPNTQTY, and computed QtyAvailable (location MAIN by default unless the user specifies sites). "
        "UsageHistory from IV30300 detail + IV30200 header where DOCTYPE=1 and TRXQTY<0 represents consumption; DOCDATE month/year drive reporting windows. "
        "SalesShipments from SOP30300 detail + SOP30200 header where SOPTYPE=3 invoices (positive) and SOPTYPE=4 returns (negative); summarize the net quantity over DOCDATE windows. "
        "ReorderCandidates are items where QtyAvailable < ORDRPNTQTY, and Shortfall = ORDRPNTQTY - QtyAvailable. "
        "Mention the dataset you plan to query inside notes/reply (e.g., 'running usage SQL on IV30300 for Jan 2025'), and rely on session context defaults (item/month/year) when the user says 'same item' or 'same period'."
    )
    if feedback:
        system_prompt += f"\nUser feedback/preferences to honor: {feedback.strip()}."

    history_messages: list[dict] = []
    for entry in history or []:
        role = entry.get("role")
        content = entry.get("content")
        if role in {"user", "assistant", "system"} and isinstance(content, str):
            history_messages.append({"role": role, "content": content})

    context_text = ""
    if memory_snippets:
        cleaned_chunks = [chunk.strip() for chunk in memory_snippets if isinstance(chunk, str) and chunk.strip()]
        if cleaned_chunks:
            context_text = "Relevant past context:\n" + "\n---\n".join(cleaned_chunks) + "\n\n"
    recent_corrections = load_recent_corrections()
    corrections_text = format_correction_examples(recent_corrections)
    if corrections_text:
        context_text += f"{corrections_text}\n\n"

    session_summary = summarize_session_context(session_snapshot, today)
    if session_summary:
        context_text += f"Most recent structured request: {session_summary}\n\n"

    user_prompt = (
        f"{context_text}"
        f"Current date: {today.isoformat()}.\n"
        f"Latest user input:\n{prompt}\n"
        "Respond with JSON only."
    )

    payload = {
        "model": model,
        "temperature": 0.0,
        "messages": [{"role": "system", "content": system_prompt}, *history_messages, {"role": "user", "content": user_prompt}],
        "response_format": {"type": "json_object"},
    }

    headers = {
        "Authorization": f"Bearer {api_key}",
        "Content-Type": "application/json",
    }

    try:
        response = requests.post(
            OPENAI_CHAT_URL,
            headers=headers,
            json=payload,
            timeout=OPENAI_TIMEOUT_SECONDS,
        )
        response.raise_for_status()
        data = response.json()
        content = data["choices"][0]["message"]["content"]
        json_text = _extract_json_block(content)
        parsed = json.loads(json_text)
    except (requests.RequestException, KeyError, json.JSONDecodeError) as err:
        LOGGER.warning("OpenAI interpretation failed: %s", err)
        return None

    result: dict[str, object] = {}
    intent = parsed.get("intent")
    if isinstance(intent, str):
        result["intent"] = intent.lower()

    item = parsed.get("item")
    if isinstance(item, str):
        result["item"] = item.strip().upper()

    month = parsed.get("month")
    try:
        month_int = int(month)
        if 1 <= month_int <= 12:
            result["month"] = month_int
    except (TypeError, ValueError):
        pass

    year = parsed.get("year")
    try:
        year_int = int(year)
        if 1900 <= year_int <= 2100:
            result["year"] = year_int
    except (TypeError, ValueError):
        pass

    multiplier = parsed.get("multiplier")
    try:
        multiplier_val = float(multiplier)
        result["multiplier"] = multiplier_val
    except (TypeError, ValueError):
        pass

    notes = parsed.get("notes")
    if isinstance(notes, str) and notes.strip():
        result["notes"] = notes.strip()

    entities = parsed.get("entities")
    if isinstance(entities, dict):
        clean_entities = {key: entities[key] for key in entities}
        result["entities"] = clean_entities
        entity_item = clean_entities.get("item")
        if isinstance(entity_item, str):
            result["item"] = entity_item.strip().upper()
        entity_month = clean_entities.get("month")
        entity_year = clean_entities.get("year")
        try:
            if entity_month and 1 <= int(entity_month) <= 12 and not result.get("month"):
                result["month"] = int(entity_month)
        except (TypeError, ValueError):
            pass
        try:
            if entity_year and 1900 <= int(entity_year) <= 2100 and not result.get("year"):
                result["year"] = int(entity_year)
        except (TypeError, ValueError):
            pass

    return result


def interpret_prompt(
    prompt: str,
    today: datetime.date,
    history: list[dict] | None = None,
    feedback: str | None = None,
    memory_context: list[dict] | None = None,
    session_context: dict | None = None,
) -> dict:
    prior_session_intent = session_context.get("intent") if isinstance(session_context, dict) else None
    pending_item_intent = session_context.get("needs_item_for_intent") if isinstance(session_context, dict) else None
    month_guess, year_guess = infer_period_from_text(prompt, today)
    item_followup_hint = looks_like_item_followup(prompt)
    graph_requested = wants_graph(prompt)
    context = {
        "intent": classify_chat_intent(prompt),
        "item": extract_item_code(prompt),
        "month": month_guess,
        "year": year_guess,
        "multiplier": extract_multiplier(prompt),
        "notes": None,
        "entities": {},
        "prompt_has_item": False,
        "followup_same_data": references_previous_data(prompt),
        "multi_intent_warning": detect_multi_intent_usage_conflict(prompt),
        "item_followup_hint": item_followup_hint,
        "graph_requested": graph_requested,
    }
    prompt_item_present = bool(context["item"])
    prompt_has_data_keywords = contains_data_request_keywords(prompt)
    prompt_small_talk = looks_like_small_talk(prompt)
    reorder_hint = looks_like_reorder_prompt(prompt)
    context["reorder_hint"] = reorder_hint
    context["zero_usage_focus"] = wants_zero_usage_only(prompt)
    baseline_intent = context["intent"]
    if reorder_hint:
        baseline_intent = "reorder"
        context["intent"] = "reorder"
    elif baseline_intent == "chitchat" and prompt_item_present and prompt_has_data_keywords:
        baseline_intent = deduce_usage_report_or_sales_intent(prompt)
        context["intent"] = baseline_intent
    elif prompt_has_data_keywords and context["intent"] not in {CUSTOM_SQL_INTENT, "inventory", "inventory_usage"}:
        multi_scope_intent = None
        if not prompt_item_present and looks_like_all_items_prompt(prompt):
            multi_scope_intent = ALL_ITEMS_INTENT
        elif looks_like_multi_item_prompt(prompt):
            multi_scope_intent = MULTI_ITEM_INTENT
        if multi_scope_intent and multi_scope_intent != baseline_intent:
            baseline_intent = multi_scope_intent
            context["intent"] = multi_scope_intent
    context["prompt_has_item"] = prompt_item_present
    if context["followup_same_data"] and context.get("item"):
        context["prompt_has_item"] = True
    context["prompt_item_candidates"] = extract_item_candidates(prompt)
    period_limit = GRAPH_MAX_USAGE_PERIODS if graph_requested else MAX_USAGE_PERIODS
    raw_periods = extract_periods_from_prompt(prompt, today.year)
    prompt_periods = deduplicate_periods(raw_periods, limit=period_limit)
    context["prompt_periods"] = prompt_periods
    context["prompt_period_count"] = len(prompt_periods)
    context["prompt_period_labels"] = [
        describe_month_year(month_val, year_val, today.year) for month_val, year_val in prompt_periods
    ]
    context["mentions_between_months"] = mentions_month_range(prompt)
    context["mentions_last_year"] = contains_last_year_reference(prompt)
    context["mentions_this_year"] = contains_this_year_reference(prompt)
    if pending_item_intent:
        context["needs_item_for_intent"] = pending_item_intent
        lowered_prompt = prompt.lower()
        if not prompt_item_present and any(keyword in lowered_prompt for keyword in PENDING_ITEM_RESET_KEYWORDS):
            context["needs_item_for_intent"] = None
            pending_item_intent = None
        elif prompt_item_present:
            context["needs_item_for_intent"] = None
    followup_item_response = bool(pending_item_intent and prompt_item_present and item_followup_hint)
    if followup_item_response:
        baseline_intent = pending_item_intent
        context["intent"] = pending_item_intent
        context["followup_same_data"] = True

    followup_same_data = bool(context["followup_same_data"])
    if followup_same_data:
        if prior_session_intent in {"usage", "report", "sales"}:
            baseline_intent = prior_session_intent
            context["intent"] = prior_session_intent
        elif graph_requested and prior_session_intent and prior_session_intent != "chitchat":
            baseline_intent = prior_session_intent
            context["intent"] = prior_session_intent

    allow_item_inheritance = not (
        context.get("intent") == "reorder"
        and not prompt_item_present
        and not followup_same_data
        and not item_followup_hint
    )

    if session_context:
        if allow_item_inheritance:
            context["item"] = context.get("item") or session_context.get("item")
        elif not prompt_item_present:
            context["item"] = None
        context["month"] = context.get("month") or session_context.get("month")
        if followup_same_data and context.get("item"):
            context["prompt_has_item"] = True
        context["year"] = context.get("year") or session_context.get("year")
        if isinstance(session_context.get("entities"), dict):
            context["entities"].update(session_context["entities"])
            if not allow_item_inheritance:
                context["entities"].pop("item", None)
                context["entities"].pop("item_description", None)

    if memory_context:
        for entry in memory_context:
            metadata = entry.get("metadata") or {}
            if allow_item_inheritance:
                context["item"] = context.get("item") or metadata.get("item")
            context["month"] = context.get("month") or metadata.get("month")
            context["year"] = context.get("year") or metadata.get("year")
            entry_entities = metadata.get("entities")
            if isinstance(entry_entities, dict):
                context["entities"].update(entry_entities)
                if not allow_item_inheritance:
                    context["entities"].pop("item", None)
                    context["entities"].pop("item_description", None)

    memory_snippets = [entry.get("text") for entry in memory_context or []]
    llm_data = call_openai_interpreter(
        prompt,
        today,
        history,
        feedback,
        memory_snippets=memory_snippets,
        session_snapshot=session_context,
    )
    if not llm_data:
        return context

    if llm_data.get("intent"):
        candidate = llm_data["intent"].lower()
        allowed_intents = {
            "usage",
            "report",
            "sales",
            "compare",
            "why_drop",
            "inventory",
            "inventory_usage",
            "reorder",
            MULTI_ITEM_INTENT,
            ALL_ITEMS_INTENT,
            CUSTOM_SQL_INTENT,
        }
        if candidate in allowed_intents:
            if candidate == "inventory" and prior_session_intent in {"usage", "report", "sales"} and followup_same_data:
                context["intent"] = prior_session_intent
            else:
                context["intent"] = candidate
        elif candidate == "chitchat":
            allow_chitchat = prompt_small_talk and not prompt_item_present and not prompt_has_data_keywords
            if allow_chitchat:
                context["intent"] = "chitchat"
            else:
                context["intent"] = baseline_intent
        else:
            context["intent"] = baseline_intent
    if llm_data.get("item") and (allow_item_inheritance or prompt_item_present):
        context["item"] = llm_data["item"]
    if llm_data.get("month"):
        context["month"] = llm_data["month"]
    if llm_data.get("year"):
        context["year"] = llm_data["year"]
    if llm_data.get("multiplier") is not None:
        context["multiplier"] = llm_data["multiplier"]
    if llm_data.get("notes"):
        context["notes"] = llm_data["notes"]
    if isinstance(llm_data.get("entities"), dict):
        context["entities"].update(llm_data["entities"])
        if not allow_item_inheritance and not prompt_item_present:
            context["entities"].pop("item", None)
            context["entities"].pop("item_description", None)
    if llm_data.get("reply"):
        context["reply"] = llm_data["reply"]
    if context.get("reorder_hint") and context.get("intent") != "reorder":
        context["intent"] = "reorder"
    if looks_like_inventory_vs_usage_prompt(prompt) and context.get("intent") not in {"reorder", "sales"}:
        context["intent"] = "inventory_usage"
    if context.get("item"):
        context["needs_item_for_intent"] = None
        if followup_same_data:
            context["prompt_has_item"] = True

    inventory_filter = detect_inventory_filter(prompt, context)
    if inventory_filter:
        context["inventory_filter"] = inventory_filter
        if not context.get("prompt_has_item"):
            context["item"] = None
            entities = context.get("entities")
            if isinstance(entities, dict):
                entities.pop("item", None)
            context["needs_item_for_intent"] = None

    return context


def build_feedback_instruction(manual_note: str, log: list[dict], session_id: str) -> str:
    notes: list[str] = []
    manual = manual_note.strip() if manual_note else ""
    if manual:
        notes.append(f"Persistent guidance from the user: {manual}")
    for entry in reversed(log):
        if session_id and entry.get("session_id") not in (None, session_id):
            continue
        if not entry.get("comment"):
            continue
        label = "Positive" if entry.get("direction") == "up" else "Needs improvement"
        notes.append(f"{label}: {entry['comment']}")
        if len(notes) >= 4:
            break
    return "\n".join(notes)


def latest_history_entry(history: list[dict], context_type: str | None = None) -> dict | None:
    for entry in reversed(history):
        if context_type is None or entry.get("context_type") == context_type:
            return entry
    return None


def generate_chitchat_reply(prompt: str, history: list[dict], llm_reply: str | None = None) -> str:
    lowered = prompt.lower()
    conceptual_question = looks_like_conceptual_question(prompt)
    concept_definition = describe_gp_concept(prompt)

    if asks_about_capabilities(prompt):
        suggestions = build_question_suggestions(history or [])
        suggestion_block = ""
        if suggestions:
            bullets = "\n".join(f"- {text}" for text in suggestions)
            suggestion_block = f"\n\nTry asking:\n{bullets}"
        return (
            "I can pull GP usage or invoiced sales for specific items, compare months or years, check current inventory, "
            "line up availability versus usage, and flag the biggest reorder gaps. "
            "Just mention the item and timeframe you care about and I'll run the numbers."
            f"{suggestion_block}"
        )

    reorder_entry = latest_history_entry(history, "reorder")
    if reorder_entry and any(word in lowered for word in ("gap", "shortfall", "worst", "order point", "buy")):
        rows = reorder_entry.get("data") or []
        extra = ""
        if rows:
            first = rows[0]
            item = first.get("Item")
            shortfall = first.get("Shortfall")
            order_point = first.get("OrderPoint")
            avail = first.get("Avail")
            if all(isinstance(val, (int, float)) for val in (shortfall, order_point, avail)):
                extra = (
                    f" For example, {item} is {shortfall:,.0f} units below its order point "
                    f"({order_point:,.0f} target vs {avail:,.0f} available)."
                )
            elif item:
                extra = f" For example, {item} currently shows the largest shortfall."
        return (
            "Worst gaps first means I'm sorting the reorder list by the shortfall amount - "
            "the difference between the order point and what is currently available. "
            "Items missing the most come first so purchasing can focus on the largest gaps."
            f"{extra}"
        )

    if concept_definition:
        return concept_definition

    explanation_triggers = ("explain", "clarify", "mean", "difference", "why", "how", "what does", "tell me more")
    needs_explanation = contains_word_boundary_keyword(lowered, explanation_triggers)
    explanation_contexts = (
        "reorder",
        "inventory",
        "inventory_usage",
        "usage",
        "sales",
        "compare",
        "why_drop",
        MULTI_ITEM_INTENT,
        ALL_ITEMS_INTENT,
        CUSTOM_SQL_INTENT,
    )
    last_context = None
    last_result = None
    if needs_explanation:
        for context_name in explanation_contexts:
            candidate = latest_history_entry(history, context_name)
            if candidate:
                last_result = candidate
                last_context = context_name
                break

    if needs_explanation and last_result:
        context_label_map = {
            "reorder": "reorder summary",
            "inventory": "inventory snapshot",
            "inventory_usage": "availability vs usage snapshot",
            "usage": "usage report",
            "sales": "sales report",
            "compare": "comparison",
            "why_drop": "drop analysis",
            MULTI_ITEM_INTENT: "multi-item summary",
            ALL_ITEMS_INTENT: "all-items summary",
        }
        label = context_label_map.get(last_context or "", "result")
        return (
            f"Tell me what part of the previous {label} to walk through - quantities, time frames, or calculations - "
            "and I'll break it down."
        )

    if conceptual_question and llm_reply:
        return ""

    if needs_explanation:
        return (
            "Happy to explain, but let me know which item, time frame, or metric you want clarified so I don't guess."
        )

    if conceptual_question:
        return (
            "I can walk through GP terms like reorder point, lead time, or safety stock - just mention the exact field you want defined."
        )

    return "I'm here to help with GP data questions - add an item, month, or describe what you'd like explained and I'll dive in."


def build_item_metric_report(
    cursor: pyodbc.Cursor,
    prompt: str,
    today: datetime.date,
    context: dict | None,
    *,
    fetcher: Callable[[pyodbc.Cursor, str, datetime.date, datetime.date], float],
    column_label: str,
    insight_key: str,
    total_key: str,
    context_type: str,
    sql_template: str,
) -> dict:
    context = context or {}
    item_code, suggestions, assumption_note = resolve_item_with_fallbacks(cursor, prompt, context)
    if not item_code:
        return {
            "error": "Please mention an item number (e.g., NO3CA12) so I know what to query.",
            "data": None,
            "sql": None,
            "context_type": context_type,
            "suggestions": suggestions,
        }

    item_description = fetch_item_description(cursor, item_code)

    periods = determine_usage_periods(prompt, context, today) or []
    if not periods:
        month_guess, year_guess = infer_period_from_text(prompt, today)
        periods = [build_month_usage_period(month_guess, year_guess)]

    rows: list[dict] = []
    period_details: list[dict] = []
    sql_previews: list[str] = []
    combined_start: datetime.date | None = None
    combined_end: datetime.date | None = None
    total_value = 0.0
    chart_payload: dict | None = None
    chart_caption: str | None = None
    chart_warning: str | None = None
    graph_requested = bool(context.get("graph_requested"))

    for period in periods:
        start_date = period.get("start_date")
        end_date = period.get("end_date")
        label = period.get("label")
        if not isinstance(start_date, datetime.date) or not isinstance(end_date, datetime.date):
            continue
        display_label = label or start_date.strftime("%B %Y")
        metric_value = fetcher(cursor, item_code, start_date, end_date)
        combined_start = start_date if combined_start is None else min(combined_start, start_date)
        combined_end = end_date if combined_end is None else max(combined_end, end_date)
        row_entry = {
            "Item": item_code,
            "Period": display_label,
            "StartDate": start_date.isoformat(),
            "EndDate": end_date.isoformat(),
            column_label: metric_value,
        }
        if item_description:
            row_entry["Description"] = item_description
        rows.append(row_entry)
        period_details.append(
            {
                "label": display_label,
                insight_key: metric_value,
                "granularity": period.get("granularity"),
            }
        )
        total_value += metric_value
        sql_previews.append(format_sql_preview(sql_template, (item_code, start_date, end_date)))

    if len(rows) > 1:
        first_label = rows[0]["Period"]
        last_label = rows[-1]["Period"]
        total_row = {
            "Item": item_code,
            "Period": f"Total ({first_label} - {last_label})",
            "StartDate": combined_start.isoformat() if combined_start else None,
            "EndDate": combined_end.isoformat() if combined_end else None,
            column_label: total_value,
        }
        if item_description:
            total_row["Description"] = item_description
        rows.append(total_row)

    multiplier = context.get("multiplier")
    if multiplier is None:
        multiplier = extract_multiplier(prompt)
    scaled_value = None
    if multiplier is not None and rows:
        for row in rows:
            metric_amount = row.get(column_label)
            if isinstance(metric_amount, (int, float)):
                row[f"{column_label} x {multiplier:g}"] = metric_amount * multiplier
        if period_details:
            base_metric = total_value if len(period_details) > 1 else period_details[0].get(insight_key, 0.0)
        else:
            base_metric = 0.0
        scaled_value = base_metric * multiplier

    sql_preview = "\n\n".join(sql_previews)
    if len(sql_previews) == 1:
        sql_preview = sql_previews[0]

    if not period_details:
        period_label = None
        metric_for_period = 0.0
    else:
        period_label = (
            f"{period_details[0]['label']} - {period_details[-1]['label']}" if len(period_details) > 1 else period_details[0]["label"]
        )
        metric_for_period = total_value if len(period_details) > 1 else period_details[0].get(insight_key, 0.0)

    period_count = len(period_details)
    insights = {
        "item": item_code,
        "period": period_label,
        insight_key: metric_for_period,
        "periods": period_details,
        total_key: total_value if len(period_details) > 1 else None,
        "metric_key": insight_key,
        "total_metric_key": total_key,
        "period_count": period_count,
        "multiplier": multiplier,
        "scaled": scaled_value,
        "description": item_description,
        "column_label": column_label,
    }
    if assumption_note:
        insights["assumption_note"] = assumption_note

    if period_count:
        average_value = total_value / period_count
        insights["average_per_period"] = average_value
        if insight_key == "usage":
            insights["burn_rate"] = average_value

    if graph_requested:
        chart_points: list[dict] = []
        for sequence, detail in enumerate(period_details):
            label = detail.get("label")
            metric_value = detail.get(insight_key)
            if not (label and isinstance(metric_value, Number)):
                continue
            chart_points.append(
                {
                    "Period": label,
                    column_label: metric_value,
                    "_sequence": sequence,
                }
            )
        if len(chart_points) >= 2:
            chart_payload = {
                "type": "line",
                "title": f"{item_code} {column_label} trend",
                "data": chart_points,
                "x_field": "Period",
                "y_field": column_label,
                "value_label": column_label,
                "item": item_code,
                "height": 280,
            }
            chart_caption = f"Line chart below: {item_code} {column_label.lower()} by period."
        else:
            chart_warning = "I need at least two periods to plot a graph. Try specifying multiple months or a range."

    result = {
        "data": rows,
        "sql": sql_preview,
        "context_type": context_type,
        "insights": insights,
    }
    if chart_payload:
        result["chart"] = chart_payload
    if chart_caption:
        result["chart_caption"] = chart_caption
    if chart_warning:
        result["chart_warning"] = chart_warning
    if suggestions:
        result["suggestions"] = suggestions
    return result


def handle_usage_question(
    cursor: pyodbc.Cursor, prompt: str, today: datetime.date, context: dict | None = None
) -> dict:
    return build_item_metric_report(
        cursor,
        prompt,
        today,
        context,
        fetcher=fetch_usage,
        column_label="Usage",
        insight_key="usage",
        total_key="total_usage",
        context_type="usage",
        sql_template=USAGE_QUERY,
    )


def handle_sales_question(
    cursor: pyodbc.Cursor, prompt: str, today: datetime.date, context: dict | None = None
) -> dict:
    return build_item_metric_report(
        cursor,
        prompt,
        today,
        context,
        fetcher=fetch_sales,
        column_label="Sales",
        insight_key="sales",
        total_key="total_sales",
        context_type="sales",
        sql_template=SALES_QUERY,
    )


def handle_multi_item_question(
    cursor: pyodbc.Cursor, prompt: str, today: datetime.date, context: dict | None = None
) -> dict:
    context = context or {}
    start_date, end_date, period_label, resolved_periods = determine_scope_period(prompt, context, today)
    site_codes, site_explicit, site_covers_all = resolve_site_filters(context)
    class_filters, class_explicit, class_covers_all = resolve_class_filters(context)
    item_list = resolve_item_list_filters(context)
    keywords = gather_scope_keywords(prompt, context)
    zero_focus = bool(context.get("zero_usage_focus"))
    requested_limit = max(len(item_list), 40) if item_list else 40
    order_mode = "abs" if zero_focus else "usage"
    rows, sql_preview = fetch_usage_scope_rows(
        cursor,
        start_date,
        end_date,
        limit=requested_limit,
        site_codes=site_codes,
        site_covers_all=site_covers_all,
        class_filters=class_filters,
        class_covers_all=class_covers_all,
        item_list=item_list,
        keywords=keywords,
        order_mode=order_mode,
    )
    zero_rows = [row for row in rows if abs(row.get("Usage", 0.0)) < ZERO_USAGE_EPSILON]
    display_rows = zero_rows if zero_focus and zero_rows else rows
    error = None
    if not rows:
        error = "No items matched those filters."
    elif zero_focus and not zero_rows:
        error = f"No items were completely idle during {period_label}."
    scope_note = build_scope_note(
        site_codes,
        site_explicit,
        site_covers_all,
        class_filters,
        class_explicit,
        class_covers_all,
    )
    insights = {
        "period": period_label,
        "row_count": len(display_rows),
        "scanned_count": len(rows),
        "zero_focus": zero_focus,
        "zero_item_count": len(zero_rows),
        "top_item": display_rows[0] if display_rows else None,
        "sites": site_codes,
        "site_explicit": site_explicit,
        "site_covers_all": site_covers_all,
        "class_filters": class_filters,
        "class_explicit": class_explicit,
        "class_covers_all": class_covers_all,
        "item_filters": item_list,
        "keywords": keywords,
        "periods": resolved_periods,
        "limit": requested_limit,
        "period_start": start_date.isoformat(),
        "period_end": end_date.isoformat(),
    }
    if scope_note:
        insights["scope_note"] = scope_note
    result = {
        "data": display_rows,
        "sql": sql_preview,
        "context_type": MULTI_ITEM_INTENT,
        "insights": insights,
    }
    if error:
        result["error"] = error
    return result


def handle_all_items_question(
    cursor: pyodbc.Cursor, prompt: str, today: datetime.date, context: dict | None = None
) -> dict:
    context = context or {}
    start_date, end_date, period_label, resolved_periods = determine_scope_period(prompt, context, today)
    site_codes, site_explicit, site_covers_all = resolve_site_filters(context)
    class_filters, class_explicit, class_covers_all = resolve_class_filters(context)
    keywords = gather_scope_keywords(prompt, context)
    zero_focus = bool(context.get("zero_usage_focus"))
    rows, sql_preview = fetch_usage_scope_rows(
        cursor,
        start_date,
        end_date,
        limit=75,
        site_codes=site_codes,
        site_covers_all=site_covers_all,
        class_filters=class_filters,
        class_covers_all=class_covers_all,
        item_list=None,
        keywords=keywords,
        order_mode="abs" if zero_focus else "usage",
    )
    zero_rows = [row for row in rows if abs(row.get("Usage", 0.0)) < ZERO_USAGE_EPSILON]
    active_rows = [row for row in rows if abs(row.get("Usage", 0.0)) >= ZERO_USAGE_EPSILON]
    top_consumers = rows[:3] if not zero_focus else zero_rows[:3]
    error = None
    if not rows:
        error = "I could not build an all-items summary for that timeframe."
    elif zero_focus and not zero_rows:
        error = f"No items were completely idle during {period_label}."
    scope_note = build_scope_note(
        site_codes,
        site_explicit,
        site_covers_all,
        class_filters,
        class_explicit,
        class_covers_all,
    )
    insights = {
        "period": period_label,
        "row_count": len(rows),
        "zero_item_count": len(zero_rows),
        "active_item_count": len(active_rows),
        "zero_focus": zero_focus,
        "top_items": top_consumers,
        "sites": site_codes,
        "site_explicit": site_explicit,
        "site_covers_all": site_covers_all,
        "class_filters": class_filters,
        "class_explicit": class_explicit,
        "class_covers_all": class_covers_all,
        "keywords": keywords,
        "periods": resolved_periods,
        "period_start": start_date.isoformat(),
        "period_end": end_date.isoformat(),
    }
    if scope_note:
        insights["scope_note"] = scope_note
    result = {
        "data": zero_rows if zero_focus and zero_rows else rows,
        "sql": sql_preview,
        "context_type": ALL_ITEMS_INTENT,
        "insights": insights,
    }
    if error:
        result["error"] = error
    return result


def handle_compare_question(
    cursor: pyodbc.Cursor, prompt: str, today: datetime.date, context: dict | None = None
) -> dict:
    context = context or {}
    item_code, suggestions, assumption_note = resolve_item_with_fallbacks(cursor, prompt, context)
    if not item_code:
        return {
            "error": "Please specify an item to compare usage across months.",
            "data": None,
            "sql": None,
            "context_type": "compare",
            "suggestions": suggestions,
        }

    month = context.get("month")
    year = context.get("year")
    if not month or not year:
        month, year = infer_period_from_text(prompt, today)

    entities = context.get("entities") or {}
    requested_periods = normalize_periods_list(entities.get("comparison_periods")) or normalize_periods_list(
        entities.get("periods")
    )
    anchor_year = context.get("year") or year or today.year
    if not requested_periods:
        requested_periods = extract_periods_from_prompt(prompt, anchor_year)
    if not requested_periods:
        requested_periods = default_comparison_periods(month, year or anchor_year)

    normalized_periods: list[tuple[int, int]] = []
    seen: set[str] = set()
    for period_month, period_year in requested_periods:
        key = month_key(period_month, period_year)
        if key in seen:
            continue
        normalized_periods.append((period_month, period_year))
        seen.add(key)
        if len(normalized_periods) >= 3:
            break
    if not normalized_periods:
        return {
            "error": "I could not determine which months to compare. Mention two months (e.g., June vs July).",
            "data": None,
            "sql": None,
            "context_type": "compare",
        }
    if len(normalized_periods) == 1:
        normalized_periods = default_comparison_periods(normalized_periods[0][0], normalized_periods[0][1])

    date_ranges = [month_date_range(period_month, period_year) for period_month, period_year in normalized_periods]
    range_start = min(start for start, _ in date_ranges)
    range_end = max(end for _, end in date_ranges)
    usage_rows = fetch_monthly_usage(cursor, item_code, range_start, range_end)
    usage_map = {row["PeriodKey"]: row for row in usage_rows if row.get("PeriodKey")}

    rows: list[UsageTimelineRow] = []
    for (period_month, period_year), (start_date, end_date) in zip(normalized_periods, date_ranges):
        key = month_key(period_month, period_year)
        usage_entry = usage_map.get(key)
        usage_value = usage_entry["UsageForPeriod"] if usage_entry else 0.0
        rows.append(
            {
                "Item": item_code,
                "Period": start_date.strftime("%B %Y"),
                "StartDate": start_date.isoformat(),
                "EndDate": end_date.isoformat(),
                "Usage": usage_value,
            }
        )

    sql_preview = format_sql_preview(USAGE_BY_MONTH_QUERY, (item_code, range_start, range_end))
    difference = None
    percent_change = None
    if len(rows) >= 2:
        anchor = rows[0]["Usage"]
        baseline = rows[1]["Usage"]
        difference = anchor - baseline
        if baseline:
            percent_change = difference / abs(baseline)
    insights = {
        "item": item_code,
        "periods": rows,
        "difference": difference,
        "percent_change": percent_change,
    }
    if assumption_note:
        insights["assumption_note"] = assumption_note
    return {
        "data": rows,
        "sql": sql_preview,
        "context_type": "compare",
        "insights": insights,
    }


class UsageTimelineRow(TypedDict):
    Item: str
    Period: str
    StartDate: str
    EndDate: str
    Usage: float


class UsageDropSummary(TypedDict):
    from_period: str
    to_period: str
    change: float


def handle_why_drop_question(
    cursor: pyodbc.Cursor, prompt: str, today: datetime.date, context: dict | None = None
) -> dict:
    context = context or {}
    item_code, suggestions, assumption_note = resolve_item_with_fallbacks(cursor, prompt, context)
    if not item_code:
        return {
            "error": "Please mention which item dropped so I can review its history.",
            "data": None,
            "sql": None,
            "context_type": "why_drop",
            "suggestions": suggestions,
        }

    month = context.get("month")
    year = context.get("year")
    if not month or not year:
        month, year = infer_period_from_text(prompt, today)

    entities = context.get("entities") or {}
    requested_periods = normalize_periods_list(entities.get("periods")) or normalize_periods_list(
        entities.get("comparison_periods")
    )
    if requested_periods:
        month, year = requested_periods[-1]

    analysis_periods: list[tuple[int, int]] = []
    cursor_month, cursor_year = month, year
    for _ in range(WHY_DROP_MONTH_WINDOW):
        analysis_periods.append((cursor_month, cursor_year))
        cursor_month, cursor_year = previous_month(cursor_month, cursor_year)
    analysis_periods.reverse()

    start_date, _ = month_date_range(analysis_periods[0][0], analysis_periods[0][1])
    _, end_date = month_date_range(analysis_periods[-1][0], analysis_periods[-1][1])
    usage_rows = fetch_monthly_usage(cursor, item_code, start_date, end_date)
    usage_map = {row["PeriodKey"]: row for row in usage_rows if row.get("PeriodKey")}

    rows: list[dict] = []
    for period_month, period_year in analysis_periods:
        period_start, period_end = month_date_range(period_month, period_year)
        key = month_key(period_month, period_year)
        entry = usage_map.get(key)
        usage_value = entry.get("UsageForPeriod", 0.0) if isinstance(entry, Mapping) else 0.0
        rows.append(
            {
                "Item": item_code,
                "Period": period_start.strftime("%B %Y"),
                "StartDate": period_start.isoformat(),
                "EndDate": period_end.isoformat(),
                "Usage": usage_value,
            }
        )

    sql_preview = format_sql_preview(USAGE_BY_MONTH_QUERY, (item_code, start_date, end_date))
    recent: UsageTimelineRow | None = rows[-1] if rows else None
    previous: UsageTimelineRow | None = rows[-2] if len(rows) >= 2 else None
    drop_amount = None
    drop_percent = None
    if recent and previous:
        recent_usage = recent.get("Usage", 0.0) or 0.0
        previous_usage = previous.get("Usage", 0.0) or 0.0
        drop_amount = recent_usage - previous_usage
        if previous_usage:
            drop_percent = drop_amount / abs(previous_usage)

    worst_drop: UsageDropSummary | None = None
    for idx in range(1, len(rows)):
        current_usage = rows[idx].get("Usage", 0.0)
        previous_usage = rows[idx - 1].get("Usage", 0.0)
        change = current_usage - previous_usage
        if change >= 0:
            continue
        previous_change = worst_drop.get("change") if isinstance(worst_drop, dict) else None
        if previous_change is None or change < previous_change:
            worst_drop = {
                "from_period": rows[idx - 1].get("Period"),
                "to_period": rows[idx].get("Period"),
                "change": change,
            }

    insights = {
        "item": item_code,
        "timeline": rows,
        "recent": recent,
        "previous": previous,
        "drop_amount": drop_amount,
        "drop_percent": drop_percent,
        "worst_drop": worst_drop,
    }
    if assumption_note:
        insights["assumption_note"] = assumption_note
    return {
        "data": rows,
        "sql": sql_preview,
        "context_type": "why_drop",
        "insights": insights,
    }


def handle_inventory_question(cursor: pyodbc.Cursor, prompt: str, context: dict | None = None) -> dict:
    context = context or {}
    suggestion_pool: list[dict] = []
    assumption_note = None
    item_code = context.get("item") or extract_item_code(prompt)
    if not item_code:
        resolved_item, suggestion_pool, assumption_note = resolve_item_with_fallbacks(cursor, prompt, context)
        if resolved_item:
            item_code = resolved_item
    inventory_filter = context.get("inventory_filter") or detect_inventory_filter(prompt, context)
    if inventory_filter and not context.get("inventory_filter"):
        context["inventory_filter"] = inventory_filter
    site_codes, site_explicit, site_covers_all = resolve_site_filters(context)
    class_filters, class_explicit, class_covers_all = resolve_class_filters(context)
    prompt_filters = extract_inventory_filters(prompt, context)
    prompt_class = prompt_filters.get("item_class")
    below_order_point = bool(prompt_filters.get("below_order_point"))
    zero_on_hand = inventory_filter == "zero_on_hand"

    if isinstance(prompt_class, str) and prompt_class.strip():
        if prompt_class not in class_filters:
            class_filters.append(prompt_class)
        class_explicit = True
        class_covers_all = False

    limit_results = not (class_filters or below_order_point or zero_on_hand)
    select_hint = "TOP 25 " if limit_results else ""
    base_query = f"""
        SELECT {select_hint}i.ITEMNMBR, m.ITEMDESC, i.QTYONHND, i.QTYONORD,
               (i.QTYONHND - i.ATYALLOC) AS QtyAvailable, i.ORDRPNTQTY, m.ITMCLSCD,
               (i.ORDRPNTQTY - (i.QTYONHND - i.ATYALLOC)) AS Shortfall
        FROM IV00102 i
        JOIN IV00101 m ON m.ITEMNMBR = i.ITEMNMBR
        WHERE 1=1
    """
    params: list = []

    if site_codes and not site_covers_all:
        placeholders = ", ".join("?" for _ in site_codes)
        base_query += f"  AND i.LOCNCODE IN ({placeholders})"
        params.extend(site_codes)
    if item_code:
        base_query += " AND i.ITEMNMBR = ?"
        params.append(item_code)
    if class_filters and not class_covers_all:
        class_clauses = []
        for _ in class_filters:
            class_clauses.append("m.ITMCLSCD LIKE ?")
        base_query += " AND (" + " OR ".join(class_clauses) + ")"
        params.extend(_wildcard_value(value) for value in class_filters)
    if below_order_point:
        base_query += " AND (i.QTYONHND - i.ATYALLOC) < i.ORDRPNTQTY"
    if zero_on_hand:
        base_query += " AND i.QTYONHND <= 0"

    if below_order_point:
        order_clause = " ORDER BY (i.ORDRPNTQTY - (i.QTYONHND - i.ATYALLOC)) DESC"
    elif zero_on_hand:
        order_clause = " ORDER BY m.ITEMDESC, i.ITEMNMBR"
    else:
        order_clause = " ORDER BY i.ORDRPNTQTY DESC"
    base_query += order_clause

    cursor.execute(base_query, params)
    fetched = cursor.fetchall()
    columns = [col[0] for col in cursor.description] if cursor.description else []
    rows = []
    for raw_row in fetched:
        record = dict(zip(columns, raw_row)) if columns else {}
        rows.append(
            {
                "Item": record.get("ITEMNMBR", getattr(raw_row, "ITEMNMBR", None)),
                "Description": record.get("ITEMDESC", getattr(raw_row, "ITEMDESC", None)),
                "OnHand": record.get("QTYONHND", getattr(raw_row, "QTYONHND", None)),
                "OnOrder": record.get("QTYONORD", getattr(raw_row, "QTYONORD", None)),
                "Avail": record.get("QtyAvailable", getattr(raw_row, "QtyAvailable", None)),
                "OrderPoint": record.get("ORDRPNTQTY", getattr(raw_row, "ORDRPNTQTY", None)),
                "Class": record.get("ITMCLSCD", getattr(raw_row, "ITMCLSCD", None)),
                "Shortfall": record.get("Shortfall", getattr(raw_row, "Shortfall", None)),
            }
        )

    sql_preview = format_sql_preview(base_query, params)
    if below_order_point:
        sort_label = "shortfall vs order point"
    elif zero_on_hand:
        sort_label = "item number"
    else:
        sort_label = "order point"
    insights = {
        "item": item_code,
        "row_count": len(rows),
        "sample": rows[0] if rows else None,
        "sites": site_codes,
        "site_explicit": site_explicit,
        "site_covers_all": site_covers_all,
        "class_filters": class_filters,
        "class_explicit": class_explicit,
        "class_covers_all": class_covers_all,
        "below_order_point": below_order_point,
        "limited": limit_results,
        "sort": sort_label,
        "filter": inventory_filter,
    }
    if assumption_note:
        insights["assumption_note"] = assumption_note
    suggestions: list[dict] = []
    error = None
    scope_note = build_scope_note(
        site_codes,
        site_explicit,
        site_covers_all,
        class_filters,
        class_explicit,
        class_covers_all,
    )
    if scope_note:
        insights["scope_note"] = scope_note
    if not rows:
        site_phrase = site_error_clause(site_codes, site_covers_all)
        class_phrase = ""
        if class_explicit and class_filters:
            class_phrase = f" (Class filter: {describe_class_scope(class_filters, False)}.)"
        if zero_on_hand and not item_code:
            error = "No items with zero on hand"
            if site_phrase:
                error += f" {site_phrase}"
            error += "."
            if class_phrase:
                error += class_phrase
            if scope_note:
                error = f"{error} {scope_note}"
        elif item_code:
            suggestions = suggestion_pool or suggest_items_by_description(cursor, prompt)
            error = f"I could not find inventory rows for {item_code}"
            if site_phrase:
                error += f" {site_phrase}"
            error += "."
            if scope_note:
                error = f"{error} {scope_note}"
        else:
            if site_phrase:
                error = f"No inventory rows matched {site_phrase}."
            else:
                error = "No inventory rows matched."
            if class_phrase:
                error += class_phrase
            elif class_explicit and class_covers_all:
                error += " (All classes included per your request.)"
            error += " Try a different item or remove filters."
            if scope_note:
                error = f"{error} {scope_note}"
    return {
        "data": rows,
        "sql": sql_preview,
        "context_type": "inventory",
        "insights": insights,
        "error": error,
        "suggestions": suggestions,
    }


def handle_inventory_usage_question(
    cursor: pyodbc.Cursor, prompt: str, today: datetime.date, context: dict | None = None
) -> dict:
    context = context or {}
    item_code, suggestions, assumption_note = resolve_item_with_fallbacks(cursor, prompt, context)
    if not item_code:
        return {
            "error": "Please mention an item number (e.g., NO3CA12) so I can line up availability vs usage.",
            "data": None,
            "sql": None,
            "context_type": "inventory_usage",
            "suggestions": suggestions,
        }
    context["item"] = context.get("item") or item_code

    inventory_payload = handle_inventory_question(cursor, prompt, context)
    rows = inventory_payload.get("data") or []
    if not rows:
        return {
            "error": inventory_payload.get("error")
            or f"I could not find inventory rows for {item_code} with the current filters.",
            "data": None,
            "sql": inventory_payload.get("sql"),
            "context_type": "inventory_usage",
            "suggestions": inventory_payload.get("suggestions"),
        }
    inventory_row = next((row for row in rows if row.get("Item") == item_code), rows[0])

    usage_periods = determine_usage_periods(prompt, context, today) or []
    if not usage_periods:
        usage_periods = [build_month_usage_period(today.month, today.year)]
    primary_period: UsagePeriod = usage_periods[0]
    start_date = primary_period["start_date"]
    end_date = primary_period["end_date"]
    usage_value = fetch_usage(cursor, item_code, start_date, end_date)
    usage_summary = {
        "Item": item_code,
        "Label": primary_period["label"],
        "StartDate": start_date.isoformat(),
        "EndDate": end_date.isoformat(),
        "Usage": usage_value,
    }

    avail_value = inventory_row.get("Avail")
    order_point = inventory_row.get("OrderPoint")
    coverage_months = None
    usage_magnitude = abs(usage_value) if isinstance(usage_value, Number) else None
    if isinstance(avail_value, Number) and isinstance(usage_magnitude, Number):
        if usage_magnitude > 0 and primary_period.get("granularity") == "month":
            coverage_months = avail_value / usage_magnitude
    order_point_gap = None
    if isinstance(avail_value, Number) and isinstance(order_point, Number):
        order_point_gap = avail_value - order_point

    usage_sql = format_sql_preview(USAGE_QUERY, (item_code, start_date, end_date))
    inventory_sql = inventory_payload.get("sql") or ""
    combined_sql = usage_sql if not inventory_sql else f"{inventory_sql}\n\n{usage_sql}"
    base_insights = inventory_payload.get("insights") or {}
    insights = {
        "item": item_code,
        "inventory": inventory_row,
        "usage": usage_summary,
        "coverage_months": coverage_months,
        "order_point_gap": order_point_gap,
        "sites": base_insights.get("sites"),
        "site_explicit": base_insights.get("site_explicit"),
        "site_covers_all": base_insights.get("site_covers_all"),
        "class_filters": base_insights.get("class_filters"),
        "class_explicit": base_insights.get("class_explicit"),
        "class_covers_all": base_insights.get("class_covers_all"),
    }
    if assumption_note:
        insights["assumption_note"] = assumption_note
    return {
        "data": {
            "inventory": inventory_row,
            "usage": usage_summary,
        },
        "sql": combined_sql,
        "context_type": "inventory_usage",
        "insights": insights,
        "suggestions": inventory_payload.get("suggestions"),
    }


def handle_reorder_question(
    cursor: pyodbc.Cursor, prompt: str, today: datetime.date, context: dict | None = None
) -> dict:
    context = context or {}
    suggestion_pool: list[dict] = []
    assumption_note = None
    item_code = context.get("item") or extract_item_code(prompt)
    if not item_code:
        resolved_item, suggestion_pool, assumption_note = resolve_item_with_fallbacks(cursor, prompt, context)
        if resolved_item:
            item_code = resolved_item
    site_codes, site_explicit, site_covers_all = resolve_site_filters(context)
    class_filters, class_explicit, class_covers_all = resolve_class_filters(context)
    params: list = []
    where_clauses = ["(i.QTYONHND - i.ATYALLOC) < i.ORDRPNTQTY"]
    if site_codes and not site_covers_all:
        placeholders = ", ".join("?" for _ in site_codes)
        where_clauses.append(f"i.LOCNCODE IN ({placeholders})")
        params.extend(site_codes)
    if class_filters and not class_covers_all:
        class_clauses = ["m.ITMCLSCD LIKE ?" for _ in class_filters]
        where_clauses.append("(" + " OR ".join(class_clauses) + ")")
        params.extend(_wildcard_value(value) for value in class_filters)
    if item_code:
        where_clauses.append("i.ITEMNMBR = ?")
        params.append(item_code)
    query = (
        REORDER_QUERY
        + "\nWHERE "
        + "\n  AND ".join(where_clauses)
        + "\nORDER BY Shortfall DESC;"
    )

    cursor.execute(query, params)
    fetched = cursor.fetchall()
    rows = [
        {
            "Item": row.ITEMNMBR,
            "Description": row.ITEMDESC,
            "OnHand": row.QTYONHND,
            "Allocated": row.ATYALLOC,
            "Avail": row.QtyAvailable,
            "OrderPoint": row.ORDRPNTQTY,
            "Shortfall": row.Shortfall,
            "OnOrder": row.QTYONORD,
            "Class": row.ITMCLSCD,
        }
        for row in fetched
    ]
    sql_preview = format_sql_preview(query, params) if params else query
    insights = {
        "count": len(rows),
        "top_row": rows[0] if rows else None,
        "item": item_code,
        "sites": site_codes,
        "site_explicit": site_explicit,
        "site_covers_all": site_covers_all,
        "class_filters": class_filters,
        "class_explicit": class_explicit,
        "class_covers_all": class_covers_all,
    }
    if assumption_note:
        insights["assumption_note"] = assumption_note
    suggestions: list[dict] = []
    error = None
    scope_note = build_scope_note(
        site_codes,
        site_explicit,
        site_covers_all,
        class_filters,
        class_explicit,
        class_covers_all,
    )
    if scope_note:
        insights["scope_note"] = scope_note
    if not rows:
        if item_code:
            scope_bits: list[str] = []
            site_phrase = site_error_clause(site_codes, site_covers_all)
            if site_phrase:
                scope_bits.append(site_phrase)
            if class_explicit:
                if class_covers_all:
                    scope_bits.append("across all classes")
                elif class_filters:
                    scope_bits.append(f"within classes {describe_class_scope(class_filters, False)}")
            scope_text = (" " + " ".join(scope_bits)) if scope_bits else ""
            error = f"I could not find reorder data for {item_code}{scope_text}."
            if scope_note:
                error = f"{error} {scope_note}"
            suggestions = suggestion_pool or suggest_items_by_description(cursor, prompt)
        else:
            site_label = describe_site_scope(site_codes, site_covers_all) or "these locations"
            error = f"All {site_label} items meet their order points right now."
            if class_explicit and class_filters:
                error += f" (Class filter: {describe_class_scope(class_filters, False)}.)"
            elif class_explicit and class_covers_all:
                error += " (All classes included per your request.)"
            if scope_note:
                error = f"{error} {scope_note}"
        return {
            "data": rows,
            "sql": sql_preview,
            "context_type": "reorder",
            "insights": insights,
            "error": error,
            "suggestions": suggestions,
        }

    def coerce_number(value) -> float | None:
        try:
            return float(value)
        except (TypeError, ValueError):
            return None

    trailing_months = extract_recent_month_count(prompt)
    note_text = str(context.get("notes") or "")
    trailing_months = trailing_months or extract_recent_month_count(note_text)
    if trailing_months is None:
        lowered_sources = [prompt.lower(), note_text.lower()]
        if any("historical usage" in source for source in lowered_sources if source):
            trailing_months = DEFAULT_USAGE_HISTORY_MONTHS
    if trailing_months is None:
        entity_periods = normalize_periods_list((context.get("entities") or {}).get("periods"))
        if entity_periods:
            trailing_months = min(len(entity_periods), MAX_USAGE_PERIODS)
        elif context.get("prompt_period_count"):
            try:
                trailing_months = min(int(context["prompt_period_count"]), MAX_USAGE_PERIODS)
            except (TypeError, ValueError):
                trailing_months = None

    if trailing_months is None and item_code:
        trailing_months = DEFAULT_USAGE_HISTORY_MONTHS

    usage_details = None
    if (
        item_code
        and trailing_months
        and isinstance(trailing_months, int)
        and trailing_months > 0
        and rows
    ):
        trailing_months = max(1, min(trailing_months, MAX_USAGE_PERIODS))
        periods: list[tuple[datetime.date, datetime.date]] = []
        month_cursor, year_cursor = today.month, today.year
        for _ in range(trailing_months):
            start_date, end_date = month_date_range(month_cursor, year_cursor)
            periods.append((start_date, end_date))
            month_cursor, year_cursor = previous_month(month_cursor, year_cursor)
        periods.reverse()

        usage_rows: list[dict] = []
        total_usage = 0.0
        for start_date, end_date in periods:
            usage_value = abs(fetch_usage(cursor, item_code, start_date, end_date))
            usage_rows.append(
                {
                    "Period": start_date.strftime("%B %Y"),
                    "StartDate": start_date.isoformat(),
                    "EndDate": end_date.isoformat(),
                    "Usage": usage_value,
                }
            )
            total_usage += usage_value

        avg_usage = total_usage / trailing_months if trailing_months else None
        top_row = rows[0]
        avail_qty = coerce_number(top_row.get("Avail") or top_row.get("QtyAvailable"))
        shortfall_value = coerce_number(top_row.get("Shortfall"))
        cover_need = None
        if avail_qty is not None:
            cover_need = max(total_usage - max(avail_qty, 0.0), 0.0)
        recommended_buy = None
        candidates = [value for value in (shortfall_value, cover_need) if value is not None]
        if candidates:
            recommended_buy = max(candidates)
        usage_details = {
            "months": trailing_months,
            "rows": usage_rows,
            "total": total_usage,
            "average": avg_usage,
            "cover_need": cover_need,
            "recommended_buy": recommended_buy,
            "burn_rate": avg_usage,
        }
        insights["usage_based_recommendation"] = usage_details

    return {
        "data": rows,
        "sql": sql_preview,
        "context_type": "reorder",
        "insights": insights,
        "error": error,
        "suggestions": suggestions,
    }


def describe_usage_message(insights: dict | None) -> str:
    if not insights:
        return "I could not calculate usage for that request."
    item = insights.get("item")
    description = insights.get("description")
    period = insights.get("period")
    usage_value = insights.get("usage")
    periods = insights.get("periods") or []
    total_usage = insights.get("total_usage")
    message_parts: list[str] = []
    if item and description:
        item_label = f"{item} ({description})"
    elif description and not item:
        item_label = description
    else:
        item_label = item
    if isinstance(periods, list) and len(periods) > 1:
        per_texts: list[str] = []
        for entry in periods:
            label = entry.get("label")
            value = entry.get("usage")
            if label and isinstance(value, (int, float)):
                per_texts.append(f"{label}: {value:,.2f} units")
        if per_texts:
            prefix = f"{item_label} usage by period" if item_label else "Usage by period"
            message_parts.append(f"{prefix} - " + "; ".join(per_texts) + ". Negative values indicate outbound activity.")
        if isinstance(total_usage, (int, float)):
            start_label = periods[0].get("label")
            end_label = periods[-1].get("label")
            if start_label and end_label:
                range_label = f"{start_label} - {end_label}" if start_label != end_label else start_label
            else:
                range_label = "the requested range"
            message_parts.append(f"Total for {range_label}: {total_usage:,.2f} units.")
    else:
        if item_label and period and isinstance(usage_value, (int, float)):
            message_parts.append(
                f"{item_label} usage for {period}: {usage_value:,.2f} units. Negative values indicate outbound activity."
            )
        elif isinstance(usage_value, (int, float)):
            message_parts.append(f"Usage for the requested period: {usage_value:,.2f} units.")

    burn_rate_value = insights.get("burn_rate")
    if not isinstance(burn_rate_value, (int, float)):
        avg_value = insights.get("average_per_period")
        if isinstance(avg_value, (int, float)):
            burn_rate_value = avg_value
    period_count = insights.get("period_count")
    if isinstance(burn_rate_value, (int, float)) and isinstance(period_count, int) and period_count > 0:
        granularity = None
        for entry in periods:
            if isinstance(entry, Mapping):
                granularity = entry.get("granularity")
                if granularity:
                    break
        if granularity == "month":
            unit_label = "units/month"
            span_label = "month" if period_count == 1 else "months"
        elif granularity == "year":
            unit_label = "units/year"
            span_label = "year" if period_count == 1 else "years"
        elif granularity == "week":
            unit_label = "units/week"
            span_label = "week" if period_count == 1 else "weeks"
        else:
            unit_label = "units per period"
            span_label = "period" if period_count == 1 else "periods"
        message_parts.append(
            f"Average burn rate over the last {period_count} {span_label}: {burn_rate_value:,.2f} {unit_label}."
        )

    multiplier = insights.get("multiplier")
    scaled = insights.get("scaled")
    if multiplier is not None and isinstance(scaled, (int, float)):
        message_parts.append(f"Multiplying by {multiplier:g} yields {scaled:,.2f}.")
    return " ".join(message_parts) if message_parts else "Usage results are ready."


def describe_sales_message(insights: dict | None) -> str:
    if not insights:
        return "I could not calculate sales for that request."
    item = insights.get("item")
    description = insights.get("description")
    period = insights.get("period")
    sales_value = insights.get("sales")
    periods = insights.get("periods") or []
    total_sales = insights.get("total_sales")
    message_parts: list[str] = []
    if item and description:
        item_label = f"{item} ({description})"
    elif description and not item:
        item_label = description
    else:
        item_label = item

    if isinstance(periods, list) and len(periods) > 1:
        per_texts: list[str] = []
        for entry in periods:
            label = entry.get("label")
            value = entry.get("sales")
            if label and isinstance(value, (int, float)):
                per_texts.append(f"{label}: {value:,.2f} units invoiced")
        if per_texts:
            prefix = f"{item_label} sales by period" if item_label else "Sales by period"
            message_parts.append(f"{prefix} - " + "; ".join(per_texts) + ". Returns reduce the totals.")
        if isinstance(total_sales, (int, float)):
            start_label = periods[0].get("label")
            end_label = periods[-1].get("label")
            if start_label and end_label:
                range_label = f"{start_label} - {end_label}" if start_label != end_label else start_label
            else:
                range_label = "the requested range"
            message_parts.append(f"Total invoiced for {range_label}: {total_sales:,.2f} units.")
    else:
        if item_label and period and isinstance(sales_value, (int, float)):
            message_parts.append(f"{item_label} sales for {period}: {sales_value:,.2f} units invoiced.")
        elif isinstance(sales_value, (int, float)):
            message_parts.append(f"Sales for the requested period: {sales_value:,.2f} units invoiced.")

    multiplier = insights.get("multiplier")
    scaled = insights.get("scaled")
    if multiplier is not None and isinstance(scaled, (int, float)):
        message_parts.append(f"Multiplying by {multiplier:g} yields {scaled:,.2f}.")
    return " ".join(message_parts) if message_parts else "Sales results are ready."


def describe_multi_item_message(insights: dict | None) -> str:
    if not insights:
        return "I could not summarize multiple items for that scope."
    period = insights.get("period") or "the requested window"
    row_count = insights.get("row_count")
    zero_focus = insights.get("zero_focus")
    zero_count = insights.get("zero_item_count")
    top_item = insights.get("top_item") or {}
    message_parts: list[str] = []
    if row_count:
        message_parts.append(f"I pulled {row_count} items for {period}.")
    if zero_focus:
        if zero_count:
            message_parts.append(f"{zero_count} item(s) showed zero usage.")
        else:
            message_parts.append("None of the items were completely idle.")
    if isinstance(top_item, dict):
        item_code = top_item.get("Item")
        usage_value = top_item.get("Usage")
        if item_code and isinstance(usage_value, (int, float)):
            descriptor = "lowest usage" if zero_focus else "highest usage"
            message_parts.append(f"{descriptor.title()}: {item_code} at {usage_value:,.2f} units.")
    scope_note = insights.get("scope_note")
    if scope_note:
        message_parts.append(scope_note)
    return " ".join(message_parts) if message_parts else "Multi-item summary is ready."


def describe_all_items_message(insights: dict | None) -> str:
    if not insights:
        return "I could not build the all-items summary."
    period = insights.get("period") or "the requested window"
    zero_count = insights.get("zero_item_count")
    active_count = insights.get("active_item_count")
    top_items = insights.get("top_items") or []
    message_parts: list[str] = [f"All-items summary for {period} is ready."]
    if zero_count is not None:
        message_parts.append(f"{zero_count} item(s) had no usage.")
    if active_count is not None:
        message_parts.append(f"{active_count} item(s) showed activity.")
    if isinstance(top_items, list) and top_items:
        highlights = []
        for entry in top_items[:2]:
            item_code = entry.get("Item")
            usage_value = entry.get("Usage")
            if item_code and isinstance(usage_value, (int, float)):
                highlights.append(f"{item_code}: {usage_value:,.2f}")
        if highlights:
            message_parts.append("Top movers: " + ", ".join(highlights) + ".")
    scope_note = insights.get("scope_note")
    if scope_note:
        message_parts.append(scope_note)
    return " ".join(message_parts)


def describe_compare_message(insights: dict | None) -> str:
    if not insights:
        return "Comparison results are ready."
    item = insights.get("item")
    periods = insights.get("periods") or []
    if len(periods) < 2:
        if item:
            return f"I only found one month of usage for {item}."
        return "I only found one month of usage for the requested item."
    anchor = periods[0]
    baseline = periods[1]
    diff = insights.get("difference")
    pct = insights.get("percent_change")
    message = (
        f"{item or 'This item'} usage {anchor['Period']} vs {baseline['Period']}: "
        f"{anchor['Usage']:,.2f} vs {baseline['Usage']:,.2f} units."
    )
    if diff is not None:
        message += f" Change {diff:,.2f}"
        if isinstance(pct, (int, float)):
            message += f" ({pct:+.1%})."
    return message


def describe_why_drop_message(insights: dict | None) -> str:
    if not insights:
        return "Trend results are ready."
    item = insights.get("item")
    recent = insights.get("recent")
    if not isinstance(recent, Mapping):
        recent = {}
    previous = insights.get("previous")
    if not isinstance(previous, Mapping):
        previous = {}
    parts: list[str] = []
    if item and recent:
        parts.append(f"{item} {recent.get('Period', 'latest period')} usage {recent.get('Usage', 0):,.2f} units.")
    if previous:
        parts.append(
            f"Prior period {previous.get('Period', '')} was {previous.get('Usage', 0):,.2f} units."
        )
    drop_amount = insights.get("drop_amount")
    drop_percent = insights.get("drop_percent")
    if isinstance(drop_amount, (int, float)):
        change_phrase = "Increase" if drop_amount > 0 else "Drop"
        phrase = f"{change_phrase} of {abs(drop_amount):,.2f} units"
        if isinstance(drop_percent, (int, float)):
            phrase += f" ({drop_percent:+.1%})"
        parts.append(phrase + ".")
    worst = insights.get("worst_drop")
    if not isinstance(worst, Mapping):
        worst = {}
    if worst.get("change"):
        parts.append(
            f"Largest drop occurred from {worst.get('from_period')} to {worst.get('to_period')} "
            f"({worst.get('change'):,.2f})."
        )
    timeline = insights.get("timeline") or []
    if timeline:
        parts.append(f"Review the {len(timeline)}-month timeline for details.")
    return " ".join(part.strip() for part in parts if part).strip()


def describe_inventory_message(insights: dict | None) -> str:
    if not insights:
        return "Inventory results are ready."
    item = insights.get("item")
    row_count = insights.get("row_count", 0) or 0
    raw_sample = insights.get("sample")
    sample = raw_sample if isinstance(raw_sample, dict) else {}
    site_codes = insights.get("sites") or []
    site_covers_all = bool(insights.get("site_covers_all"))
    site_label = describe_site_scope(site_codes, site_covers_all) or "the requested scope"
    scope_note = insights.get("scope_note")
    class_filters = insights.get("class_filters") or []
    class_covers_all = bool(insights.get("class_covers_all"))
    class_label = describe_class_scope(class_filters, class_covers_all)
    below_order_point = bool(insights.get("below_order_point"))
    limited = bool(insights.get("limited"))
    sort_label = insights.get("sort") or ("shortfall vs order point" if below_order_point else "order point")
    filter_key = insights.get("filter")
    zero_on_hand = filter_key == "zero_on_hand"

    filter_bits: list[str] = []
    if class_label:
        filter_bits.append("all classes" if class_covers_all else f"class {class_label}")
    if below_order_point:
        filter_bits.append("below their order point")
    if zero_on_hand:
        filter_bits.append("zero on hand")
    filter_summary = human_join(filter_bits)

    if row_count == 0:
        if item:
            message = f"I could not find inventory rows for {item}."
        else:
            message = "No inventory rows matched the filters."
        if scope_note:
            message = f"{message} {scope_note}"
        return message.strip()
    if item and isinstance(sample, dict):
        parts = [f"Inventory snapshot for {item} ({site_label})."]
        avail = sample.get("Avail")
        order_point = sample.get("OrderPoint")
        if isinstance(avail, (int, float)) and isinstance(order_point, (int, float)):
            parts.append(f"{avail:,.0f} available vs {order_point:,.0f} order point.")
        on_hand = sample.get("OnHand")
        if isinstance(on_hand, (int, float)):
            parts.append(f"On hand {on_hand:,.0f}.")
        on_order = sample.get("OnOrder")
        if isinstance(on_order, (int, float)):
            parts.append(f"On order {on_order:,.0f}.")
        if scope_note:
            parts.append(scope_note)
        return " ".join(parts).strip()

    scope_fragment = f" for {site_label}" if site_label else ""
    if filter_summary:
        summary = f"{row_count} items{scope_fragment} matched the filters ({filter_summary})."
        if sort_label:
            summary += f" Sorted by {sort_label}."
        if scope_note:
            summary = f"{summary} {scope_note}"
        return summary.strip()

    summary = (
        f"Top {row_count} items{scope_fragment} ordered by {sort_label}."
        if limited
        else f"{row_count} items{scope_fragment} ordered by {sort_label}."
    )
    if scope_note:
        summary = f"{summary} {scope_note}"
    return summary + " Use an item number to drill in further."


def describe_inventory_usage_message(insights: dict | None) -> str:
    if not insights:
        return "Inventory and usage snapshot is ready."
    item = insights.get("item")
    inventory = insights.get("inventory") or {}
    usage_info = insights.get("usage") or {}
    parts: list[str] = []
    if item:
        parts.append(f"{item} availability vs usage.")
    avail = inventory.get("Avail")
    order_point = inventory.get("OrderPoint")
    if isinstance(avail, Number) and isinstance(order_point, Number):
        gap = avail - order_point
        relation = "above" if gap >= 0 else "below"
        parts.append(
            f"{avail:,.0f} available vs {order_point:,.0f} order point "
            f"({abs(gap):,.0f} {relation})."
        )
    elif isinstance(avail, Number):
        parts.append(f"{avail:,.0f} available today.")
    usage_value = usage_info.get("Usage")
    usage_label = usage_info.get("Label") or usage_info.get("Period")
    if isinstance(usage_value, Number) and usage_label:
        parts.append(f"{usage_label} usage {abs(usage_value):,.0f} units.")
    coverage = insights.get("coverage_months")
    if isinstance(coverage, Number) and coverage > 0:
        parts.append(f"That covers roughly {coverage:.1f} months at the latest usage rate.")
    elif isinstance(coverage, Number) and coverage == 0:
        parts.append("No recent usage was recorded, so coverage is unlimited for now.")
    elif isinstance(coverage, Number) and coverage < 0:
        parts.append(f"Usage outpaced availability by {abs(coverage):.1f} months.")
    order_point_gap = insights.get("order_point_gap")
    if isinstance(order_point_gap, Number) and not (
        isinstance(avail, Number) and isinstance(order_point, Number)
    ):
        relation = "above" if order_point_gap >= 0 else "below"
        parts.append(f"Availability is {abs(order_point_gap):,.0f} units {relation} the order point.")
    return " ".join(part.strip() for part in parts if part).strip() or "Inventory and usage snapshot is ready."


def describe_reorder_message(insights: dict | None) -> str:
    if not insights:
        return "Unable to summarize the reorder list."
    count = insights.get("count", 0) or 0
    site_codes = insights.get("sites") or []
    site_covers_all = bool(insights.get("site_covers_all"))
    site_label = describe_site_scope(site_codes, site_covers_all) or "the requested scope"
    scope_note = insights.get("scope_note")
    if count == 0:
        message = f"All {site_label} items meet their order points right now."
        if scope_note:
            message = f"{message} {scope_note}"
        return message.strip()
    top_row = insights.get("top_row")
    if not isinstance(top_row, dict):
        top_row = {}
    requested_item = insights.get("item")
    if requested_item:
        parts: list[str] = []
        shortfall = top_row.get("Shortfall")
        order_point = top_row.get("OrderPoint")
        on_hand = top_row.get("OnHand")
        avail = top_row.get("Avail")
        on_order = top_row.get("OnOrder")
        if isinstance(shortfall, Number) and isinstance(order_point, Number):
            availability_note = None
            if isinstance(on_hand, Number):
                availability_note = f"{on_hand:,.0f} on hand today"
            elif isinstance(avail, Number):
                availability_note = f"{avail:,.0f} available today"
            base_sentence = (
                f"{requested_item} ({site_label}) needs {abs(shortfall):,.0f} units to reach its {order_point:,.0f} order point"
            )
            if availability_note:
                base_sentence += f" ({availability_note})."
            else:
                base_sentence += "."
            if isinstance(on_order, Number) and on_order > 0:
                base_sentence += f" {on_order:,.0f} already on order."
            parts.append(base_sentence)
        else:
            parts.append(f"{requested_item} currently shows the largest shortfall.")

        usage_info = insights.get("usage_based_recommendation") or {}
        months = usage_info.get("months")
        total_usage = usage_info.get("total")
        avg_usage = usage_info.get("average")
        cover_need = usage_info.get("cover_need")
        recommended = usage_info.get("recommended_buy")
        if months and total_usage is not None:
            usage_sentence = f"Last {months} months consumed {total_usage:,.0f} units"
            if avg_usage is not None:
                usage_sentence += f" (~{avg_usage:,.0f}/month burn rate)"
            usage_sentence += "."
            parts.append(usage_sentence)
            if cover_need is not None:
                parts.append(
                    f"At that burn rate you'd need roughly {cover_need:,.0f} more units to cover another {months} months beyond today's availability."
                )
            if recommended is not None:
                parts.append(
                    f"I'd plan on ordering around {recommended:,.0f} units (max of usage coverage vs order-point shortfall)."
                )
        if scope_note:
            parts.append(scope_note)
        return " ".join(part for part in parts if part).strip()

    item = top_row.get("Item")
    shortfall = top_row.get("Shortfall")
    order_point = top_row.get("OrderPoint")
    avail = top_row.get("Avail")
    message = [
        f"{count} items are below their order point for {site_label}.",
        "Worst gaps first means the table is sorted by shortfall (order point minus available quantity) so the most urgent misses float to the top.",
    ]
    if item:
        if all(isinstance(val, (int, float)) for val in (shortfall, order_point, avail)):
            message.append(
                f"{item} needs {shortfall:,.0f} more units to reach its {order_point:,.0f} target ({avail:,.0f} available today)."
            )
        else:
            message.append(f"{item} currently shows the largest shortfall.")
    if scope_note:
        message.append(scope_note)
    return " ".join(message)


def _safe_float(value) -> float | None:
    try:
        number = float(value)
    except (TypeError, ValueError):
        return None
    if math.isnan(number):
        return None
    return number


def _extract_metric_series(insights: Mapping | None) -> tuple[list[tuple[str, float]], str | None, float | None]:
    if not isinstance(insights, Mapping):
        return [], None, None
    metric_key = insights.get("metric_key")
    if not isinstance(metric_key, str):
        for candidate in ("usage", "sales"):
            if candidate in insights:
                metric_key = candidate
                break
    periods = insights.get("periods") or []
    series: list[tuple[str, float]] = []
    if metric_key:
        for entry in periods:
            if not isinstance(entry, Mapping):
                continue
            label = entry.get("label")
            value = entry.get(metric_key)
            if label and isinstance(value, (int, float)):
                series.append((label, float(value)))
    total_key = insights.get("total_metric_key")
    if not isinstance(total_key, str) and isinstance(metric_key, str):
        guessed_key = f"total_{metric_key}"
        if guessed_key in insights:
            total_key = guessed_key
    if not isinstance(total_key, str):
        for fallback in ("total_usage", "total_sales"):
            if fallback in insights:
                total_key = fallback
                break
    total_value = None
    if isinstance(total_key, str):
        total_raw = insights.get(total_key)
        if isinstance(total_raw, (int, float)):
            total_value = float(total_raw)
    column_label = insights.get("column_label")
    if not isinstance(column_label, str) and isinstance(metric_key, str):
        column_label = metric_key.title()
    return series, column_label, total_value


def _build_metric_choice_note(lowered_prompt: str, intent: str | None) -> str:
    normalized_intent = (intent or "").lower()
    mentions_sales = any(keyword in lowered_prompt for keyword in SALES_INTENT_KEYWORDS)
    mentions_usage = any(keyword in lowered_prompt for keyword in USAGE_METRIC_KEYWORDS)
    if mentions_sales and normalized_intent in {"usage", "report"}:
        return (
            "Usage looks at GP inventory adjustments/consumption (negative values mean product left stock). "
            "Ask for sales or invoices if you need customer shipment totals."
        )
    if mentions_usage and normalized_intent == "sales":
        return (
            "Sales intent returns SOP invoices and shipments. "
            "If you were looking for manufacturing or inventory usage, rerun as a usage report."
        )
    return ""


def _build_period_scope_note(
    lowered_prompt: str,
    context: Mapping | None,
    insights: Mapping | None,
) -> str:
    series, column_label, total_value = _extract_metric_series(insights)
    if not series:
        return ""
    metric_label = (column_label or "usage").lower()
    period_count = len(series)
    mentions_total = any(keyword in lowered_prompt for keyword in TOTAL_SCOPE_KEYWORDS)
    if period_count > 1:
        start_label = series[0][0]
        end_label = series[-1][0]
        coverage = start_label if start_label == end_label else f"{start_label} - {end_label}"
        parts = [f"Coverage spans {period_count} periods ({coverage})"]
        if total_value is not None:
            parts[-1] += f" totaling {total_value:,.2f} {metric_label}"
        parts[-1] += "."
        highest = max(series, key=lambda entry: entry[1])
        lowest = min(series, key=lambda entry: entry[1])
        if highest[1] != lowest[1]:
            parts.append(
                f"Peak {metric_label} was {highest[0]} at {highest[1]:,.2f}, vs {lowest[0]} at {lowest[1]:,.2f} on the low end."
            )
        return " ".join(parts)

    label, amount = series[0]
    if mentions_total:
        return f"Only {label} matched that request, so the total equals that single period ({amount:,.2f} {metric_label})."

    prompt_period_count = 0
    if isinstance(context, Mapping):
        try:
            prompt_period_count = int(context.get("prompt_period_count") or 0)
        except (TypeError, ValueError):
            prompt_period_count = 0
    if prompt_period_count and prompt_period_count > 1:
        return (
            f"I only found one period ({label}) even though multiple months were requested, "
            f"so totals mirror that month at {amount:,.2f} {metric_label}."
        )
    return ""


def _build_inventory_field_note(
    lowered_prompt: str,
    context_type: str | None,
    sql_payload: Mapping | None,
) -> str:
    intent = (context_type or "").lower()
    if intent not in {"inventory", "reorder"} or not isinstance(sql_payload, Mapping):
        return ""
    insights = sql_payload.get("insights")
    sample: Mapping | None = None
    if intent == "inventory" and isinstance(insights, Mapping):
        sample_candidate = insights.get("sample")
        if isinstance(sample_candidate, Mapping):
            sample = sample_candidate
    if intent == "reorder" and isinstance(insights, Mapping):
        top_row = insights.get("top_row")
        if isinstance(top_row, Mapping):
            sample = top_row
    if sample is None:
        data = sql_payload.get("data")
        if isinstance(data, list) and data:
            first = data[0]
            if isinstance(first, Mapping):
                sample = first
    if not isinstance(sample, Mapping):
        return ""
    avail = _safe_float(sample.get("Avail") or sample.get("QtyAvailable"))
    on_hand = _safe_float(sample.get("OnHand"))
    on_order = _safe_float(sample.get("OnOrder"))
    if avail is None and on_hand is None:
        return ""
    mention_avail = any(keyword in lowered_prompt for keyword in AVAILABLE_FIELD_KEYWORDS)
    mention_on_hand = any(keyword in lowered_prompt for keyword in ON_HAND_FIELD_KEYWORDS)
    difference = None
    if avail is not None and on_hand is not None:
        difference = on_hand - avail
    highlight = difference is not None and abs(difference) >= 1
    if not (mention_avail or mention_on_hand or highlight):
        return ""
    parts: list[str] = []
    if on_hand is not None:
        parts.append(f"On hand shows the physical stock ({on_hand:,.0f} units).")
    if avail is not None:
        if difference is not None and difference > 0:
            parts.append(f"Available backs out {difference:,.0f} allocated units, leaving {avail:,.0f} ready.")
        else:
            parts.append(f"Available after allocations is {avail:,.0f} units.")
    if on_order and on_order > 0:
        parts.append(f"{on_order:,.0f} more are on purchase orders and not yet available.")
    return " ".join(parts)


def build_business_context_note(prompt: str, context: Mapping | None, sql_payload: Mapping | None) -> str:
    if not prompt or not isinstance(context, Mapping) or not isinstance(sql_payload, Mapping):
        return ""
    lowered = prompt.lower()
    intent = context.get("intent")
    insights = sql_payload.get("insights")
    context_type = sql_payload.get("context_type") or intent
    parts: list[str] = []
    metric_note = _build_metric_choice_note(lowered, intent if isinstance(intent, str) else None)
    if metric_note:
        parts.append(metric_note)
    period_note = _build_period_scope_note(lowered, context, insights if isinstance(insights, Mapping) else None)
    if period_note:
        parts.append(period_note)
    inventory_note = _build_inventory_field_note(lowered, context_type if isinstance(context_type, str) else None, sql_payload)
    if inventory_note:
        parts.append(inventory_note)
    return " ".join(part for part in parts if part).strip()


BOM_EXPLOSION_SQL = """
WITH BOM_CTE AS (
    SELECT
        1 AS LevelNumber,
        RTRIM(bom.PPN_I) AS ParentItem,
        NULLIF(RTRIM(bom.BOMNAME_I), '') AS BomName,
        RTRIM(bom.CPN_I) AS ComponentItem,
        bom.QUANTITY_I AS QuantityPerParent,
        RTRIM(bom.UOFM) AS UofM,
        CAST(bom.QUANTITY_I AS decimal(38, 10)) AS ExtendedQuantity,
        CAST('>' + RTRIM(bom.PPN_I) + '>' + RTRIM(bom.CPN_I) + '>' AS nvarchar(4000)) AS TraversalPath
    FROM BM010115 AS bom
    WHERE RTRIM(bom.PPN_I) = ?
      AND LEN(RTRIM(bom.CPN_I)) > 0
    UNION ALL
    SELECT
        c.LevelNumber + 1,
        RTRIM(bom.PPN_I),
        NULLIF(RTRIM(bom.BOMNAME_I), ''),
        RTRIM(bom.CPN_I),
        bom.QUANTITY_I,
        RTRIM(bom.UOFM),
        CAST(c.ExtendedQuantity * bom.QUANTITY_I AS decimal(38, 10)),
        CAST(c.TraversalPath + RTRIM(bom.CPN_I) + '>' AS nvarchar(4000))
    FROM BOM_CTE AS c
    INNER JOIN BM010115 AS bom
        ON RTRIM(bom.PPN_I) = c.ComponentItem
    WHERE LEN(RTRIM(bom.CPN_I)) > 0
      AND CHARINDEX('>' + RTRIM(bom.CPN_I) + '>', c.TraversalPath) = 0
)
SELECT
    c.LevelNumber,
    c.ParentItem,
    parent_desc.ITEMDESC AS ParentDescription,
    c.ComponentItem,
    comp_desc.ITEMDESC AS ComponentDescription,
    c.QuantityPerParent,
    c.UofM,
    c.ExtendedQuantity,
    c.BomName
FROM BOM_CTE AS c
LEFT JOIN IV00101 AS parent_desc
    ON RTRIM(parent_desc.ITEMNMBR) = c.ParentItem
LEFT JOIN IV00101 AS comp_desc
    ON RTRIM(comp_desc.ITEMNMBR) = c.ComponentItem
ORDER BY c.LevelNumber, c.ParentItem, c.ComponentItem
OPTION (MAXRECURSION 32);
"""


def _summarize_bom_rows(item_code: str, rows: Iterable[Mapping]) -> str:
    rows_iter = list(rows)
    if not rows_iter:
        return f"No bill of materials rows found for {item_code}."
    max_level = 0
    unique_components: set[str] = set()
    for row in rows_iter:
        level_value = row.get("LevelNumber") if isinstance(row, Mapping) else None
        try:
            level_int = int(level_value)
        except (TypeError, ValueError):
            level_int = 0
        if level_int > max_level:
            max_level = level_int
        component_value = row.get("ComponentItem") if isinstance(row, Mapping) else None
        if isinstance(component_value, str) and component_value.strip():
            unique_components.add(component_value.strip())
    if not unique_components:
        return f"No bill of materials rows found for {item_code}."
    component_label = "component" if len(unique_components) == 1 else "components"
    level_label = "level" if max_level == 1 else "levels"
    return f"{item_code} BOM spans {max_level} {level_label} covering {len(unique_components)} unique {component_label}."


def maybe_handle_bom_explosion(
    cursor: pyodbc.Cursor, prompt: str | None, context: dict | None
) -> dict | None:
    if not prompt or not looks_like_bom_prompt(prompt):
        return None
    item_code = resolve_item_from_context(prompt, context)
    if not item_code:
        return {
            "error": "I need an item number to explode the bill of materials. Please mention the specific item (e.g., 'SOARBLM00').",
            "data": None,
            "sql": None,
            "context_type": CUSTOM_SQL_INTENT,
        }
    params = (item_code,)
    sql_preview = format_sql_preview(BOM_EXPLOSION_SQL, params)
    try:
        cursor.execute(BOM_EXPLOSION_SQL, params)
        fetched = cursor.fetchall()
        columns = [col[0] for col in cursor.description] if cursor.description else []
    except pyodbc.Error as err:
        return {
            "error": f"Bill of materials query failed: {err}",
            "data": None,
            "sql": sql_preview,
            "context_type": CUSTOM_SQL_INTENT,
        }
    rows: list[dict] = []
    if columns:
        for record in fetched:
            rows.append(dict(zip(columns, record)))
    summary = _summarize_bom_rows(item_code, rows)
    insights = {"summary": summary, "row_count": len(rows)}
    return {
        "data": rows,
        "sql": sql_preview,
        "context_type": CUSTOM_SQL_INTENT,
        "insights": insights,
    }


def describe_custom_sql_message(insights: dict | None) -> str:
    if not insights:
        return "Custom SQL results are ready."
    parts: list[str] = []
    summary = insights.get("summary")
    if isinstance(summary, str) and summary.strip():
        parts.append(summary.strip())
    row_count = insights.get("row_count")
    if isinstance(row_count, int):
        label = "row" if row_count == 1 else "rows"
        parts.append(f"Returned {row_count} {label}.")
    note = insights.get("note")
    if isinstance(note, str) and note.strip():
        parts.append(note.strip())
    return " ".join(parts) if parts else "Custom SQL results are ready."


LLM_SNAPSHOT_ROW_LIMIT = 3
LLM_SNAPSHOT_MAX_CHARS = 2000
LLM_SNAPSHOT_NUMERIC_KEYS = (
    "total",
    "average",
    "avg",
    "sum",
    "scaled",
    "count",
    "difference",
    "percent",
    "pct",
    "coverage",
    "gap",
)


def build_llm_data_snapshot(
    data,
    insights: Mapping | None,
    *,
    context_type: str | None = None,
    sql_text: str | None = None,
) -> str | None:
    row_count = _infer_snapshot_row_count(data, insights)
    rows = _extract_snapshot_rows(data, limit=LLM_SNAPSHOT_ROW_LIMIT)
    metrics = _extract_snapshot_metrics(insights)
    period_info = _extract_snapshot_periods(insights)
    summary_parts: list[str] = []
    if context_type:
        summary_parts.append(f"context={context_type}")
    if row_count is not None:
        summary_parts.append(f"rows_returned={row_count}")
    if period_info:
        summary_parts.append(f"periods={_snapshot_json(period_info)}")
    if metrics:
        summary_parts.append(f"metrics={_snapshot_json(metrics)}")
    if not rows and isinstance(insights, Mapping):
        top_item = insights.get("top_item")
        if isinstance(top_item, Mapping):
            normalized_top = _normalize_snapshot_row(top_item)
            if normalized_top:
                rows.append(normalized_top)
        top_items = insights.get("top_items")
        if isinstance(top_items, list):
            for entry in top_items:
                if len(rows) >= LLM_SNAPSHOT_ROW_LIMIT:
                    break
                normalized_entry = _normalize_snapshot_row(entry)
                if normalized_entry:
                    rows.append(normalized_entry)
    if rows:
        summary_parts.append(f"sample_rows={_snapshot_json(rows)}")
    if isinstance(sql_text, str):
        sql_compact = " ".join(sql_text.split())
        if sql_compact:
            summary_parts.append(f"sql_preview={_truncate_snapshot(sql_compact)}")
    if not summary_parts:
        return None
    snapshot = " | ".join(summary_parts)
    if len(snapshot) > LLM_SNAPSHOT_MAX_CHARS:
        snapshot = snapshot[: LLM_SNAPSHOT_MAX_CHARS - 3] + "..."
    return snapshot


def _truncate_snapshot(text: str, limit: int = 400) -> str:
    if len(text) <= limit:
        return text
    return text[: limit - 3] + "..."


def _infer_snapshot_row_count(data, insights: Mapping | None) -> int | None:
    if isinstance(data, pd.DataFrame):
        return int(data.shape[0])
    if isinstance(data, list):
        return len(data)
    if isinstance(data, Mapping):
        return 1 if data else 0
    if isinstance(insights, Mapping):
        for key in ("row_count", "scanned_count", "count"):
            value = insights.get(key)
            if isinstance(value, Number) and not isinstance(value, bool):
                try:
                    return int(value)
                except (TypeError, ValueError):
                    continue
    return None


def _extract_snapshot_rows(data, *, limit: int) -> list[dict]:
    rows: list[dict] = []
    if data is None:
        return rows
    if isinstance(data, pd.DataFrame):
        if data.empty:
            return rows
        try:
            records = data.head(limit).to_dict(orient="records")
        except (ValueError, AttributeError):
            records = []
        for record in records:
            normalized = _normalize_snapshot_row(record)
            if normalized:
                rows.append(normalized)
        return rows
    if isinstance(data, list):
        for row in data:
            if len(rows) >= limit:
                break
            normalized = _normalize_snapshot_row(row)
            if normalized:
                rows.append(normalized)
        return rows
    normalized = _normalize_snapshot_row(data)
    if normalized:
        rows.append(normalized)
    return rows


def _normalize_snapshot_row(row) -> dict | None:
    if row is None:
        return None
    if isinstance(row, Mapping):
        normalized: dict[str, object] = {}
        for key, value in row.items():
            normalized[str(key)] = _coerce_snapshot_value(value)
        return normalized
    if hasattr(row, "_asdict"):
        return _normalize_snapshot_row(row._asdict())
    if isinstance(row, Iterable) and not isinstance(row, (str, bytes)):
        normalized_iterable: dict[str, object] = {}
        for idx, value in enumerate(row):
            normalized_iterable[f"col_{idx}"] = _coerce_snapshot_value(value)
        return normalized_iterable
    return {"value": _coerce_snapshot_value(row)}


def _extract_snapshot_metrics(insights: Mapping | None) -> dict:
    metrics: dict[str, float] = {}
    if not isinstance(insights, Mapping):
        return metrics

    def _scan(mapping: Mapping, prefix: str = "") -> None:
        if len(metrics) >= 12:
            return
        for key, value in mapping.items():
            label = f"{prefix}.{key}" if prefix else str(key)
            if isinstance(value, Mapping):
                _scan(value, label)
                if len(metrics) >= 12:
                    return
                continue
            if isinstance(value, Number) and not isinstance(value, bool):
                lowered = label.lower()
                if any(token in lowered for token in LLM_SNAPSHOT_NUMERIC_KEYS):
                    try:
                        metrics[label] = float(value)
                    except (TypeError, ValueError):
                        continue
                    if len(metrics) >= 12:
                        return

    _scan(insights)
    return metrics


def _extract_snapshot_periods(insights: Mapping | None) -> dict:
    if not isinstance(insights, Mapping):
        return {}
    period_info: dict[str, object] = {}
    label = insights.get("period") or insights.get("period_label")
    if isinstance(label, str) and label.strip():
        period_info["label"] = label.strip()
    start = insights.get("period_start")
    end = insights.get("period_end")
    if start:
        period_info["start"] = _coerce_snapshot_value(start)
    if end:
        period_info["end"] = _coerce_snapshot_value(end)
    periods = insights.get("periods")
    if isinstance(periods, list) and periods:
        cleaned: list[dict] = []
        for entry in periods[:LLM_SNAPSHOT_ROW_LIMIT]:
            normalized = _normalize_snapshot_row(entry)
            if normalized:
                cleaned.append(normalized)
        if cleaned:
            period_info["series"] = cleaned
    resolved = insights.get("resolved_periods")
    if isinstance(resolved, list) and resolved and "series" not in period_info:
        cleaned: list[dict] = []
        for entry in resolved[:LLM_SNAPSHOT_ROW_LIMIT]:
            normalized = _normalize_snapshot_row(entry)
            if normalized:
                cleaned.append(normalized)
        if cleaned:
            period_info["series"] = cleaned
    return period_info


def _coerce_snapshot_value(value):
    if value is None:
        return None
    try:
        pd_isna = pd.isna  # type: ignore[attr-defined]
    except AttributeError:  # pragma: no cover - pandas always available
        pd_isna = None
    if pd_isna is not None:
        try:
            if pd_isna(value):
                return None
        except Exception:
            pass
    if isinstance(value, bool):
        return value
    if isinstance(value, int):
        return value
    if isinstance(value, float):
        if math.isnan(value) or math.isinf(value):
            return None
        return value
    if isinstance(value, Number):
        number = float(value)
        if math.isnan(number) or math.isinf(number):
            return None
        return number
    if isinstance(value, (datetime.datetime, datetime.date, datetime.time)):
        return value.isoformat()
    if hasattr(value, "isoformat"):
        try:
            return value.isoformat()  # pandas Timestamp
        except Exception:
            pass
    if hasattr(value, "item"):
        try:
            return _coerce_snapshot_value(value.item())
        except Exception:
            pass
    return str(value)


def _snapshot_json(payload: object) -> str:
    return json.dumps(payload, default=_snapshot_default)


def _snapshot_default(value):
    coerced = _coerce_snapshot_value(value)
    if isinstance(coerced, float) and (math.isnan(coerced) or math.isinf(coerced)):
        return None
    return coerced


def _column_matches_keywords(column_name: str | None, keywords: Sequence[str]) -> bool:
    if not column_name:
        return False
    lowered = column_name.lower()
    return any(keyword in lowered for keyword in keywords)


def _first_non_null(values: Sequence[object]) -> object | None:
    for value in values:
        if value is not None:
            return value
    return None


def _is_dimension_column(column_name: str, values: Sequence[object]) -> bool:
    sample = _first_non_null(values)
    if sample is None:
        return False
    if isinstance(sample, (datetime.date, datetime.datetime, str)):
        return True
    if isinstance(sample, Number) and not isinstance(sample, bool):
        return _column_matches_keywords(column_name, CUSTOM_SQL_CHART_DIMENSION_KEYWORDS)
    return False


def _is_metric_column(values: Sequence[object]) -> bool:
    has_numeric = False
    for value in values:
        if value is None:
            continue
        if isinstance(value, Number) and not isinstance(value, bool):
            has_numeric = True
            continue
        return False
    return has_numeric


def _humanize_column_label(column_name: str | None) -> str:
    if not column_name:
        return ""
    cleaned = re.sub(r"[_\s]+", " ", column_name).strip()
    return cleaned.title() if cleaned else column_name


def _format_dimension_value(value: object, column_name: str) -> str | None:
    if value is None:
        return None
    if isinstance(value, (datetime.date, datetime.datetime)):
        return value.strftime("%Y-%m-%d")
    if isinstance(value, Number) and not isinstance(value, bool):
        lowered = column_name.lower()
        if "month" in lowered:
            try:
                month_index = int(value)
            except (TypeError, ValueError):
                month_index = None
            if month_index and 1 <= month_index <= 12:
                month_label = calendar.month_abbr[month_index] or str(month_index)
                return month_label.upper()
        if isinstance(value, (int, float)):
            return f"{value:g}"
        return str(value)
    return str(value)


def build_custom_sql_chart(
    rows: list[Mapping[str, object]],
    columns: Sequence[str],
    item_code: str | None = None,
) -> tuple[dict | None, str | None, str | None]:
    if len(rows) < 2:
        return None, None, None
    column_order: list[str] = list(columns) if columns else []
    if not column_order:
        for row in rows:
            for key in row.keys():
                if key not in column_order:
                    column_order.append(key)
    if not column_order:
        return None, None, None

    values_by_column: dict[str, list[object]] = {}
    for column_name in column_order:
        values_by_column[column_name] = [
            row.get(column_name) for row in rows if isinstance(row, Mapping)
        ]

    dimension_candidates: list[tuple[int, str]] = []
    metric_candidates: list[tuple[int, str]] = []

    for column_name in column_order:
        values = values_by_column.get(column_name) or []
        if not values:
            continue
        if _is_dimension_column(column_name, values):
            score = 2 if _column_matches_keywords(column_name, CUSTOM_SQL_CHART_DIMENSION_KEYWORDS) else 1
            dimension_candidates.append((score, column_name))
        if _is_metric_column(values):
            score = 2 if _column_matches_keywords(column_name, CUSTOM_SQL_CHART_METRIC_KEYWORDS) else 1
            metric_candidates.append((score, column_name))

    if not dimension_candidates:
        for column_name in column_order:
            values = values_by_column.get(column_name) or []
            sample = _first_non_null(values)
            if isinstance(sample, str) and sample.strip():
                dimension_candidates.append((0, column_name))
                break

    if not dimension_candidates:
        return None, None, None

    def _sort_key(candidate: tuple[int, str]) -> tuple[int, int]:
        column_name = candidate[1]
        try:
            order = column_order.index(column_name)
        except ValueError:
            order = len(column_order)
        return (-candidate[0], order)

    dimension_candidates.sort(key=_sort_key)
    dimension_field = dimension_candidates[0][1]

    metric_candidates = [candidate for candidate in metric_candidates if candidate[1] != dimension_field]
    if not metric_candidates:
        for column_name in column_order:
            if column_name == dimension_field:
                continue
            values = values_by_column.get(column_name) or []
            if _is_metric_column(values):
                metric_candidates.append((0, column_name))

    if not metric_candidates:
        return None, None, None

    metric_candidates.sort(key=_sort_key)
    metric_field = metric_candidates[0][1]

    chart_points: list[dict[str, object]] = []
    for sequence, row in enumerate(rows):
        raw_label = row.get(dimension_field)
        label = _format_dimension_value(raw_label, dimension_field)
        if not label:
            continue
        raw_metric = row.get(metric_field)
        if not isinstance(raw_metric, Number) or isinstance(raw_metric, bool):
            continue
        try:
            metric_value = float(raw_metric)
        except (TypeError, ValueError):
            continue
        if math.isnan(metric_value) or math.isinf(metric_value):
            continue
        chart_points.append(
            {
                "Period": label,
                metric_field: metric_value,
                "_sequence": sequence,
            }
        )

    if len(chart_points) < 2:
        return None, None, None

    value_label = _humanize_column_label(metric_field)
    dimension_label = _humanize_column_label(dimension_field)
    title = f"{value_label} by {dimension_label}".strip()
    chart_payload: dict[str, object] = {
        "type": "line",
        "title": title,
        "data": chart_points,
        "x_field": "Period",
        "y_field": metric_field,
        "value_label": value_label or metric_field,
        "height": 280,
    }
    if item_code:
        chart_payload["item"] = item_code
    return chart_payload, dimension_label or dimension_field, value_label or metric_field


def handle_custom_sql_question(
    cursor: pyodbc.Cursor, prompt: str, today: datetime.date, context: dict | None = None
) -> dict:
    context = context or {}
    bom_payload = maybe_handle_bom_explosion(cursor, prompt, context)
    if bom_payload is not None:
        return bom_payload
    schema = load_allowed_sql_schema(cursor)
    if not schema:
        return {
            "error": "Custom SQL requires schema metadata, but it is unavailable right now.",
            "data": None,
            "sql": None,
            "context_type": CUSTOM_SQL_INTENT,
        }
    schema_summary = summarize_schema_for_prompt(schema)
    context_hint = summarize_sql_context(context)
    plan = call_openai_sql_generator(prompt, today, schema_summary, context_hint)
    if not isinstance(plan, dict):
        return {
            "error": "I wasn't able to design a custom SQL query for that request. Try rephrasing with more specifics.",
            "data": None,
            "sql": None,
            "context_type": CUSTOM_SQL_INTENT,
        }

    sql_text = plan.get("sql")
    valid, reason = validate_custom_sql(sql_text, CUSTOM_SQL_ALLOWED_TABLES)
    if not valid:
        return {
            "error": reason or "The generated SQL was not valid.",
            "data": None,
            "sql": sql_text if isinstance(sql_text, str) else None,
            "context_type": CUSTOM_SQL_INTENT,
        }

    params = normalize_sql_params(plan.get("params"))
    sql_preview = format_sql_preview(sql_text, params) if params else (sql_text or "")

    try:
        cursor.execute(sql_text, params)
        fetched = cursor.fetchmany(CUSTOM_SQL_MAX_ROWS + 1)
        columns = [col[0] for col in cursor.description] if cursor.description else []
    except pyodbc.Error as err:
        return {
            "error": f"Custom SQL failed: {err}",
            "data": None,
            "sql": sql_preview or sql_text,
            "context_type": CUSTOM_SQL_INTENT,
        }

    rows: list[dict] = []
    limit = min(len(fetched), CUSTOM_SQL_MAX_ROWS)
    for raw in fetched[:limit]:
        if columns:
            rows.append(dict(zip(columns, raw)))
        else:
            rows.append({"value": raw})
    truncated = len(fetched) > CUSTOM_SQL_MAX_ROWS
    summary_text = plan.get("summary") if isinstance(plan.get("summary"), str) else ""
    insights = {
        "summary": summary_text,
        "row_count": len(rows),
        "truncated": truncated,
    }
    if truncated:
        insights["note"] = f"Showing first {CUSTOM_SQL_MAX_ROWS} rows."
    chart_payload = None
    chart_caption = None
    chart_warning = None
    if context.get("graph_requested"):
        item_code = context.get("item") if isinstance(context.get("item"), str) else None
        chart_payload, dimension_label, value_label = build_custom_sql_chart(rows, columns, item_code)
        if chart_payload and value_label and dimension_label:
            chart_caption = f"Line chart below: {value_label} by {dimension_label}."
        else:
            chart_warning = (
                "I couldn't convert that result set into a chart. Include a time column plus a numeric metric to plot."
            )

    result = {
        "data": rows,
        "sql": sql_preview or sql_text,
        "context_type": CUSTOM_SQL_INTENT,
        "insights": insights,
    }
    if chart_payload:
        result["chart"] = chart_payload
    if chart_caption:
        result["chart_caption"] = chart_caption
    if chart_warning:
        result["chart_warning"] = chart_warning
    return result


def format_reasoning_for_message(reasoning: Mapping | None) -> str | None:
    if not isinstance(reasoning, Mapping):
        return None
    sections: list[str] = []
    steps_value = reasoning.get("steps")
    if isinstance(steps_value, Sequence) and not isinstance(steps_value, (str, bytes, bytearray)):
        rendered_steps: list[str] = []
        for index, step in enumerate(steps_value[:REASONING_STEP_LIMIT], start=1):
            step_text = step if isinstance(step, str) else str(step)
            step_text = step_text.strip()
            if step_text:
                rendered_steps.append(f"{index}. {step_text}")
        if rendered_steps:
            sections.append("Reasoning steps:\n" + "\n".join(rendered_steps))
    conclusion = reasoning.get("conclusion")
    if isinstance(conclusion, str):
        conclusion_text = conclusion.strip()
        if conclusion_text:
            sections.append(f"Conclusion: {conclusion_text}")
    confidence = reasoning.get("confidence")
    if isinstance(confidence, str):
        confidence_text = confidence.strip()
        if confidence_text:
            sections.append(f"Confidence: {confidence_text}")
    if sections:
        return "\n\n".join(sections)
    return None


def compose_conversational_message(
    prompt: str,
    context: dict,
    sql_payload: dict | None,
    session_history: list[dict],
) -> str:
    """
    Conversational agent: merge the LLM guidance with the SQL agent's findings.
    """
    intent = context.get("intent") or "usage"
    reply_sections: list[str] = []
    llm_reply = context.get("reply")
    if isinstance(llm_reply, str) and llm_reply.strip():
        reply_sections.append(llm_reply.strip())

    if intent == "chitchat":
        chitchat_addon = generate_chitchat_reply(prompt, session_history, llm_reply=llm_reply)
        if chitchat_addon:
            reply_sections.append(chitchat_addon)
        return "\n\n".join(part for part in reply_sections if part).strip()

    if not sql_payload:
        reply_sections.append("I was not able to run the SQL agent for that request.")
        return "\n\n".join(part for part in reply_sections if part).strip()

    error = sql_payload.get("error")
    if error:
        reply_sections.append(error)
        suggestions = sql_payload.get("suggestions")
        if suggestions:
            suggestion_text = format_item_suggestions(suggestions)
            if suggestion_text and suggestion_text not in reply_sections:
                reply_sections.append(suggestion_text)
        if not sql_payload.get("data"):
            return "\n\n".join(part for part in reply_sections if part).strip()

    insights = sql_payload.get("insights")
    if intent in {"usage", "report"}:
        reply_sections.append(describe_usage_message(insights))
    elif intent == "sales":
        reply_sections.append(describe_sales_message(insights))
    elif intent == "inventory":
        reply_sections.append(describe_inventory_message(insights))
    elif intent == "inventory_usage":
        reply_sections.append(describe_inventory_usage_message(insights))
    elif intent == MULTI_ITEM_INTENT:
        reply_sections.append(describe_multi_item_message(insights))
    elif intent == ALL_ITEMS_INTENT:
        reply_sections.append(describe_all_items_message(insights))
    elif intent == "reorder":
        reply_sections.append(describe_reorder_message(insights))
    elif intent == "compare":
        reply_sections.append(describe_compare_message(insights))
    elif intent == "why_drop":
        reply_sections.append(describe_why_drop_message(insights))
    elif intent == CUSTOM_SQL_INTENT:
        reply_sections.append(describe_custom_sql_message(insights))

    reasoning_section = format_reasoning_for_message(sql_payload.get("reasoning"))
    if reasoning_section:
        reply_sections.append(reasoning_section)

    context_note = build_business_context_note(prompt, context, sql_payload)
    if context_note:
        reply_sections.append(context_note)
    multi_warning = context.get("multi_intent_warning")
    if isinstance(multi_warning, str):
        warning_text = multi_warning.strip()
        if warning_text:
            reply_sections.append(warning_text)
    chart_caption = sql_payload.get("chart_caption")
    if isinstance(chart_caption, str):
        caption_text = chart_caption.strip()
        if caption_text:
            reply_sections.append(caption_text)
    chart_warning = sql_payload.get("chart_warning")
    if isinstance(chart_warning, str):
        warning_text = chart_warning.strip()
        if warning_text:
            reply_sections.append(warning_text)

    message = "\n\n".join(part for part in reply_sections if part).strip()
    footer = CORRECTION_PROMPT_FOOTER if intent != "chitchat" else ""
    if footer:
        if message:
            if footer not in message:
                message = f"{message}\n\n{footer}"
        else:
            message = footer
    return message or "Done."


def handle_chat_prompt(
    cursor: pyodbc.Cursor,
    prompt: str,
    today: datetime.date,
    history_messages: list[dict] | None,
    feedback_note: str | None,
    session_history: list[dict],
    session_context: dict | None = None,
    memory_context: list[dict] | None = None,
    override_context: dict | None = None,
) -> dict:
    if override_context:
        context = copy.deepcopy(override_context)
    else:
        context = interpret_prompt(
            prompt,
            today,
            history=history_messages,
            feedback=feedback_note,
            memory_context=memory_context,
            session_context=session_context,
        )
    intent = context.get("intent") or classify_chat_intent(prompt)
    clarification = build_clarification_question(intent, context, today)
    if clarification:
        return {
            "message": clarification,
            "data": None,
            "sql": None,
            "context_type": "chitchat",
            "context": context,
        }
    context["needs_item_for_intent"] = None

    sql_payload: dict | None = None
    if intent == "inventory":
        sql_payload = handle_inventory_question(cursor, prompt, context)
    elif intent == "inventory_usage":
        sql_payload = handle_inventory_usage_question(cursor, prompt, today, context)
    elif intent == "reorder":
        sql_payload = handle_reorder_question(cursor, prompt, today, context)
    elif intent == "compare":
        sql_payload = handle_compare_question(cursor, prompt, today, context)
    elif intent == "why_drop":
        sql_payload = handle_why_drop_question(cursor, prompt, today, context)
    elif intent == "sales":
        sql_payload = handle_sales_question(cursor, prompt, today, context)
    elif intent == MULTI_ITEM_INTENT:
        sql_payload = handle_multi_item_question(cursor, prompt, today, context)
    elif intent == ALL_ITEMS_INTENT:
        sql_payload = handle_all_items_question(cursor, prompt, today, context)
    elif intent == CUSTOM_SQL_INTENT:
        sql_payload = handle_custom_sql_question(cursor, prompt, today, context)
    elif intent in {"usage", "report"}:
        sql_payload = handle_usage_question(cursor, prompt, today, context)
    elif intent != "chitchat":
        sql_payload = handle_usage_question(cursor, prompt, today, context)

    if sql_payload:
        sanitized_insights = sanitize_insights_for_session(sql_payload.get("insights"))
        if sanitized_insights:
            context["insights"] = sanitized_insights
        row_summary = build_row_aggregates(sql_payload.get("data"))
        if row_summary:
            context["row_aggregates"] = row_summary
        if not sql_payload.get("error"):
            reasoning_summary = call_openai_reasoner(prompt, today, context, sql_payload)
            if reasoning_summary:
                sql_payload["reasoning"] = reasoning_summary
                context["reasoning"] = reasoning_summary

    message = compose_conversational_message(prompt, context, sql_payload, session_history)
    result = {
        "message": message,
        "data": sql_payload.get("data") if sql_payload else None,
        "sql": sql_payload.get("sql") if sql_payload else None,
        "chart": sql_payload.get("chart") if sql_payload else None,
        "insights": sql_payload.get("insights") if sql_payload else None,
        "reasoning": sql_payload.get("reasoning") if sql_payload else None,
        "context_type": (
            sql_payload.get("context_type")
            if sql_payload and sql_payload.get("context_type")
            else ("chitchat" if intent == "chitchat" else intent)
        ),
    }
    if context.get("notes"):
        result["notes"] = context["notes"]
    result["context"] = context
    return result


def execute_chat_turn(
    prompt: str,
    today: datetime.date,
    history_messages: list[dict] | None,
    feedback_note: str | None,
    session_history: list[dict],
    session_context: dict | None,
    memory_context: list[dict] | None,
    override_context: dict | None = None,
) -> dict:
    try:
        conn_str, server, database, auth_label = build_connection_string()
    except RuntimeError as err:
        return {
            "content": f"Unable to build SQL connection string: {err}",
            "sql": None,
            "data": None,
        }

    conn: pyodbc.Connection | None = None
    try:
        conn = pyodbc.connect(conn_str)
        cursor = conn.cursor()
        result = handle_chat_prompt(
            cursor,
            prompt,
            today,
            history_messages,
            feedback_note,
            session_history,
            session_context=session_context,
            memory_context=memory_context,
            override_context=override_context,
        )
        message = result.get("message", "Done.")
        if result.get("notes"):
            message += f"\n\nInterpretation notes: {result['notes']}"
        message += f"\n\nSource: {server}/{database} via {auth_label}."
        return {
            "content": message,
            "sql": result.get("sql"),
            "data": result.get("data"),
            "chart": result.get("chart"),
            "insights": result.get("insights"),
            "reasoning": result.get("reasoning"),
            "context": result.get("context"),
            "context_type": result.get("context_type"),
        }
    except pyodbc.Error as err:
        return {"content": f"Query failed: {err}", "sql": None, "data": None}
    finally:
        if conn is not None:
            conn.close()


def render_sql_chat(today: datetime.date, user_override: dict | None = None) -> None:
    st.subheader("SQL-style data chat")
    st.caption(
        "Ask plain-language questions about Dynamics GP data. "
        "I'll classify the intent (usage/report, sales, compare, why_drop, inventory, availability-vs-usage, multi-item summaries, all-items overview, reorder) and pull relevant memory, "
        "then either run the matching template or fall back to a safe custom SQL plan for purchase-order, vendor, or other bespoke questions. "
        "The custom SQL path is read-only and limited to vetted GP tables so nothing can be modified. "
        "Mention an item (e.g., NO3CA12), time period, and optional math like 'multiply by 3'. "
        "Use 'feedback: ...' for persistent guidance or 'reset' to clear the chat."
    )

    user_id = get_authenticated_user_id()
    user = user_override or get_authenticated_user()
    user_label = "Guest"
    if user:
        user_label = (
            user.get("name")
            or user.get("username")
            or user.get("email")
            or "Guest"
        )
    history_state_key = build_user_state_key(CHAT_HISTORY_KEY, user_id)
    feedback_log_key = build_user_state_key(CHAT_FEEDBACK_LOG_KEY, user_id)
    feedback_value_key = build_user_state_key(CHAT_FEEDBACK_KEY, user_id)
    feedback_prompt_key = build_user_state_key(CHAT_FEEDBACK_PROMPT_KEY, user_id)
    active_session_state_key = build_user_state_key(CHAT_ACTIVE_SESSION_KEY, user_id)

    sessions, active_session = ensure_chat_sessions(user_id)
    history: list[dict] = active_session["history"]
    session_context: dict = active_session.setdefault(CHAT_SESSION_CONTEXT_KEY, {})
    st.session_state[history_state_key] = history
    feedback_log: list[dict] = st.session_state.setdefault(feedback_log_key, [])
    st.session_state.setdefault(feedback_value_key, "")
    st.session_state.setdefault(feedback_prompt_key, None)

    with st.sidebar:
        st.caption(f"Signed in as {user_label}")
        if st.session_state.get(AUTH_TIMESTAMP_STATE_KEY):
            if st.button("Sign out", key="chat_logout_button"):
                logout_current_user()
        st.header("Chats")
        for session in sessions:
            label = session["name"]
            if session["id"] == active_session["id"]:
                label = f"* {label}"
            if st.button(label, key=f"select_session_{session['id']}"):
                st.session_state[active_session_state_key] = session["id"]
                st.rerun()

        new_name = st.text_input(
            "Chat title",
            value=active_session["name"],
            key=f"chat_name_{active_session['id']}",
        )
        if new_name.strip() and new_name != active_session["name"]:
            active_session["name"] = new_name.strip()

        if st.button("New chat", key="create_new_chat"):
            new_session = {
                "id": uuid.uuid4().hex,
                "name": f"Chat {len(sessions) + 1}",
                "history": [],
            }
            sessions.append(new_session)
            st.session_state[active_session_state_key] = new_session["id"]
            st.rerun()
    st.text_area(
        "Assistant guidance (optional)",
        key=feedback_value_key,
        help="Persistent feedback I'll honor for every reply. "
        "This does not trigger a query; it's saved immediately.",
    )
    for entry in history:
        entry.setdefault("id", uuid.uuid4().hex)
        with st.chat_message(entry["role"]):
            st.markdown(entry["content"])
            if entry.get("sql"):
                st.code(entry["sql"], language="sql")
            if entry.get("data"):
                st.dataframe(entry["data"], width="stretch")
            chart_payload = entry.get("chart")
            if isinstance(chart_payload, dict):
                chart_data = chart_payload.get("data")
                x_field = chart_payload.get("x_field") or "Period"
                y_field = chart_payload.get("y_field")
                if isinstance(chart_data, list) and chart_data and y_field:
                    chart_df = None
                    try:
                        chart_df = pd.DataFrame(chart_data)
                    except ValueError:
                        chart_df = None
                    if chart_df is not None and x_field in chart_df.columns and y_field in chart_df.columns:
                        if "_sequence" in chart_df.columns:
                            chart_df = chart_df.sort_values("_sequence")
                        chart_df = chart_df[[x_field, y_field]].copy()
                        value_label = chart_payload.get("value_label") or y_field
                        chart_df = chart_df.rename(columns={y_field: value_label}).set_index(x_field)
                        title = chart_payload.get("title")
                        if isinstance(title, str) and title.strip():
                            st.caption(title.strip())
                        try:
                            st.line_chart(chart_df, height=chart_payload.get("height") or 260)
                        except StreamlitAPIException:
                            st.dataframe(chart_df, width="stretch")
            if entry["role"] == "assistant":
                cols = st.columns([0.6, 0.6, 4])
                with cols[0]:
                    if st.button("👍", key=f"fb_up_{entry['id']}"):
                        st.session_state[feedback_prompt_key] = {"id": entry["id"], "direction": "up"}
                        st.rerun()
                with cols[1]:
                    if st.button("👎", key=f"fb_down_{entry['id']}"):
                        st.session_state[feedback_prompt_key] = {"id": entry["id"], "direction": "down"}
                        st.rerun()
                prompt_info = st.session_state.get(feedback_prompt_key)
                if prompt_info and prompt_info.get("id") == entry["id"]:
                    direction = prompt_info.get("direction", "up")
                    label = "What did I do well?" if direction == "up" else "How can I improve this answer?"
                    with st.form(f"feedback_form_{entry['id']}"):
                        comment = st.text_area(label, key=f"feedback_text_{entry['id']}", height=100)
                        submit_cols = st.columns([1, 1])
                        submitted = submit_cols[0].form_submit_button("Submit")
                        cancelled = submit_cols[1].form_submit_button("Cancel")
                        if submitted:
                            comment_text = comment.strip()
                            feedback_log.append(
                                {
                                    "message_id": entry["id"],
                                    "direction": direction,
                                    "comment": comment_text,
                                    "session_id": active_session["id"],
                                    "timestamp": datetime.datetime.now().isoformat(timespec="seconds"),
                                }
                            )
                            apply_feedback_to_memory(entry["id"], direction, comment_text or None)
                            st.session_state[feedback_prompt_key] = None
                            st.rerun()
                        if cancelled:
                            st.session_state[feedback_prompt_key] = None
                            st.rerun()

    prompt = st.chat_input("What data can I pull for you?")
    if not prompt:
        return

    def respond_with_correction_error(message: str) -> None:
        history.append(
            {
                "id": uuid.uuid4().hex,
                "role": "user",
                "content": prompt,
                "context_type": "correction",
            }
        )
        history.append(
            {
                "id": uuid.uuid4().hex,
                "role": "assistant",
                "content": message,
                "context_type": "correction",
            }
        )
        st.rerun()

    normalized = prompt.strip()
    lowered_prompt = normalized.lower()
    if lowered_prompt in RESET_COMMANDS:
        active_session["history"].clear()
        session_context.clear()
        st.rerun()
    if lowered_prompt.startswith("feedback:"):
        st.session_state[feedback_value_key] = normalized.split(":", 1)[1].strip()
        history.append(
            {
                "id": uuid.uuid4().hex,
                "role": "assistant",
                "content": "Thanks for the feedback - I'll keep that in mind.",
            }
        )
        st.rerun()

    correction_payload: dict | None = None
    prompt_for_execution = prompt
    correction_prefix = next((prefix for prefix in CORRECTION_PREFIXES if lowered_prompt.startswith(prefix)), None)
    if correction_prefix:
        parts = normalized.split(":", 1)
        correction_text = parts[1].strip() if len(parts) > 1 else ""
        last_assistant_entry = find_last_history_entry(history, "assistant")
        if not last_assistant_entry:
            respond_with_correction_error(
                "I don't have a previous answer to fix yet. Ask a question first, then tell me what to adjust."
            )
            return
        original_prompt = last_assistant_entry.get("source_prompt") or find_prior_user_prompt(
            history, last_assistant_entry.get("id")
        )
        if not original_prompt:
            respond_with_correction_error("I couldn't locate the earlier request. Please restate what you'd like me to pull.")
            return
        if not correction_text:
            respond_with_correction_error("Tell me what to change (for example, 'use December too' or 'wrong intent').")
            return
        prompt_for_execution = f"{original_prompt}\n\nCorrection requested: {correction_text}"
        correction_payload = {
            "original_prompt": original_prompt,
            "correction_text": correction_text,
            "target_entry": last_assistant_entry,
            "prompt_for_execution": prompt_for_execution,
        }

    seed_item = extract_item_code(prompt_for_execution) or session_context.get("item")
    seed_month, seed_year = infer_period_from_text(prompt_for_execution, today)
    seed_entities = {"item": seed_item, "month": seed_month, "year": seed_year}
    memory_context_entries = retrieve_semantic_context(prompt_for_execution, seed_entities)

    user_entry = {
        "id": uuid.uuid4().hex,
        "role": "user",
        "content": prompt,
        "resolved_prompt": prompt_for_execution,
    }
    if correction_payload:
        user_entry["context_type"] = "correction"
        target_id = correction_payload["target_entry"].get("id")
        if target_id:
            user_entry["metadata"] = {"correction_for": target_id}
    history.append(user_entry)
    log_chat_event(
        {
            "type": "user",
            "user_id": user_id,
            "session_id": active_session["id"],
            "message_id": user_entry["id"],
            "content": prompt,
            "resolved_prompt": prompt_for_execution,
            "context_type": user_entry.get("context_type"),
            "context": user_entry.get("metadata"),
        }
    )

    history_for_llm = build_history_messages_for_llm(history)
    feedback_note = build_feedback_instruction(
        st.session_state.get(feedback_value_key, ""),
        feedback_log,
        active_session["id"],
    )

    override_context = None
    if correction_payload:
        override_context = interpret_prompt(
            prompt_for_execution,
            today,
            history=history_for_llm,
            feedback=feedback_note,
            memory_context=memory_context_entries,
            session_context=session_context,
        )

    response = execute_chat_turn(
        prompt_for_execution,
        today,
        history_messages=history_for_llm,
        feedback_note=feedback_note,
        session_history=history,
        session_context=session_context,
        memory_context=memory_context_entries,
        override_context=override_context,
    )
    assistant_message_id = uuid.uuid4().hex
    context_type = response.get("context_type")
    if correction_payload:
        context_type = "correction"
        response["context_type"] = context_type
    llm_snapshot = build_llm_data_snapshot(
        response.get("data"),
        response.get("insights"),
        context_type=context_type,
        sql_text=response.get("sql"),
    )
    if llm_snapshot:
        response["llm_data_snapshot"] = llm_snapshot
    history.append(
        {
            "id": assistant_message_id,
            "role": "assistant",
            "content": response.get("content", "Done."),
            "sql": response.get("sql"),
            "data": response.get("data"),
            "chart": response.get("chart"),
            "insights": response.get("insights"),
            "reasoning": response.get("reasoning"),
            "context_type": context_type,
            "context": response.get("context"),
            "source_prompt": prompt_for_execution,
            "llm_data_snapshot": llm_snapshot,
        }
    )
    log_chat_event(
        {
            "type": "assistant",
            "user_id": user_id,
            "session_id": active_session["id"],
            "message_id": assistant_message_id,
            "content": response.get("content"),
            "context_type": context_type,
            "sql": response.get("sql"),
            "chart": response.get("chart"),
            "context": response.get("context"),
            "insights": response.get("insights"),
            "reasoning": response.get("reasoning"),
            "llm_data_snapshot": llm_snapshot,
        }
    )
    update_session_context(session_context, response.get("context"))
    record_memory_entry(
        prompt_for_execution,
        response,
        active_session["id"],
        assistant_message_id,
        user_id=user_id,
    )
    if correction_payload:
        previous_context = correction_payload["target_entry"].get("context")
        override_used = override_context or response.get("context")
        record_correction(
            {
                "user_prompt": correction_payload["original_prompt"],
                "session_snapshot": build_session_snapshot_from_context(previous_context),
                "llm_interpretation": {
                    "intent": (previous_context or {}).get("intent"),
                    "entities": (previous_context or {}).get("entities"),
                },
                "sql_preview": correction_payload["target_entry"].get("sql"),
                "error_reported": correction_payload["correction_text"],
                "corrective_action": summarize_correction_action(override_used, correction_payload["correction_text"]),
                "correct_intent": (override_used or {}).get("intent"),
                "target_message_id": correction_payload["target_entry"].get("id"),
            },
            user_id=user_id,
        )
    st.rerun()
ITEMS_QUERY = """
SELECT i.ITEMNMBR, i.QTYONHND, i.ORDRPNTQTY, i.QTYONORD,
       (i.QTYONHND - i.ATYALLOC) AS QtyAvailable, m.ITMCLSCD
FROM IV00102 i
JOIN IV00101 m ON m.ITEMNMBR = i.ITEMNMBR
WHERE i.LOCNCODE = 'MAIN'
  AND i.QTYONORD = 0
  AND i.ORDRPNTQTY > (i.QTYONHND - i.ATYALLOC)
  AND m.ITMCLSCD LIKE '%RAW%';
"""

USAGE_QUERY = """
SELECT SUM(t.TRXQTY) AS UsageForPeriod
FROM IV30300 t
JOIN IV30200 h ON t.DOCNUMBR = h.DOCNUMBR AND t.DOCTYPE = h.IVDOCTYP
WHERE t.ITEMNMBR = ?
  AND t.DOCTYPE = 1               -- Only Adjustments
  AND t.TRXQTY < 0                -- 👈 only negatives
  AND h.DOCDATE >= ?
  AND h.DOCDATE <= ?;
"""

SALES_QUERY = """
SELECT SUM(
           CASE
               WHEN l.SOPTYPE = 4 THEN -ABS(l.QUANTITY)
               ELSE ABS(l.QUANTITY)
           END
       ) AS SalesQuantity
FROM SOP30300 l
JOIN SOP30200 h ON h.SOPTYPE = l.SOPTYPE AND h.SOPNUMBE = l.SOPNUMBE
WHERE l.ITEMNMBR = ?
  AND h.DOCDATE >= ?
  AND h.DOCDATE <= ?
  AND l.SOPTYPE IN (3, 4);
"""

USAGE_BY_MONTH_QUERY = """
SELECT
    DATEFROMPARTS(YEAR(h.DOCDATE), MONTH(h.DOCDATE), 1) AS PeriodStart,
    EOMONTH(h.DOCDATE) AS PeriodEnd,
    DATENAME(MONTH, h.DOCDATE) + ' ' + CAST(YEAR(h.DOCDATE) AS varchar(4)) AS PeriodLabel,
    SUM(t.TRXQTY) AS UsageForPeriod
FROM IV30300 t
JOIN IV30200 h ON t.DOCNUMBR = h.DOCNUMBR AND t.DOCTYPE = h.IVDOCTYP
WHERE t.ITEMNMBR = ?
  AND t.DOCTYPE = 1
  AND t.TRXQTY < 0
  AND h.DOCDATE BETWEEN ?
  AND ?
GROUP BY DATEFROMPARTS(YEAR(h.DOCDATE), MONTH(h.DOCDATE), 1),
         EOMONTH(h.DOCDATE),
         DATENAME(MONTH, h.DOCDATE),
         YEAR(h.DOCDATE)
ORDER BY PeriodStart;
"""

REORDER_QUERY = """
SELECT TOP 25
    i.ITEMNMBR,
    m.ITEMDESC,
    i.QTYONHND,
    i.ATYALLOC,
    (i.QTYONHND - i.ATYALLOC) AS QtyAvailable,
    i.ORDRPNTQTY,
    m.ITMCLSCD,
    i.QTYONORD,
    (i.ORDRPNTQTY - (i.QTYONHND - i.ATYALLOC)) AS Shortfall
FROM IV00102 i
JOIN IV00101 m ON m.ITEMNMBR = i.ITEMNMBR
"""


MONTH_INPUT_FORMATS = (
    "%Y-%m",
    "%m/%Y",
    "%m-%Y",
    "%B %Y",
    "%b %Y",
    "%Y %B",
    "%Y %b",
)

HISTORICAL_YEARS = 2
WHY_DROP_MONTH_WINDOW = 6
MONTH_NAME_LOOKUP = {
    "jan": 1,
    "feb": 2,
    "mar": 3,
    "apr": 4,
    "may": 5,
    "jun": 6,
    "jul": 7,
    "aug": 8,
    "sep": 9,
    "sept": 9,
    "oct": 10,
    "nov": 11,
    "dec": 12,
}
MONTH_NAME_REGEX = re.compile(
    r"\b("
    r"jan(?:uary)?|feb(?:ruary)?|mar(?:ch)?|apr(?:il)?|may|jun(?:e)?|jul(?:y)?|"
    r"aug(?:ust)?|sep(?:t|tember)|oct(?:ober)?|nov(?:ember)?|dec(?:ember)?"
    r")\b(?:\s+(\d{2,4}))?",
    flags=re.IGNORECASE,
)
YEAR_TOKEN_REGEX = re.compile(r"\b(19|20)\d{2}\b")


st.set_page_config(page_title="Adjustment Usage Explorer", page_icon="dY", layout="wide")


def parse_month_input(raw_input: str, today: datetime.date) -> tuple[int, int, str]:
    """
    Return (month_number, anchor_year, label) based on text input.
    Anchor year is the latest year included in the average.
    """

    def label_for(month_num: int, year_num: int) -> str:
        return datetime.date(year_num, month_num, 1).strftime("%B %Y")

    def default_anchor_year(month_num: int) -> int:
        return today.year if month_num <= today.month else today.year - 1

    if not raw_input:
        anchor_year = today.year
        return today.month, anchor_year, label_for(today.month, anchor_year)

    for fmt in MONTH_INPUT_FORMATS:
        try:
            parsed = datetime.datetime.strptime(raw_input, fmt)
            anchor_year = parsed.year
            return parsed.month, anchor_year, label_for(parsed.month, anchor_year)
        except ValueError:
            continue

    for fmt in ("%B", "%b"):
        try:
            parsed = datetime.datetime.strptime(raw_input, fmt)
            month_num = parsed.month
            anchor_year = default_anchor_year(month_num)
            return month_num, anchor_year, label_for(month_num, anchor_year)
        except ValueError:
            continue

    raise ValueError(
        "Unable to understand the month. Acceptable formats include 'July', '2024-07', '07/2023'."
    )


def build_month_periods(month: int, anchor_year: int, years: int) -> list[tuple[datetime.date, datetime.date]]:
    """Return (start_date, end_date) for the requested month across `years` historical years."""
    periods: list[tuple[datetime.date, datetime.date]] = []
    for offset in range(years):
        year = anchor_year - offset
        start = datetime.date(year, month, 1)
        periods.append((start, _month_end(start)))
    return periods


def _month_end(start_date: datetime.date) -> datetime.date:
    """Return the last day of start_date's month."""
    if start_date.month == 12:
        return datetime.date(start_date.year, 12, 31)
    next_month = datetime.date(start_date.year, start_date.month + 1, 1)
    return next_month - datetime.timedelta(days=1)


def average(values: Iterable[float]) -> float:
    collected = list(values)
    if not collected:
        return 0.0
    return sum(collected) / len(collected)


def fetch_items(cursor: pyodbc.Cursor):
    cursor.execute(ITEMS_QUERY)
    return cursor.fetchall()


def fetch_item_description(cursor: pyodbc.Cursor, item_number: str) -> str | None:
    try:
        cursor.execute("SELECT TOP 1 ITEMDESC FROM IV00101 WHERE ITEMNMBR = ?", item_number)
        row = cursor.fetchone()
        if not row:
            return None
        if isinstance(row, tuple):
            return row[0]
        return getattr(row, "ITEMDESC", None)
    except pyodbc.Error:
        return None


def fetch_usage(cursor: pyodbc.Cursor, item_number: str, start_date: datetime.date, end_date: datetime.date) -> float:
    cursor.execute(USAGE_QUERY, item_number, start_date, end_date)
    result = cursor.fetchone()
    return float(result[0]) if result and result[0] is not None else 0.0


def fetch_sales(cursor: pyodbc.Cursor, item_number: str, start_date: datetime.date, end_date: datetime.date) -> float:
    cursor.execute(SALES_QUERY, item_number, start_date, end_date)
    result = cursor.fetchone()
    return float(result[0]) if result and result[0] is not None else 0.0


def fetch_usage_scope_rows(
    cursor: pyodbc.Cursor,
    start_date: datetime.date,
    end_date: datetime.date,
    *,
    limit: int = 40,
    site_codes: list[str] | None = None,
    site_covers_all: bool = False,
    class_filters: list[str] | None = None,
    class_covers_all: bool = False,
    item_list: list[str] | None = None,
    keywords: list[str] | None = None,
    order_mode: str = "usage",
) -> tuple[list[dict], str]:
    site_codes = site_codes or []
    class_filters = class_filters or []
    item_list = [code.strip().upper() for code in item_list or [] if code]
    keywords = keywords or []
    scoped_limit = max(1, int(limit)) if limit else 40
    clauses: list[str] = []
    params: list = [start_date, end_date]

    if site_covers_all:
        pass
    elif site_codes:
        placeholders = ", ".join("?" for _ in site_codes)
        clauses.append(f"EXISTS (SELECT 1 FROM IV00102 i WHERE i.ITEMNMBR = m.ITEMNMBR AND i.LOCNCODE IN ({placeholders}))")
        params.extend(site_codes)
    else:
        clauses.append("EXISTS (SELECT 1 FROM IV00102 i WHERE i.ITEMNMBR = m.ITEMNMBR AND i.LOCNCODE = ?)")
        params.append("MAIN")

    if class_filters and not class_covers_all:
        class_clause = " OR ".join("m.ITMCLSCD LIKE ?" for _ in class_filters)
        clauses.append(f"({class_clause})")
        params.extend(_wildcard_value(value) for value in class_filters)

    if item_list:
        placeholders = ", ".join("?" for _ in item_list)
        clauses.append(f"m.ITEMNMBR IN ({placeholders})")
        params.extend(item_list)

    for keyword in keywords:
        clauses.append("UPPER(m.ITEMDESC) LIKE ?")
        params.append(f"%{keyword}%")

    clause_sql = ""
    if clauses:
        clause_sql = "\n  AND " + "\n  AND ".join(clauses)

    if order_mode == "abs":
        order_clause = "ORDER BY ABS(COALESCE(u.UsageQty, 0)) ASC, m.ITEMNMBR"
    elif order_mode == "desc":
        order_clause = "ORDER BY COALESCE(u.UsageQty, 0) DESC, m.ITEMNMBR"
    else:
        order_clause = "ORDER BY COALESCE(u.UsageQty, 0) ASC, m.ITEMNMBR"

    query = f"""
    WITH UsageTotals AS (
        SELECT t.ITEMNMBR, SUM(t.TRXQTY) AS UsageQty
        FROM IV30300 t
        JOIN IV30200 h ON h.DOCNUMBR = t.DOCNUMBR AND h.IVDOCTYP = t.DOCTYPE
        WHERE t.DOCTYPE = 1
          AND t.TRXQTY < 0
          AND h.DOCDATE BETWEEN ? AND ?
        GROUP BY t.ITEMNMBR
    )
    SELECT TOP {scoped_limit}
        m.ITEMNMBR,
        m.ITEMDESC,
        m.ITMCLSCD,
        COALESCE(u.UsageQty, 0) AS UsageQty
    FROM IV00101 m
    LEFT JOIN UsageTotals u ON u.ITEMNMBR = m.ITEMNMBR
    WHERE 1=1
    {clause_sql}
    {order_clause};
    """
    cursor.execute(query, params)
    fetched = cursor.fetchall()
    rows: list[dict] = []
    for row in fetched:
        item = getattr(row, "ITEMNMBR", None)
        usage_value = getattr(row, "UsageQty", 0.0) or 0.0
        rows.append(
            {
                "Item": item,
                "Description": getattr(row, "ITEMDESC", None),
                "Class": getattr(row, "ITMCLSCD", None),
                "Usage": float(usage_value),
                "AbsUsage": abs(float(usage_value)),
            }
        )
    sql_preview = format_sql_preview(query, params)
    return rows, sql_preview


def fetch_monthly_usage(
    cursor: pyodbc.Cursor,
    item_number: str,
    start_date: datetime.date,
    end_date: datetime.date,
) -> list[dict]:
    cursor.execute(USAGE_BY_MONTH_QUERY, item_number, start_date, end_date)
    fetched = cursor.fetchall()
    columns = [col[0] for col in cursor.description] if cursor.description else []
    rows: list[dict] = []
    for raw_row in fetched:
        record = dict(zip(columns, raw_row)) if columns else {}
        period_start = record.get("PeriodStart")
        period_end = record.get("PeriodEnd")
        if isinstance(period_start, datetime.datetime):
            period_start = period_start.date()
        if isinstance(period_end, datetime.datetime):
            period_end = period_end.date()
        period_key = None
        if isinstance(period_start, datetime.date):
            period_key = month_key(period_start.month, period_start.year)
        entry = {
            "PeriodKey": period_key,
            "PeriodLabel": record.get("PeriodLabel"),
            "PeriodStart": period_start.isoformat() if isinstance(period_start, datetime.date) else None,
            "PeriodEnd": period_end.isoformat() if isinstance(period_end, datetime.date) else None,
            "UsageForPeriod": float(record.get("UsageForPeriod") or 0.0),
        }
        rows.append(entry)
    return rows


def items_preview(items) -> list[dict]:
    sample = []
    for row in items[:10]:
        item, onhand, order_point, on_order, avail, class_code = row
        sample.append(
            {
                "Item": item,
                "OnHand": onhand,
                "OnOrder": on_order,
                "Avail": avail,
                "OrderPoint": order_point,
                "Class": class_code,
            }
        )
    return sample


def build_usage_rows(cursor: pyodbc.Cursor, items, periods) -> list[dict]:
    rows: list[dict] = []
    for row in items:
        item_number = row[0]
        period_values = {}
        for start_date, end_date in periods:
            label = start_date.strftime("%b %Y")
            period_values[label] = fetch_usage(cursor, item_number, start_date, end_date)

        rows.append(
            {
                "Item": item_number,
                "AverageUsage": average(period_values.values()),
                **period_values,
            }
        )
    return rows


def to_csv(data: list[dict]) -> bytes:
    if not data:
        return b""
    buffer = io.StringIO()
    writer = csv.DictWriter(buffer, fieldnames=data[0].keys())
    writer.writeheader()
    writer.writerows(data)
    return buffer.getvalue().encode("utf-8")


def run_report(month_raw: str) -> None:
    today = datetime.date.today()
    try:
        month_num, anchor_year, label = parse_month_input(month_raw.strip(), today)
    except ValueError as err:
        st.error(str(err))
        return

    periods = build_month_periods(month_num, anchor_year, HISTORICAL_YEARS)
    period_labels = ", ".join(start.strftime("%b %Y") for start, _ in periods)

    try:
        conn_str, server_name, database_name, auth_label = build_connection_string()
    except RuntimeError as err:
        st.error(str(err))
        return

    st.caption(
        f"Evaluating {HISTORICAL_YEARS}-year average using periods: {period_labels} "
        f"(connecting to {server_name}/{database_name} via {auth_label})."
    )

    conn: pyodbc.Connection | None = None
    try:
        conn = pyodbc.connect(conn_str)
    except pyodbc.Error as err:
        st.error(f"Failed to connect to SQL Server: {err}")
        return

    try:
        cursor = conn.cursor()
        with st.spinner("Querying Dynamics GP..."):
            items = fetch_items(cursor)

            if not items:
                st.warning("No items met the criteria.")
                return

            st.subheader(f"{len(items)} items match the criteria")
            st.dataframe(items_preview(items), width="stretch")

            usage_rows = build_usage_rows(cursor, items, periods)
            usage_rows.sort(key=lambda row: row["AverageUsage"])

        st.subheader(f"{HISTORICAL_YEARS}-year average adjustment usage for {label}")
        st.dataframe(usage_rows, width="stretch")

        csv_bytes = to_csv(usage_rows)
        st.download_button(
            label="Download results as CSV",
            data=csv_bytes,
            file_name=f"usage_{label.replace(' ', '_')}.csv",
            mime="text/csv",
        )
    except pyodbc.Error as err:
        st.error(f"Query failed: {err}")
    finally:
        if conn is not None:
            conn.close()


current_user = ensure_authenticated_user()

st.title("Chemical Dynamics")
st.write(
    "To Help you Grow "
    "Interpreter handles the reasoning and logic, then the app runs the SQL locally and securely."
)

today_global = datetime.date.today()
render_sql_chat(today_global, current_user)
