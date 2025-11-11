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
from collections.abc import Iterable, Mapping
from pathlib import Path
from typing import TypedDict

import pyodbc
import requests
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
    "THANK",
    "THANKS",
    "ALSO",
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
RESET_COMMANDS = {"reset", "clear", "clear chat", "restart"}
CORRECTION_PREFIXES = ("correction:", "fix:")
CORRECTION_PROMPT_FOOTER = "If this isn’t what you meant, tell me what to fix (e.g., 'use December too' or 'wrong intent')."
OPENAI_CHAT_URL = "https://api.openai.com/v1/chat/completions"
OPENAI_DEFAULT_MODEL = "gpt-4o-mini"
OPENAI_TIMEOUT_SECONDS = 15
OPENAI_EMBEDDING_URL = "https://api.openai.com/v1/embeddings"
OPENAI_EMBEDDING_MODEL = "text-embedding-3-small"
TRAINING_FEEDBACK_DIR = APP_ROOT / "training_feedback"
LOCAL_SECRETS_PATHS = (
    APP_ROOT / ".streamlit" / "secrets.toml",
    APP_ROOT / "secrets.toml",
)
_PROJECT_SECRETS_CACHE: dict | None = None
RECENT_CORRECTION_LIMIT = 5
CHAT_EVENT_LOG_FILENAME = "chat_events.jsonl"
AUTH_USER_STATE_KEY = "auth_user"
AUTH_ERROR_STATE_KEY = "auth_error"
AUTH_TIMESTAMP_STATE_KEY = "auth_last_authenticated"
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
    registry = build_auth_registry(config)
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


def load_project_secrets() -> dict:
    """
    Return secrets parsed from a local secrets.toml when Streamlit secrets are unavailable.
    """

    global _PROJECT_SECRETS_CACHE
    if _PROJECT_SECRETS_CACHE is not None:
        return _PROJECT_SECRETS_CACHE
    if tomllib is None:
        _PROJECT_SECRETS_CACHE = {}
        return _PROJECT_SECRETS_CACHE
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
            _PROJECT_SECRETS_CACHE = dict(parsed)
        else:
            try:
                _PROJECT_SECRETS_CACHE = {key: parsed[key] for key in parsed}
            except Exception as err:  # pragma: no cover - defensive guard.
                LOGGER.warning("Unexpected secrets structure in %s: %s", candidate, err)
                _PROJECT_SECRETS_CACHE = {}
        return _PROJECT_SECRETS_CACHE
    _PROJECT_SECRETS_CACHE = {}
    return _PROJECT_SECRETS_CACHE


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
    store_semantic_memory("\n".join(parts), metadata)


def ensure_training_feedback_dir() -> Path:
    directory = TRAINING_FEEDBACK_DIR
    directory.mkdir(parents=True, exist_ok=True)
    return directory


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
        with filename.open("a", encoding="utf-8") as handle:
            handle.write(json.dumps(payload) + "\n")
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
        with filename.open("a", encoding="utf-8") as handle:
            handle.write(json.dumps(payload) + "\n")
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
    return {"api_key": api_key, "model": model}


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
        )
        return conn_str, server, database, "SQL user credentials"

    trusted_flag = secrets_config.get("trusted_connection", "yes")
    conn_str = (
        f"Driver={{{driver}}};"
        f"Server={server};"
        f"Database={database};"
        f"Trusted_Connection={trusted_flag};"
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


def build_auth_registry(config: dict) -> dict[str, dict]:
    """
    Return {login_identifier: user_entry} with passwords retained for verification.
    """

    registry: dict[str, dict] = {}
    for entry in normalize_auth_users(config):
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
            st.rerun()
        else:
            st.session_state[AUTH_ERROR_STATE_KEY] = "Invalid username or password."
            st.rerun()

    if auth_error:
        st.error(auth_error)
    st.info("Contact your administrator if you need access.")
    st.stop()


def logout_current_user() -> None:
    user = get_authenticated_user()
    if user:
        clear_user_scoped_state(user.get("id"))
    st.session_state.pop(AUTH_USER_STATE_KEY, None)
    st.session_state.pop(AUTH_TIMESTAMP_STATE_KEY, None)
    st.session_state.pop(AUTH_ERROR_STATE_KEY, None)
    st.rerun()


def extract_item_code(prompt: str) -> str | None:
    """
    Return the first uppercase token that looks like an item number.
    """

    raw_tokens = ITEM_TOKEN_PATTERN.findall(prompt.upper())
    if not raw_tokens:
        return None

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
        if has_digit(token):
            digit_candidates.append(token)
            continue
        if keyword_nearby(idx):
            keyword_candidates.append(token)
            continue
        if idx == 0:
            leading_candidates.append(token)

    if digit_candidates:
        return digit_candidates[0]
    if keyword_candidates:
        return keyword_candidates[0]
    if leading_candidates:
        return leading_candidates[0]
    return None


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


def resolve_item_from_context(prompt: str, context: dict | None) -> str | None:
    """
    Prefer explicit context/entity values, then fall back to token extraction.
    """

    if not context:
        return extract_item_code(prompt)
    entities = context.get("entities") or {}
    candidate = context.get("item") or entities.get("item")
    return candidate or extract_item_code(prompt)


def update_session_context(session_context: dict, context: dict | None) -> None:
    """
    Persist the latest interpreted context so follow-up questions inherit it.
    """

    if not isinstance(session_context, dict) or not isinstance(context, dict):
        return
    for key in ("intent", "item", "month", "year", "multiplier"):
        if context.get(key) is not None:
            session_context[key] = context[key]
    entities = context.get("entities")
    if isinstance(entities, dict) and entities:
        session_context.setdefault("entities", {})
        session_context["entities"].update(entities)


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


MAX_USAGE_PERIODS = 6


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


def determine_usage_periods(prompt: str, context: dict | None, today: datetime.date) -> list[tuple[int, int]]:
    """
    Combine LLM entities, explicit prompt months, and fallbacks to decide which periods to query.
    """

    if not isinstance(context, dict):
        month_guess, year_guess = infer_period_from_text(prompt, today)
        return [(month_guess, year_guess)]

    entities = context.get("entities") or {}
    entity_periods = normalize_periods_list(entities.get("periods")) or normalize_periods_list(
        entities.get("comparison_periods")
    )
    prompt_periods = context.get("prompt_periods") or []
    candidates = entity_periods or prompt_periods
    if not candidates:
        month_val = context.get("month")
        year_val = context.get("year")
        if not month_val or not year_val:
            month_val, year_val = infer_period_from_text(prompt, today)
        candidates = [(month_val, year_val)]

    return deduplicate_periods(candidates, limit=MAX_USAGE_PERIODS)


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


def classify_chat_intent(prompt: str) -> str:
    lowered = prompt.lower()
    compare_keywords = ("compare", "versus", "vs ", "vs.", "difference between", "diff between")
    if any(keyword in lowered for keyword in compare_keywords):
        return "compare"

    drop_keywords = ("drop", "decline", "decrease", "fall", "slump", "down", "lower")
    if ("why" in lowered or "reason" in lowered) and any(keyword in lowered for keyword in drop_keywords):
        return "why_drop"

    reorder_keywords = (
        "buy",
        "purchase",
        "restock",
        "reorder",
        "need to order",
        "need to buy",
        "order more",
        "running low",
        "inventory low",
    )
    if any(keyword in lowered for keyword in reorder_keywords):
        return "reorder"
    explanation_keywords = ("mean", "explain", "why", "how", "what does", "difference", "clarify", "tell me more")
    if any(keyword in lowered for keyword in explanation_keywords):
        return "chitchat"
    if any(keyword in lowered for keyword in ("sale", "sales", "usage", "adjust", "consumption", "report", "summary")):
        return "report"
    if any(keyword in lowered for keyword in ("inventory", "on hand", "stock", "available", "order point")):
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
    "use",
    "using",
    "demand",
    "forecast",
    "how much",
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
)


def contains_data_request_keywords(prompt: str) -> bool:
    lowered = prompt.lower()
    return any(keyword in lowered for keyword in DATA_REQUEST_KEYWORDS)


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


def asks_about_capabilities(prompt: str) -> bool:
    normalized = " ".join(prompt.lower().split())
    if not normalized:
        return False
    return any(phrase in normalized for phrase in CAPABILITY_QUESTION_PHRASES)


def deduce_usage_or_report_intent(prompt: str) -> str:
    lowered = prompt.lower()
    usage_markers = ("usage", "use", "using", "consume", "consumed", "consumption", "how much")
    if any(marker in lowered for marker in usage_markers):
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
    lowered = prompt.lower()
    return any(keyword in lowered for keyword in RANGE_KEYWORDS)


def describe_month_year(month: int | None, year: int | None, fallback_year: int) -> str:
    if not month:
        return "that month"
    safe_year = year if year else fallback_year
    safe_year = max(1900, min(2100, safe_year))
    return datetime.date(safe_year, month, 1).strftime("%B %Y")


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


def references_previous_data(prompt: str) -> bool:
    lowered = prompt.lower()
    return any(phrase in lowered for phrase in FOLLOWUP_DATA_PHRASES)


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

    return "; ".join(pieces)


INTENT_ITEM_ACTIONS: dict[str, str] = {
    "usage": "usage report",
    "report": "usage report",
    "inventory": "inventory check",
    "compare": "usage comparison",
    "why_drop": "drop analysis",
    "reorder": "reorder summary",
}


def build_clarification_question(intent: str, context: dict, today: datetime.date) -> str | None:
    """
    Decide whether we should ask the user clarifying questions before running SQL.
    """

    action = INTENT_ITEM_ACTIONS.get(intent)
    if not action:
        return None

    prompt_has_item = bool(context.get("prompt_has_item"))
    entities = context.get("entities") or {}
    candidate_item = context.get("item") or entities.get("item")

    if not candidate_item:
        return f"Before I run that {action}, which item number should I use?"
    if not prompt_has_item:
        return (
            f"Before I run that {action}, should I use {candidate_item}? "
            "If you meant a different item, let me know its item number."
        )

    if intent not in {"usage", "report", "compare"}:
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


def _extract_json_block(text: str) -> str:
    cleaned = text.strip()
    if "```" in cleaned:
        fence_match = re.findall(r"```(?:json)?\s*(.*?)```", cleaned, flags=re.DOTALL | re.IGNORECASE)
        if fence_match:
            return fence_match[0].strip()
    return cleaned


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
        "Supported intents: 'report' (single-period usage summary), 'compare' (contrast two or more periods), "
        "'why_drop' (explain a decline), 'inventory', 'reorder', 'usage' (legacy synonym for report), and 'chitchat' when no data is needed. "
        "When unsure but data is requested, choose 'report'. "
        "Always emit strict JSON with keys: intent, item, month, year, multiplier, notes, reply, entities. "
        "entities must be an object capturing structured details such as item, metric, month/year, "
        "periods (list of {\"month\": int, \"year\": int}), comparison_periods, sites, and any filters you inferred. "
        "Use uppercase item codes. reply must be a concise conversational response that references what you plan to run or clarifies missing info. "
        "If the user asks what to buy or restock, choose intent 'reorder'. "
        "If they omit the item, leave item null and explain assumptions in notes. "
        "Honor any Relevant past context that appears before the latest input."
    )
    if feedback:
        system_prompt += f"\nUser feedback/preferences to honor: {feedback.strip()}."

    history_messages: list[dict] = []
    for entry in history or []:
        role = entry.get("role")
        content = entry.get("content")
        if role in {"user", "assistant"} and isinstance(content, str):
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
    month_guess, year_guess = infer_period_from_text(prompt, today)
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
    }
    prompt_item_present = bool(context["item"])
    prompt_has_data_keywords = contains_data_request_keywords(prompt)
    prompt_small_talk = looks_like_small_talk(prompt)
    baseline_intent = context["intent"]
    if baseline_intent == "chitchat" and prompt_item_present and prompt_has_data_keywords:
        baseline_intent = deduce_usage_or_report_intent(prompt)
        context["intent"] = baseline_intent
    context["prompt_has_item"] = prompt_item_present
    raw_periods = extract_periods_from_prompt(prompt, today.year)
    prompt_periods = deduplicate_periods(raw_periods, limit=MAX_USAGE_PERIODS)
    context["prompt_periods"] = prompt_periods
    context["prompt_period_count"] = len(prompt_periods)
    context["prompt_period_labels"] = [
        describe_month_year(month_val, year_val, today.year) for month_val, year_val in prompt_periods
    ]
    context["mentions_between_months"] = mentions_month_range(prompt)
    context["mentions_last_year"] = contains_last_year_reference(prompt)
    context["mentions_this_year"] = contains_this_year_reference(prompt)

    followup_same_data = bool(context["followup_same_data"])
    if prior_session_intent in {"usage", "report"} and followup_same_data:
        baseline_intent = prior_session_intent
        context["intent"] = prior_session_intent

    if session_context:
        context["item"] = context.get("item") or session_context.get("item")
        context["month"] = context.get("month") or session_context.get("month")
        context["year"] = context.get("year") or session_context.get("year")
        if isinstance(session_context.get("entities"), dict):
            context["entities"].update(session_context["entities"])

    if memory_context:
        for entry in memory_context:
            metadata = entry.get("metadata") or {}
            context["item"] = context.get("item") or metadata.get("item")
            context["month"] = context.get("month") or metadata.get("month")
            context["year"] = context.get("year") or metadata.get("year")
            entry_entities = metadata.get("entities")
            if isinstance(entry_entities, dict):
                context["entities"].update(entry_entities)

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
        allowed_intents = {"usage", "report", "compare", "why_drop", "inventory", "reorder"}
        if candidate in allowed_intents:
            if candidate == "inventory" and prior_session_intent in {"usage", "report"} and followup_same_data:
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
    if llm_data.get("item"):
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
    if llm_data.get("reply"):
        context["reply"] = llm_data["reply"]

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


def generate_chitchat_reply(prompt: str, history: list[dict]) -> str:
    lowered = prompt.lower()
    if asks_about_capabilities(prompt):
        return (
            "I can pull GP usage for specific items, compare months or years, check current inventory, "
            "and flag the biggest reorder gaps. Try prompts like \"Show NO3CA12 usage for March 2024,\" "
            "\"Compare NO3CA12 this March versus last March,\" or "
            "\"List items below their reorder point for the South Plant.\" "
            "Just mention the item and timeframe you care about and I'll run the numbers."
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

    last_result = latest_history_entry(history, "usage") or latest_history_entry(history, "inventory")
    if last_result and any(word in lowered for word in ("explain", "clarify", "mean", "difference", "why")):
        return "Let me know what part of the previous table you want clarified - quantities, dates, or calculations - and I'll break it down."

    return "I'm here to help with GP data questions - add an item, month, or describe what you'd like explained and I'll dive in."


def handle_usage_question(
    cursor: pyodbc.Cursor, prompt: str, today: datetime.date, context: dict | None = None
) -> dict:
    context = context or {}
    item_code = resolve_item_from_context(prompt, context)
    if not item_code:
        suggestions = suggest_items_by_description(cursor, prompt)
        return {
            "error": "Please mention an item number (e.g., NO3CA12) so I know what to query.",
            "data": None,
            "sql": None,
            "context_type": "usage",
            "suggestions": suggestions,
        }

    item_description = fetch_item_description(cursor, item_code)

    periods = determine_usage_periods(prompt, context, today) or []
    if not periods:
        month_guess, year_guess = infer_period_from_text(prompt, today)
        periods = [(month_guess, year_guess)]

    rows: list[dict] = []
    period_details: list[dict] = []
    sql_previews: list[str] = []
    combined_start: datetime.date | None = None
    combined_end: datetime.date | None = None
    total_usage = 0.0

    for period_month, period_year in periods:
        start_date, end_date = month_date_range(period_month, period_year)
        usage_value = fetch_usage(cursor, item_code, start_date, end_date)
        combined_start = start_date if combined_start is None else min(combined_start, start_date)
        combined_end = end_date if combined_end is None else max(combined_end, end_date)
        row_entry = {
            "Item": item_code,
            "Period": start_date.strftime("%B %Y"),
            "StartDate": start_date.isoformat(),
            "EndDate": end_date.isoformat(),
            "Usage": usage_value,
        }
        if item_description:
            row_entry["Description"] = item_description
        rows.append(row_entry)
        period_details.append({"label": start_date.strftime("%B %Y"), "usage": usage_value})
        total_usage += usage_value
        sql_previews.append(format_sql_preview(USAGE_QUERY, (item_code, start_date, end_date)))

    if len(rows) > 1:
        first_label = rows[0]["Period"]
        last_label = rows[-1]["Period"]
        total_row = {
            "Item": item_code,
            "Period": f"Total ({first_label} - {last_label})",
            "StartDate": combined_start.isoformat() if combined_start else None,
            "EndDate": combined_end.isoformat() if combined_end else None,
            "Usage": total_usage,
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
            usage_metric = row.get("Usage")
            if isinstance(usage_metric, (int, float)):
                row[f"Usage x {multiplier:g}"] = usage_metric * multiplier
        base_usage = total_usage if len(period_details) > 1 else period_details[0]["usage"]
        scaled_value = base_usage * multiplier

    sql_preview = "\n\n".join(sql_previews)
    if len(sql_previews) == 1:
        sql_preview = sql_previews[0]

    if not period_details:
        period_label = None
        usage_value = 0.0
    else:
        period_label = (
            f"{period_details[0]['label']} - {period_details[-1]['label']}"
            if len(period_details) > 1
            else period_details[0]["label"]
        )
        usage_value = total_usage if len(period_details) > 1 else period_details[0]["usage"]

    insights = {
        "item": item_code,
        "period": period_label,
        "usage": usage_value,
        "periods": period_details,
        "total_usage": total_usage if len(period_details) > 1 else None,
        "multiplier": multiplier,
        "scaled": scaled_value,
        "description": item_description,
    }
    return {
        "data": rows,
        "sql": sql_preview,
        "context_type": "usage",
        "insights": insights,
    }


def handle_compare_question(
    cursor: pyodbc.Cursor, prompt: str, today: datetime.date, context: dict | None = None
) -> dict:
    context = context or {}
    item_code = resolve_item_from_context(prompt, context)
    if not item_code:
        return {
            "error": "Please specify an item to compare usage across months.",
            "data": None,
            "sql": None,
            "context_type": "compare",
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
    item_code = resolve_item_from_context(prompt, context)
    if not item_code:
        return {
            "error": "Please mention which item dropped so I can review its history.",
            "data": None,
            "sql": None,
            "context_type": "why_drop",
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
    return {
        "data": rows,
        "sql": sql_preview,
        "context_type": "why_drop",
        "insights": insights,
    }


def handle_inventory_question(cursor: pyodbc.Cursor, prompt: str, context: dict | None = None) -> dict:
    context = context or {}
    item_code = context.get("item") or extract_item_code(prompt)
    base_query = """
        SELECT TOP 25 i.ITEMNMBR, m.ITEMDESC, i.QTYONHND, i.QTYONORD,
               (i.QTYONHND - i.ATYALLOC) AS QtyAvailable, i.ORDRPNTQTY, m.ITMCLSCD
        FROM IV00102 i
        JOIN IV00101 m ON m.ITEMNMBR = i.ITEMNMBR
        WHERE i.LOCNCODE = 'MAIN'
    """
    params: list = []

    if item_code:
        base_query += " AND i.ITEMNMBR = ?"
        params.append(item_code)
    base_query += " ORDER BY i.ORDRPNTQTY DESC"

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
            }
        )

    sql_preview = format_sql_preview(base_query, params) if params else base_query
    insights = {
        "item": item_code,
        "row_count": len(rows),
        "sample": rows[0] if rows else None,
    }
    suggestions: list[dict] = []
    error = None
    if not rows:
        if item_code:
            suggestions = suggest_items_by_description(cursor, prompt)
            error = f"I could not find inventory rows for {item_code} at MAIN."
        else:
            error = "No inventory rows matched. Try a different item or remove filters."
    return {
        "data": rows,
        "sql": sql_preview,
        "context_type": "inventory",
        "insights": insights,
        "error": error,
        "suggestions": suggestions,
    }


def handle_reorder_question(cursor: pyodbc.Cursor) -> dict:
    cursor.execute(REORDER_QUERY)
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
    insights = {
        "count": len(rows),
        "top_row": rows[0] if rows else None,
    }
    error = None
    if not rows:
        error = "All MAIN items meet their order points right now."
    return {
        "data": rows,
        "sql": REORDER_QUERY,
        "context_type": "reorder",
        "insights": insights,
        "error": error,
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
    multiplier = insights.get("multiplier")
    scaled = insights.get("scaled")
    if multiplier is not None and isinstance(scaled, (int, float)):
        message_parts.append(f"Multiplying by {multiplier:g} yields {scaled:,.2f}.")
    return " ".join(message_parts) if message_parts else "Usage results are ready."


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
    if row_count == 0:
        if item:
            return f"I could not find inventory rows for {item} at MAIN."
        return "No inventory rows matched the filters."
    if item and isinstance(sample, dict):
        parts = [f"Inventory snapshot for {item} at MAIN."]
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
        return " ".join(parts).strip()
    return f"Top {row_count} MAIN items ordered by order point. Use an item number to drill in further."


def describe_reorder_message(insights: dict | None) -> str:
    if not insights:
        return "Unable to summarize the reorder list."
    count = insights.get("count", 0) or 0
    if count == 0:
        return "All MAIN items meet their order points right now."
    top_row = insights.get("top_row")
    if not isinstance(top_row, dict):
        top_row = {}
    item = top_row.get("Item")
    shortfall = top_row.get("Shortfall")
    order_point = top_row.get("OrderPoint")
    avail = top_row.get("Avail")
    message = [
        f"{count} items are below their order point.",
        "Worst gaps first means the table is sorted by shortfall (order point minus available quantity) so the most urgent misses float to the top.",
    ]
    if item:
        if all(isinstance(val, (int, float)) for val in (shortfall, order_point, avail)):
            message.append(
                f"{item} needs {shortfall:,.0f} more units to reach its {order_point:,.0f} target ({avail:,.0f} available today)."
            )
        else:
            message.append(f"{item} currently shows the largest shortfall.")
    return " ".join(message)


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
        reply_sections.append(generate_chitchat_reply(prompt, session_history))
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
    elif intent == "inventory":
        reply_sections.append(describe_inventory_message(insights))
    elif intent == "reorder":
        reply_sections.append(describe_reorder_message(insights))
    elif intent == "compare":
        reply_sections.append(describe_compare_message(insights))
    elif intent == "why_drop":
        reply_sections.append(describe_why_drop_message(insights))

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

    sql_payload: dict | None = None
    if intent == "inventory":
        sql_payload = handle_inventory_question(cursor, prompt, context)
    elif intent == "reorder":
        sql_payload = handle_reorder_question(cursor)
    elif intent == "compare":
        sql_payload = handle_compare_question(cursor, prompt, today, context)
    elif intent == "why_drop":
        sql_payload = handle_why_drop_question(cursor, prompt, today, context)
    elif intent in {"usage", "report"}:
        sql_payload = handle_usage_question(cursor, prompt, today, context)
    elif intent != "chitchat":
        sql_payload = handle_usage_question(cursor, prompt, today, context)

    message = compose_conversational_message(prompt, context, sql_payload, session_history)
    result = {
        "message": message,
        "data": sql_payload.get("data") if sql_payload else None,
        "sql": sql_payload.get("sql") if sql_payload else None,
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
            "context": result.get("context"),
            "context_type": result.get("context_type"),
        }
    except pyodbc.Error as err:
        return {"content": f"Query failed: {err}", "sql": None, "data": None}
    finally:
        if conn is not None:
            conn.close()


def render_sql_chat(today: datetime.date, current_user: dict | None = None) -> None:
    st.subheader("SQL-style data chat")
    st.caption(
        "Ask plain-language questions about Dynamics GP data. "
        "I'll classify the intent (report, compare, why_drop, inventory, reorder), pull relevant memory, "
        "and fill the right SQL template automatically. Mention an item (e.g., NO3CA12), time period, "
        "and optional math like 'multiply by 3'. Use 'feedback: ...' for persistent guidance or 'reset' to clear the chat."
    )

    user_id = get_authenticated_user_id()
    user = current_user or get_authenticated_user()
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

    history_for_llm = [
        {"role": entry["role"], "content": entry["content"]}
        for entry in history[-6:]
        if entry["role"] in {"user", "assistant"}
    ]
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
    history.append(
        {
            "id": assistant_message_id,
            "role": "assistant",
            "content": response.get("content", "Done."),
            "sql": response.get("sql"),
            "data": response.get("data"),
            "context_type": context_type,
            "context": response.get("context"),
            "source_prompt": prompt_for_execution,
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
            "context": response.get("context"),
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
WHERE i.LOCNCODE = 'MAIN'
  AND (i.QTYONHND - i.ATYALLOC) < i.ORDRPNTQTY
ORDER BY Shortfall DESC;
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
    "To Help you Grow"
    "Interpreter handles the reasoning and logic, then the app runs the SQL locally and securely."
)

today_global = datetime.date.today()
render_sql_chat(today_global, current_user)
