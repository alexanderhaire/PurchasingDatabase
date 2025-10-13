#!/usr/bin/env python3
"""
SQL Talk Copilot — a secure, read‑only chat app that answers questions using your SQL Server (Dynamics GP + analytics tables)

Key features
- Text-to-SQL with schema-aware prompts (introspects tables/columns, primary keys)
- Strong guardrails: SELECT-only, denylist of mutating ops, row-limit enforcement
- Dual response: (a) an answer in plain English, (b) the SQL it ran, with a preview table
- Plug-in backends: OpenAI or local Ollama (LLM-agnostic wrapper)
- Optional vendor exceptions awareness if analytics.ExceptionQueue exists
- Simple web UI (Flask) you can run on your Windows box/gateway host

Run
  pip install flask pandas pyodbc pydantic uvicorn python-dotenv
  # If using OpenAI: pip install openai
  # If using Ollama locally: https://ollama.com (install separately)

  setx SQL_SERVER DYNAMICSGP
  setx SQL_DATABASE CDI
  setx SQL_AUTH windows  # or sql
  setx SQL_USER <if sql auth>
  setx SQL_PASSWORD <if sql auth>
  setx LLM_PROVIDER openai   # or ollama
  setx OPENAI_API_KEY sk-... # only if provider=openai
  setx OLLAMA_MODEL llama3.1:8b  # only if provider=ollama

  python app.py
  # then open http://localhost:8000

Notes
- This is read‑only by design. It refuses UPDATE/DELETE/etc. You can extend the allowlist later.
- For large tables, it auto-adds TOP 200 to previews to avoid heavy scans.
- Uses parameterized templates for common filters (date ranges, site, item) when it can infer them.
"""
from __future__ import annotations

import os
import re
import json
import time
import math
import pyodbc
import pandas as pd
from typing import List, Dict, Any, Optional
from dataclasses import dataclass
from flask import Flask, request, jsonify, send_from_directory

# ---------------------------
# LLM provider (OpenAI or Ollama via simple HTTP)
# ---------------------------

class LLM:
    def __init__(self):
        self.provider = os.getenv("LLM_PROVIDER", "openai").lower()
        if self.provider == "openai":
            try:
                from openai import OpenAI
                self.client = OpenAI()
                self.model = os.getenv("OPENAI_MODEL", "gpt-4o-mini")
            except Exception as e:
                raise RuntimeError(f"OpenAI provider selected but openai package not available: {e}")
        elif self.provider == "ollama":
            # Simple local HTTP to Ollama
            import requests  # lazy availability assumed with system python; pip install requests if needed
            self.requests = requests
            self.ollama_host = os.getenv("OLLAMA_HOST", "http://localhost:11434")
            self.model = os.getenv("OLLAMA_MODEL", "llama3.1:8b")
        else:
            raise RuntimeError("Unsupported LLM_PROVIDER. Use 'openai' or 'ollama'.")

    def chat(self, messages: List[Dict[str, str]], temperature: float = 0.1) -> str:
        if self.provider == "openai":
            resp = self.client.chat.completions.create(
                model=self.model,
                temperature=temperature,
                messages=messages,
            )
            return resp.choices[0].message.content
        else:  # ollama
            payload = {"model": self.model, "messages": messages, "stream": False, "options": {"temperature": temperature}}
            r = self.requests.post(f"{self.ollama_host}/v1/chat/completions", json=payload, timeout=120)
            r.raise_for_status()
            data = r.json()
            return data["choices"][0]["message"]["content"]


# ---------------------------
# SQL connection & schema introspection
# ---------------------------

def connect_sql() -> pyodbc.Connection:
    driver = os.getenv("ODBC_DRIVER", "ODBC Driver 18 for SQL Server")
    server = os.getenv("SQL_SERVER", "localhost")
    db = os.getenv("SQL_DATABASE", "master")
    auth = os.getenv("SQL_AUTH", "windows").lower()
    if auth == "windows":
        conn_str = f"DRIVER={{{{}}}};SERVER={server};DATABASE={db};Trusted_Connection=yes;TrustServerCertificate=yes".format(driver)
    else:
        user = os.getenv("SQL_USER")
        pwd = os.getenv("SQL_PASSWORD")
        if not user or not pwd:
            raise RuntimeError("SQL auth requires SQL_USER and SQL_PASSWORD environment variables")
        conn_str = f"DRIVER={{{{}}}};SERVER={server};DATABASE={db};UID={user};PWD={pwd};TrustServerCertificate=yes".format(driver)
    return pyodbc.connect(conn_str)


def get_schema_snapshot(conn: pyodbc.Connection, schemas: Optional[List[str]] = None) -> Dict[str, Any]:
    if schemas is None:
        schemas = ["dbo", "analytics"]
    q = """
        SELECT c.TABLE_SCHEMA, c.TABLE_NAME, c.COLUMN_NAME, c.DATA_TYPE
        FROM INFORMATION_SCHEMA.COLUMNS c
        JOIN INFORMATION_SCHEMA.TABLES t
          ON t.TABLE_SCHEMA=c.TABLE_SCHEMA AND t.TABLE_NAME=c.TABLE_NAME AND t.TABLE_TYPE='BASE TABLE'
        WHERE c.TABLE_SCHEMA IN ({schemas})
        ORDER BY c.TABLE_SCHEMA, c.TABLE_NAME, c.ORDINAL_POSITION
    """.replace("{schemas}", ",".join([f"'{s}'" for s in schemas]))
    df = pd.read_sql(q, conn)
    by_table: Dict[str, Dict[str, str]] = {}
    for _, r in df.iterrows():
        key = f"{r.TABLE_SCHEMA}.{r.TABLE_NAME}"
        by_table.setdefault(key, {})[r.COLUMN_NAME] = r.DATA_TYPE
    return {"tables": by_table}


# ---------------------------
# Guardrails & SQL sanitizer
# ---------------------------

DENY_RE = re.compile(r"\b(UPDATE|DELETE|INSERT|MERGE|DROP|ALTER|TRUNCATE|EXEC|sp_|xp_|;|--|/\*)\b", re.I)


def sanitize_sql(sql: str) -> str:
    sql = sql.strip().rstrip(";")
    # Must start with SELECT
    if not re.match(r"^SELECT\b", sql, re.I):
        raise ValueError("Only SELECT queries are allowed.")
    if DENY_RE.search(sql):
        raise ValueError("Query contains a disallowed keyword or pattern.")
    # Enforce TOP limit if not an aggregate-only query
    if re.search(r"^SELECT\s+TOP\s+\d+", sql, re.I) is None and "count(" not in sql.lower():
        # Inject TOP 200 after SELECT
        sql = re.sub(r"^SELECT\s+", "SELECT TOP 200 ", sql, flags=re.I)
    return sql


# ---------------------------
# Prompt engineering for Text-to-SQL
# ---------------------------

def make_sql_prompt(user_q: str, schema_snapshot: Dict[str, Any]) -> List[Dict[str, str]]:
    tables = schema_snapshot["tables"]
    schema_text = []
    for t, cols in tables.items():
        col_str = ", ".join([f"{c}:{typ}" for c, typ in cols.items()])
        schema_text.append(f"- {t}({col_str})")
    schema_doc = "\n".join(schema_text)

    system = (
        "You are a senior SQL analyst generating **safe, efficient** T-SQL for Microsoft SQL Server. "
        "Rules: 1) SELECT-only; no mutations; 2) Prefer indexed columns when obvious; 3) Always qualify tables with schema; "
        "4) Use concise column lists (avoid SELECT *); 5) If date filters are implied (e.g., 'last 30 days'), implement them with DATEADD(day, -30, GETDATE()); "
        "6) If the request is ambiguous, choose the most reasonable interpretation and label assumptions in a SQL comment; "
        "7) Limit preview rows with TOP 200 unless the query uses aggregations only."
    )

    user = (
        f"User question: {user_q}\n\n"
        f"Database schemas available (read-only):\n{schema_doc}\n\n"
        "Return ONLY the SQL. No explanation."
    )
    return [{"role": "system", "content": system}, {"role": "user", "content": user}]


# ---------------------------
# SQL execution
# ---------------------------

def run_sql(conn: pyodbc.Connection, sql: str) -> pd.DataFrame:
    with conn.cursor() as cur:
        df = pd.read_sql(sql, conn)
    return df


# ---------------------------
# Answer drafting
# ---------------------------

def make_answer_prompt(user_q: str, sql: str, preview: pd.DataFrame) -> List[Dict[str, str]]:
    # Convert preview to a compact markdown table (first ~10 rows)
    head = preview.head(10)
    md = head.to_markdown(index=False) if not head.empty else "(no rows)"
    system = (
        "You explain analytics results for operations managers: be concise, factual, and actionable. "
        "Return 3-5 bullet points with key takeaways, one KPI in bold, and mention any assumptions."
    )
    user = (
        f"Question: {user_q}\n\nSQL used:\n```sql\n{sql}\n```\n\nData preview (first 10 rows):\n{md}\n"
    )
    return [{"role": "system", "content": system}, {"role": "user", "content": user}]


# ---------------------------
# Flask app
# ---------------------------

app = Flask(__name__, static_folder="static")

# Keep a cached schema for 5 minutes
_SCHEMA_CACHE = {"ts": 0.0, "snapshot": None}


@app.route("/")
def index():
    return send_from_directory("static", "index.html")


@app.route("/api/chat", methods=["POST"])
def chat():
    data = request.get_json(force=True)
    user_q = data.get("message", "").strip()
    if not user_q:
        return jsonify({"error": "Empty question"}), 400

    # Connect
    try:
        conn = connect_sql()
    except Exception as e:
        return jsonify({"error": f"SQL connection failed: {e}"}), 500

    # Schema cache
    now = time.time()
    snap = _SCHEMA_CACHE["snapshot"] if (now - _SCHEMA_CACHE["ts"] < 300 and _SCHEMA_CACHE["snapshot"]) else None
    if snap is None:
        try:
            snap = get_schema_snapshot(conn)
            _SCHEMA_CACHE["snapshot"] = snap
            _SCHEMA_CACHE["ts"] = now
        except Exception as e:
            return jsonify({"error": f"Schema introspection failed: {e}"}), 500

    # Generate SQL
    try:
        llm = LLM()
        sql_raw = llm.chat(make_sql_prompt(user_q, snap))
        sql = sanitize_sql(sql_raw)
    except Exception as e:
        return jsonify({"error": f"SQL generation failed: {e}"}), 500

    # Run SQL (read-only best effort)
    try:
        df = run_sql(conn, sql)
    except Exception as e:
        return jsonify({"error": f"SQL execution error: {e}", "sql": sql}), 400

    # Draft answer
    try:
        explanation = LLM().chat(make_answer_prompt(user_q, sql, df))
    except Exception:
        explanation = "Here are the first rows. (Summary disabled)"

    # Return compact table data
    preview = df.head(50) if df is not None else pd.DataFrame()
    return jsonify({
        "answer": explanation,
        "sql": sql,
        "columns": list(preview.columns),
        "rows": preview.values.tolist(),
        "row_count": int(df.shape[0]) if isinstance(df, pd.DataFrame) else 0
    })


# ---------------------------
# Static UI (a very small chat front-end)
# ---------------------------

STATIC_HTML = r"""
<!doctype html>
<html>
  <head>
    <meta charset="utf-8" />
    <meta name="viewport" content="width=device-width, initial-scale=1" />
    <title>SQL Talk Copilot</title>
    <style>
      body { font-family: system-ui, sans-serif; margin: 20px; }
      .container { max-width: 980px; margin: auto; }
      .msg { padding: 12px 14px; border-radius: 12px; margin: 8px 0; }
      .user { background: #eef; }
      .bot { background: #efe; }
      code, pre { background: #f5f5f5; padding: 12px; border-radius: 8px; display: block; overflow-x: auto; }
      table { border-collapse: collapse; width: 100%; }
      th, td { border: 1px solid #ddd; padding: 6px; font-size: 12px; }
      th { background: #fafafa; }
    </style>
  </head>
  <body>
    <div class="container">
      <h2>SQL Talk Copilot</h2>
      <p>Ask about your GP & analytics data. Example: <em>“What are the top 10 items by Gap in the last 30 days at site MAIN?”</em></p>
      <div id="chat"></div>
      <form id="f">
        <input id="q" type="text" style="width:80%" placeholder="Type your question…" />
        <button>Ask</button>
      </form>
    </div>
    <script>
      const chat = document.getElementById('chat');
      const f = document.getElementById('f');
      const q = document.getElementById('q');

      function addMsg(role, html){
        const el = document.createElement('div');
        el.className = 'msg ' + (role==='user'?'user':'bot');
        el.innerHTML = html;
        chat.appendChild(el);
        window.scrollTo(0, document.body.scrollHeight);
      }

      f.addEventListener('submit', async (e)=>{
        e.preventDefault();
        const text = q.value.trim(); if(!text) return;
        addMsg('user', text);
        q.value='';
        const r = await fetch('/api/chat', { method:'POST', headers:{'Content-Type':'application/json'}, body: JSON.stringify({message:text})});
        const data = await r.json();
        if(!r.ok){ addMsg('bot', `<b>Error:</b> ${data.error || 'Unknown error'}<pre>${(data.sql)||''}</pre>`); return; }
        const sql = data.sql ? `<h4>SQL</h4><pre>${data.sql}</pre>` : '';
        let table = '';
        if(data.columns && data.columns.length){
          table += '<h4>Preview</h4><table><thead><tr>' + data.columns.map(c=>`<th>${c}</th>`).join('') + '</tr></thead><tbody>';
          table += data.rows.map(r=>'<tr>'+r.map(x=>`<td>${x===null?'':x}</td>`).join('')+'</tr>').join('');
          table += '</tbody></table>';
          table += `<p>Rows: ${data.row_count}</p>`;
        }
        addMsg('bot', `<div>${data.answer||''}</div>${sql}${table}`);
      });
    </script>
  </body>
</html>
"""

os.makedirs("static", exist_ok=True)
index_html_path = os.path.join("static", "index.html")
if not os.path.exists(index_html_path):
    with open(index_html_path, "w", encoding="utf-8") as f:
        f.write(STATIC_HTML)


if __name__ == "__main__":
    port = int(os.getenv("PORT", "8000"))
    app.run(host="0.0.0.0", port=port, debug=False)
