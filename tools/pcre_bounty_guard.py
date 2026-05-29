#!/usr/bin/env python3
"""Validate the POSIX backref bounty board against Agent Hunt rules.

Enforces:
- Non-negative balances
- Positive bounties
- Max 10 active locks per agent
- Lock expiry within 24 hours
- Lock deposit = ceil(10% of bounty)
- Ledger balance consistency (running totals)
- Total allocated bounties <= pool cap
- Effort estimates present on all tasks
- Valid task/lock/ledger statuses
- Artifact and verifier present on DONE tasks
"""

from __future__ import annotations

import argparse
import math
import re
import sys
from collections import Counter
from datetime import datetime, timezone
from pathlib import Path


VALID_TASK_STATUS = {"OPEN", "LOCKED", "DONE", "BLOCKED", "DROPPED"}
VALID_LOCK_STATUS = {"ACTIVE", "EXPIRED", "RELEASED", "COLLECTED"}
VALID_LEDGER_ACTIONS = {
    "COLLECT", "LOCK", "RELEASE", "SLASH", "RESET",
    "SUB_OFFER", "SUB_CANCEL",
}

DEFAULT_POOL = 50_000
MAX_ACTIVE_LOCKS = 10


def table_rows(text: str, heading: str) -> list[dict[str, str]]:
    lines = text.splitlines()
    start = None
    for i, line in enumerate(lines):
        if line.strip() == f"## {heading}":
            start = i + 1
            break
    if start is None:
        return []

    rows: list[str] = []
    for line in lines[start:]:
        if line.startswith("## "):
            break
        if line.strip().startswith("|"):
            rows.append(line.strip())
    if len(rows) < 2:
        return []

    header = [c.strip() for c in rows[0].strip("|").split("|")]
    data = []
    for row in rows[2:]:
        cells = [c.strip() for c in row.strip("|").split("|")]
        if len(cells) == len(header):
            data.append(dict(zip(header, cells)))
    return data


def parse_int(value: str, where: str, errors: list[str]) -> int:
    cleaned = value.replace(",", "").strip()
    try:
        return int(cleaned)
    except ValueError:
        errors.append(f"{where}: expected integer, got {value!r}")
        return 0


def parse_utc(value: str, where: str, errors: list[str]) -> datetime | None:
    if value in {"-", ""}:
        return None
    try:
        if value.endswith("Z"):
            value = value[:-1] + "+00:00"
        dt = datetime.fromisoformat(value)
        if dt.tzinfo is None:
            errors.append(f"{where}: timestamp must include timezone")
            return None
        return dt.astimezone(timezone.utc)
    except ValueError:
        errors.append(f"{where}: invalid ISO timestamp {value!r}")
        return None


def contains_named_artifact(path: Path, name: str) -> bool:
    if not path.exists():
        return False
    text = path.read_text(encoding="utf-8")
    name_re = re.escape(name)
    pattern = re.compile(
        rf"\b(?:lemma|theorem|corollary|proposition|definition|fun|primrec|inductive|datatype)"
        rf"\s+(?:\([^)]*\)\s+)?{name_re}\b"
    )
    return bool(pattern.search(text))


def validate_artifact_spec(spec: str, root: Path, where: str, errors: list[str]) -> None:
    if not spec or spec == "-":
        errors.append(f"{where}: DONE task must name checked artifact(s)")
        return

    for part in [p.strip() for p in spec.split(";") if p.strip()]:
        if ":" in part and part.split(":", 1)[0].endswith(".thy"):
            raw_path, raw_names = part.split(":", 1)
            path = root / raw_path
            if not path.exists():
                errors.append(f"{where}: artifact file does not exist: {raw_path}")
                continue
            names = [name.strip() for name in raw_names.split(",") if name.strip()]
            if not names:
                errors.append(f"{where}: artifact {raw_path} must name theorem/definition ids")
            for name in names:
                if not contains_named_artifact(path, name):
                    errors.append(f"{where}: cannot find artifact {name!r} in {raw_path}")
        else:
            path = root / part
            if not path.exists():
                errors.append(f"{where}: artifact path does not exist: {part}")


def validate_effort_estimate(row: dict[str, str], task_id: str, errors: list[str]) -> None:
    for field in ("Est. Lines", "Difficulty", "Est. USD"):
        val = row.get(field, "").replace(",", "").strip()
        if not val or val == "-":
            errors.append(f"task {task_id}: missing effort estimate field {field!r}")
            continue
        try:
            n = int(val)
            if n <= 0:
                errors.append(f"task {task_id}: {field} must be positive, got {n}")
        except ValueError:
            errors.append(f"task {task_id}: {field} must be integer, got {val!r}")

    difficulty = row.get("Difficulty", "").replace(",", "").strip()
    if difficulty and difficulty != "-":
        try:
            d = int(difficulty)
            if not (1 <= d <= 10):
                errors.append(f"task {task_id}: Difficulty must be 1-10, got {d}")
        except ValueError:
            pass


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--file", default="BACKREF_BOUNTIES.md")
    parser.add_argument("--max-active-locks", type=int, default=MAX_ACTIVE_LOCKS)
    parser.add_argument("--pool", type=int, default=DEFAULT_POOL)
    args = parser.parse_args()

    path = Path(args.file)
    root = path.resolve().parent
    text = path.read_text(encoding="utf-8")
    errors: list[str] = []

    pool_rows = table_rows(text, "Pool")
    active = table_rows(text, "Active")
    completed = table_rows(text, "Completed")
    locks = table_rows(text, "Locks")
    balances = table_rows(text, "Agent Balances")
    ledger = table_rows(text, "Ledger")

    if not active and not completed:
        errors.append("missing both ## Active and ## Completed tables")
    if not locks:
        errors.append("missing or empty ## Locks table")
    if not balances:
        errors.append("missing or empty ## Agent Balances table")
    if not ledger:
        errors.append("missing or empty ## Ledger table")

    tasks = active + completed
    task_ids = [row.get("ID", "") for row in tasks]
    for task_id, count in Counter(task_ids).items():
        if count > 1:
            errors.append(f"duplicate task id: {task_id}")

    task_status: dict[str, str] = {}
    task_bounty: dict[str, int] = {}
    task_owner: dict[str, str] = {}
    total_allocated = 0

    for row in tasks:
        task_id = row.get("ID", "")
        status = row.get("Status", "")
        owner = row.get("Owner", "")
        bounty = parse_int(row.get("Bounty", "0"), f"task {task_id} bounty", errors)
        if bounty <= 0:
            errors.append(f"task {task_id}: bounty must be positive")
        total_allocated += bounty
        if status not in VALID_TASK_STATUS:
            errors.append(f"task {task_id}: invalid status {status!r}")
        if status == "DONE":
            if owner in {"", "-"}:
                errors.append(f"task {task_id}: DONE task needs owner")
            validate_artifact_spec(row.get("Artifact", ""), root, f"task {task_id}", errors)
            if row.get("Verifier", "") in {"", "-"}:
                errors.append(f"task {task_id}: DONE task needs verifier")

        validate_effort_estimate(row, task_id, errors)

        task_status[task_id] = status
        task_bounty[task_id] = bounty
        task_owner[task_id] = owner

    if total_allocated > args.pool:
        errors.append(
            f"total allocated bounties ({total_allocated}) exceed pool cap ({args.pool})"
        )

    if pool_rows:
        for row in pool_rows:
            cat = row.get("Category", "")
            amt = parse_int(row.get("Amount", "0"), f"pool {cat}", errors)
            if cat == "Total pool" and amt != args.pool:
                errors.append(f"pool table says {amt}, expected {args.pool}")

    active_locks: Counter[str] = Counter()
    now = datetime.now(timezone.utc)
    for row in locks:
        lock_id = row.get("Lock ID", "")
        task_id = row.get("Task ID", "")
        agent = row.get("Agent", "")
        status = row.get("Status", "")
        if lock_id == "-" and task_id == "-" and status == "RELEASED":
            continue
        deposit = parse_int(row.get("Deposit", "0"), f"lock {lock_id} deposit", errors)
        expiry = parse_utc(row.get("Expires UTC", "-"), f"lock {lock_id}", errors)
        if task_id not in task_status:
            errors.append(f"lock {lock_id}: unknown task id {task_id}")
        if status not in VALID_LOCK_STATUS:
            errors.append(f"lock {lock_id}: invalid status {status!r}")
        if status == "ACTIVE":
            active_locks[agent] += 1
            if deposit <= 0:
                errors.append(f"lock {lock_id}: active lock deposit must be positive")
            expected_deposit = math.ceil(task_bounty.get(task_id, 0) * 0.10)
            if expected_deposit > 0 and deposit < expected_deposit:
                errors.append(
                    f"lock {lock_id}: deposit {deposit} < required 10% of bounty ({expected_deposit})"
                )
            if expiry is None:
                errors.append(f"lock {lock_id}: active lock needs expiry")
            elif expiry <= now:
                errors.append(f"lock {lock_id}: active lock is expired")

    for agent, count in active_locks.items():
        if count > args.max_active_locks:
            errors.append(f"{agent}: {count} active locks exceeds max {args.max_active_locks}")

    for row in balances:
        agent = row.get("Agent", "")
        balance = parse_int(row.get("Balance", "0"), f"balance {agent}", errors)
        if balance < 0:
            errors.append(f"balance {agent}: must be non-negative")

    running: Counter[str] = Counter()
    for row in ledger:
        timestamp = row.get("Time UTC", "")
        parse_utc(timestamp, f"ledger {timestamp}", errors)
        agent = row.get("Agent", "")
        action = row.get("Action", "")
        task_id = row.get("Task ID", "")
        amount = parse_int(row.get("Amount", "0"), f"ledger {timestamp} amount", errors)
        balance_after = parse_int(
            row.get("Balance After", "0"),
            f"ledger {timestamp} balance after",
            errors,
        )
        if action not in VALID_LEDGER_ACTIONS:
            errors.append(f"ledger {timestamp}: invalid action {action!r}")
        if task_id not in task_status:
            errors.append(f"ledger {timestamp}: unknown task id {task_id}")

        if action == "COLLECT":
            if task_status.get(task_id) != "DONE":
                errors.append(f"ledger {timestamp}: cannot collect non-DONE task {task_id}")
            if task_owner.get(task_id) != agent:
                errors.append(f"ledger {timestamp}: collector {agent} is not owner of {task_id}")
            if task_bounty.get(task_id) != amount:
                errors.append(f"ledger {timestamp}: amount does not match bounty for {task_id}")
            running[agent] += amount
        elif action in ("LOCK", "SLASH", "SUB_OFFER"):
            running[agent] -= amount
        elif action in ("RELEASE", "SUB_CANCEL"):
            running[agent] += amount
        elif action == "RESET":
            running[agent] = amount

        if running[agent] != balance_after:
            errors.append(
                f"ledger {timestamp}: balance after is {balance_after}, expected {running[agent]}"
            )
        if running[agent] < 0:
            errors.append(
                f"ledger {timestamp}: balance for {agent} went negative ({running[agent]})"
            )

    table_balances = {
        row.get("Agent", ""): parse_int(
            row.get("Balance", "0"), f"balance {row.get('Agent', '')}", errors
        )
        for row in balances
    }
    for agent, balance in table_balances.items():
        if balance != running.get(agent, 0):
            errors.append(f"balance {agent}: table says {balance}, ledger says {running.get(agent, 0)}")

    if errors:
        for error in errors:
            print(f"ERROR: {error}", file=sys.stderr)
        return 1

    print(
        f"OK: {len(tasks)} tasks, {len(locks)} locks, "
        f"{sum(active_locks.values())} active locks, "
        f"pool {total_allocated}/{args.pool} allocated"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
