#!/usr/bin/env python3
"""Reject proof-bypass markers in POSIX backref Isabelle sources."""

from __future__ import annotations

import argparse
import re
import subprocess
import sys
from pathlib import Path


BLOCKED = {
    "sorry": re.compile(r"\bsorry\b"),
    "oops": re.compile(r"\boops\b"),
    "quick_and_dirty": re.compile(r"\bquick_and_dirty\b"),
    "axiomatization": re.compile(r"\baxiomatization\b"),
    "oracle": re.compile(r"\boracle\b"),
    "admit": re.compile(r"\badmit\b", re.IGNORECASE),
}


def git_files(root: Path) -> list[Path]:
    try:
        proc = subprocess.run(
            ["git", "-C", str(root), "ls-files", "*.thy"],
            check=True,
            text=True,
            stdout=subprocess.PIPE,
        )
        tracked = [root / line for line in proc.stdout.splitlines() if line]
    except (OSError, subprocess.CalledProcessError):
        tracked = []

    found = {path.resolve() for path in tracked}
    for path in root.rglob("*.thy"):
        if ".git" not in path.parts:
            found.add(path.resolve())
    return sorted(found)


def strip_isabelle_comments(text: str) -> str:
    out: list[str] = []
    depth = 0
    i = 0
    while i < len(text):
        two = text[i : i + 2]
        if two == "(*":
            depth += 1
            out.append(" ")
            out.append(" ")
            i += 2
            continue
        if two == "*)" and depth:
            depth -= 1
            out.append(" ")
            out.append(" ")
            i += 2
            continue
        char = text[i]
        out.append("\n" if char == "\n" else (" " if depth else char))
        i += 1
    return "".join(out)


def line_number(text: str, offset: int) -> int:
    return text.count("\n", 0, offset) + 1


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", default=".")
    args = parser.parse_args()

    root = Path(args.root).resolve()
    errors: list[str] = []

    for path in git_files(root):
        text = path.read_text(encoding="utf-8")
        stripped = strip_isabelle_comments(text)
        rel = path.relative_to(root)
        for name, pattern in BLOCKED.items():
            for match in pattern.finditer(stripped):
                errors.append(f"{rel}:{line_number(stripped, match.start())}: blocked token {name!r}")

    if errors:
        for error in errors:
            print(f"ERROR: {error}", file=sys.stderr)
        return 1

    print(f"OK: no blocked proof-bypass markers in {len(git_files(root))} Isabelle files")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
