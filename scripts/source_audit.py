#!/usr/bin/env python3
"""Reject unfinished proof tokens and project-local axiom declarations in Lean code.

This scanner strips Lean line comments, nested block comments, and string
literals before checking tokens. It is intentionally conservative about actual
code while allowing words such as "admit" in prose comments.
"""

from __future__ import annotations

import pathlib
import re
import sys

ROOTS = [pathlib.Path("DistinctionSelfReference"), pathlib.Path("DistinctionSelfReference.lean")]
FORBIDDEN = re.compile(r"\b(sorry|admit|axiom|constant)\b")


def strip_non_code(text: str) -> str:
    out: list[str] = []
    i = 0
    block_depth = 0
    in_string = False
    escaped = False

    while i < len(text):
        if block_depth:
            if text.startswith("/-", i):
                block_depth += 1
                out.extend("  ")
                i += 2
            elif text.startswith("-/", i):
                block_depth -= 1
                out.extend("  ")
                i += 2
            else:
                out.append("\n" if text[i] == "\n" else " ")
                i += 1
            continue

        if in_string:
            ch = text[i]
            if escaped:
                escaped = False
                out.append(" ")
                i += 1
            elif ch == "\\":
                escaped = True
                out.append(" ")
                i += 1
            elif ch == '"':
                in_string = False
                out.append(" ")
                i += 1
            else:
                out.append("\n" if ch == "\n" else " ")
                i += 1
            continue

        if text.startswith("--", i):
            while i < len(text) and text[i] != "\n":
                out.append(" ")
                i += 1
            continue

        if text.startswith("/-", i):
            block_depth = 1
            out.extend("  ")
            i += 2
            continue

        if text[i] == '"':
            in_string = True
            out.append(" ")
            i += 1
            continue

        out.append(text[i])
        i += 1

    return "".join(out)


def lean_files() -> list[pathlib.Path]:
    files: list[pathlib.Path] = []
    for root in ROOTS:
        if root.is_dir():
            files.extend(sorted(root.rglob("*.lean")))
        elif root.suffix == ".lean" and root.exists():
            files.append(root)
    return files


def main() -> int:
    failures: list[str] = []
    for path in lean_files():
        raw = path.read_text(encoding="utf-8")
        code = strip_non_code(raw)
        for match in FORBIDDEN.finditer(code):
            line = code.count("\n", 0, match.start()) + 1
            failures.append(f"{path}:{line}: forbidden Lean token '{match.group(1)}'")

    if failures:
        print("\n".join(failures))
        return 1

    print("Lean source audit passed: no sorry/admit/axiom/constant tokens in code.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
