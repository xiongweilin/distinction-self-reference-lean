#!/usr/bin/env python3
from pathlib import Path
import re
import sys

ROOTS = [Path("DistinctionSelfReference"), Path("DistinctionSelfReference.lean")]
BANNED_WORDS = re.compile(r"\b(sorry|admit|axiom|constant)\b")

def strip_comments_and_strings(text: str) -> str:
    out = []
    i = 0
    n = len(text)
    block_depth = 0
    in_line = False
    in_string = False
    escaped = False

    while i < n:
        ch = text[i]
        nxt = text[i + 1] if i + 1 < n else ""

        if in_line:
            if ch == "\n":
                in_line = False
                out.append("\n")
            else:
                out.append(" ")
            i += 1
            continue

        if block_depth:
            if ch == "/" and nxt == "-":
                block_depth += 1
                out.extend((" ", " "))
                i += 2
                continue
            if ch == "-" and nxt == "/":
                block_depth -= 1
                out.extend((" ", " "))
                i += 2
                continue
            out.append("\n" if ch == "\n" else " ")
            i += 1
            continue

        if in_string:
            if escaped:
                escaped = False
                out.append(" ")
                i += 1
                continue
            if ch == "\\":
                escaped = True
                out.append(" ")
                i += 1
                continue
            if ch == '"':
                in_string = False
                out.append(" ")
                i += 1
                continue
            out.append("\n" if ch == "\n" else " ")
            i += 1
            continue

        if ch == "-" and nxt == "-":
            in_line = True
            out.extend((" ", " "))
            i += 2
            continue
        if ch == "/" and nxt == "-":
            block_depth = 1
            out.extend((" ", " "))
            i += 2
            continue
        if ch == '"':
            in_string = True
            out.append(" ")
            i += 1
            continue

        out.append(ch)
        i += 1

    if block_depth:
        raise ValueError("unterminated block comment")
    if in_string:
        raise ValueError("unterminated string literal")
    return "".join(out)

def lean_files():
    for root in ROOTS:
        if root.is_file():
            yield root
        elif root.is_dir():
            yield from sorted(root.rglob("*.lean"))

def main() -> int:
    failures = []
    for path in lean_files():
        try:
            source = path.read_text(encoding="utf-8")
            code = strip_comments_and_strings(source)
        except Exception as exc:
            failures.append(f"{path}: lexical audit failed: {exc}")
            continue

        for lineno, line in enumerate(code.splitlines(), start=1):
            for match in BANNED_WORDS.finditer(line):
                failures.append(
                    f"{path}:{lineno}: forbidden Lean token {match.group(1)!r}"
                )

    if failures:
        print("\n".join(failures))
        return 1

    print("Lean source audit passed: no sorry/admit/axiom/constant tokens in code.")
    return 0

if __name__ == "__main__":
    sys.exit(main())
