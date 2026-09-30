#!/usr/bin/env python3
import json
import sys

PREFIX = "DistinctionSelfReference."

if len(sys.argv) != 2:
    raise SystemExit("usage: extract_project_constants.py <solution.export>")

names = {0: ""}
decls = set()

def decode_name(idx):
    return names.get(idx)

with open(sys.argv[1], "r", encoding="utf-8") as f:
    for line_no, line in enumerate(f, 1):
        line = line.strip()
        if not line:
            continue
        obj = json.loads(line)

        if "in" in obj:
            idx = obj["in"]
            if "str" in obj:
                data = obj["str"]
                pre = names[data["pre"]]
                part = data["str"]
                names[idx] = f"{pre}.{part}" if pre else part
            elif "num" in obj:
                data = obj["num"]
                pre = names[data["pre"]]
                part = str(data["i"])
                names[idx] = f"{pre}.{part}" if pre else part
            continue

        for key in ("axiom", "def", "opaque", "thm"):
            data = obj.get(key)
            if isinstance(data, dict) and "name" in data:
                name = decode_name(data["name"])
                if name and name.startswith(PREFIX):
                    decls.add(name)

        data = obj.get("inductive")
        if isinstance(data, dict):
            for group in ("types", "ctors", "recs"):
                for item in data.get(group, []):
                    if isinstance(item, dict) and "name" in item:
                        name = decode_name(item["name"])
                        if name and name.startswith(PREFIX):
                            decls.add(name)

        data = obj.get("quot")
        if isinstance(data, dict) and "name" in data:
            name = decode_name(data["name"])
            if name and name.startswith(PREFIX):
                decls.add(name)

for name in sorted(decls):
    print(name)

if not decls:
    raise SystemExit("no project declarations found in export")
