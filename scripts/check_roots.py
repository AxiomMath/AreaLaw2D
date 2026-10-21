#!/usr/bin/env python3
"""Check that every module of each library directory is imported, directly or
transitively, by the library's root file.

The roots are curated (`AreaLaw.lean` imports the section umbrellas and `Transfer`,
`AreaLawForMathlib.lean` lists its files), so `lake exe mk_all --check`, which demands
one import line per file, does not apply. A module no root reaches is not built by
`lake build` and fails this check.

Run from the repository root: `python3 scripts/check_roots.py`.
"""
import os
import re
import sys

LIBS = ["AreaLaw", "AreaLawForMathlib"]
IMPORT = re.compile(r"\s*(?:public\s+)?import\s+(\S+)")


def path(module):
    return module.replace(".", "/") + ".lean"


def imports(module):
    p = path(module)
    if not os.path.exists(p):
        return []
    with open(p, encoding="utf-8") as f:
        return [m.group(1) for line in f if (m := IMPORT.match(line))]


def closure(root):
    seen, stack = set(), [root]
    while stack:
        m = stack.pop()
        if m not in seen:
            seen.add(m)
            stack.extend(imports(m))
    return seen


def modules(lib):
    for d, _, files in os.walk(lib):
        for f in files:
            if f.endswith(".lean"):
                yield os.path.join(d, f)[: -len(".lean")].replace("/", ".")


failed = False
for lib in LIBS:
    if not os.path.exists(path(lib)):
        print(f"error: root {path(lib)} does not exist")
        failed = True
        continue
    reached = closure(lib)
    missing = sorted(set(modules(lib)) - reached)
    for m in missing:
        print(f"error: {path(m)} is not imported by {path(lib)} (directly or transitively)")
    for m in sorted(i for i in reached if i.split(".")[0] == lib and not os.path.exists(path(i))):
        print(f"error: {m} is imported but {path(m)} does not exist")
        missing.append(m)
    failed |= bool(missing)
    if not missing:
        print(f"{path(lib)}: all {len(set(modules(lib)))} modules of {lib}/ reachable")
sys.exit(1 if failed else 0)
