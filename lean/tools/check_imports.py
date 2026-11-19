#!/usr/bin/env python3
"""Check the file names of the project against its imports, as a case-sensitive file system reads
them.

The development machine (macOS) has a case-insensitive file system; the comparator runs on Linux.
An import whose module name differs from the file name only in case, or two paths that differ
only in case, would build on the first and fail on the second. This script checks, from the
directory listings (which preserve case):

* every `import` of a project module names a file that exists with exactly that spelling
  (libraries below `Proofs/`, `Solution`, `Challenge` and `Challenge/` at the root);
* no two paths of the project differ only in case, and every file name is ASCII;
* no file has Windows line endings.

    python3 tools/check_imports.py        # from the folder lean; exit 1 on a finding
"""
import collections
import os
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
EXTERNAL = ("Mathlib", "Lean", "Std", "Batteries", "Aesop", "Qq", "Init", "Plausible",
            "ProofWidgets", "ImportGraph", "LeanSearchClient", "Cli")


def main() -> int:
    files = set()
    for d, dirs, names in os.walk(ROOT):
        dirs[:] = [x for x in dirs if x not in (".lake", ".git", "__pycache__")]
        for n in names:
            files.add(os.path.relpath(os.path.join(d, n), ROOT))
    errors = []
    lower = collections.Counter(f.lower() for f in files)
    errors += [f"paths differ only in case: {f}" for f, c in lower.items() if c > 1]
    errors += [f"non-ASCII file name: {f}" for f in sorted(files) if not f.isascii()]
    imports = 0
    for f in sorted(files):
        if not f.endswith(".lean"):
            continue
        text = (ROOT / f).read_text(encoding="utf-8")
        if "\r" in text:
            errors.append(f"Windows line endings: {f}")
        for ln in text.splitlines():
            m = re.match(r"import\s+(\S+)", ln)
            if not m:
                continue
            mod = m.group(1)
            if mod.split(".")[0] in EXTERNAL:
                continue
            imports += 1
            rel = mod.replace(".", "/") + ".lean"
            if rel not in files and os.path.join("Proofs", rel) not in files:
                errors.append(f"{f}: import {mod}: no file with exactly this name")
    for e in errors:
        print(e)
    if errors:
        return 1
    lean = sum(1 for f in files if f.endswith(".lean"))
    print(f"{lean} Lean files, {imports} imports of project modules: every import names an "
          f"existing file with the same spelling; no case collisions")
    return 0


if __name__ == "__main__":
    sys.exit(main())
