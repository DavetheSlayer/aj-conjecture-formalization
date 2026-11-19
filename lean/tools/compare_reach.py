#!/usr/bin/env python3
"""Apply the comparator's identity rule to the compiled challenge and solution.

`lake comparator` requires every constant reachable from the statements of the named theorems to
be identical in the challenge (`Challenge`) and the solution (`Solution`), including the auxiliary
proofs Lean generates inside definitions. This script checks that rule directly on the built
modules, without the comparator's sandbox, for the theorems of `comparator.json`:

* for each side it collects every constant reachable from the *types* of the theorems (through
  types, values, constructors and recursor rules; the theorems' own proofs are not followed) and
  writes each name with a structural hash of its type and value; the two lists must be equal;
* it compares the types (and universe parameters) of the theorems themselves on the two sides.

Run from the folder `lean` after `lake build Proofs Solution Challenge`:

    python3 tools/compare_reach.py

It does not replace `lake comparator` (sandboxed build, export, independent kernels).
"""
import json
import pathlib
import subprocess
import sys
import tempfile

ROOT = pathlib.Path(__file__).resolve().parent.parent

REACH = '''import {module}
open Lean

def reachDump (roots : List Name) (out : System.FilePath) : CoreM Unit := do
  let env ← getEnv
  let mut seen : NameSet := {{}}
  let mut stack : Array Name := #[]
  for r in roots do
    let some ci := env.find? r | throwError "missing {{r}}"
    stack := stack ++ ci.type.getUsedConstants
  let mut lines : Array String := #[]
  while 0 < stack.size do
    let n := stack.back!
    stack := stack.pop
    if seen.contains n then continue
    seen := seen.insert n
    let some ci := env.find? n | throwError "missing {{n}}"
    let mut h := hash ci.type
    let mut deps := ci.type.getUsedConstants
    match ci.value? (allowOpaque := true) with
    | some v => h := mixHash h (hash v); deps := deps ++ v.getUsedConstants
    | none => pure ()
    match ci with
    | .inductInfo ii => deps := deps ++ ii.ctors.toArray ++ #[mkRecName n]
    | .ctorInfo c => deps := deps.push c.induct
    | .recInfo ri =>
      for rule in ri.rules do
        h := mixHash h (hash rule.rhs); deps := deps ++ rule.rhs.getUsedConstants
    | _ => pure ()
    lines := lines.push s!"{{n}} {{h}}"
    stack := stack ++ deps
  IO.FS.writeFile out (String.intercalate "\\n" (lines.qsort (· < ·)).toList ++ "\\n")

#eval reachDump [{roots}] "{out}"
'''

TYPES = '''import {module}
open Lean
#eval show CoreM Unit from do
  let env ← getEnv
  let mut out := ""
  for r in [{roots}] do
    let some ci := env.find? r | throwError "missing {{r}}"
    out := out ++ s!"{{r}} {{hash ci.type}} {{ci.levelParams}}\\n"
  IO.FS.writeFile "{out}" out
'''


def dump(template: str, kind: str, module: str, roots: list[str], tmp: pathlib.Path) -> list[str]:
    out = tmp / f"{kind}_{module}.txt"
    src = tmp / f"{kind.capitalize()}_{module}.lean"
    src.write_text(template.format(module=module, roots=", ".join("`" + r for r in roots),
                                   out=out.as_posix()), encoding="utf-8")
    subprocess.run(["lake", "env", "lean", str(src)], cwd=ROOT, check=True)
    return out.read_text(encoding="utf-8").splitlines()


def main() -> int:
    cfg = json.loads((ROOT / "comparator.json").read_text(encoding="utf-8"))
    roots = cfg["theorem_names"]
    with tempfile.TemporaryDirectory() as d:
        tmp = pathlib.Path(d)
        a = dump(REACH, "reach", cfg["challenge_module"], roots, tmp)
        b = dump(REACH, "reach", cfg["solution_module"], roots, tmp)
        ta = dump(TYPES, "types", cfg["challenge_module"], roots, tmp)
        tb = dump(TYPES, "types", cfg["solution_module"], roots, tmp)
    rc = 0
    if a != b:
        sa, sb = set(a), set(b)
        for line in sorted((sa ^ sb))[:40]:
            print(("challenge only: " if line in sa else "solution only:  ") + line)
        print(f"DIFFERENT: {len(sa - sb)} challenge-only and {len(sb - sa)} solution-only entries")
        rc = 1
    else:
        own = sum(1 for ln in a if ln.startswith("AJConjecture."))
        print(f"identical: {len(a)} constants reachable from the {len(roots)} theorems of "
              f"comparator.json ({own} of them from this development)")
    if ta != tb:
        for x, y in zip(ta, tb):
            if x != y:
                print(f"challenge: {x}\nsolution:  {y}")
        print("theorem types: DIFFERENT")
        rc = 1
    else:
        print(f"theorem types: identical ({len(ta)} theorems)")
        print("\n".join(ta))
    return rc


if __name__ == "__main__":
    sys.exit(main())
