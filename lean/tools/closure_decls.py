#!/usr/bin/env python3
"""Compute (or check) the list `DECLS` of `tools/make_challenge.py`.

`DECLS` names, per source file of the library, the declarations that the challenge copies: every
declaration that the statements of `STATEMENTS` depend on. This script computes the list from the
built library:

* it collects every constant of the library reachable from the *types* of the statement theorems,
  through types, values (the proofs of theorems reached through a value included), constructors
  and recursor rules: the traversal of `tools/compare_reach.py`, i.e. of `lake comparator`;
* it maps each constant to the source declaration that creates it (auxiliary constants such as
  `f.match_1` or `f._proof_2` to `f`, derived instances to their `deriving` declaration);
* it adds the declarations of the touched files that a selected declaration names in its code
  (e.g. `rfl` lemmas in a `simp only [...]`, which leave no trace in the term), and repeats the
  traversal from the values of the selected declarations until nothing is added.

A private constant among them stops the script: such a declaration cannot be copied, and the
statement has to avoid it (see `Proofs/SolutionDefs.lean`).

Run from the folder `lean` after `lake build`, with the new theorems already in
`Solution.lean` and in `STATEMENTS`:

    python3 tools/closure_decls.py            # exit 1 if DECLS differs from the computed list
    python3 tools/closure_decls.py --write    # rewrite the DECLS block of make_challenge.py

then `python3 tools/make_challenge.py`, update `comparator.json`, `lake build Challenge` and
`python3 tools/compare_reach.py`.
"""
import importlib.util, pathlib, re, subprocess, sys, tempfile

LEAN = pathlib.Path(__file__).resolve().parent.parent
_tmp = tempfile.TemporaryDirectory()
OUT = pathlib.Path(_tmp.name)
spec = importlib.util.spec_from_file_location("g", LEAN / "tools" / "make_challenge.py")
g = importlib.util.module_from_spec(spec)
spec.loader.exec_module(g)
# the libraries of Proofs/ (every root listed in lakefile.toml); a library missing here is not
# searched, and its declarations would be missing from the challenge
PREFIXES = ("AJConjecture", "AJFamily", "AJHandoff", "AJTwist", "AJPaper", "SolutionDefs")

_roots = re.search(r'roots = \[(.*?)\]', (LEAN / "lakefile.toml").read_text(encoding="utf-8")).group(1)
assert sorted(re.findall(r'"([^"]+)"', _roots)) == sorted(PREFIXES), (
    "PREFIXES differs from the roots of the library in lakefile.toml", _roots)
stmt_modules = sorted({rel.removesuffix(".lean").replace("/", ".") for rel, _ in g.STATEMENTS})
IMPORTS = ["Solution", "SolutionDefs"] + [m for m in stmt_modules if m != "Solution"]

TEMPLATE = '''{imports}
open Lean

def kindOf : ConstantInfo → String
  | .defnInfo _ => "def" | .thmInfo _ => "thm" | .axiomInfo _ => "axiom" | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quot" | .inductInfo _ => "induct" | .ctorInfo _ => "ctor" | .recInfo _ => "rec"

def ours (env : Environment) (n : Name) : Option String :=
  match env.getModuleIdxFor? n with
  | some i =>
    let m := env.header.moduleNames[i.toNat]!
    if [{prefixes}].any (fun p => p.isPrefixOf m) then some m.toString else none
  | none => none

def reachAll (roots : List Name) (values : Bool) : CoreM (Array String) := do
  let env ← getEnv
  let mut seen : NameSet := {{}}
  let mut stack : Array Name := #[]
  for r in roots do
    let some ci := env.find? r | throwError "missing {{r}}"
    stack := stack ++ ci.type.getUsedConstants
    if values then
      stack := stack ++ ((ci.value? (allowOpaque := true)).map (·.getUsedConstants) |>.getD #[])
  let mut lines : Array String := #[]
  while 0 < stack.size do
    let n := stack.back!
    stack := stack.pop
    if seen.contains n then continue
    seen := seen.insert n
    let some ci := env.find? n | throwError "missing {{n}}"
    let mut deps := ci.type.getUsedConstants
    match ci.value? (allowOpaque := true) with
    | some v => deps := deps ++ v.getUsedConstants
    | none => pure ()
    match ci with
    | .inductInfo ii => deps := deps ++ ii.ctors.toArray ++ #[mkRecName n]
    | .ctorInfo c => deps := deps.push c.induct
    | .recInfo ri => for rule in ri.rules do deps := deps ++ rule.rhs.getUsedConstants
    | _ => pure ()
    match ours env n with
    | some m => lines := lines.push s!"{{n}}\\t{{m}}\\t{{kindOf ci}}"
    | none => pure ()
    stack := stack ++ deps
  return lines

#eval show CoreM Unit from do
  let ls ← reachAll [{roots}] {values}
  IO.FS.writeFile "{out}" (String.intercalate "\\n" ls.toList ++ "\\n")
'''

MODORDER = '''{imports}
open Lean
#eval show CoreM Unit from do
  let env ← getEnv
  let names := env.header.moduleNames.filter fun n => [{prefixes}].any (fun p => p.isPrefixOf n)
  IO.FS.writeFile "{out}" (String.intercalate "\\n" (names.map toString).toList)
'''

def lean(src_name: str, text: str) -> None:
    src = OUT / src_name
    src.write_text(text, encoding="utf-8")
    subprocess.run(["lake", "env", "lean", str(src)], cwd=LEAN, check=True)

def fmt(**kw) -> dict:
    return dict(imports="\n".join("import " + i for i in IMPORTS),
                prefixes=", ".join("`" + p for p in PREFIXES), **kw)

def explore(roots: list[str], values: bool, tag: str) -> dict[str, str]:
    out = OUT / f"reach_{tag}.txt"
    lean(f"Reach_{tag}.lean", TEMPLATE.format(**fmt(
        roots=", ".join("`AJConjecture." + r for r in roots),
        values="true" if values else "false", out=out.as_posix())))
    res = {}
    for ln in out.read_text(encoding="utf-8").splitlines():
        if ln:
            n, m, _k = ln.split("\t")
            res[n] = m
    return res

lean("ModOrder.lean", MODORDER.format(**fmt(out=(OUT / "modorder.txt").as_posix())))
order = (OUT / "modorder.txt").read_text(encoding="utf-8").split()

cache: dict[str, list] = {}
def decls_of(mod: str):
    if mod not in cache:
        cache[mod] = g.declarations(mod.replace(".", "/"))
    return cache[mod]

def owner(const: str, mod: str):
    assert not const.startswith("_private"), ("private constant reached", const, mod)
    n = const.removeprefix("AJConjecture.")
    ds = decls_of(mod)
    best = None
    for d in ds:
        if n == d.name or n.startswith(d.name + "."):
            if best is None or len(d.name) > len(best.name):
                best = d
    if best:
        return best
    if n.startswith("inst"):
        first = n.split(".")[0]
        cands = [d for d in ds if d.name in first and any(
            ln.lstrip().startswith("deriving") or " deriving " in ln for ln in d.lines)]
        if cands:
            return max(cands, key=lambda d: len(d.name))
    raise SystemExit(f"no owner for {const} in {mod}")

roots0 = [n for _, n in g.STATEMENTS]
union = explore(roots0, False, "0")
union = {n: m for n, m in union.items() if m != "Solution"}
selected: dict[tuple[str, str], bool] = {}
it = 0
while True:
    new = {}
    for n, m in union.items():
        new[(m, owner(n, m).name)] = True
    # textual dependencies: names used in the code of a selected declaration (e.g. rfl lemmas in
    # `simp only [...]`, which leave no trace in the proof term) that are declarations of a touched
    # source file
    changed = True
    while changed:
        changed = False
        cur = {**selected, **new}
        touched = {m for (m, _) in cur}
        names: dict[str, set[str]] = {}
        for m in touched:
            for d in decls_of(m):
                names.setdefault(d.name, set()).add(m)
        for (m, nm) in list(cur):
            d = [x for x in decls_of(m) if x.name == nm][0]
            toks = set(re.findall(r"[^\W\d][\w'.₀-₉ℚ]*", "\n".join(d.lines)))
            for t in toks:
                for cand in (t, t.split(".")[-1]):
                    for m2 in names.get(cand, ()):
                        if (m2, cand) not in selected and (m2, cand) not in new and cand != nm:
                            dd = [x for x in decls_of(m2) if x.name == cand][0]
                            if m2 == m or not dd.private:
                                new[(m2, cand)] = True
                                changed = True
    added = [k for k in new if k not in selected]
    selected.update(new)
    print(f"iteration {it}: {len(selected)} declarations, {len(added)} new", file=sys.stderr)
    if not added:
        break
    it += 1
    more = explore([nm for (_m, nm) in selected], True, str(it))
    union = {**union, **{n: m for n, m in more.items() if m != "Solution"}}

bymod: dict[str, list[str]] = {}
for (m, nm) in selected:
    bymod.setdefault(m, []).append(nm)
assert set(bymod) <= set(order), set(bymod) - set(order)
out = []
for m in order:
    if m in bymod:
        pos = {d.name: i for i, d in enumerate(decls_of(m))}
        names_m = sorted(bymod[m], key=lambda x: pos[x])
        allnames = [d.name for d in decls_of(m)]
        out.append((m.replace(".", "/"), "*" if names_m == allnames else names_m))
def render(decls) -> str:
    text = "DECLS: list[tuple[str, list[str] | str]] = [\n"
    for rel, names in decls:
        line = f"    ({rel!r}, {names!r}),"
        if len(line) > 100 and names != "*":
            parts, cur = [], f"    ({rel!r}, ["
            for i, n in enumerate(names):
                tok = repr(n) + (", " if i < len(names) - 1 else "]),")
                if len(cur) + len(tok) > 99:
                    parts.append(cur.rstrip())
                    cur = "        "
                cur += tok
            parts.append(cur)
            line = "\n".join(parts)
        text += line + "\n"
    return text + "]\n"


count = sum(len(decls_of(r.replace("/", "."))) if n == "*" else len(n) for r, n in out)
if "--write" in sys.argv:
    path = LEAN / "tools" / "make_challenge.py"
    s = path.read_text(encoding="utf-8")
    s2, k = re.subn(r"# @@DECLS@@.*?# @@END_DECLS@@", lambda m: (
        "# @@DECLS@@ (generated by the closure helper; source files in import order)\n"
        + render(out) + "# @@END_DECLS@@"), s, flags=re.S)
    assert k == 1, "DECLS markers not found"
    path.write_text(s2, encoding="utf-8")
    print(f"wrote DECLS: {len(out)} source files, {count} declarations")
    sys.exit(0)
have = [(r, n) for r, n in g.DECLS]
want = [(r, n) for r, n in out]
if have == want:
    print(f"DECLS is the computed closure: {len(out)} source files, {count} declarations")
    sys.exit(0)
hd, wd = dict(have), dict(want)
for r in sorted(set(hd) | set(wd)):
    if hd.get(r) != wd.get(r):
        print(f"{r}:\n  DECLS:    {hd.get(r)}\n  computed: {wd.get(r)}")
if [r for r, _ in have] != [r for r, _ in want]:
    print("the order of the source files differs")
print("run tools/closure_decls.py --write")
sys.exit(1)
