# Running `lake comparator` on this repository

`lake comparator` (part of Lake since Lean 4.35; `lake comparator --help`) judges a solution against a challenge. For each theorem named in the configuration it establishes that the solution proves the same statement as the challenge from identical declarations, that the proof uses no axiom outside the permitted list, and that Lean's kernel and every additional kernel named in the configuration accept it. It builds and exports both sides inside a `bwrap` sandbox.

**State.** The comparator has not been run on this version. Everything below prepares that run. The local checks that were made instead are in [`reports/local-checks-2026-11-20b.md`](reports/local-checks-2026-11-20b.md); they do not replace it.

## What is judged

| | |
|---|---|
| Directory | `lean/` |
| Configuration | [`lean/comparator.json`](lean/comparator.json) (the default file name, so no `--config` is needed) |
| Challenge | module `Challenge`: `lean/Challenge.lean`, on top of the 106 modules `lean/Challenge/C_*.lean`; it imports only Mathlib and contains 60 statements with `sorry` |
| Solution | module `Solution`: `lean/Solution.lean`, which imports the libraries of `lean/Proofs/` |
| Theorems | the 60 names of `theorem_names`: the 47 of the untwisted release, the two of the four families (`AJConjecture.release_theoremFourFamilies`, `AJConjecture.release_fourFamilies_coloredJones`) and the eleven on the further claims of the paper ([`docs/FURTHER_CLAIMS.md`](docs/FURTHER_CLAIMS.md)) |
| Definition holes | none |
| Permitted axioms | `propext`, `Quot.sound`, `Classical.choice` |
| Kernels | Lean's kernel, and `nanoda` (`"external_kernels": {"nanoda": ["nanoda_bin"]}`) |
| Toolchain | `leanprover/lean4:v4.36.0-rc2` (`lean/lean-toolchain`) |
| Mathlib | `26573066084e6e2aa8526ea358bc43b66d96f970` (`lean/lakefile.toml`; transitive pins in `lean/lake-manifest.json`) |

## Requirements

- Linux with [`bubblewrap`](https://github.com/containers/bubblewrap) (`bwrap`), with unprivileged user namespaces enabled or `bwrap` installed setuid root.
- [elan](https://github.com/leanprover/elan); it installs the toolchain on first use.
- Network access for the two preparation commands only.
- Python 3.9 or later, for the two source checks of the preflight only.

## Steps

```sh
git clone https://github.com/DavetheSlayer/aj-conjecture-formalization.git
cd aj-conjecture-formalization
git checkout <commit to be tested>       # record it; the report must name it
cd lean
lake exe cache get                       # needs the network: downloads the pre-built Mathlib
bash tools/run_comparator.sh --preflight # prerequisites, source checks, environment
bash tools/run_comparator.sh             # runs `lake comparator`, writes ../reports/comparator-run-<time>/
echo "exit code: $?"                     # 0 accepted, 1 rejected, 2 could not start, 3 prerequisite missing
```

`tools/run_comparator.sh` appends the toolchain's `bin/` to `PATH` (see below), raises the stack limit if it can, runs `lake comparator` with the committed `comparator.json`, and writes `environment.txt` (commit, tree, toolchain, Lake, Mathlib pin, `bwrap`, kernel binary, system, limits, checksums of the inputs), `comparator.log` (the complete output), `result.txt` (times and exit code) and, where GNU `time` exists, `time.txt` (peak memory). Arguments after `--` are passed on, for example `bash tools/run_comparator.sh -- --paranoid`.

Without the script, the run is

```sh
cd lean
PATH="$PATH:$(lean --print-prefix)/bin" lake comparator 2>&1 | tee comparator.log
```

A run is **accepted** when the exit code is 0 and the log ends with

```
Running nanoda kernel on solution
nanoda kernel accepts the solution
Running Lean default kernel on solution
Lean default kernel accepts the solution
Your solution is okay!
```

## Points to observe

These come from the accepted run of 15 November 2026 on the single-braid theorem ([report](reports/comparator-2026-11-15.md)) and from the structure of the present version.

1. **Do not run `lake build` before the comparator** if the project is to be built inside the sandbox, as in the earlier run: start from a checkout whose `.lake` holds only the Mathlib cache. The comparator then compiles the 1,273 project modules itself (1,166 of the library and the solution, 107 of the challenge). The preflight reports whether `.lake/build` already exists; the report should say which was the case.
2. **`nanoda_bin` must be on `PATH`.** It ships in the toolchain's `bin/`, for which elan makes no proxy; without it the comparator stops at once with ``error: `nanoda` kernel `nanoda_bin` was not found`` (exit code 2). The script handles this; by hand use the `PATH` line above.
3. **`lake exe cache get` on an old distribution.** The command first compiles Mathlib's cache tool with the toolchain's bundled `clang`, which needs glibc 2.30 or later. On Rocky Linux 8 (glibc 2.28) the earlier run made the download inside an Ubuntu 24.04 container writing into the same `.lake` directory; everything else ran natively.
4. **Stack size.** Some proofs are kernel evaluations with deep recursion (`decide` on the isotopy certificates of `Proofs/AJFamily/Skein/TorusPhase*.lean` and of the satellite bridge). If a replay step ends with a segmentation fault, run with `ulimit -s unlimited`. The script tries to raise the limit and records the value in force.
5. **Local disk.** On a cluster, copy the checkout, the toolchain (`~/.elan`) and `.lake` to node-local disk first; importing Mathlib from a network file system is slow.
6. **Resources.** The earlier run (426 project modules, one theorem) took 14 minutes on 64 cores and peaked at 44.7 GB with up to 31 Lean processes at once. The present version has 1,273 project modules and 60 theorems, and its export and the two kernel passes cover much more; their times have not been measured. A build from scratch of the same modules outside the sandbox took about half an hour on a 10-core laptop with 32 GB (see the local records), with single modules of up to two minutes. Request memory in proportion to the number of cores Lake will use, and several hours of wall-clock time.
7. **`--paranoid`** also runs `leanchecker-paranoid`, `lean4lean`, `con-leche` and `con-ron`. On the single-braid version `con-ron` exhausted memory on two certificate declarations that Lean's kernel and `nanoda` check in seconds. Run the plain command first and report `--paranoid` separately if it is tried.
8. **Logging the sandbox calls (optional).** If the environment variable `COMPARATOR_BWRAP` names a wrapper script, the comparator calls it in place of `bwrap`; the earlier run used a wrapper that appends each command line to a log and then runs `/usr/bin/bwrap` with the same arguments. The seven calls were: `lake env` (the only one with network), `lake build` of the challenge, `leanexport` of the challenge, `lake build` of the solution, `leanexport` of the solution, `nanoda_bin` on the export, `leanchecker --silent --from-export`.
9. **The sandbox flag.** Do not pass `--inadvisably-no-sandbox`: a run without the sandbox is not a comparator verification.

## If the comparator rejects

Exit code 1 means a theorem was not accepted; the log names the theorem and the reason. The cases to tell apart:

- *a constant differs between challenge and solution.* The comparator requires every constant reachable from a statement to be identical on both sides, including the auxiliary proofs Lean generates inside definitions. `python3 tools/compare_reach.py` (after `lake build` and `lake build Challenge`) applies the same rule to the built modules and prints the constants that differ; it reported none on this version, so a difference found by the comparator is a difference between that script and the comparator and should be reported with the name of the constant.
- *an axiom outside the list*, or *a kernel rejecting a proof*: report the declaration.
- *the challenge or the solution does not build in the sandbox*: report the failing module and the error; `python3 tools/check_imports.py` rules out file-name case as the cause.

Keep the complete log in every case and file the report with the outcome as it is.

## After the run

Optional, outside the sandbox, on the build products the comparator made:

```sh
lake build                                   # nothing should be left to build
for f in PrintAxioms PrintAxiomsHandoff PrintAxiomsV1 PrintAxiomsFourFamilies PrintAxiomsPaper; do
  lake env lean checks/$f.lean | diff - checks/$f.expected.txt && echo "$f: as recorded"
done
python3 tools/make_challenge.py --check
```

Then write the report from [`reports/comparator-TEMPLATE.md`](reports/comparator-TEMPLATE.md), add it to `reports/` together with the files of `reports/comparator-run-<time>/` (or a stable reference to them if the log is too large), and update the status paragraph of the [`README.md`](README.md) and the index [`reports/README.md`](reports/README.md). A comparator run certifies the commit it was run on: the report names that commit, and later commits that touch `lean/` are not covered by it.

## What the comparator does not establish

It does not check that the statements of the challenge say what the paper says. That rests on reading the declarations of `lean/Challenge/` and `lean/Challenge.lean` (see "What a reader has to trust" in the [`README.md`](README.md)), and on the identification of the closed braids with the knots of the paper, which is outside Lean.
