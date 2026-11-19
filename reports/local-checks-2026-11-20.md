# Local build and checks, 20 November 2026

**Kind of record: local.** Everything below was run on a development machine, outside the comparator's sandbox. It is not a `lake comparator` run and does not replace one ([`../COMPARATOR.md`](../COMPARATOR.md)).

**Result.** The project builds from scratch without errors, and every check listed below passes.

## What was checked

| | |
|---|---|
| Tree | the folder `lean/` of the commit that adds this record: git tree `99977091c33aae01d692f4ff204fd8f65953f9b3` (compare with `git rev-parse <commit>:lean`; a later commit with the same tree has the same Lean project) |
| Scope | all 1,031 files of `lean/Proofs/`, `lean/Solution.lean` (49 theorems), `lean/Challenge.lean` with the 97 modules of `lean/Challenge/` |
| Toolchain | `leanprover/lean4:v4.36.0-rc2` (Lean commit `b35cb10cf2ced51a2fd1880cfdbf75c71ab7a35a`), Lake `5.0.0-src+b35cb10`, elan 4.2.4 |
| Dependencies | Mathlib `26573066084e6e2aa8526ea358bc43b66d96f970` and the transitive pins of `lean/lake-manifest.json`, pre-built (`lake exe cache get`) |
| Machine | Apple M2 Pro (10 cores, 32 GB), macOS 27.2.1, arm64; Python 3.9.6 |
| State before the build | `lean/.lake` held only `packages/` (Mathlib and its dependencies, pre-built, copied from another checkout); no build product of this project |

## Build

| Command (in `lean/`) | Result |
|---|---|
| `lake build` | `Build completed successfully (20303 jobs)`; the 1,031 modules of `Proofs/` and `Solution` were compiled; no error; no warning other than Lake's advisory about importing `Mathlib` as a whole |
| `lake build Challenge` | `Build completed successfully (18434 jobs)`; 98 modules compiled; 49 warnings `declaration uses sorry`, all in `Challenge.lean` (the 49 statements), no other warning |

Both together took 22 minutes of wall-clock time (19 November 2026, 15:52 to 16:14 UTC). The slowest modules were `AJHandoff.TorusKnot.PairKIsoStrip` (122 s), `AJFamily.Skein.TorusPhaseOneClimb` (102 s), `AJFamily.Skein.TorusPhaseOneTop` (81 s) and `AJTwist.Classical.TwCGapForward` (67 s).

## Checks on the built project

| Check (in `lean/`) | Result |
|---|---|
| `lake env lean checks/PrintAxioms.lean`, `PrintAxiomsHandoff.lean`, `PrintAxiomsV1.lean`, `PrintAxiomsFourFamilies.lean` | each output equals its `*.expected.txt` (19, 73, 76 and 38 reports). Of the 206 reports, 205 are `[propext, Classical.choice, Quot.sound]` and one is a subset; none contains `sorryAx` or another axiom. The 49 theorems of `comparator.json` are among them. |
| `python3 tools/make_challenge.py --check` | `98 challenge modules match the source declarations and statements; comparator.json names the 49 theorems` |
| `python3 tools/closure_decls.py` | `DECLS is the computed closure: 97 source files, 376 declarations` (the declarations copied into the challenge are exactly those the 49 statements depend on) |
| `python3 tools/compare_reach.py` | `identical: 46846 constants reachable from the 49 theorems of comparator.json (563 of them from this development)`; `theorem types: identical (49 theorems)`. This is the comparator's identity rule applied to the compiled `Challenge` and `Solution`, without its sandbox, export and kernels. |
| `python3 tools/check_imports.py` | `1139 Lean files, 2907 imports of project modules: every import names an existing file with the same spelling; no case collisions` (the build machine's file system is case-insensitive, the comparator's is not) |
| `lake env lean tools/AuditReach.lean` | groups `CORE` and `MARK` reach only `MarkovEquiv` among the watched premises; `BRIDGE` and `FOUR_FAMILIES` reach none (no estimate of Zheng, no JSJ input, no triangulation, no `sorryAx`); the control groups reach theirs |
| `lake env lean tools/WhdWords.lean`, `tools/TwWords.lean` | outputs equal `scripts/whitehead_double/lean_words.txt` and `scripts/four_families/lean_words.txt`, the inputs of the checks outside Lean |
| text search of `Proofs/`, `Solution.lean`, `Challenge/`, `Challenge.lean` | `sorry` occurs as code only in the 49 statements of `Challenge.lean`; no `admit`, no `native_decide`, no `axiom` declaration |
| `bash tools/run_comparator.sh --preflight` | the source checks pass; it stops, as it must on this machine, at `bwrap MISSING` |

## Kernel replay

`tools/replay_modules.sh` replays every module with `leanchecker`, one process per module. On a checkout of the audit repository whose `Proofs/` and `Solution.lean` are byte-identical to those of this tree, all modules were accepted: the 807 earlier modules of `Proofs/` on 18 November 2026, and the 224 modules of `AJTwist` and `Solution` on 20 November 2026. The replay on the build described above was started when this record was written; its result is in the addendum below once it is there.

## Checks outside Lean

The scripts of `scripts/four_families/` were run on 20 November 2026 on the braid words printed by `tools/TwWords.lean` (identical to the output on this build): Alexander polynomials of 56 braids as expected, colour-2 coloured Jones values equal to the manuscript's formula in 36 of 36 instances, `twistPoly` and `twistPolyNeg` equal to the manuscript's `B_k` and `C_k` for `k ≤ 6`. The outputs are stored next to the scripts. The scripts of `scripts/whitehead_double/`, `scripts/mark/` and `scripts/zheng/` were not rerun for this record; their recorded outputs are those of 17 and 18 November.

## Not done

- `lake comparator` (needs Linux with `bubblewrap`), and therefore the export, `nanoda` and `leanchecker` on the export;
- the checkers of `--paranoid`;
- a build on Linux.

## Relation to the audit repository

`lean/Proofs/`, `lean/Solution.lean`, `lean/Challenge.lean`, `lean/Challenge/`, `lean/comparator.json`, `lean/lake-manifest.json` and `lean/lean-toolchain` are byte-identical to the working tree of the audit repository in which the four-family library was added on 19–20 November. The differences in `lean/` are path names in comments of `lakefile.toml`, of the four files `checks/PrintAxioms*.lean` and of six tools (`AuditReach.lean`, `TwWords.lean`, `V1Appendix.lean`, `closure_decls.py`, `compare_reach.py`, `replay_modules.sh`), and the two new tools `check_imports.py` and `run_comparator.sh`.
