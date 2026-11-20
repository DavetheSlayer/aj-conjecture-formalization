# Local build and checks, 20 November 2026, second record: the version with the further claims

**Kind of record: local.** Everything below was run on a development machine, outside the comparator's sandbox. It is not a `lake comparator` run and does not replace one ([`../COMPARATOR.md`](../COMPARATOR.md)).

**Result.** The project builds without errors, and every check listed below passes.

## What was checked

| | |
|---|---|
| Tree | the folder `lean/` of the commit that adds this record: git tree `2ad5a66b4d7e60752f810a6b8a0f8b6439a19569` (compare with `git rev-parse <commit>:lean`) |
| Change since the first record | [`local-checks-2026-11-20.md`](local-checks-2026-11-20.md) describes commit `25449d1` (tree `99977091c33aae01d692f4ff204fd8f65953f9b3`). Added since: the library `lean/Proofs/AJPaper/` (133 files and its root file), three theorems in `Solution.lean`, eleven statements in the challenge (five new challenge modules for `AJPaper`, four for the transfer operator of `AJTwist`), `checks/PrintAxiomsPaper.*`, `checks/PAPER_THEOREMS.txt`, `tools/check_autoimplicit.sh`. The libraries `AJConjecture`, `AJFamily`, `AJHandoff`, `AJTwist` and `SolutionDefs.lean` are unchanged, and so are the 49 earlier statements. |
| Scope | all 1,165 files of `lean/Proofs/`, `lean/Solution.lean` (60 theorems), `lean/Challenge.lean` with the 106 modules of `lean/Challenge/` |
| Toolchain | `leanprover/lean4:v4.36.0-rc2` (Lean commit `b35cb10cf2ced51a2fd1880cfdbf75c71ab7a35a`), Lake `5.0.0-src+b35cb10`, elan 4.2.4 |
| Dependencies | Mathlib `26573066084e6e2aa8526ea358bc43b66d96f970` and the transitive pins of `lean/lake-manifest.json`, pre-built |
| Machine | Apple M2 Pro (10 cores, 32 GB), macOS 27.2.1, arm64; Python 3.9.6 |
| State before the build | the build products of the from-scratch build of the first record; so the four earlier libraries were not rebuilt, and the 134 modules of `AJPaper`, `Solution` and the challenge were built new |

## Build

| Command (in `lean/`) | Result |
|---|---|
| `lake build` | `Build completed successfully (20571 jobs)`; the 134 modules of `AJPaper` (3 minutes) and `Solution` compiled; no error; no warning other than Lake's advisory about importing `Mathlib` as a whole |
| `lake build Challenge` | `Build completed successfully (18452 jobs)`; 60 warnings `declaration uses sorry`, all in `Challenge.lean` (the 60 statements), no other warning |

## Checks on the built project

| Check (in `lean/`) | Result |
|---|---|
| `lake env lean checks/PrintAxioms.lean`, `PrintAxiomsHandoff.lean`, `PrintAxiomsV1.lean`, `PrintAxiomsFourFamilies.lean`, `PrintAxiomsPaper.lean` | each output equals its `*.expected.txt` (19, 73, 76, 38 and 47 reports). All 253 reports list only `propext`, `Classical.choice`, `Quot.sound` or a subset; none contains `sorryAx`. The 60 theorems of `comparator.json` are among them. |
| `python3 tools/make_challenge.py --check` | `107 challenge modules match the source declarations and statements; comparator.json names the 60 theorems` |
| `python3 tools/closure_decls.py` | `DECLS is the computed closure: 106 source files, 414 declarations` |
| `python3 tools/compare_reach.py` | `identical: 46912 constants reachable from the 60 theorems of comparator.json (605 of them from this development)`; `theorem types: identical (60 theorems)` |
| `python3 tools/check_imports.py` | `1283 Lean files, 3239 imports of project modules: every import names an existing file with the same spelling; no case collisions` |
| `bash tools/check_autoimplicit.sh` | `files: 242; with errors: 0`: the 106 challenge modules, `Challenge.lean`, `Solution.lean`, `SolutionDefs.lean` and the 133 files of `Proofs/AJPaper/` elaborate with the option `autoImplicit` switched off, so no statement of the challenge or the solution depends on an auto-bound variable |
| `lake env lean tools/AuditReach.lean` | `CORE` and `MARK` reach only `MarkovEquiv` among the watched premises; `BRIDGE`, `FOUR_FAMILIES` and `PAPER` (Sections 7.6, 8.4, 8.5, 9) reach none; `PHYS` (`geo_phys_holds`, `zhengEstimates_holds`) reaches only the predicates of Zheng's estimates, which are now proved; the control groups reach theirs |
| `lake env lean tools/WhdWords.lean`, `tools/TwWords.lean` | outputs equal `scripts/whitehead_double/lean_words.txt` and `scripts/four_families/lean_words.txt` |
| text search of `Proofs/`, `Solution.lean`, `Challenge/`, `Challenge.lean` | `sorry` occurs as code only in the 60 statements of `Challenge.lean`; no `admit`, no `native_decide`, no `axiom` declaration |

## Kernel replay

The 133 modules of `Proofs/AJPaper/` were replayed by `leanchecker`, one process per module, and the root module `AJPaper` and the present `Solution` by `tools/ReplayExact.lean` (19 November 2026, 19:29 to 19:36 UTC, 6 processes): 135 results, all with exit code 0. The modules of the four earlier libraries are those of the build of the first record, whose replay (all 1,032 modules accepted) is in its addendum; they were not rebuilt.

## Audits of the new statements

Two independent audits on 20 November 2026 compared the statements of `Proofs/AJPaper/` with the paper and the cited sources (Tran, arXiv:1111.5065; Sikora, arXiv:0807.0943v2; Zheng, arXiv:math/0508138v4), each without knowledge of how the statements were designed. Both found them faithful; the deviations are strengthenings or stated interpretations and are listed in [`../docs/FURTHER_CLAIMS.md`](../docs/FURTHER_CLAIMS.md), Section 2. Checked by computation in the audits: `twP k` against the paper's `B_k`, `C_k` for `|k| ≤ 6`; the positive-clasp polynomials against the paper's `M ↦ M⁻¹` form; the definitions of Section 9 on toy polynomials; the twist-knot braids for `-4 ≤ ℓ ≤ 4` (components, Alexander and Jones polynomials, SnapPy identification, representations on the expected curves); the diagonal quotient of Theorem B.1 (4) numerically for `a = 3, 5`. The audits read statements and definitions, not proofs.

## Not done

- `lake comparator` (needs Linux with `bubblewrap`), and therefore the export, `nanoda` and `leanchecker` on the export;
- the checkers of `--paranoid`;
- a build on Linux;
- a second from-scratch build of the whole tree: the earlier libraries are those of the from-scratch build of the first record.
