# `lake comparator` run, 21 November 2026 (UTC)

**Result: accepted.** In `lean/`, `lake comparator` with the committed `comparator.json` exited with code `0` on commit `da0776daa799ac8a267bbbbd365374802ec9df82` of `DavetheSlayer/aj-conjecture-formalization`.

```
Running nanoda kernel on solution
nanoda kernel accepts the solution
Running Lean default kernel on solution
Lean default kernel accepts the solution
Your solution is okay!
```

All 60 theorems of `lean/comparator.json` were judged, and both kernels accepted them: Lean's kernel and `nanoda`. `--paranoid` was not run.

## What was run

| | |
|---|---|
| Repository | commit `da0776daa799ac8a267bbbbd365374802ec9df82` ("Merge pull request #2 from DavetheSlayer/lean-sources"); working tree clean; tree of `lean/`: `2ad5a66b4d7e60752f810a6b8a0f8b6439a19569`. This is the tree described by [`local-checks-2026-11-20b.md`](local-checks-2026-11-20b.md). |
| Configuration | `lean/comparator.json` as committed (sha256 `830a94922fc22d3d5dd7576810859ead2da1808e9cf0154c57e77f1d4af4b14c`): challenge `Challenge`, solution `Solution`, 60 theorems, no definition holes, permitted axioms `propext`, `Quot.sound`, `Classical.choice`, external kernel `nanoda` (`nanoda_bin`) |
| Theorems | all 60 names of `theorem_names` |
| Toolchain | `leanprover/lean4:v4.36.0-rc2` (Lean commit `b35cb10cf2ced51a2fd1880cfdbf75c71ab7a35a`), Lake `5.0.0-src+b35cb10`, elan `4.2.4`, `nanoda_bin` `0.4.17` (bundled with the toolchain) |
| Mathlib | `26573066084e6e2aa8526ea358bc43b66d96f970`, pre-built, from `lake exe cache get` (9,111 files). See [Deviations](#deviations-from-comparatormd), item 1. |
| Sandbox | bubblewrap `0.11.2`, unprivileged user namespaces |
| Machine | One node of the Harvard FASRC cluster: Intel Xeon Platinum 8480CL (Sapphire Rapids), 112 cores, 1 TB RAM, Rocky Linux 8.10, kernel 4.18.0-553.155.1.el8_10, glibc 2.28. The Slurm job held 32 cores and 512 GB. Stack limit `unlimited`, before and during the run. |
| Command | `bash tools/run_comparator.sh <record folder>` in `lean/`, after `bash tools/run_comparator.sh --preflight` (which reported `preflight: ok`). The script appends the toolchain's `bin/` to `PATH` and runs `lake comparator` with no arguments. `COMPARATOR_BWRAP` named a wrapper that logs each sandbox call and runs `/usr/bin/bwrap` with the same arguments (`COMPARATOR.md`, point 8). |
| State of `.lake` before the run | only the Mathlib cache ("project build products: none before the run", in `environment.txt`) |

## Comparator output

Excerpts from the log:

```
Resolving dependencies
Building Challenge
warning: Challenge.lean:…: declaration uses `sorry`        (60 times)
Build completed successfully (18452 jobs).
Exporting #[Quot, Quot.mk, Quot.lift, Quot.ind, AJConjecture.not_ajSquareFreeConjecture, AJConjecture.release_theoremT,
  …, AJConjecture.zhengEstimates_holds, AJConjecture.geo_phys_holds, propext, Quot.sound, Classical.choice, …]
  from Challenge
Building Solution
Build completed successfully (20554 jobs).
Exporting #[…the same list…] from Solution
Running nanoda kernel on solution
nanoda kernel accepts the solution
Running Lean default kernel on solution
Lean default kernel accepts the solution
Your solution is okay!
```

- **Modules.** Comparator compiled 1,265 project modules inside its sandbox: the 107 of the challenge (`Challenge` and the 106 modules of `lean/Challenge/`), then 1,158 of the solution side. No module failed. That is 8 fewer than the 1,273 of `COMPARATOR.md` point 1: the 8 modules `Solution` does not import (see [Further checks](#further-checks)).
- **Warnings.** There were 60 `declaration uses sorry` warnings, all in `Challenge.lean`, one per statement. The only other warning is Lake's advisory about importing `Mathlib` in files without `module`.

Complete log: [`comparator-run-20261121T233419Z/comparator.log`](comparator-run-20261121T233419Z/comparator.log), with the other files `lean/tools/run_comparator.sh` wrote: `environment.txt`, `result.txt` and `time.txt`.

## Time and memory

Start times are those of the sandbox calls in the wrapper's log; each step ends where the next begins.

| Step (inside the sandbox) | Start (UTC) | Duration |
|---|---|---|
| dependency resolution, build of `Challenge` | 23:34:20 | 1 min 11 s |
| export of `Challenge` | 23:35:31 | 17 s |
| build of `Solution` | 23:35:48 | 8 min 45 s |
| export of `Solution` | 23:44:33 | 3 min 59 s |
| `nanoda_bin` on the export | 23:48:32 | 2 min 17 s |
| `leanchecker` on the export | 23:50:49 | 12 min 59 s |
| **Total** | 23:34:20 | **29 min 28 s** (ended 00:03:48 on 22 November) |

**Peak memory.** The job's peak was 54.8 GB, during the build of `Solution`. This is the Slurm cgroup's `memory.peak`, page cache included. Up to 71 Lean processes ran at once early in the build. `time.txt` gives 3.5 GB maximum resident size, but that is the largest single process GNU `time` saw, not the job's total. Resident memory was sampled once a minute, so short peaks may be missing:
- `leanexport` of the solution: up to 9.1 GB;
- `nanoda_bin`: up to 2.5 GB;
- `leanchecker`: up to 2.9 GB.

**Slowest modules.**

| Module | Time |
|---|---|
| `AJHandoff.TorusKnot.PairKIsoStrip` | 116 s |
| `AJFamily.Skein.TorusWordPerm` | 101 s |
| `AJFamily.Skein.TorusPhaseOneClimb` | 80 s |
| `AJHandoff.TorusKnot.PairKPeriGapRel` | 73 s |
| `AJFamily.Quantum.EbNodeCertificateIdentity` | 70 s |
| `AJFamily.Skein.TorusPhaseOneTop` | 68 s |

## Deviations from `COMPARATOR.md`

1. **Mathlib was copied, not downloaded again.** `lake exe cache get` was not run in this checkout. The Mathlib checkout and its build were copied from the folder of the 15 and 20 November runs on the same cluster, where `lake exe cache get` had fetched them. That download ran inside an Ubuntu 24.04 container because of the cluster's glibc (`COMPARATOR.md`, point 3). `lake-manifest.json` is byte-identical to the one used there. Before the run, `lake build --no-build Mathlib` reported "All targets up-to-date (18237 jobs)", and the preflight found the cache present.
2. **Node-local copy.** As `COMPARATOR.md` point 5 advises, the checkout, the toolchain and `.lake` were copied to the node's local disk and run there. In `environment.txt` as committed here, the 7 paths into that copy are shortened to `<node-local copy>`; nothing else in the file is changed.
3. **The record folder was outside the checkout.** The script got an explicit output folder outside the repository, so the record would not count as an untracked path in the "working tree" line. The files were copied into `reports/` afterwards.
4. **`python3` was Python 3.12.** The cluster's default `python3` is 3.6, and the scripts need 3.9 or later, so `python3` on `PATH` pointed to `/usr/bin/python3.12`.
5. **Sandbox call log** (`COMPARATOR.md`, point 8).
   - Comparator made the 7 calls listed there: `lake env`, the build of the challenge, its export, the build of the solution, its export, `nanoda_bin`, and `leanchecker --silent --from-export`.
   - All 7 use `--clearenv`, `--unshare-all` and `--new-session`. Only the first, `lake env`, has `--share-net`.
   - The wrapper added nothing.

Otherwise the steps of `COMPARATOR.md` were followed as written, and `--inadvisably-no-sandbox` was not used.

## Further checks

These are the optional checks of "After the run" in `COMPARATOR.md`, plus `check_imports.py` and `compare_reach.py`. They ran outside the sandbox, in the same job, on the build products comparator had made.

| Check (in `lean/`) | Result |
|---|---|
| `lake build` | exit 0. It compiled 8 modules that `Solution` does not import, so comparator had not built them: the five of the unknot sanity check (`AJConjecture.Unknot`, `UnknotAPolynomial`, `UnknotColoredJones`, `UnknotRecurrence`, `UnknotAJ`), `AJTwist.Classical.TwCPolysTwQ`, `AJTwist.Quantum.TwQPhysicalForcing` and `AJPaper.Finger.PpFUnique`. Everything else was replayed. So "nothing should be left to build" holds for the modules the 60 theorems need, but not for the whole default target. |
| `lake build Challenge` | `Build completed successfully (18452 jobs)`, nothing compiled |
| `lake env lean checks/PrintAxioms.lean` and the same for `PrintAxiomsHandoff`, `PrintAxiomsV1`, `PrintAxiomsFourFamilies`, `PrintAxiomsPaper` | each output identical to its `checks/*.expected.txt` |
| `python3 tools/make_challenge.py --check` | "107 challenge modules match the source declarations and statements; comparator.json names the 60 theorems" |
| `python3 tools/check_imports.py` | "1283 Lean files, 3239 imports of project modules: every import names an existing file with the same spelling; no case collisions" |
| `python3 tools/compare_reach.py` | "identical: 46912 constants reachable from the 60 theorems of comparator.json (605 of them from this development)"; "theorem types: identical (60 theorems)" |

All exit codes were 0, and the counts agree with [`local-checks-2026-11-20b.md`](local-checks-2026-11-20b.md). The per-module kernel replay `tools/replay_modules.sh` was not run.

## Scope

This run establishes three things about each of the 60 theorems named in `lean/comparator.json`, at commit `da0776d` (tree of `lean/` `2ad5a66`):
- the solution proves the statement of the challenge, from identical declarations;
- the proof uses no axiom beyond `propext`, `Quot.sound` and `Classical.choice`;
- Lean's kernel and `nanoda` both accept it.

It does not establish:
- that the statements of the challenge say what the paper says. That rests on reading `lean/Challenge.lean` and `lean/Challenge/`, and on identifying the closed braids with the knots of the paper, which is outside Lean (see "What a reader has to trust" in the [`README.md`](../README.md)).
- anything about later commits that change `lean/`.
- anything from the `--paranoid` checkers (`leanchecker-paranoid`, `lean4lean`, `con-leche`, `con-ron`), which were not run.
- whether the default 8 MB stack suffices, since the stack was unlimited throughout.
