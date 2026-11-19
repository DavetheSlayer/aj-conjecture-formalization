# `lake comparator` run, 15 November 2026 (UTC)

**Result: accepted.** In `formalization/lean`, `lake comparator` with the committed `comparator.json` exited with
code 0 on commit `8dd21cfdd1030612b0c377b4e4b4f5f913690073`, which was the head of `main` at the time of the run:

```
Running nanoda kernel on solution
nanoda kernel accepts the solution
Running Lean default kernel on solution
Lean default kernel accepts the solution
Your solution is okay!
```

Both kernels named by the configuration accepted the solution: nanoda, as the external kernel, and Lean's own kernel
through `leanchecker`. `--paranoid` was not run.

One change to the environment was needed, none to the repository: `nanoda_bin` had to be on `PATH` (see
[Deviations](#deviations-from-the-readme)).

## What was run

| | |
|---|---|
| Repository | `8dd21cf` ("Merge pull request #2 from DavetheSlayer/formalization-whitehead"), no local changes; run in `formalization/lean` |
| Configuration | `comparator.json` as committed: challenge `AJChallenge`, solution `AJConjecture`, theorem `AJConjecture.not_ajSquareFreeConjecture`, no definition holes, permitted axioms `propext`, `Quot.sound`, `Classical.choice`, external kernel `nanoda` (`nanoda_bin`) |
| Toolchain | `leanprover/lean4:v4.36.0-rc2` (Lean commit `b35cb10cf2ced51a2fd1880cfdbf75c71ab7a35a`), Lake `5.0.0-src+b35cb10`, elan 4.2.4, bundled `nanoda_bin` 0.4.17 |
| Mathlib | `26573066084e6e2aa8526ea358bc43b66d96f970`, from `lake exe cache get` (9,111 files) |
| Sandbox | bubblewrap 0.11.2, unprivileged user namespaces |
| Machine | One node of the Harvard FASRC cluster: Intel Sapphire Rapids, 112 cores, 1 TB RAM, Rocky Linux 8.10 (kernel 4.18.0-553, glibc 2.28). The Slurm job held 64 cores and 512 GB. The stack limit was `unlimited` throughout (the cluster's default, inherited by the job). |
| Command | `lake comparator` at Lean's default parallelism, with the toolchain's `bin/` appended to `PATH`, and with `COMPARATOR_BWRAP` set to a wrapper that logs each sandbox call and runs `bwrap` with the same arguments |

Before the run, `.lake` held only the Mathlib cache and no project build products. So comparator compiled all 426
project modules inside its sandbox, as the README asks: the 425 files under `AJConjecture/` and the root module.

## Comparator output

Excerpts from the 1,744-line log:

```
Resolving dependencies
Building AJChallenge
warning: AJChallenge.lean:156:8: declaration uses `sorry`
Build completed successfully (18240 jobs).
Exporting #[Quot, Quot.mk, Quot.lift, Quot.ind, AJConjecture.not_ajSquareFreeConjecture, propext, Quot.sound,
  Classical.choice, Nat.add, …, outParam] from AJChallenge
Building AJConjecture
…
Build completed successfully (19090 jobs).
Exporting #[…same list…] from AJConjecture
Running nanoda kernel on solution
nanoda kernel accepts the solution
Running Lean default kernel on solution
Lean default kernel accepts the solution
Your solution is okay!
```

No module failed. There are two kinds of warning, both as the README describes: the challenge's `sorry`, and Lake's
advisory about importing `Mathlib` in files without `module`.

## Time and memory

| Step (inside the sandbox) | Start (UTC) | Duration |
|---|---|---|
| dependency resolution (`lake env`, with network), `lake build AJChallenge` | 00:38:27 | 11 s |
| `leanexport` of `AJChallenge` | 00:38:38 | 7 s |
| `lake build AJConjecture` (426 modules) | 00:38:45 | 7 min 55 s |
| `leanexport` of `AJConjecture` | 00:46:40 | 1 min 27 s |
| `nanoda_bin` on the export | 00:48:07 | 43 s |
| `leanchecker --silent --from-export` | 00:48:50 | 3 min 49 s |
| **Total** (`lake comparator` wall clock) | | **14 min 12 s** |

- **Memory.** The job's peak was 44.7 GB, early in the build, when up to 31 Lean processes ran at once. This is the
  Slurm cgroup's `memory.peak`, page cache included. Resident memory was sampled once a minute, so short peaks may be
  missing: about 7.3 GB for `leanexport`, 0.8 GB for `nanoda_bin` and 1.1 GB for `leanchecker`.
- **Slowest modules.** `AJConjecture.WTArcsPeripheral` took 408 s and set the length of the build. Next were
  `WTPeripheralAbstract` (34 s) and `QAlgNodeExtraBezoutData` (23 s); every other module took at most 20 s.
- **Stack.** The README warns that `leanchecker` might hit a segmentation fault under the default 8 MB stack. This run
  had an unlimited stack from the start, so it does not show whether 8 MB is enough.

## Further checks from the README

These ran outside the sandbox, after comparator, on the build products comparator had made.

- `lake build` had nothing left to build: all 19,090 jobs were replayed. Comparator's build of `AJConjecture` had
  already covered every module of the library, the 18 side modules included.
- `lake env lean PrintAxioms.lean` printed output identical to `PrintAxioms.expected.txt`. That covers the main theorem
  and 17 further results, each with `[propext, Classical.choice, Quot.sound]`.
- `python3 tools/make_challenge.py --check`, run with Python 3.12, printed "AJChallenge.lean matches the seven
  definition files".

## Deviations from the README

1. **`nanoda_bin` on `PATH`.** The first attempt ran the README's command unchanged and stopped at once with exit code 2:

   ```
   error: `nanoda` kernel `nanoda_bin` was not found
   ```

   Comparator looks up the commands in `external_kernels` on `PATH`. `nanoda_bin` ships in the toolchain's `bin/`, but
   elan 4.2.4 makes proxies only for `lean`, `lake`, `leanc`, `leanchecker`, `leanmake` and `leanpkg`. The accepted
   run appended the toolchain's `bin/` after elan's proxies:

   ```sh
   PATH="$PATH:$(lean --print-prefix)/bin" lake comparator
   ```

   Anyone who follows the README with a standard elan installation will hit the same error.
2. **`lake exe cache get` inside a container.** That command first compiles Mathlib's cache tool with the toolchain's
   bundled `clang`. `clang` loads `lib/libLLVM.so.23.1` and `lib/libclang-cpp.so.23.1`, which need `GLIBC_2.29` and
   `GLIBC_2.30`, and Rocky Linux 8 has glibc 2.28. So the download ran in an Ubuntu 24.04 image
   (`docker://buildpack-deps:noble-scm` under Singularity), writing into the same `.lake` directory. Everything else
   ran natively on the host: `lake`, `lean`, `leanexport`, `nanoda_bin`, `leanchecker` and `bwrap`.
3. **Node-local copy.** The repository, toolchain and `.lake` were copied to the node's local disk before the run,
   because importing Mathlib from the cluster's NFS scratch is slow. This does not change what is checked.
4. **Logging wrapper.** `COMPARATOR_BWRAP` pointed to a script that appends each sandbox command line to a log and then
   runs `/usr/bin/bwrap` with the same arguments.

   The logged calls are, in order:
   1. `lake env`, with network;
   2. `lake build AJChallenge`;
   3. `leanexport` of `AJChallenge`;
   4. `lake build AJConjecture`;
   5. `leanexport` of `AJConjecture`;
   6. `nanoda_bin` on the export;
   7. `leanchecker --silent --from-export`.

   Every call uses `--clearenv`, `--unshare-all` and `--new-session`. Only the first also has `--share-net`.

## Suggestions for the README

- In **Checking with the comparator**, add the `PATH` line above, or say that `nanoda_bin` must be on `PATH`.
- "It has **not** been run yet" and the table row "`lake comparator` | not run (requires Linux)" are out of date as of
  this run. This report does not edit the README.
- Resources: about 15 minutes and at most 45 GB on a 64-core node at default parallelism.
- The table row "Bundled `leanchecker` over all modules | started and cancelled; no result" is partly answered. Inside
  comparator, `leanchecker` accepted the export of the solution, which holds the main theorem and everything it
  depends on, in under 4 minutes. That export is not every module of the library: it holds only what the main
  theorem depends on, so the side results in the 18 modules that the root module does not import are not in it.

## Scope

Comparator established three facts about `AJConjecture.not_ajSquareFreeConjecture`:
- The solution proves the same statement as `AJChallenge`, and the constants the statement depends on are identical
  in both (the README describes this rule).
- The proof uses no axiom beyond `propext`, `Quot.sound` and `Classical.choice`.
- nanoda and Lean's kernel both accept it.

Comparator does not check that the seven definition files, and so the challenge, state the AJ conjecture faithfully.
The README names an independent reading of those files by a knot theorist as the most valuable remaining check.
`--paranoid` was not run, so `con-ron`, `con-leche`, `lean4lean` and `leanchecker-paranoid` have no result here.
