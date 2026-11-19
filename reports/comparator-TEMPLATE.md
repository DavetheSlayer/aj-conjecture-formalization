# `lake comparator` run, <date> (UTC)

<!-- Copy this file to comparator-<date>.md and replace every <...>. Keep the headings. The files
     written by lean/tools/run_comparator.sh (environment.txt, comparator.log, result.txt,
     time.txt) contain most of what is asked for. State the outcome as it is, also if the run was
     rejected or could not start. -->

**Result: <accepted | rejected | could not start>.** In `lean/`, `lake comparator` with the committed `comparator.json` exited with code `<0|1|2>` on commit `<full hash>` of `DavetheSlayer/aj-conjecture-formalization`.

```
<the last lines of the log, e.g.
Running nanoda kernel on solution
nanoda kernel accepts the solution
Running Lean default kernel on solution
Lean default kernel accepts the solution
Your solution is okay!>
```

## What was run

| | |
|---|---|
| Repository | commit `<full hash>` (`<subject line>`); working tree <clean | changes: ...>; tree of `lean/`: `<git rev-parse HEAD:lean>` |
| Configuration | `lean/comparator.json` as committed (sha256 `<...>`): challenge `Challenge`, solution `Solution`, <49> theorems, no definition holes, permitted axioms `propext`, `Quot.sound`, `Classical.choice`, external kernel `nanoda` (`nanoda_bin`) |
| Theorems | <all 49 names of `theorem_names` | the subset ...> |
| Toolchain | `<lean-toolchain>` (Lean commit `<...>`), Lake `<...>`, elan `<...>`, `nanoda_bin` `<version>` |
| Mathlib | `<rev>`, from `lake exe cache get` (<n> files) |
| Sandbox | bubblewrap `<version>`, <unprivileged user namespaces | setuid> |
| Machine | <CPU, cores, memory, distribution, kernel, glibc>; <job limits>; stack limit `<...>` |
| Command | `<exact command line, with environment variables that matter (PATH addition, COMPARATOR_BWRAP)>` |
| State of `.lake` before the run | <only the Mathlib cache | project build products present> |

## Comparator output

<Excerpts of the log: the build of the challenge (number of jobs, the 49 `sorry` warnings), the
export, the build of the solution, the export, the kernels, the verdict. Warnings other than the
`sorry`s of the challenge and Lake's advisory about importing `Mathlib`, if any.>

Complete log: <path in this repository | stable reference>.

## Time and memory

| Step (inside the sandbox) | Start (UTC) | Duration |
|---|---|---|
| dependency resolution, build of `Challenge` | | |
| export of `Challenge` | | |
| build of `Solution` | | |
| export of `Solution` | | |
| `nanoda_bin` on the export | | |
| `leanchecker` on the export | | |
| **Total** | | |

Peak memory: <...>. Slowest modules: <...>.

## Deviations from `COMPARATOR.md`

<Anything done differently from the documented steps, and why; "none" if none.>

## Further checks

<Optional checks made after the run, outside the sandbox (see "After the run" in COMPARATOR.md),
labelled as such.>

## Scope

<What this run establishes: for each theorem judged, that the solution proves the statement of the
challenge from identical declarations, with no axiom beyond the permitted three, accepted by
Lean's kernel and nanoda. What it does not: that the statements say what the paper says; anything
about commits that changed `lean/` afterwards; `--paranoid` checkers unless run.>
