# Verification records

Local builds and comparator runs are kept apart. A local record says what was built and checked on a development machine, outside the comparator's sandbox. A comparator record says that `lake comparator` was run on a named commit, with which configuration and kernels, and what it answered.

| Record | Kind | Commit | Scope | Outcome |
|---|---|---|---|---|
| [`comparator-2026-11-15.md`](comparator-2026-11-15.md) | **comparator** run (Lean kernel and `nanoda`) | audit repository `8dd21cf` (imported; report archived there at `418b3ed`) | one theorem, `AJConjecture.not_ajSquareFreeConjecture`, for one fixed seven-strand braid, in the layout and with the challenge of that commit | accepted |
| [`local-checks-2026-11-20.md`](local-checks-2026-11-20.md) | **local** build and checks | this repository, the commit that added the record (tree of `lean/` named in it) | all 1,031 library files, the solution and the challenge with their 49 theorems | no error; all checks pass |
| — | **comparator** run on the present version | — | the 49 theorems of `lean/comparator.json` | **not yet run**; see [`../COMPARATOR.md`](../COMPARATOR.md) |

The record of 15 November concerns an earlier proof of the single counterexample (a different braid of the same knot, in a library that was later replaced by the family proof). It is kept as the historical acceptance cited as reference [1] of the paper; it says nothing about the present 49 theorems.

To add a comparator record, copy [`comparator-TEMPLATE.md`](comparator-TEMPLATE.md) to `comparator-<date>.md`, fill it from the files that `lean/tools/run_comparator.sh` wrote, add those files (or a stable reference to them), and add a row above.
