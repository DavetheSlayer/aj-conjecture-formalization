#!/bin/bash
# Kernel replay of every module of the development, one module per process.
#
# Run from the folder lean after `lake build`:   bash tools/replay_modules.sh [JOBS]
#
# `leanchecker M` replays the declarations of every module whose name starts with M, all in one
# process; on the roots (AJConjecture, AJFamily, AJHandoff, AJTwist in Proofs/, and Solution) that
# is the whole library, and on macOS the process runs out of resources and dies with a segmentation
# fault (exit 139, printed by no one). So every non-root module is replayed by its own `leanchecker`
# process, and the five roots by tools/ReplayExact.lean, which applies leanchecker's per-module
# routine to exactly the named module. Prints one "<module> <exit code>" line per module and a summary; exit code 0 iff
# every replay succeeded.
set -u
cd "$(dirname "$0")/.."
JOBS="${1:-4}"
OUT="$(mktemp -d)"
{ ls Solution.lean
  ( cd Proofs && ls AJConjecture.lean AJFamily.lean AJHandoff.lean AJTwist.lean SolutionDefs.lean &&
    find AJConjecture AJFamily AJHandoff AJTwist -name '*.lean' ); } |
  sed 's/\.lean$//; s|/|.|g' | sort -u > "$OUT/modules.txt"
grep -vxE 'AJConjecture|AJFamily|AJHandoff|AJTwist|Solution' "$OUT/modules.txt" > "$OUT/leaf.txt"
lake env bash -c "xargs -P $JOBS -I{} sh -c 'leanchecker {} >/dev/null 2>&1; echo \"{} \$?\"' < '$OUT/leaf.txt'" \
  > "$OUT/results.txt"
for m in AJConjecture AJFamily AJHandoff AJTwist Solution; do
  lake env lean --run tools/ReplayExact.lean "$m" >/dev/null 2>&1
  echo "$m $?" >> "$OUT/results.txt"
done
cat "$OUT/results.txt"
echo "modules: $(wc -l < "$OUT/modules.txt"), results: $(wc -l < "$OUT/results.txt")"
awk '{print "exit " $2}' "$OUT/results.txt" | sort | uniq -c
! awk '$2 != 0 {bad=1} END {exit !bad}' "$OUT/results.txt"
