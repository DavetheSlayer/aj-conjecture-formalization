#!/bin/bash
# Elaborate the challenge, the solution and the files of Proofs/AJPaper/ again with the option
# `autoImplicit` switched off.
#
# The project does not set `autoImplicit false`, so an unknown identifier in a statement would be
# bound silently as a new variable instead of being reported. This script shows that no statement
# of the challenge or of the solution depends on that: every file must elaborate without error
# when the option is off. Run from the folder lean after `lake build` and `lake build Challenge`:
#
#     bash tools/check_autoimplicit.sh [JOBS]
#
# Exit code 0 iff no file reports an error.
set -u
cd "$(dirname "$0")/.."
JOBS="${1:-4}"
OUT="$(mktemp -d)"
{ ls Challenge/C_*.lean Challenge.lean Solution.lean Proofs/SolutionDefs.lean
  find Proofs/AJPaper -name '*.lean'; } > "$OUT/files.txt"
xargs -P "$JOBS" -n 1 sh -c 'lake env lean -D autoImplicit=false "$1" 2>&1 | grep -c "error" | sed "s|^|$1 |"' _ \
  < "$OUT/files.txt" > "$OUT/results.txt"
echo "files: $(wc -l < "$OUT/results.txt" | tr -d ' '); with errors: $(awk '$2 != 0' "$OUT/results.txt" | wc -l | tr -d ' ')"
awk '$2 != 0' "$OUT/results.txt" | head
! awk '$2 != 0 {bad=1} END {exit !bad}' "$OUT/results.txt"
