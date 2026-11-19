#!/bin/bash
# Run `lake comparator` on the committed configuration and collect the record that
# reports/comparator-TEMPLATE.md asks for. See COMPARATOR.md.
#
#   bash tools/run_comparator.sh --preflight          check the prerequisites, run nothing
#   bash tools/run_comparator.sh [OUTDIR] [-- ARGS]   run; ARGS are passed to `lake comparator`
#
# The script works in the folder lean, wherever it is called from. OUTDIR defaults to
# ../reports/comparator-run-<UTC time>. Exit code: that of `lake comparator` (0 accepted,
# 1 rejected, 2 could not start), or 3 if a prerequisite is missing.
set -u
cd "$(dirname "$0")/.." || exit 3
MODE=run
OUT=""
ARGS=()
while [ $# -gt 0 ]; do
  case "$1" in
    --preflight) MODE=preflight ;;
    --) shift; ARGS=("$@"); break ;;
    *) OUT="$1" ;;
  esac
  shift
done

# `nanoda_bin` (named in comparator.json) ships in the toolchain's bin/, for which elan makes no
# proxy; append that folder to PATH, after elan's proxies.
if command -v lean >/dev/null 2>&1; then
  PREFIX="$(lean --print-prefix 2>/dev/null)"
  [ -n "${PREFIX:-}" ] && PATH="$PATH:$PREFIX/bin"
fi
export PATH

FAIL=0
row() { printf '%-28s %s\n' "$1" "$2"; }
need() {
  if command -v "$1" >/dev/null 2>&1; then row "$1" "$(command -v "$1")"
  else row "$1" "MISSING ($2)"; FAIL=1; fi
}

environment() {
  row "date (UTC)" "$(date -u +%Y-%m-%dT%H:%M:%SZ)"
  row "commit" "$(git rev-parse HEAD 2>/dev/null || echo 'not a git checkout')"
  row "tree of lean/" "$(git rev-parse --verify --quiet HEAD:lean || echo '?')"
  if [ -z "$(git status --porcelain 2>/dev/null)" ]; then row "working tree" "clean"
  else row "working tree" "NOT CLEAN: $(git status --porcelain | wc -l | tr -d ' ') changed or untracked paths"; fi
  row "lean-toolchain" "$(cat lean-toolchain)"
  row "lean" "$(lean --version 2>&1 | head -1)"
  row "lake" "$(lake --version 2>&1 | head -1)"
  row "elan" "$(elan --version 2>&1 | head -1)"
  row "mathlib (manifest)" "$(python3 -c "import json;print([p['rev'] for p in json.load(open('lake-manifest.json'))['packages'] if p['name']=='mathlib'][0])" 2>/dev/null || echo '?')"
  row "bwrap" "$(command -v bwrap >/dev/null 2>&1 && bwrap --version 2>&1 | head -1 || echo 'not found')"
  row "COMPARATOR_BWRAP" "${COMPARATOR_BWRAP:-(unset)}"
  row "nanoda_bin" "$(command -v nanoda_bin || echo 'not on PATH')"
  row "python3" "$(python3 --version 2>&1)"
  row "system" "$(uname -srm)"
  [ -r /etc/os-release ] && row "distribution" "$(. /etc/os-release; echo "${PRETTY_NAME:-?}")"
  row "glibc" "$(command -v ldd >/dev/null 2>&1 && ldd --version 2>&1 | head -1 || echo '?')"
  row "cpus" "$(nproc 2>/dev/null || sysctl -n hw.ncpu 2>/dev/null || echo '?')"
  row "memory" "$(command -v free >/dev/null 2>&1 && free -g | awk '/^Mem:/ {print $2 " GB"}' || echo '?')"
  row "stack limit" "$(ulimit -s)"
  row "project build products" "$([ -d .lake/build ] && echo 'present before the run (.lake/build exists)' || echo 'none before the run')"
  row "Mathlib cache" "$([ -f .lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean ] && echo present || echo 'MISSING: run lake exe cache get')"
  for f in comparator.json lake-manifest.json Challenge.lean Solution.lean; do
    row "sha256 $f" "$( (sha256sum "$f" 2>/dev/null || shasum -a 256 "$f") | cut -d' ' -f1)"
  done
}

preflight() {
  echo "== prerequisites"
  need lean "install elan; the toolchain is named in lean-toolchain"
  need lake "install elan"
  need bwrap "bubblewrap is required by lake comparator; Linux only"
  need nanoda_bin "it is in the toolchain's bin/: PATH=\"\$PATH:\$(lean --print-prefix)/bin\""
  need leanchecker "part of the toolchain"
  need python3 "only for the two source checks below"
  if command -v bwrap >/dev/null 2>&1; then
    if bwrap --unshare-all --ro-bind / / true 2>/dev/null; then row "sandbox test" "ok"
    else row "sandbox test" "FAILED: bwrap cannot create a sandbox (unprivileged user namespaces?)"; FAIL=1; fi
  fi
  [ -f lake-manifest.json ] || { row "lake-manifest.json" "MISSING"; FAIL=1; }
  [ -f .lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean ] ||
    { row "Mathlib cache" "MISSING: run lake exe cache get (needs the network)"; FAIL=1; }
  WANT="$(sed 's/.*://' lean-toolchain)"
  lean --version 2>/dev/null | grep -q "version ${WANT#v}" ||
    { row "toolchain" "lean --version does not report ${WANT#v}"; FAIL=1; }
  if command -v python3 >/dev/null 2>&1; then
    echo "== sources"
    python3 tools/check_imports.py || FAIL=1
    python3 tools/make_challenge.py --check || FAIL=1
  fi
  [ "$(ulimit -s)" = "unlimited" ] || echo "note: stack limit is $(ulimit -s) kB; the run raises it to the hard limit if it can"
  [ -d .lake/build ] && echo "note: .lake/build exists; for a build inside the sandbox start from a checkout with only the Mathlib cache"
  echo "== environment"
  environment
}

if [ "$MODE" = preflight ]; then
  preflight
  [ "$FAIL" = 0 ] && echo "preflight: ok" || echo "preflight: NOT ok"
  [ "$FAIL" = 0 ] && exit 0 || exit 3
fi

[ -n "$OUT" ] || OUT="../reports/comparator-run-$(date -u +%Y%m%dT%H%M%SZ)"
mkdir -p "$OUT" || exit 3
preflight > "$OUT/environment.txt" 2>&1
if [ "$FAIL" != 0 ]; then
  cat "$OUT/environment.txt"
  echo "a prerequisite is missing; nothing was run (record: $OUT/environment.txt)"
  exit 3
fi
ulimit -s unlimited 2>/dev/null || ulimit -s "$(ulimit -Hs)" 2>/dev/null || true
echo "stack limit during the run: $(ulimit -s)" >> "$OUT/environment.txt"
echo "command: lake comparator ${ARGS[*]:-}" | tee -a "$OUT/environment.txt"
START="$(date -u +%Y-%m-%dT%H:%M:%SZ)"
if /usr/bin/time -v true >/dev/null 2>&1; then
  /usr/bin/time -v -o "$OUT/time.txt" lake comparator ${ARGS[@]+"${ARGS[@]}"} 2>&1 | tee "$OUT/comparator.log"
else
  lake comparator ${ARGS[@]+"${ARGS[@]}"} 2>&1 | tee "$OUT/comparator.log"
fi
RC=${PIPESTATUS[0]}
{
  echo "start (UTC): $START"
  echo "end (UTC):   $(date -u +%Y-%m-%dT%H:%M:%SZ)"
  echo "exit code:   $RC   (0 accepted, 1 rejected, 2 could not start)"
  echo "last lines of the log:"
  tail -n 8 "$OUT/comparator.log"
} > "$OUT/result.txt"
cat "$OUT/result.txt"
echo "record written to $OUT (environment.txt, comparator.log, result.txt$([ -f "$OUT/time.txt" ] && echo ', time.txt'))"
exit "$RC"
