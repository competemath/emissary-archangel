#!/bin/bash
# Build lean4export for one toolchain: the exporter must match the toolchain
# whose .oleans it reads (Gate 2 replays its output). One build per toolchain —
# scripts/setup-source.mjs keeps them under infra/lean4export/<toolchain>/.
#   scripts/build-lean4export.sh [toolchain] [dest]
#     default leanprover/lean4:v4.29.1, infra/lean4export
set -euo pipefail
TC=${1:-leanprover/lean4:v4.29.1}
ROOT=$(cd "$(dirname "$0")/.." && pwd)
DEST=${2:-$ROOT/infra/lean4export}
[ -d "$DEST/.git" ] || git clone -q https://github.com/leanprover/lean4export "$DEST"
cd "$DEST"
git fetch -q --all 2>/dev/null || true
git checkout -q -- lean-toolchain 2>/dev/null || true   # a previous run overwrote it below
mm=$(echo "$TC" | sed -E 's/.*v([0-9]+\.[0-9]+).*/\1/'); major=${mm%%.*}; minor=${mm##*.}
# The last commit pinning this minor; failing that the nearest lower minor that
# has one. The exporter is built against $TC either way — what matters is that
# it compiles, and lean4export lags new Lean releases by a version or two.
c=""; used=""
# An exact pin first (lean4export has bump commits per release candidate).
for h in $(git log --format=%h --all -- lean-toolchain); do
  if [ "$(git show "$h:lean-toolchain" 2>/dev/null | tr -d '[:space:]')" = "$TC" ]; then c=$h; used=$minor; break; fi
done
[ -n "$c" ] || for m in $(seq "$minor" -1 0); do
  for h in $(git log --format=%h --all -- lean-toolchain); do
    if git show "$h:lean-toolchain" 2>/dev/null | grep -q "v$major\.$m\."; then c=$h; used=$m; break; fi
  done
  [ -n "$c" ] && break
done
[ -n "$c" ] || { echo "no lean4export commit pins v$major.$minor or lower"; exit 1; }
[ "$used" = "$minor" ] || echo "no lean4export commit pins v$major.$minor; using the last one for v$major.$used"
echo "lean4export at $c ($(git show "$c:lean-toolchain")), built with $TC"
git checkout -q "$c"
echo "$TC" > lean-toolchain
lake build
ls -la .lake/build/bin/lean4export
