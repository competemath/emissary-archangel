#!/bin/bash
# Build lean4export on the corpus toolchain: the exporter must match the
# toolchain whose .oleans it reads (Gate 2 replays its output).
#   scripts/build-lean4export.sh [toolchain]     default leanprover/lean4:v4.29.1
set -euo pipefail
TC=${1:-leanprover/lean4:v4.29.1}
ROOT=$(cd "$(dirname "$0")/.." && pwd)
DEST=$ROOT/infra/lean4export
[ -d "$DEST/.git" ] || git clone -q https://github.com/leanprover/lean4export "$DEST"
cd "$DEST"
minor=$(echo "$TC" | sed -E 's/.*v([0-9]+\.[0-9]+).*/\1/')
c=""
for h in $(git log --format=%h -- lean-toolchain); do
  if git show "$h:lean-toolchain" 2>/dev/null | grep -q "v$minor\."; then c=$h; break; fi
done
[ -n "$c" ] || { echo "no lean4export commit pins a v$minor toolchain"; exit 1; }
echo "lean4export at $c ($(git show "$c:lean-toolchain")), built with $TC"
git checkout -q "$c"
echo "$TC" > lean-toolchain
lake build
ls -la .lake/build/bin/lean4export
