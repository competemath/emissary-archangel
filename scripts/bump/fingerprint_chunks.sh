#!/usr/bin/env bash
# fingerprint_chunks.sh LIST WHOLE OUT MINUTES [JOBS] — ModuleFingerprint.lean over the modules named in LIST (one per line), in JOBS processes at once (default 3: each loads the library's closure,
# a few GB), every process on its share of the list and under its own `timeout`, the results joined in OUT (stderr in OUT.err).
#
# What this guarantees: every module of LIST is given to exactly one process; a process that fails or is killed loses only the modules it had not finished (the program prints a module's lines
# only when it is complete, tree_dups.parse_fp reads only the complete ones), never another process's. It guarantees nothing about the fingerprints: that is the program's and the reader's.
#
# Run from the workspace that has the checkout of the tree in `tree/`. LIST and WHOLE are absolute paths, OUT may be relative.
set -u
list=$1 whole=$2 out=$3 minutes=$4 jobs=${5:-3}
here=$(cd "$(dirname "$0")" && pwd)
: > "$out"
: > "$out.err"
[ -s "$list" ] || exit 0
work=$(mktemp -d)
# round robin: the first module goes to chunk 0, the second to chunk 1, …
awk -v n="$jobs" -v dir="$work" 'NF { print > (dir "/part-" (cnt++ % n)) }' "$list"
for p in "$work"/part-*; do
  ( cd tree && timeout -k 30 "${minutes}m" lake env lean --run "$here/ModuleFingerprint.lean" "$p" "$whole" > "$p.fp" 2> "$p.err" ) || true &
done
wait
cat "$work"/part-*.fp >> "$out" 2>/dev/null || true
cat "$work"/part-*.err >> "$out.err" 2>/dev/null || true
rm -rf "$work"
