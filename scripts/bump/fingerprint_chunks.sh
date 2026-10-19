#!/usr/bin/env bash
# fingerprint_chunks.sh LIST WHOLE OUT MINUTES [JOBS [BATCH]] — ModuleFingerprint.lean over the modules named in LIST (one per line), in JOBS processes at once (default 3: each loads the library's
# closure, a few GB), every process on its share of the list, a share given to the program BATCH modules at a time (default 4), the results joined in OUT (stderr in OUT.err).
#
# Why batches: the program never frees the files it maps (freeing them under an environment that still points into them crashes the process, emissary#71), and a process may hold only ~65,000
# mappings: one module's closure is several thousand files. A new process every few modules keeps that bound. It also bounds a loss: a batch that dies or runs past its time loses its own
# modules, and the program flushes after each module, so a killed batch keeps the ones it finished.
#
# What this guarantees: every module of LIST is given to exactly one batch of exactly one process; whatever a batch or a process loses is only the modules it had not finished (the program prints
# a module's lines only when it is complete, tree_dups.parse_fp reads only the complete ones), never another batch's. When MINUTES have passed no further batch is started. It guarantees nothing
# about the fingerprints: that is the program's and the reader's.
#
# Run from the workspace that has the checkout of the tree in `tree/`. LIST and WHOLE are absolute paths, OUT may be relative.
set -u
list=$1 whole=$2 out=$3 minutes=$4 jobs=${5:-3} batch=${6:-4}
here=$(cd "$(dirname "$0")" && pwd)
: > "$out"
: > "$out.err"
[ -s "$list" ] || exit 0
work=$(mktemp -d)
budget=$(awk -v m="$minutes" 'BEGIN { printf "%d", m * 60 }')
# round robin: the first module goes to chunk 0, the second to chunk 1, …
awk -v n="$jobs" -v dir="$work" 'NF { print > (dir "/part-" (cnt++ % n)) }' "$list"

run_part() {
  local part=$1 start=$SECONDS left cap
  split -l "$batch" -a 5 "$part" "$part.b."
  for b in "$part".b.*; do
    left=$(( budget - (SECONDS - start) ))
    [ "$left" -ge 5 ] || { echo "no time left: $(basename "$b") and the batches after it were not started" >> "$part.err"; break; }
    cap=$(( left < 1200 ? left : 1200 ))  # one batch may not take the rest of the share
    ( cd tree && timeout -k 30 "${cap}s" lake env lean --run "$here/ModuleFingerprint.lean" "$b" "$whole" ) >> "$part.fp" 2>> "$part.err" || true
  done
}

for p in "$work"/part-*; do  # expanded once, before any batch file exists
  run_part "$p" &
done
wait
cat "$work"/part-*.fp >> "$out" 2>/dev/null || true
cat "$work"/part-*.err >> "$out.err" 2>/dev/null || true
rm -rf "$work"
