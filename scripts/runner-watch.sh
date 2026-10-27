#!/bin/sh
# runner-watch.sh <olean-dir> <out.tsv> [interval-seconds]
# Writes one line every interval (default 60 s) to <out.tsv>: time, free memory (MB), modules built so far (.olean files under
# <olean-dir>), the biggest process (MB, name). Every 5th sample is also printed, so that the log of a long build step is never silent
# (round 7 of flt-anthropic logged nothing for 2.5 hours: the output of the last chunk is only printed when the chunk ends).
# Runs until it is terminated (TERM), and takes one last sample then, so the end of the round is in the file. It reads nothing but counters and process sizes, and sends nothing anywhere.
dir=$1; out=$2; every=${3:-60}
[ -n "$dir" ] && [ -n "$out" ] || { echo "usage: runner-watch.sh <olean-dir> <out.tsv> [seconds]" >&2; exit 2; }
case $every in ''|*[!0-9]*|0) echo "runner-watch.sh: the interval must be a positive whole number of seconds, not '$every'" >&2; exit 2 ;; esac
n=0
printf 'time\tfree_mb\tbuilt\ttop_mb\ttop_name\n' > "$out"
sample() {
  free=$(awk '/^MemAvailable:/ {printf "%d", $2/1024}' /proc/meminfo 2>/dev/null); free=${free:-NA}
  built=$(find "$dir" -name '*.olean' 2>/dev/null | wc -l | tr -d ' ')
  top=$(ps -eo rss=,comm= 2>/dev/null | sort -rn | head -n 1 | awk '{printf "%d\t%s", $1/1024, $2}'); top=${top:-NA	NA}
  line=$(printf '%s\t%s\t%s\t%s' "$(date -u +%H:%M:%S)" "$free" "$built" "$top")
  echo "$line" >> "$out"
  n=$((n + 1)); [ $((n % 5)) -eq 1 ] && echo "[watch] $line"
  return 0
}
trap 'sample; exit 0' TERM
while :; do
  sample
  sleep "$every" &  # in the background and waited for, so that TERM is handled at once and not after the sleep
  wait $!
done
