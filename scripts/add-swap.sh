#!/bin/sh
# add-swap.sh MAX_GB KEEP_GB [WAIT_FILE]
# Adds a swap file on / for modules that do not fit in a runner's RAM (flt-anthropic's P2M.Sol proofs, 100-900 KB each, killed at 14 GB on a 16 GB runner).
# The size is what the disk can spare, never more than MAX_GB: free space minus KEEP_GB, which is left for the build. A fixed 48 GB took the space the previous
# round's build needs to unpack (the first retry of flt-anthropic, 5 Nov 2026, died with "No space left on device" four minutes into the restore).
# With WAIT_FILE the swap is added only once that file is gone: the archive of the earlier build, deleted by setup-source.mjs after it is unpacked
# (EMISSARY_DROP_RESTORED=1), so that the free space is measured when it is known and not guessed before the unpack.
# Fewer than MIN_GB (8) to spare: no swap, said plainly, and exit 0 (the build then runs as it would have without it; the module is reported as too big again).
max=$1; keep=$2; wait_file=${3:-}
case $max in ''|*[!0-9]*|0) echo "add-swap.sh: MAX_GB is a positive whole number, not '$max'" >&2; exit 2 ;; esac
case $keep in ''|*[!0-9]*) echo "add-swap.sh: KEEP_GB is a whole number, not '$keep'" >&2; exit 2 ;; esac
if [ -n "$wait_file" ]; then
  waited=0
  while [ -e "$wait_file" ]; do
    sleep "${ADD_SWAP_POLL_S:-5}"
    waited=$((waited + 1))
    [ "$waited" -le "${ADD_SWAP_MAX_POLLS:-1440}" ] || { echo "add-swap.sh: $wait_file is still there after the wait; no swap" >&2; exit 0; }
  done
fi
avail=$(df -BG --output=avail / | tail -n 1 | tr -dc '0-9')
case $avail in ''|*[!0-9]*) echo "add-swap.sh: cannot read the free space; no swap" >&2; exit 0 ;; esac
room=$((avail - keep))
if [ "$room" -lt 8 ]; then
  echo "add-swap.sh: ${avail} GB free, ${keep} GB kept for the build: under 8 GB to spare, no swap"
  exit 0
fi
size=$room
[ "$size" -le "$max" ] || size=$max
sudo swapoff -a || true
sudo fallocate -l "${size}G" /swapfile
sudo chmod 600 /swapfile
sudo mkswap /swapfile
sudo swapon /swapfile
echo "add-swap.sh: ${size} GB of swap (${avail} GB were free, ${keep} kept, at most ${max})"
free -g
