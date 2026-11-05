#!/bin/sh
# add-swap.sh MAX_GB KEEP_GB
# Adds a swap file on / for modules that do not fit in a runner's RAM (flt-anthropic's P2M.Sol proofs, 100-900 KB each, killed at 14 GB on a 16 GB runner).
# The size is what the disk can spare, never more than MAX_GB: free space (whole GB, rounded DOWN) minus KEEP_GB, which is left for the build. A fixed 48 GB took the space the
# previous round's build needs to unpack (the first retry of flt-anthropic, 5 Nov 2026, died with "No space left on device" four minutes into the restore).
# setup-source.mjs runs this itself, right after it has unpacked the earlier build and deleted its archive (EMISSARY_ADD_SWAP_GB), so the free space is measured when it is known
# and the swap is there before the first module is compiled. bump-shard.yml runs it before it builds the library.
# Under 8 GB to spare: no swap, said plainly, exit 0 (nothing to add, nothing broken). A command that fails (fallocate, mkswap, swapon): the file is removed and the exit is 1,
# so that the job stops instead of running a big-memory round without the memory.
max=$1; keep=$2
case $max in ''|*[!0-9]*|0) echo "add-swap.sh: MAX_GB is a positive whole number, not '$max'" >&2; exit 2 ;; esac
case $keep in ''|*[!0-9]*) echo "add-swap.sh: KEEP_GB is a whole number, not '$keep'" >&2; exit 2 ;; esac
bytes=$(df -B1 --output=avail / | tail -n 1 | tr -dc '0-9')
case $bytes in ''|*[!0-9]*) echo "add-swap.sh: cannot read the free space; no swap" >&2; exit 0 ;; esac
avail=$((bytes / 1073741824))
room=$((avail - keep))
if [ "$room" -lt 8 ]; then
  echo "add-swap.sh: ${avail} GB free, ${keep} GB kept for the build: under 8 GB to spare, no swap"
  exit 0
fi
size=$room
[ "$size" -le "$max" ] || size=$max
fail() {
  echo "add-swap.sh: $1 failed; the swap file is removed" >&2
  sudo swapoff /swapfile 2> /dev/null || true
  sudo rm -f /swapfile
  exit 1
}
sudo swapoff -a || true
sudo fallocate -l "${size}G" /swapfile || fail fallocate
sudo chmod 600 /swapfile || fail chmod
sudo mkswap /swapfile || fail mkswap
sudo swapon /swapfile || fail swapon
echo "add-swap.sh: ${size} GB of swap (${avail} GB were free, ${keep} kept, at most ${max})"
free -g || true
