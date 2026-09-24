#!/bin/bash

# An outage must pause the runner, not fail every remaining library in a second each.
wait_for_network() {
  until curl -sI -m 10 https://github.com >/dev/null 2>&1; do
    echo "[$(date +%T)] network down (github.com unreachable) — waiting"
    sleep 60
  done
}
# Set up every corpus source in sources.json that is not set up yet, one at a
# time, grouped by toolchain (the tree's own first). One build is on disk at a
# time: each library's .lake is removed when its exports exist, and a toolchain
# that is neither the tree's nor 4.29.1 is uninstalled once its last library
# is done. Logs: data/pipeline/setup-<key>.log, summary on stdout.
#   scripts/setup-sources.sh [key...]        default: every corpus source without infra/<key>/setup.json
set -u
ROOT=$(cd "$(dirname "$0")/.." && pwd); cd "$ROOT" || exit 1
mkdir -p data/pipeline
if [ $# -gt 0 ]; then KEYS="$*"; else
  KEYS=$(python3 - <<'PY'
import json, os
d = json.load(open("sources.json"))
tree = d["targetToolchain"]
rows = []
for k, s in d["sources"].items():
    if not s.get("repo") or os.path.exists(f"infra/{k}/setup.json"): continue
    rows.append((0 if s["toolchain"] == tree else 1, s["toolchain"], k))
for _, _, k in sorted(rows, key=lambda r: (r[0], r[1], r[2]), reverse=False): print(k)
PY
)
fi
# Reverse-sort within the non-tree group puts newer toolchains first (v4.34.0-rc1, v4.33.1, v4.32.2 ... v4.18.0).
KEYS=$(python3 - "$KEYS" <<'PY'
import json, sys
d = json.load(open("sources.json")); tree = d["targetToolchain"]
keys = sys.argv[1].split()
def ver(tc):
    import re; m = re.search(r"v(\d+)\.(\d+)\.(\d+)(?:-rc(\d+))?", tc); return (int(m[1]), int(m[2]), int(m[3]), int(m[4] or 99)) if m else (0,0,0,0)
keys.sort(key=lambda k: (0 if d["sources"][k]["toolchain"] == tree else 1, tuple(-v for v in ver(d["sources"][k]["toolchain"])), k))
print(" ".join(keys))
PY
)
echo "order: $KEYS"
prev_tc=""
for k in $KEYS; do
  tc=$(python3 -c "import json; print(json.load(open('sources.json'))['sources']['$k']['toolchain'])")
  next=""; after=0
  for j in $KEYS; do [ $after = 1 ] && { next=$j; break; }; [ "$j" = "$k" ] && after=1; done
  next_tc=""; [ -n "$next" ] && next_tc=$(python3 -c "import json; print(json.load(open('sources.json'))['sources']['$next']['toolchain'])")
  uninstall=""; [ "$next_tc" != "$tc" ] && uninstall="--uninstall-toolchain"
  echo "[$(date +%T)] === $k ($tc) → data/pipeline/setup-$k.log"
  wait_for_network
  node scripts/setup-source.mjs "$k" $uninstall > "data/pipeline/setup-$k.log" 2>&1
  rc=$?
  tail -3 "data/pipeline/setup-$k.log" | sed 's/^/    /'
  echo "[$(date +%T)] === $k rc=$rc"
done
echo "[$(date +%T)] all done"
