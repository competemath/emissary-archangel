#!/usr/bin/env python3
"""ledger_rows.py — the ledger lines for the declarations a bump settled, in the format scripts/translate-finish.mjs appends.

  ledger_rows.py --ledger data/translate/<key>.jsonl --log gate2.log --run RUN --out rows.jsonl

One row per name that passed the batched Gate 2 AND is already in the ledger (the row's `id` is the queue id the ledger knows
it by): {id, name, sourcePath, outcome: "bump", via: equal|entails, at, run}. queue-server.mjs reads `bump` as verified, so
the per-theorem pipeline never spends a Leak/Gate 2 call or an agent on it again.
"""

import argparse
import json
import re
from datetime import datetime, timezone
from pathlib import Path

ap = argparse.ArgumentParser()
for f in ("ledger", "log", "run", "out"):
    ap.add_argument(f"--{f}", required=True)
a = ap.parse_args()
latest = {}
for line in Path(a.ledger).read_text().splitlines():
    try:
        r = json.loads(line)
    except ValueError:
        continue
    latest[r["name"]] = r
via = {}
for m in re.finditer(r"GATE2B_PASS old=(\S+) new=(\S+) via=(\w+)", Path(a.log).read_text(errors="replace")):
    if m.group(1) == m.group(2):
        via[m.group(1)] = m.group(3)
now = datetime.now(timezone.utc).isoformat().replace("+00:00", "Z")
rows = []
for name, how in sorted(via.items()):
    r = latest.get(name)
    if r and r.get("outcome") not in ("mechanical", "cached-mechanical", "agentic", "bump"):
        rows.append({"id": r["id"], "name": name, "sourcePath": r["sourcePath"], "outcome": "bump", "via": how, "at": now, "run": a.run})
Path(a.out).write_text("".join(json.dumps(r) + "\n" for r in rows))
print(json.dumps({"passed": len(via), "new_settled_rows": len(rows), "already_settled": len(via) - len(rows)}))
