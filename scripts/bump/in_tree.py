#!/usr/bin/env python3
"""in_tree.py — a fresh bump of a library whose parts are in the tree already is cut from the tree, or it does not start.

foundation (2026-11-07, run 42370781841): its parts 001-002 had merged; a new bump without `from_tree` cut its bundle into parts numbered from 001 again, the opener said
"every part is in the tree" and opened nothing, and 108 theorems that had passed every check waited until a recut by hand (`recut_from` + `from_tree=true`, run 42376189191,
which cut part 003). The opener knows a run continues the tree only from its title, which the dispatch fixes; so the plan refuses the run at once, naming the dispatch that works,
instead of running for hours and shipping nothing. `from_tree` also needs `parts` (the pack step cuts no part when it is 0).

  git -C tengoku ls-tree -r --name-only main -- data/intake/KEY | in_tree.py --key KEY --from-tree "$FROM_TREE" --parts "$PARTS"

Exit 0: the bump may run. Exit 1: a GitHub error line says why and what to dispatch.
"""

from __future__ import annotations

import argparse
import re
import sys


def merged_parts(paths: list[str], key: str) -> list[int]:
    """the part numbers the tree records for `key`: data/intake/<key>/parts/NNN.json, and part 001 for a library merged in one part (the tree then records only
    data/intake/<key>/manifest.jsonl: lana-pi1, ns-p23, flt-anthropic on 7 Nov). The same rule as the pack step's next part number (its last part defaults to 1)."""
    rx = re.compile(rf"^data/intake/{re.escape(key)}/parts/(\d{{3}})\.json$")
    nums = {int(m.group(1)) for p in paths for m in [rx.match(p.strip())] if m}
    if not nums and any(p.strip() == f"data/intake/{key}/manifest.jsonl" for p in paths):
        nums = {1}
    return sorted(nums)


def verdict(paths: list[str], key: str, from_tree: str, parts: str) -> tuple[bool, str]:
    nums = merged_parts(paths, key)
    want = from_tree.strip() == "true"
    try:
        n_parts = int(parts.strip() or "0")
    except ValueError:
        return False, f"parts={parts!r} is not a number"
    if n_parts < 0:
        return False, f"parts={parts!r} is negative: a part holds at least one module (0 = no parts)"
    if want and n_parts <= 0:
        return False, f"from_tree=true cuts parts after the tree's, but parts={parts or 0}: no part would be cut. Dispatch again with parts=300 (or the size you want)"
    if nums and not want:
        return False, (
            f"{key} is in the tree already (part(s) {', '.join(f'{n:03d}' for n in nums)} in data/intake/{key}/parts): a bump without from_tree=true numbers its parts from 001, "
            f"and the opener skips them as 'every part is in the tree'. Dispatch again with from_tree=true parts={n_parts if n_parts > 0 else 300}: the new modules are cut from part {nums[-1] + 1:03d}"
        )
    if nums:
        return True, f"{key} is in the tree (last part {nums[-1]:03d}): the parts are cut from the tree, from part {nums[-1] + 1:03d}"
    return True, f"{key} has no part in the tree: the parts start at 001" if n_parts > 0 else f"{key} has no part in the tree"


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--key", required=True)
    ap.add_argument("--from-tree", default="")
    ap.add_argument("--parts", default="0")
    a = ap.parse_args()
    ok, why = verdict(sys.stdin.read().splitlines(), a.key, a.from_tree, a.parts)
    print(why if ok else f"::error::{why}")
    sys.exit(0 if ok else 1)
