#!/usr/bin/env python3
"""last_part.py — the number of the last part the tree has for a library, from the GitHub answer for `data/intake/KEY/parts`, or a loud failure.

  curl … -w '\\n%{http_code}' …/contents/data/intake/KEY/parts | (split the status off) | last_part.py --status 200      prints the number

15 Nov 2026, flt-anthropic: the recut's pack step asked GitHub for that listing WITHOUT a token and read anything that was not a list as "no parts" (`max(n, default=1)`). On a runner that
GitHub rate-limited the answer was `{"message": "API rate limit exceeded …"}`, the last part came out as 1 instead of 3, and the parts were cut from 002: they collided with the merged parts 002
and 003. The opener (which skips the numbers the tree has) opened the third chunk as "part 4 of 18", whose umbrella named modules of the two chunks before it: tengoku#842 failed `imports`, `intake`,
`pr-gate` and its tag build, and four hours of tree build had produced a part nobody could merge. Only a real answer counts now: 200 with a list, or 404 (no `parts` directory: a library merged in
one part, or not in the tree: 1). Anything else (a rate limit, a 5xx, a body that is not a list) stops the step, which names what to do.
"""

from __future__ import annotations

import argparse
import json
import re
import sys

PART = re.compile(r"(\d{3})\.json$")


def last_part(body: str, status: str) -> int:
    code = status.strip()
    if code == "404":
        return 1
    if code != "200":
        raise SystemExit(f"GitHub answered {code or 'nothing'} for the tree's parts (data/intake/KEY/parts), not a listing: the number of the next part is not known, and cutting from 002 again would collide with the parts that merged. Run the step again")
    try:
        listing = json.loads(body)
    except ValueError:
        raise SystemExit("the answer for the tree's parts is not JSON: the number of the next part is not known") from None
    if isinstance(listing, dict):
        raise SystemExit(f"the answer for the tree's parts is not a listing ({str(listing.get('message', listing))[:120]!r}): the number of the next part is not known")
    if not isinstance(listing, list):
        raise SystemExit(f"the answer for the tree's parts is not a listing (a {type(listing).__name__}): the number of the next part is not known")
    for x in listing:  # an entry without a name would be skipped and the number understated (cubic on #206)
        if not isinstance(x, dict) or not isinstance(x.get("name"), str):
            raise SystemExit(f"an entry of the tree's parts has no name ({str(x)[:80]!r}): the number of the next part is not known")
    nums = [int(m.group(1)) for x in listing for m in [PART.match(x["name"])] if m]
    return max(nums, default=1)


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description="the last part the tree has for a library")
    ap.add_argument("--status", required=True, help="the HTTP status of the answer on stdin")
    a = ap.parse_args(argv)
    print(last_part(sys.stdin.read(), a.status))
    return 0


if __name__ == "__main__":
    sys.exit(main())
