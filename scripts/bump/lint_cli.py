#!/usr/bin/env python3
"""lint_cli.py — the tree's content lint (scripts/bump/lint/allowlist.py) and the repair of its inert refusals (inert_commands.py), for the mechanical pass of the bridge.

The bridge is JavaScript and used to keep its own regular-expression copy of the lint (BANK_FORBIDDEN, BANK_ALLOWED_OPTIONS). It had drifted: eight options the tree allows were missing from it
(`linter.unusedSectionVars`, `linter.flexible`, …), so entries were sent to the agent for something the tree accepts. There is one lint now: the one the bundle lane runs, read from the
allow-list files next to it. This program is how the bridge asks it.

  lint_cli.py check    < {"text": "…"}   ->  {"violations": ["…", …]}
  lint_cli.py repair   < {"text": "…"}   ->  {"text": "…", "removed": [{"line", "kind", "text"}, …], "violations": ["…", …]}   (the violations of the REPAIRED text)

Several texts at a time: {"texts": ["…", …]} answers {"results": [ … one object per text … ]}, so that one process start serves a whole batch.
Exit status is 0 whenever it could answer; an unreadable input or a missing allow-list file is a nonzero exit and a message on stderr, never an empty list of violations.
"""

from __future__ import annotations

import json
import re
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE / "lint"))
sys.path.insert(0, str(HERE))
import allowlist  # noqa: E402
import inert_commands  # noqa: E402

ALLOWED = set(json.loads((HERE / "lint" / "allowed-options.json").read_text())["allowed"])
KEYWORDS = set(json.loads((HERE / "lint" / "command-keywords.json").read_text())["commands"])
# the verifier's own import lines are stripped before a record is staged (queue/route.ts); the lint reads what is left
_LEADING_IMPORTS = re.compile(r"^(?:\s*import\s+\S+\s*\n)+")


def violations(text: str) -> list[str]:
    return allowlist.violations(_LEADING_IMPORTS.sub("", text), ALLOWED, KEYWORDS)


def answer(mode: str, text: str) -> dict:
    if mode == "check":
        return {"violations": violations(text)}
    lead = _LEADING_IMPORTS.match(text)
    head = lead.group(0) if lead else ""
    repaired, removed = inert_commands.repair(text[len(head):], ALLOWED)
    return {"text": head + repaired if removed else text, "removed": removed, "violations": violations(repaired)}


def main(argv: list[str]) -> int:
    if len(argv) != 2 or argv[1] not in ("check", "repair"):
        print("usage: lint_cli.py check|repair  (JSON on stdin)", file=sys.stderr)
        return 2
    try:
        data = json.loads(sys.stdin.read())
        texts = data["texts"] if "texts" in data else None
        if texts is None:
            json.dump(answer(argv[1], data["text"]), sys.stdout)
        else:
            json.dump({"results": [answer(argv[1], t) for t in texts]}, sys.stdout)
    except (ValueError, KeyError, TypeError) as e:
        print(f"lint_cli.py: unreadable input: {e}", file=sys.stderr)
        return 2
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
