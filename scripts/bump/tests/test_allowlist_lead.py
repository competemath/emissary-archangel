"""The allow-list lint on a column-0 line whose second word starts with a symbol.

Regression (2026-10-06): bump-sharded run 37409123807 (lean-pool) died in `bundle.py compose` with `AttributeError: 'NoneType' object has no attribute 'group'` on a
column-0 line such as `meta : Nat` (a structure field called meta): after the modifier is dropped the next word starts with a symbol, not a command."""

from __future__ import annotations

import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "lint"))
import allowlist  # noqa: E402

KEYWORDS = {"theorem", "def", "structure", "namespace", "open", "section", "end"}


class ModifierThenSymbol(unittest.TestCase):
    def test_not_a_command_and_no_crash(self):
        for text in ("structure S where\nmeta : Nat\n", "def f := 1\nprivate (x : Nat)\n", "def f := 1\nlocal ⟨x⟩\n", "theorem t : True := by\n  trivial\nprotected :=\n"):
            for keywords in (KEYWORDS, None):
                self.assertEqual(allowlist.violations(text, set(), keywords), [], (text, keywords))

    def test_a_modifier_in_front_of_a_forbidden_command_is_still_refused(self):
        self.assertTrue(allowlist.violations("private elab \"x\" : command => pure ()\n", set(), KEYWORDS | {"elab"}))


if __name__ == "__main__":
    unittest.main()
