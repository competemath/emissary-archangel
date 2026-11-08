"""The ledger names the refused modules a cascade is behind (bundle.cascade_roots, held_back_by_root).

The real case: foundation's re-bump (8 Nov 2026) left 2,491 passed theorems out as "imports a module that cannot go to the tree", arklib 1,291, cslib 1,236, tnlean 1,074,
and nothing said behind which modules: the few refused roots that hold back thousands could not be found and fixed first.

Fixture: the real import graph of flt-anthropic (fixtures/real-flt-imports.json.gz, 60,474 modules). Real modules are refused for a reason of their own (P2M.Util, which every
Theorems module imports, and 40 P2M.Sol proofs); every module that imports a refused one, directly or not, is dropped as the cascade (computed here by its own reverse search).
Invariants: every cascade module's roots are exactly the refused modules it reaches through dropped imports (an independent forward search, on 3,000 cascade modules and on
every Theorems module); a module dropped for its own reason is no cascade entry; held_back_by_root counts each root's own theorems plus those of every cascade module behind
it, largest first; a cycle among dropped modules ends.
"""

from __future__ import annotations

import gzip
import json
import random
import sys
import unittest
from collections import deque
from pathlib import Path

HERE = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(HERE))
import bundle  # noqa: E402

IMPORTS: dict[str, list[str]] = json.load(gzip.open(HERE / "tests" / "fixtures" / "real-flt-imports.json.gz"))["imports"]


class CascadeRoots(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        rng = random.Random(8)
        sols = sorted(m for m in IMPORTS if m.startswith("P2M.Sol."))
        cls.roots = {"P2M.Util"} | set(rng.sample(sols, 40))
        importers: dict[str, list[str]] = {}
        for m, ds in IMPORTS.items():
            for d in ds:
                importers.setdefault(d, []).append(m)
        dropped = {r: "lint: a refused command" for r in cls.roots}
        q = deque(cls.roots)
        while q:  # every module that imports a refused one, directly or not
            m = q.popleft()
            for u in importers.get(m, []):
                if u not in dropped:
                    dropped[u] = bundle.CASCADE
                    q.append(u)
        cls.dropped = dropped
        cls.got = bundle.cascade_roots(IMPORTS, dropped)

    def expected(self, mod: str) -> list[str]:
        seen, q, out = {mod}, deque([mod]), set()
        while q:
            m = q.popleft()
            for d in IMPORTS.get(m, []):
                if d in self.dropped and d not in seen:
                    seen.add(d)
                    if self.dropped[d] == bundle.CASCADE:
                        q.append(d)
                    else:
                        out.add(d)
        return sorted(out)

    def test_the_fixture_is_the_real_case(self):
        self.assertGreater(len(IMPORTS), 60000)
        cascade = [m for m, w in self.dropped.items() if w == bundle.CASCADE]
        self.assertGreater(len(cascade), 1000)
        self.assertTrue(any(m.startswith("Theorems.") for m in cascade))

    def test_each_cascade_module_names_exactly_the_roots_it_is_behind(self):
        cascade = sorted(m for m, w in self.dropped.items() if w == bundle.CASCADE)
        self.assertEqual(set(self.got), set(cascade))  # a module refused for its own reason is no cascade entry
        sample = random.Random(1).sample(cascade, 3000) + [m for m in cascade if m.startswith("Theorems.")]
        for m in sample:
            self.assertEqual(self.got[m], self.expected(m), m)
            self.assertTrue(self.got[m], m)  # a cascade module is behind at least one root

    def test_held_back_counts_each_roots_own_and_its_cascade(self):
        ledger = {m: {"reason": w, "names": 1 + (len(m) % 3)} for m, w in self.dropped.items()}
        held = bundle.held_back_by_root(ledger, self.got)
        want: dict[str, int] = {}
        for m, e in ledger.items():
            for r in (self.got[m] if e["reason"] == bundle.CASCADE else [m]):
                want[r] = want.get(r, 0) + e["names"]
        self.assertEqual(held, dict(sorted(want.items(), key=lambda x: (-x[1], x[0]))))
        self.assertEqual(set(held), self.roots)
        self.assertEqual(next(iter(held)), "P2M.Util")  # every Theorems module is behind it: it holds back the most
        vals = list(held.values())
        self.assertEqual(vals, sorted(vals, reverse=True))

    def test_a_cycle_among_dropped_modules_ends(self):
        imports = {"A": ["B"], "B": ["A", "R"], "R": []}
        dropped = {"A": bundle.CASCADE, "B": bundle.CASCADE, "R": "lint"}
        self.assertEqual(bundle.cascade_roots(imports, dropped), {"A": ["R"], "B": ["R"]})


if __name__ == "__main__":
    unittest.main()
