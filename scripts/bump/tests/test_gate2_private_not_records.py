"""A private declaration that passes Gate 2 is not a record (gate2_batch.py parse writes passed.json without it).

The real case: once Gate 2 read private names (emissary #157), primecert's bump passed 45 declarations, all private, and its part 1 (tengoku #758, 8 Nov 2026) was 16
private lemmas and nothing else. The tree refused it: "not born tagged" for every file, and the tag job "nothing was tagged". The tree's isnad population leaves internal
declarations out (TengokuIsnad.okName), and no other module can cite a private one, so no prover can use it. Its Gate 2 verdict is kept in the results; only the record goes.

Fixture: the real Gate 2 verdict lines and the passed.json of the two shards (fixtures/real-gate2-private.json.gz): primecert (65 verdicts, 45 passed, all private) and
padic-l-functions (1,261 verdicts, 208 passed, 70 private, 12 modules whose passes are all private). Invariants, per library:
  * every public name the real shard passed is in passed.json, in its module, and nothing else is;
  * no private name is in passed.json, and a module whose passes were all private is not in it at all;
  * the results still count every pass (the verdict is untouched) and say how many private passes made no record.
"""

from __future__ import annotations

import gzip
import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parents[1]
FIXTURE = json.loads(gzip.open(HERE / "tests" / "fixtures" / "real-gate2-private.json.gz", "rt").read())


class PrivateNotRecords(unittest.TestCase):
    def parse(self, lib: dict) -> tuple[dict, dict]:
        with tempfile.TemporaryDirectory() as tmp:
            t = Path(tmp)
            (t / "gate2.log").write_text("\n".join(lib["gate2_lines"]) + "\n")
            # the entries the shard looked the names up in: each passed name under its module's source path (what the tentative records gave the real run)
            rows = [{"name": n, "sourcePath": m.replace(".", "/") + ".lean", "outcome": "tentative"} for m, ns in lib["passed"].items() for n in ns]
            (t / "ledger.jsonl").write_text("".join(json.dumps(r) + "\n" for r in rows))
            r = subprocess.run([sys.executable, str(HERE / "gate2_batch.py"), "parse", "--log", str(t / "gate2.log"), "--ledger", str(t / "ledger.jsonl"), "--out", str(t / "gate2-results.json")],
                               capture_output=True, text=True, check=False)
            self.assertEqual(r.returncode, 0, r.stderr[-2000:])
            return json.loads((t / "passed.json").read_text()), json.loads((t / "gate2-results.json").read_text())

    def test_the_fixture_is_the_real_case(self):
        pc, pd = FIXTURE["libraries"]["primecert"], FIXTURE["libraries"]["padic-l-functions"]
        names = lambda lib: [n for ns in lib["passed"].values() for n in ns]
        self.assertEqual((len(pc["gate2_lines"]), len(names(pc)), sum(n.startswith("_private.") for n in names(pc))), (65, 45, 45))
        self.assertEqual((len(pd["gate2_lines"]), len(names(pd)), sum(n.startswith("_private.") for n in names(pd))), (1261, 208, 70))

    def test_public_passes_are_records_and_private_ones_are_not(self):
        for key, lib in FIXTURE["libraries"].items():
            passed, res = self.parse(lib)
            want = {m: sorted(n for n in ns if not n.startswith("_private.")) for m, ns in lib["passed"].items()}
            want = {m: ns for m, ns in want.items() if ns}
            self.assertEqual(passed, want, key)
            self.assertFalse(any(n.startswith("_private.") for ns in passed.values() for n in ns), key)
            only_private = [m for m, ns in lib["passed"].items() if all(n.startswith("_private.") for n in ns)]
            self.assertTrue(all(m not in passed for m in only_private), key)
            total = sum(len(ns) for ns in lib["passed"].values())
            private = sum(n.startswith("_private.") for ns in lib["passed"].values() for n in ns)
            self.assertEqual(res["pass"], total, key)  # the verdicts are untouched
            self.assertEqual(res["pass_private_not_records"], private, key)

    def test_primecert_makes_no_record_and_padic_keeps_its_138_public_passes(self):
        passed, _ = self.parse(FIXTURE["libraries"]["primecert"])
        self.assertEqual(passed, {})
        passed, _ = self.parse(FIXTURE["libraries"]["padic-l-functions"])
        self.assertEqual(sum(len(ns) for ns in passed.values()), 138)
        self.assertEqual(len(passed), 44 - 12)


if __name__ == "__main__":
    unittest.main()
