"""completeness.py: every verified theorem is shipped or in the ledger with a reason, and the chain to the tree is counted."""

import json
import sys
import tempfile
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(HERE))
import completeness  # noqa: E402


def rows(names):
    return "".join(json.dumps({"name": n}) + "\n" for n in names)


class Account(unittest.TestCase):
    def setup(self, shipped, left_out, modules, tree, verified=None, ledger=True):
        art, tr = Path(tempfile.mkdtemp()), Path(tempfile.mkdtemp())
        b = art / "bundle-proposed"
        b.mkdir()
        (b / "manifest.jsonl").write_text(rows(shipped))
        total = verified if verified is not None else len(shipped) + sum(left_out.values())
        (b / "report.json").write_text(json.dumps({"passed_total": total, "left_out": left_out}))
        if ledger:
            (art / "bundle-proposed.ledger.json").write_text(json.dumps({"verified": total, "shipped": len(shipped), "left_out": left_out, "modules": modules}))
        (art / "logs").mkdir()
        (art / "logs" / "gate2-results.json").write_text(json.dumps({"checked": 100, "pass": total}))
        d = tr / "data" / "intake" / "lib"
        d.mkdir(parents=True)
        (d / "manifest.jsonl").write_text(rows(tree))
        return art, tr

    def test_a_consistent_chain_has_nothing_unaccounted_and_counts_pending_and_tree_only(self):
        art, tr = self.setup(["a", "b", "c"], {"imports a module that cannot go to the tree": 2}, {"M": {"reason": "imports a module that cannot go to the tree", "names": 2}}, ["a", "old"])
        r = completeness.account(art, tr, "lib", "proposed")
        self.assertEqual(r["problems"], [])
        self.assertEqual((r["verified"], r["shipped"], r["in_tree"], r["pending"], r["tree_only"]), (5, 3, 2, 2, 1))
        self.assertEqual(r["left_out"], {"imports a module that cannot go to the tree": 2})

    def test_a_hole_in_the_identity_is_reported(self):
        art, tr = self.setup(["a"], {"lint": 1}, {"M": {"reason": "lint", "names": 1}}, ["a"], verified=5)  # 5 verified, 1 + 1 accounted
        r = completeness.account(art, tr, "lib", "proposed")
        self.assertTrue(any("verified 5" in p for p in r["problems"]))
        self.assertEqual(completeness.main(["--artifact", str(art), "--tree", str(tr), "--lib", "lib"]), 1)

    def test_a_ledger_that_lists_fewer_theorems_than_were_left_out_is_reported(self):
        art, tr = self.setup(["a"], {"lint": 3}, {"M": {"reason": "lint", "names": 1}}, ["a"])
        r = completeness.account(art, tr, "lib", "proposed")
        self.assertTrue(any("the ledger lists 1" in p for p in r["problems"]))

    def test_reasons_are_grouped_without_their_names(self):
        art, tr = self.setup(["a"], {"declares a record the tree already has: X, Y": 2, "declares a record the tree already has: Z": 1}, {}, ["a"], ledger=False)
        r = completeness.account(art, tr, "lib", "proposed")
        self.assertEqual(r["left_out"], {"declares a record the tree already has": 3})
        self.assertFalse(r["ledger_file"])

    def rewrite_ledger(self, art, **fields):
        f = art / "bundle-proposed" / "ledger.json"
        d = json.loads(f.read_text())
        d.update(fields)
        f.write_text(json.dumps(d))

    def test_a_ledger_that_left_nothing_out_is_not_a_missing_key(self):
        art, tr = self.setup(["a", "b"], {}, {}, ["a"])
        r = completeness.account(art, tr, "lib", "proposed")
        self.assertEqual((r["problems"], r["left_out"]), ([], {}))

    def test_an_empty_ledger_left_out_is_not_replaced_by_the_reports(self):
        art, tr = self.setup(["a"], {"lint": 2}, {"M": {"reason": "lint", "names": 2}}, ["a"])
        self.rewrite_ledger(art, left_out={}, modules={})  # the ledger claims nothing was left out; the report says 2
        r = completeness.account(art, tr, "lib", "proposed")
        self.assertTrue(any("the ledger left out 0" in p and "the report 2" in p for p in r["problems"]), r["problems"])
        self.assertEqual(r["left_out"], {})  # the ledger's own (empty) answer is what is reported, not the report's

    def test_the_ledgers_verified_and_shipped_totals_must_match_the_report_and_the_manifest(self):
        art, tr = self.setup(["a", "b"], {"lint": 1}, {"M": {"reason": "lint", "names": 1}}, ["a"])
        self.rewrite_ledger(art, verified=9)
        r = completeness.account(art, tr, "lib", "proposed")
        self.assertTrue(any("the ledger says 9 verified" in p for p in r["problems"]), r["problems"])
        art, tr = self.setup(["a", "b"], {"lint": 1}, {"M": {"reason": "lint", "names": 1}}, ["a"])
        self.rewrite_ledger(art, shipped=5)
        r = completeness.account(art, tr, "lib", "proposed")
        self.assertTrue(any("the ledger says 5 shipped" in p and "the manifest has 2" in p for p in r["problems"]), r["problems"])


if __name__ == "__main__":
    unittest.main()
