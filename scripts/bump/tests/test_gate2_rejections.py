"""The words of a Gate 2B refusal are kept in the results file, not only its count (scripts/bump/gate2_batch.py `rejections`)."""
import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import gate2_batch as g  # noqa: E402

LOG = """
GATE2B_PASS old=Foo.a new=Foo.a via=equal
GATE2B_FAIL old=Foo.b new=Foo.b reason=name_collision names=FreeMagma,FreeMagma.of GATE2B_DIFF FreeMagma: kinds old=inductive new=inductive; old type = Type u → Type u || new type =
   Type u → Type u GATE2B_END
GATE2B_FAIL old=Foo.c new=Foo.c reason=universe_param_count_mismatch
GATE2B_FAIL old=Foo.d new=Foo.d reason=kernel_error
GATE2B_FAIL old=Foo.e new=Foo.e reason=rejected msg=Unknown constant `algebraMap` GATE2B_DIFF old type = ∀ x, f x = 1 || new type = ∀ x,
    f x ≤ 1 GATE2B_END
GATE2B_FAIL old=Foo.f new=Foo.f reason=rejected msg=Type mismatch
GATE2B_PASS old=Foo.a new=Foo.b via=entails
GATE2B_FAIL old=Foo.a new=Foo.z reason=name_collision names=Q GATE2B_DIFF control GATE2B_END
"""


class RejectionsCase(unittest.TestCase):
    def test_a_refusal_keeps_its_reason_its_names_and_its_first_differences(self):
        r = g.rejections(LOG)
        self.assertEqual(r["total"], 5)
        byold = {i["old"]: i for i in r["items"]}
        b = byold["Foo.b"]
        self.assertEqual(b["reason"], "name_collision")
        self.assertEqual(b["names"], ["FreeMagma", "FreeMagma.of"])
        self.assertIn("kinds old=inductive new=inductive", b["diff"])
        self.assertNotIn("\n", b["diff"], "one line")
        self.assertEqual(byold["Foo.c"], {"old": "Foo.c", "reason": "universe_param_count_mismatch"})
        self.assertEqual(byold["Foo.d"]["reason"], "kernel_error")

    def test_a_rejected_bridge_keeps_the_first_line_of_what_the_kernel_said(self):
        byold = {i["old"]: i for i in g.rejections(LOG)["items"]}
        self.assertEqual(byold["Foo.e"]["msg"], "Unknown constant `algebraMap`")
        self.assertEqual(byold["Foo.f"], {"old": "Foo.f", "reason": "rejected", "msg": "Type mismatch"}, "no statements logged, none invented")
        self.assertNotIn("msg", byold["Foo.c"], "a refusal with no message has none")
        # a rejected bridge keeps both statements, one line each, cut separately
        self.assertEqual(byold["Foo.e"]["old_type"], "∀ x, f x = 1")
        self.assertEqual(byold["Foo.e"]["new_type"], "∀ x, f x ≤ 1")
        self.assertNotIn("diff", byold["Foo.e"])

    def test_a_long_old_statement_cannot_hide_the_new_one(self):
        long = "x" * 5000
        r = g.rejections(f"GATE2B_FAIL old=A new=A reason=rejected msg=Type mismatch GATE2B_DIFF old type = {long} || new type = NEWSTATEMENT GATE2B_END\n")
        item = r["items"][0]
        self.assertLessEqual(len(item["old_type"]), 700)
        self.assertEqual(item["new_type"], "NEWSTATEMENT")

    def test_controls_are_not_refusals(self):
        r = g.rejections(LOG)
        self.assertNotIn("Foo.a", [i["old"] for i in r["items"]], "a pass is not a refusal")
        self.assertFalse(any(i.get("names") == ["Q"] for i in r["items"]), "old != new is a control, not a refusal of anything")

    def test_the_file_stays_small_however_many_are_refused(self):
        big = "".join(f"GATE2B_FAIL old=N{i} new=N{i} reason=name_collision names=X GATE2B_DIFF {'d' * 5000} GATE2B_END\n" for i in range(1000))
        r = g.rejections(big)
        self.assertEqual(r["total"], 1000)
        self.assertEqual(r["kept"], g.REJECTIONS_KEPT)
        self.assertEqual(len(r["items"]), g.REJECTIONS_KEPT)
        self.assertTrue(all(len(i["diff"]) <= 500 for i in r["items"]))

    def test_an_empty_log_is_empty(self):
        self.assertEqual(g.rejections(""), {"total": 0, "kept": 0, "items": []})


if __name__ == "__main__":
    unittest.main()
