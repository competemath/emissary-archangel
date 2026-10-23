import json
import unittest

from scripts.memory_intake import compose as C
from scripts.memory_intake.tests.helpers import candidate, entry, fake_review


class Compose(unittest.TestCase):
    def comp(self, cand=None, verdicts=None):
        return C.compose(cand or candidate(), fake_review(verdicts))

    def test_every_accepted_theorem_becomes_a_module_a_manifest_line_and_a_report_entry(self):
        cand = candidate()
        c = self.comp(cand)
        ids = [e["id"] for e in cand["entries"]]
        self.assertEqual(len(c.accepted), 3)
        self.assertEqual(sorted(c.modules), sorted(f"Tengoku/Studied/Erdos396/S{i[:12]}.lean" for i in ids))
        self.assertEqual(c.bundle, C.bundle_id("erdos-396", "ada", ids))
        rows = [json.loads(ln) for ln in c.manifest_lines]
        self.assertEqual([r["entry"] for r in rows], ids)
        r = rows[0]
        self.assertEqual((r["name"], r["target"], r["author"], r["stars"], r["source"], r["bundle"]), ("lemma_1", "erdos-396", "ada", 4, "leak-memory", c.bundle))
        self.assertEqual(r["module"], f"Tengoku.Studied.Erdos396.S{ids[0][:12]}")
        self.assertEqual(r["toolchain"], "{toolchain}")
        self.assertEqual(C.fill_toolchain(c.manifest_lines, "leanprover/lean4:v4.34.0-rc2")[0].count("{toolchain}"), 0)

    def test_the_module_is_what_the_gate_wants(self):
        c = self.comp(candidate([1]))
        (path, text), = c.modules.items()
        mod = path[: -len(".lean")].replace("/", ".")
        self.assertTrue(text.startswith("import Tengoku.Seed\n"))
        self.assertEqual(text.count("namespace "), 1)
        self.assertIn(f"namespace {mod}\n", text)
        self.assertTrue(text.rstrip().endswith(f"end {mod}"))
        self.assertIn("/-!\n# lemma_1", text)
        self.assertIn("## Main results", text)
        self.assertIn(C.squash(entry(1)["statement"]), C.squash(text))
        self.assertTrue(text.endswith("\n") and not text.endswith("\n\n"))

    def test_the_closure_is_tidied(self):
        e = entry(1, closure="import Mathlib\n\ntheorem lemma_1 (a : Nat) : a + 1 = 1 + a := by   \n\tomega\n\n\n")
        text = C.render_module(e, "erdos-396", "ada", "Tengoku.Studied.Erdos396.S000000000001")
        self.assertNotIn("import Mathlib", text)
        self.assertNotIn("\t", text)
        self.assertFalse(any(ln != ln.rstrip() for ln in text.split("\n")))

    def test_the_report_says_what_was_done_and_what_was_not(self):
        c = self.comp(candidate([1, 2]))
        r = c.report
        self.assertEqual((r["schema"], r["target"], r["author"], r["bundle"]), ("studied-bundle/1", "erdos-396", "ada", c.bundle))
        self.assertEqual(r["preflight"]["compiled"], 2)
        self.assertIn("Leak IV", r["preflight"]["how"])
        self.assertEqual([x["stars"] for x in r["rerated"]], [4, 4])
        self.assertTrue(all(x["by"] == "bar/0" for x in r["rerated"]))
        self.assertNotIn("jinshi", r, "this job runs no Jinshi and does not say it did")
        self.assertEqual(r["review"]["model"], "praiser")
        self.assertEqual(r["review"]["blocking"], 0)
        h = r["harness"][0]
        self.assertEqual((h["ticket_age_s"], h["seconds"], h["verify_ok"], h["verify_fail"], h["strategy"], h["build_verified"]), (3600, 3590, 60, 40, "control-lucid-iv", True))

    def test_returned_and_rejected_theorems_stay_out_and_become_events(self):
        cand = candidate([1, 2, 3, 4])
        ids = [e["id"] for e in cand["entries"]]
        c = self.comp(cand, {
            ids[1]: {"verdict": "return", "codes": ["bar.merit"], "merit": []},
            ids[2]: {"verdict": "return", "codes": ["bar.merit", "naming.placeholder"], "merit": []},
            ids[3]: {"verdict": "reject", "codes": ["style.sorry"], "merit": []},
        })
        self.assertEqual([v.entry["id"] for v in c.accepted], [ids[0]])
        self.assertEqual(len(c.modules), 1)
        ev = {(e["kind"], e["code"]): e for e in c.events()}
        self.assertEqual(sorted(ev), [("rejected", "style.sorry"), ("returned", "bar.merit"), ("returned", "naming.placeholder")])
        self.assertEqual(ev[("returned", "bar.merit")]["names"], ["lemma_2", "lemma_3"])
        self.assertEqual(ev[("returned", "bar.merit")]["ids"], [ids[1], ids[2]])
        self.assertTrue(all(e["username"] == "ada" and e["target"] == "erdos-396" for e in ev.values()))

    def test_nothing_accepted_makes_no_bundle(self):
        cand = candidate([1])
        c = self.comp(cand, {cand["entries"][0]["id"]: {"verdict": "return", "codes": ["bar.merit"], "merit": []}})
        self.assertEqual((c.accepted, c.modules, c.manifest_lines, c.report, c.bundle), ([], {}, [], {}, ""))
        self.assertEqual(len(c.events()), 1)

    def test_what_the_gate_would_refuse_is_returned_before_the_reviewer_is_asked(self):
        cand = candidate([1, 2, 3, 4, 5])
        es = cand["entries"]
        es[0]["quality"] = {"s": 3, "u": 0}  # not four stars
        es[1]["harness"] = {}  # no harness evidence the report could carry
        es[2]["statement"] = "theorem lemma_3 (a : Nat) : a = a"  # not what the closure declares
        es[3]["closure"] = "namespace Mine\n" + es[3]["closure"] + "\nend Mine"  # its own namespace
        c = self.comp(cand)
        got = {v.entry["name"]: (v.verdict, v.codes) for v in c.verdicts}
        self.assertEqual(got["lemma_1"], ("return", ["bar.merit"]))
        self.assertEqual(got["lemma_2"], ("return", ["gate.studied"]))
        self.assertEqual(got["lemma_3"], ("return", ["gate.studied"]))
        self.assertEqual(got["lemma_4"], ("return", ["gate.studied"]))
        self.assertEqual(got["lemma_5"][0], "accept")

    def test_the_reviewer_sees_the_modules_and_the_facts(self):
        seen = {}

        def review(modules, facts):
            seen.update(modules=modules, facts=facts)
            return {eid: {"verdict": "accept", "codes": [], "merit": ["cited"]} for eid in facts}, set()

        cand = candidate([1, 2])
        cand["entries"][1]["closure"] += "\n-- uses lemma_1\ntheorem uses_1 : True := by\n  have := lemma_1 0\n  trivial"
        cand["entries"][1]["closure"] = cand["entries"][0]["closure"] + "\n" + cand["entries"][1]["closure"]
        C.compose(cand, review)
        self.assertEqual(len(seen["modules"]), 2)
        f = {v["module"].rsplit(".", 1)[1]: v for v in seen["facts"].values()}
        self.assertEqual(sorted(v["stars"] for v in f.values()), [4, 4])
        self.assertEqual(sum(v["cited_by"] for v in f.values()), 1, "lemma_2's closure carries lemma_1 and uses it")

    def test_a_candidate_out_of_shape_is_refused_whole(self):
        for bad, why in (
            (None, "not an object"), ({}, "target or author"), (candidate(target="Bad Target"), "target or author"), (candidate(author="x y"), "target or author"),
            ({**candidate(), "entries": []}, "entries"), ({**candidate(), "entries": [entry(i) for i in range(11)]}, "entries"),
            ({**candidate(), "entries": [{**entry(1), "closure": ""}]}, "lacks"), ({**candidate(), "entries": [{**entry(1), "id": "zz"}]}, "well formed"),
            ({**candidate(), "entries": [entry(1), entry(1)]}, "share"),
        ):
            with self.assertRaises(ValueError, msg=str(why)) as cm:
                C.compose(bad, fake_review())
            self.assertIn(why, str(cm.exception))

    def test_pascal_and_module_names(self):
        self.assertEqual(C.pascal("erdos-396"), "Erdos396")
        self.assertEqual(C.pascal("collatz"), "Collatz")
        self.assertEqual(C.entry_module("erdos-396", "0123456789abcdef")[0], "Tengoku.Studied.Erdos396.S0123456789ab")

    def test_the_bundle_id_does_not_depend_on_order(self):
        self.assertEqual(C.bundle_id("t", "a", ["2", "1"]), C.bundle_id("t", "a", ["1", "2"]))
        self.assertNotEqual(C.bundle_id("t", "a", ["1"]), C.bundle_id("t", "b", ["1"]))


if __name__ == "__main__":
    unittest.main()
