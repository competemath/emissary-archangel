"""A name that two modules of a library declare is judged once per copy, and Gate 2 names only the name.

navier-stokes-euler (2026-10-16) ships its challenge statements with `sorry` (ComparatorChallenges) and the proofs of the same names in NavierStokes/ComparatorSolution. Gate 2 passed the
solution's copy and failed the challenge's copy, and `bundle.py compose` read the failure as the solution's: the headline module was dropped as "names a declaration with sorry that the
pruning leaves out". Where the module's own copy passed (the module is in passed.json with that name), a failure of the name belongs to another module's copy."""

import collections
import json
import sys
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(HERE / "tests"))
import test_faithful_imports as tfi  # the toy library and its compose
import test_keep_closure as tkc  # FakeModule

PASS = "GATE2B_PASS old=Toy.uses_one_pos new=Toy.uses_one_pos via=equal\n"
FAIL_NAME = "GATE2B_FAIL old=Toy.uses_one_pos new=Toy.uses_one_pos reason=uses_sorry\n"
# the challenge: the same theorem, closed with `sorry`, in a module of its own
CHALLENGE = "import Toy.A\n\nnamespace Toy\n\ntheorem uses_one_pos : 0 < one := sorry\n\nend Toy\n"
CHALLENGE_ROWS = [["Toy.uses_one_pos", 5, 5]]


class DuplicateNames(unittest.TestCase):
    def compose(self, gate2, modules=None, **kw):
        return tfi.Compose("compose").compose(gate2=gate2, extra_modules=modules, **kw)

    def shipped(self, d, rel):
        return (d / "bundle-proposed" / "Tengoku" / "ToyLib" / rel).exists()

    def report(self, d):
        return json.loads((d / "bundle-proposed" / "report.json").read_text())

    def manifest(self, d):
        return [json.loads(ln)["name"] for ln in (d / "bundle-proposed" / "manifest.jsonl").read_text().splitlines()]

    def test_the_copy_that_passed_ships_although_another_modules_copy_of_the_name_failed_for_sorry(self):
        d, r = self.compose(PASS + FAIL_NAME, {"Toy/C": (CHALLENGE, CHALLENGE_ROWS)})
        self.assertEqual(r.returncode, 0, r.stderr)
        self.assertTrue(self.shipped(d, "Toy/B.lean"), self.report(d)["left_out"])
        self.assertEqual(self.manifest(d), ["Toy.uses_one_pos"])
        self.assertNotIn("names a declaration with sorry", json.dumps(self.report(d)))

    def test_the_challenge_module_itself_does_not_ship(self):
        d, r = self.compose(PASS + FAIL_NAME, {"Toy/C": (CHALLENGE, CHALLENGE_ROWS)})
        self.assertEqual(r.returncode, 0, r.stderr)
        self.assertFalse(self.shipped(d, "Toy/C.lean"))

    def test_a_module_that_names_the_passed_copy_by_its_name_ships_too(self):
        # D proves a theorem with `uses_one_pos` (B's copy): the failure of the name is the challenge's, so B's block is not a failed block for D's text to stumble on
        d_text = "import Toy.B\n\nnamespace Toy\n\ntheorem d_uses : 0 < one := uses_one_pos\n\nend Toy\n"
        d, r = self.compose(
            PASS + "GATE2B_PASS old=Toy.d_uses new=Toy.d_uses via=equal\n" + FAIL_NAME,
            {"Toy/C": (CHALLENGE, CHALLENGE_ROWS), "Toy/D": (d_text, [["Toy.d_uses", 5, 5]])},
            passed={"Toy.B": ["Toy.uses_one_pos"], "Toy.D": ["Toy.d_uses"]},
            keep=[["Toy.D", "Toy.d_uses"], ["Toy.B", "Toy.uses_one_pos"], ["Toy.A", "Toy.one_pos"], ["Toy.A", "Toy.one"]],
        )
        self.assertEqual(r.returncode, 0, r.stderr)
        self.assertTrue(self.shipped(d, "Toy/D.lean"), self.report(d)["left_out"])
        self.assertTrue(self.shipped(d, "Toy/B.lean"))
        self.assertEqual(sorted(self.manifest(d)), ["Toy.d_uses", "Toy.uses_one_pos"])

    def test_without_a_duplicate_nothing_changes(self):
        d, r = self.compose(PASS)
        self.assertEqual(r.returncode, 0, r.stderr)
        self.assertTrue(self.shipped(d, "Toy/B.lean"))
        self.assertEqual(self.manifest(d), ["Toy.uses_one_pos"])


class Resolution(unittest.TestCase):
    """keep_closure.close, directly: a full name that two modules declare resolves to the copy the naming module can see."""

    def setup(self, importer_lines):
        challenge = tkc.FakeModule(["theorem Toy.dup : True := by", "  sorry"], [(1, 2)])  # closed with sorry, imported by nobody
        solution = tkc.FakeModule(["theorem kept : True := by", "  exact Toy.dup", "theorem Toy.dup : True := by", "  trivial"], [(1, 2), (3, 4)])
        importer = tkc.FakeModule(importer_lines, [(3, 4)])
        modules = {"Toy.Ch": challenge, "Toy.So": solution, "Toy.Im": importer}
        sidecars = {"Toy.Ch": {"Toy.dup": (1, 2)}, "Toy.So": {"Toy.kept": (1, 2), "Toy.dup": (3, 4)}, "Toy.Im": {"Toy.use_dup": (3, 4)}}
        return modules, sidecars

    def test_a_module_that_declares_the_name_itself_is_not_stopped_by_the_other_copy(self):
        modules, sidecars = self.setup(["import Toy.So", "", "theorem Toy.use_dup : True := by", "  trivial"])
        added, unresolved = __import__("keep_closure").close(modules, sidecars, collections.defaultdict(set, {"Toy.So": {(1, 2)}}))
        self.assertEqual(unresolved, {})
        self.assertEqual(added, 1)  # its own `Toy.dup`

    def test_a_module_that_imports_the_passed_copy_resolves_to_it(self):
        modules, sidecars = self.setup(["import Toy.So", "", "theorem Toy.use_dup : True := by", "  exact Toy.dup"])
        added, unresolved = __import__("keep_closure").close(modules, sidecars, collections.defaultdict(set, {"Toy.Im": {(3, 4)}}))
        self.assertEqual(unresolved, {})
        self.assertEqual(added, 1)

    def test_a_module_that_imports_the_challenge_resolves_to_the_challenge_and_is_stopped_by_it(self):
        # the rule the filter must not break: the copy it can see is the one with the sorry
        modules, sidecars = self.setup(["import Toy.Ch", "", "theorem Toy.use_dup : True := by", "  exact Toy.dup"])
        _, unresolved = __import__("keep_closure").close(modules, sidecars, collections.defaultdict(set, {"Toy.Im": {(3, 4)}}))
        self.assertEqual(unresolved, {"Toy.Im": {"Toy.dup"}})

    def test_when_no_copy_is_visible_the_names_are_resolved_as_before(self):
        modules, sidecars = self.setup(["", "", "theorem Toy.use_dup : True := by", "  exact Toy.dup"])  # imports nothing
        _, unresolved = __import__("keep_closure").close(modules, sidecars, collections.defaultdict(set, {"Toy.Im": {(3, 4)}}))
        self.assertEqual(unresolved, {"Toy.Im": {"Toy.dup"}})  # the sorry copy is among the candidates, as it was


if __name__ == "__main__":
    unittest.main()
