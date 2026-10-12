"""tree_verify.py: the bundle is built in the tree's environment before it is cut; what ships is byte for byte what was built there."""

import json
import sys
import tempfile
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(HERE))
import tree_verify as tv  # noqa: E402

UMBRELLA = "".join(f"import Tengoku.ToyLib.Toy.{m}\n" for m in "ABCD")
FILES = {
    "Tengoku/ToyLib.lean": UMBRELLA,
    "Tengoku/ToyLib/Deps.lean": "-- ToyLib: a factory bundle\n",
    "Tengoku/ToyLib/Toy/A.lean": "theorem a : 1 = 1 := rfl\n",
    "Tengoku/ToyLib/Toy/B.lean": "import Tengoku.ToyLib.Toy.A\n\ntheorem b : 2 = 2 := rfl\n",
    "Tengoku/ToyLib/Toy/C.lean": "theorem c : 3 = 3 := rfl\n",
    "Tengoku/ToyLib/Toy/D.lean": "import Tengoku.ToyLib.Toy.C\n\ntheorem d : 4 = 4 := rfl\n",
}
LOG_C_FAILS = """✔ [10/14] Built Tengoku.ToyLib.Toy.B (2.1s)
error: Tengoku/ToyLib/Toy/C.lean:1:9: type mismatch
error: Lean exited with code 1
Some required targets logged failures:
- Tengoku.ToyLib.Toy.C
error: build failed
"""


def write(root: Path, files: dict[str, str]) -> Path:
    for rel, text in files.items():
        p = root / rel
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(text)
    return root


class Fixture(unittest.TestCase):
    def setUp(self):
        self.d = Path(tempfile.mkdtemp())
        self.bundle = write(self.d / "bundle", FILES)
        self.tree = write(self.d / "tree", {"Tengoku/ToyLib.lean": "import Tengoku.ToyLib.Toy.A\n", "Tengoku/ToyLib/Toy/A.lean": "theorem a : 1 = 1 := rfl\n"})
        self.out = self.d / "out"

    def apply(self):
        tv.main(["apply", "--bundle", str(self.bundle), "--tree", str(self.tree), "--out", str(self.out)])

    def collect(self, log: str):
        (self.d / "build.log").write_text(log)
        tv.main(["collect", "--new", str(self.out / "new.json"), "--log", str(self.d / "build.log"), "--out", str(self.out), "--bundle", str(self.bundle)])


class Apply(Fixture):
    def test_the_modules_the_tree_has_are_not_new_and_the_marker_is_no_module(self):
        files = tv.bl.read_bundle(self.bundle)
        new = tv.new_modules(files, "ToyLib", UMBRELLA.split("\n")[0] + "\n")
        self.assertEqual(sorted(new), ["Tengoku.ToyLib.Toy.B", "Tengoku.ToyLib.Toy.C", "Tengoku.ToyLib.Toy.D"])

    def test_without_a_tree_umbrella_every_module_is_new(self):
        files = tv.bl.read_bundle(self.bundle)
        self.assertEqual(len(tv.new_modules(files, "ToyLib", None)), 4)

    def test_apply_copies_the_new_modules_into_the_tree_and_lists_the_targets(self):
        self.apply()
        self.assertEqual((self.out / "targets.txt").read_text().split(), ["Tengoku.ToyLib.Toy.B", "Tengoku.ToyLib.Toy.C", "Tengoku.ToyLib.Toy.D"])
        for m in "BCD":
            self.assertEqual((self.tree / f"Tengoku/ToyLib/Toy/{m}.lean").read_text(), FILES[f"Tengoku/ToyLib/Toy/{m}.lean"])
        new = json.loads((self.out / "new.json").read_text())
        self.assertEqual(new["ns"], "ToyLib")
        self.assertEqual(new["modules"]["Tengoku.ToyLib.Toy.B"]["sha256"], tv.sha256(FILES["Tengoku/ToyLib/Toy/B.lean"].encode()))

    def test_a_module_the_tree_has_is_left_as_the_tree_has_it(self):
        (self.tree / "Tengoku/ToyLib/Toy/A.lean").write_text("theorem a : 1 = 1 := rfl -- the tree's own version\n")
        self.apply()
        self.assertIn("the tree's own version", (self.tree / "Tengoku/ToyLib/Toy/A.lean").read_text())


class Collect(Fixture):
    def test_errors_sorry_and_failing_targets_are_failures(self):
        log = "error: Tengoku/ToyLib/Toy/C.lean:1:9: x\nwarning: Tengoku/ToyLib/Toy/B.lean:3:0: declaration uses `sorry`\n- Tengoku.ToyLib.Toy.D\nerror: Tengoku/Other/X.lean:1:0: elsewhere\n"
        self.assertEqual(tv.failures_from_log(log, "ToyLib"), {"Tengoku.ToyLib.Toy.C", "Tengoku.ToyLib.Toy.B", "Tengoku.ToyLib.Toy.D"})

    def test_a_guillemet_module_is_spelled_as_lean_spells_it(self):
        log = "error: Tengoku/ToyLib/Toy/A-B.lean:1:0: x\n"
        self.assertEqual(tv.failures_from_log(log, "ToyLib"), {"Tengoku.ToyLib.Toy.«A-B»"})

    def test_a_refused_module_and_its_importers_are_out_and_the_rest_is_ok_with_its_bytes(self):
        self.apply()
        self.collect(LOG_C_FAILS)
        self.assertEqual((self.out / "failing.txt").read_text().split(), ["Toy.C"])  # the library's own name, what `compose --tree-failures` takes
        ok = json.loads((self.out / "ok.json").read_text())
        self.assertEqual(sorted(ok), ["Tengoku.ToyLib.Toy.B"])  # D imports C: not verified, and it goes with it
        self.assertEqual(ok["Tengoku.ToyLib.Toy.B"], tv.sha256(FILES["Tengoku/ToyLib/Toy/B.lean"].encode()))
        self.assertIn("1 built in the tree, 1 refused", (self.out / "summary.txt").read_text())

    def test_a_clean_build_accepts_everything(self):
        self.apply()
        self.collect("".join(f"✔ [{i}/9] Built Tengoku.ToyLib.Toy.{m} (1s)\n" for i, m in enumerate("BCD")) + "Build completed successfully.\n")
        self.assertEqual((self.out / "failing.txt").read_text(), "")
        self.assertEqual(len(json.loads((self.out / "ok.json").read_text())), 3)

    def test_a_module_the_build_never_reached_is_not_verified(self):
        self.apply()
        self.collect("✔ [1/9] Built Tengoku.ToyLib.Toy.B (1s)\n✔ [2/9] Built Tengoku.ToyLib.Toy.C (1s)\nBuild completed successfully.\n")  # D: no line, no error
        self.assertEqual((self.out / "failing.txt").read_text().split(), ["Toy.D"])
        self.assertEqual(sorted(json.loads((self.out / "ok.json").read_text())), ["Tengoku.ToyLib.Toy.B", "Tengoku.ToyLib.Toy.C"])

    def test_a_build_that_ran_out_of_time_can_still_ship_what_it_built(self):
        self.apply()
        (self.d / "build.log").write_text("✔ [1/9] Built Tengoku.ToyLib.Toy.C (1s)\n✔ [2/9] Built Tengoku.ToyLib.Toy.D (1s)\n")  # killed: B was never reached
        tv.main(["collect", "--new", str(self.out / "new.json"), "--log", str(self.d / "build.log"), "--out", str(self.out), "--bundle", str(self.bundle), "--allow-unfinished"])
        self.assertEqual((self.out / "failing.txt").read_text().split(), ["Toy.B"])
        self.assertEqual(sorted(json.loads((self.out / "ok.json").read_text())), ["Tengoku.ToyLib.Toy.C", "Tengoku.ToyLib.Toy.D"])
        self.assertIn("did not finish", (self.out / "summary.txt").read_text())

    def test_a_partial_build_still_refuses_what_it_saw_fail(self):
        self.apply()
        (self.d / "build.log").write_text("✔ [1/9] Built Tengoku.ToyLib.Toy.C (1s)\nerror: Tengoku/ToyLib/Toy/B.lean:1:0: x\n")
        tv.main(["collect", "--new", str(self.out / "new.json"), "--log", str(self.d / "build.log"), "--out", str(self.out), "--bundle", str(self.bundle), "--allow-unfinished"])
        self.assertEqual((self.out / "failing.txt").read_text().split(), ["Toy.B", "Toy.D"])  # D was not reached either
        self.assertEqual(sorted(json.loads((self.out / "ok.json").read_text())), ["Tengoku.ToyLib.Toy.C"])

    def test_a_finished_build_says_nothing_about_a_budget(self):
        self.apply()
        self.collect(LOG_C_FAILS)
        self.assertNotIn("did not finish", (self.out / "summary.txt").read_text())

    def test_a_log_without_an_ending_is_refused(self):
        self.apply()
        with self.assertRaises(SystemExit) as r:
            self.collect("✔ [1/9] Built Tengoku.ToyLib.Toy.B (1s)\n")
        self.assertIn("no ending", str(r.exception.code))

    def test_the_dependents_are_transitive(self):
        graph = {"X": [], "Y": ["X"], "Z": ["Y"], "W": []}
        self.assertEqual(tv.dependents({"X"}, graph), {"Y", "Z"})

    def test_the_library_name_of_a_module(self):
        self.assertEqual(tv.library_module("Tengoku.LeanPool.LeanPool.Foo.Bar", "LeanPool"), "LeanPool.Foo.Bar")


AXIOMS_CLEAN = "axioms: 41 declarations checked, 0 with non-standard axioms\n"
AXIOMS_ONE_BAD = "AXIOM\tTengoku.ToyLib.Toy.B\tToy.instReprSequent\tlcProof\naxioms: 41 declarations checked, 1 with non-standard axioms\n"


class Axioms(Fixture):
    """The queue's axiom check, on the modules that built (2026-10-12: lean-pool part 10 compiled and was rejected on `PDL.instReprSequent depends on [lcProof]`)."""

    def collect_with(self, log: str, axioms: str):
        (self.d / "axioms.txt").write_text(axioms)
        (self.d / "build.log").write_text(log)
        tv.main(["collect", "--new", str(self.out / "new.json"), "--log", str(self.d / "build.log"), "--out", str(self.out), "--bundle", str(self.bundle), "--axioms", str(self.d / "axioms.txt")])

    BUILT_ALL = "".join(f"✔ [{i}/9] Built Tengoku.ToyLib.Toy.{m} (1s)\n" for i, m in enumerate("BCD")) + "Build completed successfully.\n"

    def test_the_modules_to_check_are_the_ones_that_built_without_guillemets(self):
        self.apply()
        self.collect(LOG_C_FAILS)
        self.assertEqual((self.out / "built.txt").read_text().split(), ["Tengoku.ToyLib.Toy.B"])

    def test_a_module_with_a_dash_in_its_name_is_listed_without_guillemets_and_matched_with_or_without(self):
        write(self.bundle, {"Tengoku/ToyLib/Toy/A-B.lean": "theorem ab : 5 = 5 := rfl\n", "Tengoku/ToyLib.lean": UMBRELLA + "import Tengoku.ToyLib.Toy.«A-B»\n"})
        self.apply()
        self.collect("✔ [1/9] Built Tengoku.ToyLib.Toy.«A-B» (1s)\nBuild completed successfully.\n")
        self.assertIn("Tengoku.ToyLib.Toy.A-B", (self.out / "built.txt").read_text().split())  # what `String.toName` splits on dots: no « » in the file
        self.assertNotIn("«", (self.out / "built.txt").read_text())
        (self.d / "axioms.txt").write_text("AXIOM\tTengoku.ToyLib.Toy.A-B\td\tlcProof\naxioms: 3 declarations checked, 1 with non-standard axioms\n")
        tv.main(["collect", "--new", str(self.out / "new.json"), "--log", str(self.d / "build.log"), "--out", str(self.out), "--axioms", str(self.d / "axioms.txt")])
        self.assertIn("Toy.«A-B»", (self.out / "failing.txt").read_text().split())

    def test_a_module_with_a_declaration_on_an_axiom_is_refused_with_its_importers(self):
        self.apply()
        self.collect_with(self.BUILT_ALL, AXIOMS_ONE_BAD)  # B built, and has an offender: D does not import B, C neither: only B goes
        self.assertEqual((self.out / "failing.txt").read_text().split(), ["Toy.B"])
        self.assertEqual(sorted(json.loads((self.out / "ok.json").read_text())), ["Tengoku.ToyLib.Toy.C", "Tengoku.ToyLib.Toy.D"])
        self.assertIn("1 on an axiom", (self.out / "summary.txt").read_text())
        self.assertIn("Toy.B: Toy.instReprSequent [lcProof]", (self.out / "summary.txt").read_text())

    def test_what_imports_an_offender_goes_with_it(self):
        self.apply()
        bad_c = AXIOMS_ONE_BAD.replace("Toy.B", "Toy.C")
        self.collect_with(self.BUILT_ALL, bad_c)  # D imports C
        self.assertEqual((self.out / "failing.txt").read_text().split(), ["Toy.C"])
        self.assertEqual(sorted(json.loads((self.out / "ok.json").read_text())), ["Tengoku.ToyLib.Toy.B"])

    def test_a_clean_check_changes_nothing(self):
        self.apply()
        self.collect_with(self.BUILT_ALL, AXIOMS_CLEAN)
        self.assertEqual((self.out / "failing.txt").read_text(), "")

    def test_guillemets_are_compared_without_them(self):
        self.assertEqual(tv.plain("Tengoku.L.«A-B».C"), "Tengoku.L.A-B.C")
        got = tv.axiom_offenders("AXIOM\tTengoku.L.A-B\td\tlcProof\naxioms: 1 declarations checked, 1 with non-standard axioms\n", {"Tengoku.L.«A-B»"})
        self.assertEqual(got, {"Tengoku.L.«A-B»": ["d [lcProof]"]})

    def test_an_offender_outside_the_new_modules_is_not_ours(self):
        got = tv.axiom_offenders("AXIOM\tTengoku.Other.X\td\tlcProof\naxioms: 5 declarations checked, 1 with non-standard axioms\n", {"Tengoku.ToyLib.Toy.B"})
        self.assertEqual(got, {})

    def test_a_check_that_never_finished_is_refused(self):
        with self.assertRaises(SystemExit) as r:
            tv.axiom_offenders("AXIOM\tTengoku.ToyLib.Toy.B\td\tlcProof\n", {"Tengoku.ToyLib.Toy.B"})
        self.assertIn("no ending", str(r.exception.code))

    def test_a_check_whose_output_is_cut_short_is_refused(self):
        with self.assertRaises(SystemExit) as r:
            tv.axiom_offenders("axioms: 9 declarations checked, 2 with non-standard axioms\n", {"Tengoku.ToyLib.Toy.B"})
        self.assertIn("incomplete", str(r.exception.code))

    def test_several_offenders_in_one_module_are_one_refusal(self):
        text = "AXIOM\tM.A\tx\tlcProof\nAXIOM\tM.A\ty\tLean.ofReduceBool\naxioms: 3 declarations checked, 2 with non-standard axioms\n"
        self.assertEqual(tv.axiom_offenders(text, {"M.A"}), {"M.A": ["x [lcProof]", "y [Lean.ofReduceBool]"]})


class Check(Fixture):
    def verified(self):
        self.apply()
        self.collect(LOG_C_FAILS)

    def final_bundle(self, drop=("C", "D")):
        files = {k: v for k, v in FILES.items() if not any(k.endswith(f"/Toy/{m}.lean") for m in drop)}
        return write(self.d / "final", files)

    def check(self, bundle):
        tv.main(["check", "--bundle", str(bundle), "--new", str(self.out / "new.json"), "--ok", str(self.out / "ok.json")])

    def test_a_bundle_that_ships_only_what_was_built_passes(self):
        self.verified()
        self.check(self.final_bundle())

    def test_a_refused_module_that_still_ships_fails(self):
        self.verified()
        with self.assertRaises(SystemExit) as r:
            self.check(self.final_bundle(drop=()))
        self.assertIn("Tengoku.ToyLib.Toy.C: ships, but the tree's build did not accept it", str(r.exception.code))

    def test_a_module_that_ships_with_other_bytes_fails(self):
        self.verified()
        b = self.final_bundle()
        (b / "Tengoku/ToyLib/Toy/B.lean").write_text(FILES["Tengoku/ToyLib/Toy/B.lean"] + "-- changed after the build\n")
        with self.assertRaises(SystemExit) as r:
            self.check(b)
        self.assertIn("other bytes", str(r.exception.code))

    def test_a_module_the_tree_already_had_is_not_checked(self):
        self.verified()
        b = self.final_bundle()
        (b / "Tengoku/ToyLib/Toy/A.lean").write_text("theorem a : 1 = 1 := rfl -- the bundle's version differs: the tree's own is what was built against\n")
        self.check(b)


if __name__ == "__main__":
    unittest.main()
