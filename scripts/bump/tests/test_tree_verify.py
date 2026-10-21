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

    def test_a_build_that_finished_built_every_target_even_one_without_a_built_line(self):
        self.apply()
        self.collect("✔ [1/9] Built Tengoku.ToyLib.Toy.B (1s)\n✔ [2/9] Built Tengoku.ToyLib.Toy.C (1s)\nBuild completed successfully.\n")  # D: no line, no error (Navier 2026-10-20: 67 of 917)
        self.assertEqual((self.out / "failing.txt").read_text(), "")
        self.assertEqual(sorted(json.loads((self.out / "ok.json").read_text())), ["Tengoku.ToyLib.Toy.B", "Tengoku.ToyLib.Toy.C", "Tengoku.ToyLib.Toy.D"])

    def test_a_build_that_failed_and_stopped_did_not_reach_a_module_with_no_line(self):
        self.apply()
        self.collect(LOG_C_FAILS)  # B built; C failed and D imports it; there is no evidence about a module that is not downstream of the failure
        (self.d / "build.log").write_text("error: Tengoku/ToyLib/Toy/B.lean:1:0: x\nSome required targets logged failures:\n- Tengoku.ToyLib.Toy.B\nerror: build failed\n")
        tv.main(["collect", "--new", str(self.out / "new.json"), "--log", str(self.d / "build.log"), "--out", str(self.out), "--bundle", str(self.bundle)])
        self.assertEqual((self.out / "failing.txt").read_text().split(), ["Toy.B", "Toy.C", "Toy.D"])  # C and D: the build stopped at B's failure and never got to them
        self.assertEqual(json.loads((self.out / "ok.json").read_text()), {})

    def test_a_build_that_ran_out_of_time_can_still_ship_what_it_built(self):
        self.apply()
        (self.d / "build.log").write_text("✔ [1/9] Built Tengoku.ToyLib.Toy.C (1s)\n✔ [2/9] Built Tengoku.ToyLib.Toy.D (1s)\n")  # killed: B was never reached
        tv.main(["collect", "--new", str(self.out / "new.json"), "--log", str(self.d / "build.log"), "--out", str(self.out), "--bundle", str(self.bundle), "--allow-unfinished"])
        self.assertEqual((self.out / "failing.txt").read_text().split(), ["Toy.B"])
        self.assertEqual(sorted(json.loads((self.out / "ok.json").read_text())), ["Tengoku.ToyLib.Toy.C", "Tengoku.ToyLib.Toy.D"])
        self.assertIn("did not finish", (self.out / "summary.txt").read_text())

    def test_a_partial_build_accepts_a_module_with_no_line_when_a_built_module_imports_it(self):
        self.apply()
        (self.d / "build.log").write_text("✔ [1/9] Built Tengoku.ToyLib.Toy.D (1s)\n")  # killed: C has no line, but D imports C and was built; B was never reached
        tv.main(["collect", "--new", str(self.out / "new.json"), "--log", str(self.d / "build.log"), "--out", str(self.out), "--bundle", str(self.bundle), "--allow-unfinished"])
        self.assertEqual((self.out / "failing.txt").read_text().split(), ["Toy.B"])
        self.assertEqual(sorted(json.loads((self.out / "ok.json").read_text())), ["Tengoku.ToyLib.Toy.C", "Tengoku.ToyLib.Toy.D"])

    def test_the_second_build_s_ending_is_not_the_ending_of_the_first(self):
        self.apply()
        log = "✔ [1/9] Built Tengoku.ToyLib.Toy.C (1s)\n" + tv.DUPS_MARKER + "\n✔ [1/9] Built Tengoku.ToyLib.Toy.D (1s)\nBuild completed successfully.\n"  # the first build was killed
        (self.d / "build.log").write_text(log)
        with self.assertRaises(SystemExit) as r:
            tv.main(["collect", "--new", str(self.out / "new.json"), "--log", str(self.d / "build.log"), "--out", str(self.out), "--bundle", str(self.bundle)])
        self.assertIn("no ending", str(r.exception.code))
        tv.main(["collect", "--new", str(self.out / "new.json"), "--log", str(self.d / "build.log"), "--out", str(self.out), "--bundle", str(self.bundle), "--allow-unfinished"])
        self.assertEqual((self.out / "failing.txt").read_text().split(), ["Toy.B"])  # B: no line, and the success below the marker is not about it
        self.assertIn("did not finish", (self.out / "summary.txt").read_text())

    def test_a_second_build_that_finished_does_not_make_an_unfinished_first_one_complete(self):
        self.apply()
        (self.d / "build.log").write_text("✔ [1/9] Built Tengoku.ToyLib.Toy.C (1s)\n" + tv.DUPS_MARKER + "\nBuild completed successfully.\n")
        tv.main(["collect", "--new", str(self.out / "new.json"), "--log", str(self.d / "build.log"), "--out", str(self.out), "--bundle", str(self.bundle), "--allow-unfinished"])
        self.assertEqual((self.out / "failing.txt").read_text().split(), ["Toy.B", "Toy.D"])  # C has a line; B and D have none, nothing built imports them, and the success below the marker is not about this build

    def test_a_partial_build_that_built_nothing_never_got_going_and_is_refused(self):
        """Navier 2026-10-21: the toolchain did not download, `lake build` ended after seven seconds; 0 of 1,066 built and the run was a success with an empty cut"""
        self.apply()
        (self.d / "build.log").write_text("error: could not download file from 'https://releases.lean-lang.org/x.tar.zst'\ninfo: caused by: [35] SSL connect error\n")
        with self.assertRaises(SystemExit) as r:
            tv.main(["collect", "--new", str(self.out / "new.json"), "--log", str(self.d / "build.log"), "--out", str(self.out), "--bundle", str(self.bundle), "--allow-unfinished"])
        self.assertIn("never got going", str(r.exception.code))

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


CLASH_B = "CLASH\tTengoku.ToyLib.Toy.B\tTengoku.Other.Lib.X\t3\tIndicator.«term𝟭_[_]»\nclashes: 1 module pair(s), 3 name(s)\n"


class Clashes(Fixture):
    """Two modules that declare the same name stop `import Tengoku.All` (lean-pool part 10, 2026-10-12: its vendored copy of AddCombi against the tree's AddCombi; the
    merge queue found it, one part at a time). The new module of the pair is refused; the module already in the tree stays."""

    BUILT_ALL = Axioms.BUILT_ALL

    def collect_with(self, clashes: str):
        (self.d / "clashes.txt").write_text(clashes)
        (self.d / "build.log").write_text(self.BUILT_ALL)
        tv.main(["collect", "--new", str(self.out / "new.json"), "--log", str(self.d / "build.log"), "--out", str(self.out), "--bundle", str(self.bundle), "--clashes", str(self.d / "clashes.txt")])

    def test_the_new_module_of_a_clashing_pair_is_refused_and_the_incumbent_is_not_ours(self):
        self.apply()
        self.collect_with(CLASH_B)
        self.assertEqual((self.out / "failing.txt").read_text().split(), ["Toy.B"])
        self.assertEqual(sorted(json.loads((self.out / "ok.json").read_text())), ["Tengoku.ToyLib.Toy.C", "Tengoku.ToyLib.Toy.D"])
        summary = (self.out / "summary.txt").read_text()
        self.assertIn("1 on a name another module declares", summary)
        self.assertIn("Toy.B: Indicator.«term𝟭_[_]» (+2 more) also declared by Tengoku.Other.Lib.X", summary)

    def test_the_list_the_axiom_check_imports_is_without_the_clashing_module_and_its_importers(self):
        """The axiom check imports `built.txt` in one environment: a module that shares a name with the tree stops it (lana-oka, 2026-10-19), so it is out of the list before that runs."""
        self.apply()
        self.collect_with(CLASH_B)
        self.assertEqual((self.out / "built.txt").read_text().split(), ["Tengoku.ToyLib.Toy.C", "Tengoku.ToyLib.Toy.D"])
        self.collect_with(CLASH_B.replace("Toy.B", "Toy.C"))  # D imports C
        self.assertEqual((self.out / "built.txt").read_text().split(), ["Tengoku.ToyLib.Toy.B"])

    def test_the_pair_may_name_the_new_module_on_either_side(self):
        got = tv.clash_offenders("CLASH\tTengoku.Other.Lib.X\tTengoku.ToyLib.Toy.B\t1\tfoo\nclashes: 1 module pair(s), 1 name(s)\n", {"Tengoku.ToyLib.Toy.B"})
        self.assertEqual(got, {"Tengoku.ToyLib.Toy.B": ["foo also declared by Tengoku.Other.Lib.X"]})

    def test_what_imports_a_clashing_module_goes_with_it(self):
        self.apply()
        self.collect_with(CLASH_B.replace("Toy.B", "Toy.C"))  # D imports C
        self.assertEqual((self.out / "failing.txt").read_text().split(), ["Toy.C"])
        self.assertEqual(sorted(json.loads((self.out / "ok.json").read_text())), ["Tengoku.ToyLib.Toy.B"])

    def test_a_pair_of_two_modules_that_are_both_new_refuses_both(self):
        got = tv.clash_offenders("CLASH\tM.A\tM.B\t1\tfoo\nclashes: 1 module pair(s), 1 name(s)\n", {"M.A", "M.B"})
        self.assertEqual(sorted(got), ["M.A", "M.B"])

    def test_a_clash_between_two_modules_that_are_not_new_is_not_ours(self):
        self.assertEqual(tv.clash_offenders("CLASH\tA.X\tA.Y\t1\tfoo\nclashes: 1 module pair(s), 1 name(s)\n", {"M.A"}), {})

    def test_guillemets_are_compared_without_them(self):
        got = tv.clash_offenders("CLASH\tTengoku.L.A-B\tTengoku.O.X\t1\tfoo\nclashes: 1 module pair(s), 1 name(s)\n", {"Tengoku.L.«A-B»"})
        self.assertEqual(list(got), ["Tengoku.L.«A-B»"])

    def test_a_clean_check_changes_nothing(self):
        self.apply()
        self.collect_with("clashes: 0 module pair(s), 0 name(s)\n")
        self.assertEqual((self.out / "failing.txt").read_text(), "")

    def test_a_check_that_never_finished_is_refused(self):
        with self.assertRaises(SystemExit) as r:
            tv.clash_offenders("CLASH\tM.A\tM.B\t1\tfoo\n", {"M.A"})
        self.assertIn("no ending", str(r.exception.code))

    def test_a_check_whose_output_is_cut_short_is_refused(self):
        with self.assertRaises(SystemExit) as r:
            tv.clash_offenders("clashes: 2 module pair(s), 5 name(s)\n", {"M.A"})
        self.assertIn("incomplete", str(r.exception.code))

    def test_clashes_and_axioms_are_both_applied(self):
        self.apply()
        (self.d / "axioms.txt").write_text(AXIOMS_ONE_BAD.replace("Toy.B", "Toy.C"))
        (self.d / "clashes.txt").write_text(CLASH_B)
        (self.d / "build.log").write_text(self.BUILT_ALL)
        tv.main(["collect", "--new", str(self.out / "new.json"), "--log", str(self.d / "build.log"), "--out", str(self.out), "--bundle", str(self.bundle), "--axioms", str(self.d / "axioms.txt"), "--clashes", str(self.d / "clashes.txt")])
        self.assertEqual((self.out / "failing.txt").read_text().split(), ["Toy.B", "Toy.C"])
        self.assertEqual(json.loads((self.out / "ok.json").read_text()), {})  # D imports C


REFUSAL = "U.lean:3:0: error: import Tengoku.ToyLib.Toy.C failed, environment already contains 'Indicator.«term𝟭_[_]»' from Tengoku.Tree.Lib.Indicator\n"


class UnionImport(Fixture):
    """The queue's last step imports the whole tree (`import Tengoku.All`); lean-pool part 10 was rejected there on a name two libraries declare, twice, after a static scan of the
    oleans had missed it (the tree's module is a module-system file: its olean has a public part and a private part). Lean itself is asked instead: a file that imports every module
    of the tree and the new ones is elaborated, its refusal names the pair, the new module of the pair goes (with its importers), and the file is elaborated again."""

    def prepare(self, built=("Tengoku.ToyLib.Toy.B", "Tengoku.ToyLib.Toy.C", "Tengoku.ToyLib.Toy.D")):
        self.apply()
        (self.d / "built.txt").write_text("".join(m + "\n" for m in built))
        (self.d / "excluded.txt").write_text("")

    def union_input(self, *extra):
        tv.main(["union-input", *extra, "--new", str(self.out / "new.json"), "--keep", str(self.d / "built.txt"), "--excluded", str(self.d / "excluded.txt"), "--out", str(self.d / "U.lean")])
        return (self.d / "U.lean").read_text().split("\n")

    def union_next(self, message: str, bundle=True):
        (self.d / "msg.txt").write_text(message)
        args = ["union-next", "--message", str(self.d / "msg.txt"), "--new", str(self.out / "new.json"), "--keep", str(self.d / "built.txt"), "--excluded", str(self.d / "excluded.txt")]
        tv.main(args + (["--bundle", str(self.bundle)] if bundle else []))
        return (self.d / "excluded.txt").read_text().split()

    def test_a_name_with_primes_is_read_whole(self):
        """CodeRabbit (emissary#41): Mathlib-style names end in primes; the first version of the pattern stopped at the first quote and the job failed on a clash it should handle."""
        for name in ("mul_comm'", "foo'_eq", "Foo.bar''", "Foo.«a'b».c'", "x'"):
            text = f"U.lean:1:0: error: import Tengoku.ToyLib.Toy.C failed, environment already contains '{name}' from Tengoku.Tree.Lib.Indicator\n"
            self.assertEqual(tv.union_failure(text), ("Tengoku.ToyLib.Toy.C", name, "Tengoku.Tree.Lib.Indicator"), name)

    def test_the_first_refusal_in_a_longer_output_is_the_one_read(self):
        text = "warning: x\nU.lean:1:0: error: import A.B failed, environment already contains 'n'' from C.D\nU.lean:2:0: error: import E failed, environment already contains 'm' from F\n"
        self.assertEqual(tv.union_failure(text), ("A.B", "n'", "C.D"))

    def test_the_refusal_is_read_with_its_guillemets(self):
        self.assertEqual(tv.union_failure(REFUSAL), ("Tengoku.ToyLib.Toy.C", "Indicator.«term𝟭_[_]»", "Tengoku.Tree.Lib.Indicator"))
        self.assertIsNone(tv.union_failure("U.lean:1:0: error: unknown module prefix 'Foo'\n"))

    def test_the_union_file_imports_the_root_and_the_new_modules_that_built(self):
        self.prepare()
        lines = self.union_input()
        self.assertEqual(lines[0], "import Tengoku.All")  # the tree as the queue builds it
        self.assertEqual(sorted(lines[1:-1]), ["import Tengoku.ToyLib.Toy.B", "import Tengoku.ToyLib.Toy.C", "import Tengoku.ToyLib.Toy.D"])

    def test_the_root_can_be_named_and_a_module_with_a_dash_is_quoted_as_an_import_writes_it(self):
        write(self.bundle, {"Tengoku/ToyLib/Toy/A-B.lean": "theorem ab : 5 = 5 := rfl\n"})
        self.prepare(built=("Tengoku.ToyLib.Toy.A-B",))
        lines = self.union_input("--root", "Tengoku.Other")
        self.assertEqual(lines[:2], ["import Tengoku.Other", "import Tengoku.ToyLib.Toy.«A-B»"])

    def test_a_new_module_that_did_not_build_is_not_imported_even_if_it_has_an_olean(self):
        self.prepare(built=("Tengoku.ToyLib.Toy.B",))
        lines = self.union_input()
        self.assertNotIn("import Tengoku.ToyLib.Toy.C", lines)
        self.assertNotIn("import Tengoku.ToyLib.Toy.D", lines)
        self.assertIn("import Tengoku.ToyLib.Toy.B", lines)

    def test_the_new_module_of_the_refused_import_is_excluded_with_its_importers_and_the_next_file_lacks_them(self):
        self.prepare()
        self.assertEqual(self.union_next(REFUSAL), ["Tengoku.ToyLib.Toy.C", "Tengoku.ToyLib.Toy.D"])  # D imports C
        lines = self.union_input()
        self.assertNotIn("import Tengoku.ToyLib.Toy.C", lines)
        self.assertNotIn("import Tengoku.ToyLib.Toy.D", lines)
        self.assertIn("import Tengoku.ToyLib.Toy.B", lines)
        self.assertIn("`Indicator.«term𝟭_[_]»` is also declared by Tengoku.Tree.Lib.Indicator", (self.d / "excluded.reasons").read_text())

    def test_when_the_new_module_is_the_earlier_import_it_is_the_one_that_goes(self):
        self.prepare()
        got = self.union_next("U.lean:3:0: error: import Tengoku.Tree.Lib.Indicator failed, environment already contains 'N' from Tengoku.ToyLib.Toy.B\n")
        self.assertEqual(got, ["Tengoku.ToyLib.Toy.B"])

    def test_a_refusal_between_two_modules_of_the_tree_is_not_ours_and_stops_the_run(self):
        self.prepare()
        with self.assertRaises(SystemExit) as r:
            self.union_next("U.lean:3:0: error: import Tengoku.Tree.Lib.A failed, environment already contains 'N' from Tengoku.Tree.Lib.Indicator\n")
        self.assertIn("the tree does not import", str(r.exception.code))

    def test_a_module_already_excluded_is_not_blamed_again(self):
        self.prepare()
        (self.d / "excluded.txt").write_text("Tengoku.ToyLib.Toy.C\n")
        with self.assertRaises(SystemExit):
            self.union_next(REFUSAL)

    def test_a_failure_that_is_not_a_name_clash_stops_the_run(self):
        self.prepare()
        for text in ("U.lean:1:0: error: object file '/x/Foo.olean' of module Foo does not exist\n", "", "Killed\n"):
            with self.assertRaises(SystemExit) as r:
                self.union_next(text)
            self.assertIn("refusing to guess", str(r.exception.code))

    def test_the_excluded_modules_are_refused_by_collect_with_their_importers_and_the_reason(self):
        self.prepare()
        self.union_next(REFUSAL)
        (self.d / "build.log").write_text(Axioms.BUILT_ALL)
        tv.main(["collect", "--new", str(self.out / "new.json"), "--log", str(self.d / "build.log"), "--out", str(self.out), "--bundle", str(self.bundle), "--union-excluded", str(self.d / "excluded.txt")])
        self.assertEqual((self.out / "failing.txt").read_text().split(), ["Toy.C", "Toy.D"])  # the union loop already excluded the importer, so both are named
        self.assertEqual(sorted(json.loads((self.out / "ok.json").read_text())), ["Tengoku.ToyLib.Toy.B"])
        summary = (self.out / "summary.txt").read_text()
        self.assertIn("2 on the import of the whole tree", summary)
        self.assertIn("import: Tengoku.ToyLib.Toy.C: `Indicator.«term𝟭_[_]»` is also declared by Tengoku.Tree.Lib.Indicator", summary)

    def test_without_the_union_nothing_changes(self):
        self.apply()
        (self.d / "build.log").write_text(Axioms.BUILT_ALL)
        tv.main(["collect", "--new", str(self.out / "new.json"), "--log", str(self.d / "build.log"), "--out", str(self.out), "--bundle", str(self.bundle)])
        self.assertEqual((self.out / "failing.txt").read_text(), "")


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
