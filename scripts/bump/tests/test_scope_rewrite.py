import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import scope_rewrite as sr  # noqa: E402

REPORT = """leak: instance Imo1977P2.instCoeForallIntForallReal registered in Tengoku.Compfiles.Compfiles.Imo1977P2 (declared at line 4)
leak: simp Imo1979P6.Walk.take_append registered in Tengoku.Compfiles.Compfiles.Imo1979P6 (declared at line 3)
leak: instance Matrix.linftyOpNormedAddCommGroup registered in Tengoku.Compfiles.Compfiles.Riccati (declared in Tengoku.Analysis.Matrix.Normed: an `attribute` command of the library turns it on)
leakscan: 18 global instances (3 touch no type of the library), 0 scoped; 47 global simp lemmas (0 trigger on nothing of the library), 0 scoped"""


class Parse(unittest.TestCase):
    def test_lines_are_read(self):
        leaks = sr.parse(REPORT)
        self.assertEqual([(x["kind"], x["name"], x["line"]) for x in leaks], [("instance", "Imo1977P2.instCoeForallIntForallReal", 4), ("simp", "Imo1979P6.Walk.take_append", 3), ("instance", "Matrix.linftyOpNormedAddCommGroup", None)])

    def test_flattened_to_one_line(self):
        self.assertEqual(len(sr.parse(REPORT.replace("\n", " "))), 3)

    def test_semicolon_separated(self):
        self.assertEqual(len(sr.parse(REPORT.replace("\n", ";"))), 3)


class Rewrite(unittest.TestCase):
    def run_one(self, text, leaks):
        f = sr.Lines(text)
        res = [sr.edit_declaration(f, lk["line"], lk["kind"]) if lk["line"] else sr.edit_attribute_command(f, lk["name"], lk["kind"]) for lk in leaks]
        return f.text, res

    def test_instance_command(self):
        lines, res = self.run_one("namespace A\n\n/-- doc -/\ninstance : Coe (α → ℤ) (α → ℝ) := {\n  coe := f\n}\nend A", [{"kind": "instance", "name": "A.i", "line": 3}])
        self.assertEqual(res, ["edited"])
        self.assertEqual(lines[3], "local instance : Coe (α → ℤ) (α → ℝ) := {")

    def test_a_docstring_that_says_instance_is_not_edited(self):
        text = "/-- The target of the sum also carries an\n  instance thereof. -/\ninstance : Foo := x"
        lines, res = self.run_one(text, [{"kind": "instance", "name": "foo", "line": 1}])
        self.assertEqual(res, ["edited"])
        self.assertEqual(lines[0], "/-- The target of the sum also carries an")
        self.assertEqual(lines[1], "  instance thereof. -/")
        self.assertEqual(lines[2], "local instance : Foo := x")

    def test_a_comment_before_the_keyword_on_the_same_line(self):
        lines, res = self.run_one("/-- an instance -/ instance : Foo := x", [{"kind": "instance", "name": "foo", "line": 1}])
        self.assertEqual(res, ["edited"])
        self.assertEqual(lines[0], "/-- an instance -/ local instance : Foo := x")

    def test_instance_after_modifiers_and_attributes(self):
        lines, res = self.run_one("@[reducible] noncomputable instance foo : Foo := x", [{"kind": "instance", "name": "foo", "line": 1}])
        self.assertEqual(res, ["edited"])
        self.assertEqual(lines[0], "@[reducible] noncomputable local instance foo : Foo := x")

    def test_an_instance_already_local_is_left_alone(self):
        _, res = self.run_one("local instance : Foo := x", [{"kind": "instance", "name": "foo", "line": 1}])
        self.assertEqual(res, ["already"])

    def test_simp_attribute(self):
        lines, res = self.run_one("@[simp, to_additive]\ntheorem take_append : x = y := rfl", [{"kind": "simp", "name": "take_append", "line": 1}])
        self.assertEqual(res, ["edited"])
        self.assertEqual(lines[0], "@[local simp, to_additive]")

    def test_simp_with_arrow_and_priority(self):
        lines, _ = self.run_one("@[simp ↓ high]\ntheorem t : x = y := rfl", [{"kind": "simp", "name": "t", "line": 1}])
        self.assertEqual(lines[0], "@[local simp ↓ high]")

    def test_a_simp_in_a_string_or_comment_is_not_edited(self):
        lines, res = self.run_one('-- @[simp]\n@[simp] theorem t : x = y := by simp', [{"kind": "simp", "name": "t", "line": 1}])
        self.assertEqual(res, ["edited"])
        self.assertEqual(lines[0], "-- @[simp]")
        self.assertEqual(lines[1], "@[local simp] theorem t : x = y := by simp")

    def test_attribute_command(self):
        lines, res = self.run_one("open scoped Matrix.Norms.Operator\nattribute [instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace\nvariable {n : Type*}", [{"kind": "instance", "name": "Matrix.linftyOpNormedAddCommGroup", "line": None}, {"kind": "instance", "name": "Matrix.linftyOpNormedSpace", "line": None}])
        self.assertEqual(res, ["edited", "already"])
        self.assertEqual(lines[1], "attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace")

    def test_a_comment_mentioning_instance_is_not_edited(self):
        lines, res = self.run_one("-- an instance of the thing\ninstance : Foo := x", [{"kind": "instance", "name": "foo", "line": 1}])
        self.assertEqual(res, ["edited"])
        self.assertEqual(lines[0], "-- an instance of the thing")
        self.assertEqual(lines[1], "local instance : Foo := x")


class Bundle(unittest.TestCase):
    def test_a_bundle_tree_is_rewritten_in_place_with_a_note(self):
        with tempfile.TemporaryDirectory() as d:
            f = Path(d, "Tengoku", "Compfiles", "Compfiles", "Imo1977P2.lean")
            f.parent.mkdir(parents=True)
            f.write_text("import Tengoku\n\nnamespace Imo1977P2\n\ninstance : Coe (α → ℤ) (α → ℝ) := ⟨fun f x => f x⟩\n\nend Imo1977P2\n")
            rep = sr.apply_bundle(Path(d), sr.parse("leak: instance Imo1977P2.i registered in Tengoku.Compfiles.Compfiles.Imo1977P2 (declared at line 5)"))
            self.assertEqual(rep["rewritten"], 1)
            text = f.read_text()
            self.assertIn("local instance : Coe", text)
            self.assertTrue(text.rstrip().endswith("(generated)"))
            self.assertEqual(text.split("\n")[4], "local instance : Coe (α → ℤ) (α → ℝ) := ⟨fun f x => f x⟩")  # the line numbers did not move

    def test_the_librarys_own_layout_drops_the_tree_prefix(self):
        with tempfile.TemporaryDirectory() as d:
            f = Path(d, "Compfiles", "Imo1977P2.lean")
            f.parent.mkdir(parents=True)
            f.write_text("namespace A\ninstance : Foo := x\nend A\n")
            rep = sr.apply_bundle(Path(d), sr.parse("leak: instance A.i registered in Tengoku.Compfiles.Compfiles.Imo1977P2 (declared at line 2)"), skip=2)
            self.assertEqual(rep["rewritten"], 1)
            self.assertIn("local instance : Foo", f.read_text())

    def test_escaped_module_names(self):
        self.assertEqual(sr.parts_of("Tengoku.X.«1102.4662».Basic"), ["Tengoku", "X", "1102.4662", "Basic"])
        self.assertIsNone(sr.parts_of("Tengoku.X/../Y"))
        self.assertIsNone(sr.parts_of("a b"))

    def test_a_leak_of_a_module_the_bundle_lacks_is_reported_not_fatal(self):
        with tempfile.TemporaryDirectory() as d:
            rep = sr.apply_bundle(Path(d), sr.parse("leak: simp a registered in Tengoku.X.Y (declared at line 1)"))
            self.assertEqual(rep["missing_modules"], ["Tengoku.X.Y"])

    def test_a_module_name_never_leaves_the_bundle(self):
        with tempfile.TemporaryDirectory() as d, tempfile.TemporaryDirectory() as outside:
            Path(outside, "victim.lean").write_text("instance : Foo := x\n")
            root = Path(d, "b")
            root.mkdir()
            self.assertIsNone(sr.module_file(root, "Tengoku/../../x"))
            self.assertIsNone(sr.module_file(root, "a..b"))
            (root / "Tengoku").mkdir()
            (root / "Tengoku" / "Y.lean").symlink_to(Path(outside, "victim.lean"))
            self.assertIsNone(sr.module_file(root, "Tengoku.Y"))
            rep = sr.apply_bundle(root, sr.parse("leak: instance i registered in Tengoku.Y (declared at line 1)"))
            self.assertEqual(rep["rewritten"], 0)
            self.assertEqual(Path(outside, "victim.lean").read_text(), "instance : Foo := x\n")


class Reexport(unittest.TestCase):
    def make(self, d: Path, prefix: str):
        root = d / prefix if prefix else d
        root.mkdir(parents=True, exist_ok=True)
        imp = (lambda m: f"import Tengoku.Lib.{m}") if prefix else (lambda m: f"import {m}")
        (root / "A.lean").write_text("module\n\npublic import Tengoku\n\nnamespace X\ninstance : Foo := x\n@[simp] theorem s : a = b := rfl\nend X\n")
        (root / "B.lean").write_text(f"/-\nCopyright\n-/\nmodule\n\npublic import Tengoku\n{imp('L.A')}\n\n/-! doc -/\n\n@[expose] public section\n\ntheorem b : True := trivial\n")
        (root / "C.lean").write_text(f"{imp('L.B')}\n\ntheorem c : True := trivial\n")
        (root / "D.lean").write_text("import Tengoku\n\ntheorem d : True := trivial\n")

    def test_importers_get_the_registrations_local_and_the_module_itself_does_not(self):
        with tempfile.TemporaryDirectory() as t:
            d = Path(t)
            self.make(d / "Tengoku" / "Lib", "L")
            leaks = sr.parse("leak: instance X.instFoo registered in Tengoku.Lib.L.A (priority 100) (declared at line 5)\nleak: simp X.s registered in Tengoku.Lib.L.A (declared at line 6)")
            rep = sr.reexport(d, leaks, skip=0)
            self.assertEqual((rep["modules"], rep["reexported"]), (2, 4))
            b = (d / "Tengoku/Lib/L/B.lean").read_text()
            self.assertIn("attribute [local instance 100] X.instFoo", b)
            self.assertIn("attribute [local simp] X.s", b)
            self.assertLess(b.index("public section"), b.index("attribute [local"))  # inside the section that opens the body
            self.assertIn("attribute [local instance 100] X.instFoo", (d / "Tengoku/Lib/L/C.lean").read_text())  # indirect importer
            self.assertNotIn("attribute", (d / "Tengoku/Lib/L/A.lean").read_text())
            self.assertNotIn("attribute", (d / "Tengoku/Lib/L/D.lean").read_text())

    def test_a_private_or_hygienic_name_is_not_reexported(self):
        with tempfile.TemporaryDirectory() as t:
            d = Path(t)
            self.make(d / "Tengoku" / "Lib", "L")
            leaks = sr.parse("leak: instance _private.Tengoku.Lib.L.A.0.X.inst registered in Tengoku.Lib.L.A (declared at line 5)")
            self.assertEqual(sr.reexport(d, leaks, skip=0)["modules"], 0)

    def test_the_header_ends_before_the_first_command(self):
        lines = ["/-", "doc", "-/", "module", "", "public import A", "import B", "", "/-! m -/", "", "open X", "theorem t : True := trivial"]
        self.assertEqual(sr.body_start(lines), 10)
        self.assertEqual(sr.body_start(["import A", "@[expose] public section", "def x := 1"]), 2)

    def test_the_librarys_own_layout(self):
        with tempfile.TemporaryDirectory() as t:
            d = Path(t)
            self.make(d, "")
            (d / "A.lean").rename(d / "L_A.lean")  # a flat layout: module names are the file names
            leaks = sr.parse("leak: instance X.instFoo registered in Tengoku.Lib.L_A (declared at line 5)")
            (d / "B.lean").write_text("import L_A\n\ntheorem b : True := trivial\n")
            rep = sr.reexport(d, leaks, skip=2)
            self.assertEqual(rep["modules"], 1)
            self.assertIn("attribute [local instance] X.instFoo", (d / "B.lean").read_text())


if __name__ == "__main__":
    unittest.main()
