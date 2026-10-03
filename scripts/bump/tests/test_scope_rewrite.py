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

    def test_semicolon_separated(self):
        self.assertEqual(len(sr.parse(REPORT.replace("\n", ";"))), 3)


class Rewrite(unittest.TestCase):
    def run_one(self, text, leaks):
        lines = text.split("\n")
        return lines, [sr.edit_declaration(lines, lk["line"], lk["kind"]) if lk["line"] else sr.edit_attribute_command(lines, lk["name"], lk["kind"]) for lk in leaks]

    def test_instance_command(self):
        lines, ok = self.run_one("namespace A\n\n/-- doc -/\ninstance : Coe (α → ℤ) (α → ℝ) := ⟨fun f x => f x⟩\nend A", [{"kind": "instance", "name": "A.i", "line": 3}])
        self.assertEqual(ok, [True])
        self.assertEqual(lines[3], "local instance : Coe (α → ℤ) (α → ℝ) := ⟨fun f x => f x⟩")

    def test_instance_after_modifiers_and_attributes(self):
        lines, ok = self.run_one("@[reducible] noncomputable instance foo : Foo := x", [{"kind": "instance", "name": "foo", "line": 1}])
        self.assertEqual(ok, [True])
        self.assertEqual(lines[0], "@[reducible] noncomputable local instance foo : Foo := x")

    def test_an_instance_already_local_is_left_alone(self):
        _, ok = self.run_one("local instance : Foo := x", [{"kind": "instance", "name": "foo", "line": 1}])
        self.assertEqual(ok, [False])

    def test_simp_attribute(self):
        lines, ok = self.run_one("@[simp, to_additive]\ntheorem take_append : x = y := rfl", [{"kind": "simp", "name": "take_append", "line": 1}])
        self.assertEqual(ok, [True])
        self.assertEqual(lines[0], "@[local simp, to_additive]")

    def test_simp_with_arrow_and_priority(self):
        lines, _ = self.run_one("@[simp ↓ high]\ntheorem t : x = y := rfl", [{"kind": "simp", "name": "t", "line": 1}])
        self.assertEqual(lines[0], "@[local simp ↓ high]")

    def test_attribute_command(self):
        lines, ok = self.run_one("open scoped Matrix.Norms.Operator\nattribute [instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace\nvariable {n : Type*}", [{"kind": "instance", "name": "Matrix.linftyOpNormedAddCommGroup", "line": None}])
        self.assertEqual(ok, [True])
        self.assertEqual(lines[1], "attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace")

    def test_a_comment_mentioning_instance_is_not_edited(self):
        lines, ok = self.run_one("-- an instance of the thing\ninstance : Foo := x", [{"kind": "instance", "name": "foo", "line": 1}])
        self.assertEqual(ok, [True])
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


if __name__ == "__main__":
    unittest.main()
