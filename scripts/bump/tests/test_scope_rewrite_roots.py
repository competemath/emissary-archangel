"""scope_rewrite --qualify-roots: a library's declarations in the root namespace move to Tengoku.<Library>.<name>.

2026-11-12: formal-forbidden-matrix declares a root `X`, `Y`, `A`, `C` and `L`; compfiles' `Usa1980P3` (which builds in its own library) fails in the one environment
(`failed to synthesize HAdd Bool (MvPolynomial …)`, `Ambiguous term C: _root_.C vs MvPolynomial.C`) because a bare `X`/`C` after `open MvPolynomial` also reads as the
other library's. The leak scan lists those declarations (`root: X`) and the rewrite now qualifies them, with no line added or moved.
"""

import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import scope_rewrite as sr  # noqa: E402

NS = "Tengoku.ForbiddenMatrix"

MATRIX = """module

public import Tengoku

public section

open OrderDual

variable {α β γ δ : Type*}

def X : (Fin 3)ᵒᵈ → Bool := ![true, false, false] ∘ ofDual
def Y : Fin 3 → Bool := ![false, false, true]
def L : Fin 2 → Fin 2 → Prop := fun _ _ => True
theorem L_true : L 0 0 := trivial
def Z : Nat := 1 -- not a root
"""


def edit(text, roots, ns=NS):
    f = sr.Lines(text)
    done = sr.qualify_roots_in_file(f, set(roots), ns)
    return "\n".join(f.text), done


class Parse(unittest.TestCase):
    def test_root_lines(self):
        rep = "roots: 3 declarations of the library are in the root namespace (...)\nroot: X\nroot: A'\nleak: instance I registered in M (declared at line 2)\nroot: f"
        self.assertEqual(sr.parse_roots(rep), {"X", "A'", "f"})

    def test_semicolon_separated_and_the_totals_line_is_not_a_name(self):
        self.assertEqual(sr.parse_roots("roots: 2 declarations;root: X;root: C"), {"X", "C"})

    def test_a_blank_after_the_semicolon_is_fine(self):
        self.assertEqual(sr.parse_roots("roots: 2 declarations; root: X; root: C ;  root: D"), {"X", "C", "D"})

    def test_quoted_names_are_one_name(self):
        self.assertEqual(sr.parse_roots("root: «foo bar»\nroot: «foo.bar»\nroot: plain"), {"«foo bar»", "«foo.bar»", "plain"})

    def test_head_of(self):
        self.assertEqual(sr.head_of("Foo.bar"), "Foo")
        self.assertEqual(sr.head_of("«a.b».c"), "«a.b»")
        self.assertEqual(sr.head_of("«foo bar»"), "«foo bar»")
        self.assertEqual(sr.head_of("plain"), "plain")

    def test_none(self):
        self.assertEqual(sr.parse_roots("leakscan: 0 global instances"), set())


class OneFile(unittest.TestCase):
    def test_declarations_are_qualified_and_no_line_moves(self):
        new, done = edit(MATRIX, {"X", "Y", "L", "L_true"})
        old_lines, new_lines = MATRIX.split("\n"), new.split("\n")
        self.assertEqual(len(old_lines), len(new_lines))
        edited = {i for i, (a, b) in enumerate(zip(old_lines, new_lines)) if a != b}
        self.assertEqual(edited, {i for i, ln in enumerate(old_lines) if ln.startswith(("def X", "def Y", "def L ", "theorem L_true"))} | {i for i, ln in enumerate(new_lines) if ln.startswith("namespace " + NS)})
        for i, (a, b) in enumerate(zip(old_lines, new_lines)):
            if i in edited:
                self.assertTrue(b.endswith(a) or a.split(" ", 1)[0] == b.split(" ", 1)[0], (i, a, b))  # the same declaration on the same line, only a prefix added
            else:
                self.assertEqual(a, b)
        self.assertIn(f"def {NS}.X : (Fin 3)ᵒᵈ → Bool", new)
        self.assertIn(f"def {NS}.Y : Fin 3 → Bool", new)
        self.assertIn(f"theorem {NS}.L_true : L 0 0 := trivial", new)
        self.assertIn("def Z : Nat := 1", new)  # not a root of the library: untouched
        self.assertEqual(sorted(done["declared"]), ["L", "L_true", "X", "Y"])

    def test_the_first_body_line_opens_the_namespace(self):
        new, done = edit(MATRIX, {"X"})
        self.assertTrue(done["opened"])
        lines = new.split("\n")
        i = next(k for k, ln in enumerate(lines) if ln.startswith(f"namespace {NS} end {NS} open {NS}"))
        self.assertEqual(lines[i + 1], "open OrderDual")  # on the blank line after `public section`, before the file's own `open`

    def test_a_bare_use_is_left_for_the_open_to_resolve(self):
        new, _ = edit(MATRIX, {"L", "L_true"})
        self.assertIn(": L 0 0 := trivial", new)  # `L` in the statement is still the bare name; `open` resolves it

    def test_a_module_that_only_uses_a_root_gets_just_the_open(self):
        text = "module\n\npublic import Tengoku\n\nopen Foo\n\ntheorem t : X 0 = true := rfl\n"
        new, done = edit(text, {"X"})
        self.assertEqual(done["declared"], [])
        self.assertTrue(done["opened"])
        self.assertIn(f"namespace {NS} end {NS} open {NS} open Foo", new)
        self.assertEqual(len(text.split("\n")), len(new.split("\n")))

    def test_a_module_that_does_not_mention_a_root_is_untouched(self):
        text = "module\n\npublic import Tengoku\n\ndef Z : Nat := 1\ntheorem t : Z = 1 := rfl\n"
        new, done = edit(text, {"X"})
        self.assertEqual(new, text)
        self.assertFalse(done["opened"])

    def test_names_in_comments_and_strings_are_not_edited(self):
        text = 'module\n\npublic import Tengoku\n\n/-- X is the pattern -/\n-- def X : Nat := 1\ndef msg : String := "def X"\n'
        new, done = edit(text, {"X"})
        self.assertEqual(new, text)

    def test_inside_a_namespace_nothing_is_a_root(self):
        text = "module\n\npublic import Tengoku\n\nnamespace Inner\ndef X : Nat := 1\nend Inner\n"
        new, done = edit(text, {"X"})
        self.assertEqual(done["declared"], [])
        self.assertIn("def X : Nat := 1", new)

    def test_a_section_does_not_hide_a_root(self):
        text = "module\n\npublic import Tengoku\n\nsection S\ndef X : Nat := 1\nend S\n"
        new, done = edit(text, {"X"})
        self.assertEqual(done["declared"], ["X"])
        self.assertIn(f"def {NS}.X : Nat := 1", new)

    def test_modifiers_attributes_and_named_instances(self):
        text = "module\n\npublic import Tengoku\n\n@[simp] def X : Nat := 1\nprivate noncomputable def Y : Nat := 2\nnoncomputable instance instW : Inhabited Nat := ⟨0⟩\n@[reducible]\nabbrev A : Type := Nat\n"
        new, done = edit(text, {"X", "Y", "instW", "A"})
        self.assertEqual(sorted(done["declared"]), ["A", "X", "Y", "instW"])
        self.assertIn(f"@[simp] def {NS}.X", new)
        self.assertIn(f"private noncomputable def {NS}.Y", new)
        self.assertIn(f"noncomputable instance {NS}.instW", new)
        self.assertIn(f"abbrev {NS}.A : Type", new)

    def test_a_root_structure_its_namespace_and_dotted_members(self):
        text = "module\n\npublic import Tengoku\n\nstructure Cell where\n  v : Nat\n\nnamespace Cell\ndef inc (c : Cell) : Cell := ⟨c.v + 1⟩\nend Cell\n\ndef Cell.dec (c : Cell) : Cell := ⟨c.v - 1⟩\n"
        new, done = edit(text, {"Cell"})
        self.assertEqual(done["declared"], ["Cell"])
        self.assertEqual(done["namespaces"], 1)
        self.assertEqual(done["dotted"], 1)
        self.assertIn(f"structure {NS}.Cell where", new)
        self.assertIn(f"namespace {NS}.Cell\n", new)
        self.assertIn(f"end {NS}.Cell\n", new)
        self.assertIn(f"def {NS}.Cell.dec", new)

    def test_open_of_a_root_namespace_follows_the_namespace(self):
        text = "module\n\npublic import Tengoku\n\nopen Cell\nopen scoped Cell Other\nopen Cell hiding inc\nopen Other\n\nstructure Cell where\n  v : Nat\n"
        new, done = edit(text, {"Cell"})
        self.assertIn(f"open {NS}.Cell\n", new)
        self.assertIn(f"open scoped {NS}.Cell Other\n", new)
        self.assertIn(f"open {NS}.Cell hiding inc\n", new)
        self.assertIn("\nopen Other\n", new)  # not a root
        self.assertEqual(done["opens"], 3)

    def test_quoted_root_names(self):
        text = "module\n\npublic import Tengoku\n\ndef «foo bar» : Nat := 1\ndef «foo.bar» : Nat := 2\nnamespace «foo bar»\ndef x : Nat := 3\nend «foo bar»\ndef «foo bar».y : Nat := 4\nopen «foo bar» in\ntheorem t : «foo.bar» = 2 := rfl\n"
        new, done = edit(text, {"«foo bar»", "«foo.bar»"})
        self.assertIn(f"def {NS}.«foo bar» : Nat := 1", new)
        self.assertIn(f"def {NS}.«foo.bar» : Nat := 2", new)
        self.assertIn(f"namespace {NS}.«foo bar»\n", new)
        self.assertIn(f"end {NS}.«foo bar»\n", new)
        self.assertIn(f"def {NS}.«foo bar».y", new)
        self.assertIn(f"open {NS}.«foo bar» in", new)
        self.assertEqual(sorted(done["declared"]), ["«foo bar»", "«foo.bar»"])

    def test_an_end_without_a_name_is_left_alone(self):
        text = "module\n\npublic import Tengoku\n\nnamespace Cell\ndef inc : Nat := 1\nend\n"
        new, done = edit(text, {"Cell"})
        self.assertIn(f"namespace {NS}.Cell\n", new)
        self.assertIn("\nend\n", new)

    def test_it_is_idempotent(self):
        once, _ = edit(MATRIX, {"X", "L", "L_true"})
        twice, done = edit(once, {"X", "L", "L_true"})
        self.assertEqual(once, twice)
        self.assertFalse(done["opened"])

    def test_a_name_that_extends_an_outside_namespace_is_not_touched(self):
        text = "module\n\npublic import Tengoku\n\ndef Nat.double (n : Nat) : Nat := 2 * n\n"
        new, done = edit(text, {"X"})
        self.assertEqual(new, text)


class Bundle(unittest.TestCase):
    def layout(self, d: Path):
        b = d / "bundle" / "Tengoku" / "ForbiddenMatrix" / "ForbiddenMatrix"
        b.mkdir(parents=True)
        (b / "MatrixOperations.lean").write_text(MATRIX)
        (b / "Containment.lean").write_text("module\n\npublic import Tengoku\npublic import Tengoku.ForbiddenMatrix.ForbiddenMatrix.MatrixOperations\n\ntheorem c : X 0 = true := rfl\n")
        (b / "Other.lean").write_text("module\n\npublic import Tengoku\n\ndef Q : Nat := 1\n")
        rows = [
            {"name": "L_true", "statement": "theorem L_true : L 0 0", "module": f"{NS}.ForbiddenMatrix.MatrixOperations"},
            {"name": "c", "statement": "theorem c : X 0 = true", "module": f"{NS}.ForbiddenMatrix.Containment"},
        ]
        (d / "bundle" / "manifest.jsonl").write_text("".join(json.dumps(r, ensure_ascii=False) + "\n" for r in rows))
        return b

    def test_bundle_report_and_files(self):
        with tempfile.TemporaryDirectory() as t:
            d = Path(t)
            b = self.layout(d)
            rep = sr.qualify_bundle(d / "bundle", {"X", "L", "L_true", "instAddFoo"}, NS, 0)
            self.assertEqual(rep["qualified"], 3)
            self.assertEqual(rep["unresolved"], ["instAddFoo"])  # an anonymous instance: no text names it
            self.assertEqual(rep["modules_opened"], 2)  # MatrixOperations declares, Containment uses `X`
            self.assertIn(f"def {NS}.X", (b / "MatrixOperations.lean").read_text())
            self.assertIn(f"namespace {NS} end {NS} open {NS} ", (b / "Containment.lean").read_text())
            self.assertEqual((b / "Other.lean").read_text(), "module\n\npublic import Tengoku\n\ndef Q : Nat := 1\n")
            self.assertIn("root names of this library moved to", (b / "MatrixOperations.lean").read_text())

    def test_manifest_records_follow_the_modules(self):
        with tempfile.TemporaryDirectory() as t:
            d = Path(t)
            self.layout(d)
            n = sr.qualify_manifest(d / "bundle", {"L_true"}, NS)
            rows = [json.loads(x) for x in (d / "bundle" / "manifest.jsonl").read_text().splitlines()]
            self.assertEqual(n, 1)
            self.assertEqual(rows[0]["name"], f"{NS}.L_true")
            self.assertEqual(rows[0]["statement"], f"theorem {NS}.L_true : L 0 0")
            self.assertEqual(rows[1]["name"], "c")  # not a root: unchanged

    def test_a_record_follows_by_head_component_not_by_exact_name(self):
        with tempfile.TemporaryDirectory() as t:
            d = Path(t)
            self.layout(d)
            rows = [
                {"name": "Helper.inner", "statement": "def Helper.inner : Nat := 3", "module": f"{NS}.ForbiddenMatrix.MatrixOperations"},  # a member of a root's namespace block
                {"name": "Nat.double", "statement": "def Nat.double (n : Nat) : Nat := 2 * n", "module": f"{NS}.ForbiddenMatrix.MatrixOperations"},  # an extension of an outside namespace
            ]
            (d / "bundle" / "manifest.jsonl").write_text("".join(json.dumps(r) + "\n" for r in rows))
            self.assertEqual(sr.qualify_manifest(d / "bundle", {"Helper"}, NS), 1)
            out = [json.loads(x) for x in (d / "bundle" / "manifest.jsonl").read_text().splitlines()]
            self.assertEqual(out[0]["name"], f"{NS}.Helper.inner")
            self.assertEqual(out[0]["statement"], f"def {NS}.Helper.inner : Nat := 3")
            self.assertEqual(out[1]["name"], "Nat.double")

    def test_the_cli_leaves_the_record_of_a_root_no_module_renamed_alone(self):
        with tempfile.TemporaryDirectory() as t:
            d = Path(t)
            self.layout(d)
            rows = [json.loads(x) for x in (d / "bundle" / "manifest.jsonl").read_text().splitlines()]
            rows.append({"name": "instAddFoo", "statement": "instance : Add Foo := inferInstance", "module": f"{NS}.ForbiddenMatrix.MatrixOperations"})
            (d / "bundle" / "manifest.jsonl").write_text("".join(json.dumps(r) + "\n" for r in rows))
            r = subprocess.run(
                [sys.executable, str(Path(sr.__file__)), "--bundle", str(d / "bundle"), "--qualify-roots", "--leaks", "roots: 2 declarations\nroot: X\nroot: instAddFoo"],
                capture_output=True,
                text=True,
            )
            self.assertEqual(r.returncode, 0, r.stderr)
            out = [json.loads(x) for x in (d / "bundle" / "manifest.jsonl").read_text().splitlines()]
            self.assertEqual([x["name"] for x in out], ["L_true", "c", "instAddFoo"])

    def test_cli_end_to_end_default_namespace(self):
        with tempfile.TemporaryDirectory() as t:
            d = Path(t)
            b = self.layout(d)
            r = subprocess.run(
                [sys.executable, str(Path(sr.__file__)), "--bundle", str(d / "bundle"), "--qualify-roots", "--leaks", "roots: 2 declarations\nroot: X\nroot: L_true"],
                capture_output=True,
                text=True,
            )
            self.assertEqual(r.returncode, 0, r.stderr)
            out = json.loads(r.stdout.split(" ", 1)[1])
            self.assertEqual(out["roots"]["qualified"], 2)
            self.assertEqual(out["roots"]["manifest_records"], 1)
            self.assertIn(f"def {NS}.X", (b / "MatrixOperations.lean").read_text())

    def test_the_library_layout_takes_the_bundles_namespace(self):
        with tempfile.TemporaryDirectory() as t:
            d = Path(t)
            self.layout(d)
            p = d / "pruned" / "ForbiddenMatrix"
            p.mkdir(parents=True)
            (p / "MatrixOperations.lean").write_text(MATRIX)
            r = subprocess.run(
                [sys.executable, str(Path(sr.__file__)), "--bundle", str(d / "bundle"), "--pruned", str(d / "pruned"), "--qualify-roots", "--leaks", "root: X"],
                capture_output=True,
                text=True,
            )
            self.assertEqual(r.returncode, 0, r.stderr)
            self.assertIn(f"def {NS}.X", (p / "MatrixOperations.lean").read_text())

    def test_a_namespace_that_is_not_a_lean_name_is_refused_and_nothing_is_written(self):
        for bad in ("Tengoku.A\nend", "Tengoku.A end X", "A..B", "", "A;B"):
            with tempfile.TemporaryDirectory() as t:
                d = Path(t)
                b = self.layout(d)
                before = (b / "MatrixOperations.lean").read_text()
                r = subprocess.run([sys.executable, str(Path(sr.__file__)), "--bundle", str(d / "bundle"), "--qualify-roots", "--namespace", bad, "--leaks", "root: X"], capture_output=True, text=True)
                self.assertNotEqual(r.returncode, 0, bad)
                self.assertEqual((b / "MatrixOperations.lean").read_text(), before, bad)

    def test_a_directory_name_that_is_no_lean_name_gives_no_namespace(self):
        with tempfile.TemporaryDirectory() as t:
            d = Path(t)
            (d / "Tengoku" / "Bad Name").mkdir(parents=True)
            self.assertIsNone(sr.library_namespace(d, 0))

    def test_without_the_flag_roots_are_only_reported(self):
        with tempfile.TemporaryDirectory() as t:
            d = Path(t)
            b = self.layout(d)
            before = (b / "MatrixOperations.lean").read_text()
            r = subprocess.run([sys.executable, str(Path(sr.__file__)), "--bundle", str(d / "bundle"), "--leaks", "root: X"], capture_output=True, text=True)
            self.assertEqual(r.returncode, 0, r.stderr)
            self.assertEqual((b / "MatrixOperations.lean").read_text(), before)


if __name__ == "__main__":
    unittest.main()
