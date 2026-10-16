"""Repair: a `#print` / `#check` command only prints, and the tree's lint refuses every `#` command. It is removed, and the module says so in one docstring line per command.

navier-stokes-euler (2026-10-16): the module that proves the headline results ends with `#print axioms NavierStokes.Comparator.navier_stokes_breakdown_R3` (the library's own check that
the proof rests on the three axioms). The lint dropped the module, and with it the headline theorems. No Lean: the stripper, the note, and a whole compose on the toy library."""

import json
import sys
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(HERE / "tests"))
import test_faithful_imports as tfi  # the toy library and its compose

sys.path.insert(0, str(HERE))
import bundle  # noqa: E402
import strip_attrs as sa  # noqa: E402


class Strip(unittest.TestCase):
    def test_a_print_command_at_the_end_goes_with_its_blank_line(self):
        out, gone = sa.strip_print_commands("theorem a : 1 = 1 := rfl\n\n#print axioms a\n")
        self.assertEqual((out, gone), ("theorem a : 1 = 1 := rfl\n", ["#print axioms a"]))

    def test_one_blank_line_of_two_around_a_command_goes_and_the_other_stays(self):
        out, gone = sa.strip_print_commands("theorem a : 1 = 1 := rfl\n\n#check a\n\ntheorem b : 2 = 2 := rfl\n")
        self.assertEqual(out, "theorem a : 1 = 1 := rfl\n\ntheorem b : 2 = 2 := rfl\n")
        self.assertEqual(gone, ["#check a"])

    def test_a_command_right_under_a_declaration_leaves_no_gap(self):
        out, _ = sa.strip_print_commands("theorem a : 1 = 1 := rfl\n#print axioms a\ntheorem b : 2 = 2 := rfl\n")
        self.assertEqual(out, "theorem a : 1 = 1 := rfl\ntheorem b : 2 = 2 := rfl\n")

    def test_a_command_with_a_blank_line_only_after_it_keeps_that_blank_line(self):
        out, _ = sa.strip_print_commands("theorem a : 1 = 1 := rfl\n#print axioms a\n\ntheorem b : 2 = 2 := rfl\n")
        self.assertEqual(out, "theorem a : 1 = 1 := rfl\n\ntheorem b : 2 = 2 := rfl\n")

    def test_every_command_is_listed_in_file_order(self):
        _, gone = sa.strip_print_commands("#check a\ntheorem a : 1 = 1 := rfl\n#print a\n\n#print axioms a\n")
        self.assertEqual(gone, ["#check a", "#print a", "#print axioms a"])

    def test_a_command_in_a_comment_or_a_string_is_not_one(self):
        text = '/-\n#print axioms a\n-/\n-- #check a\ndef s : String := "\n#print axioms a\n"\n/-- doc\n#check a\n-/\ntheorem a : 1 = 1 := rfl\n'
        out, gone = sa.strip_print_commands(text)
        self.assertEqual((out, gone), (text, []))

    def test_an_indented_command_is_left(self):
        text = "theorem a : 1 = 1 := by\n  #check 1\n  rfl\n"
        self.assertEqual(sa.strip_print_commands(text), (text, []))

    def test_a_command_that_goes_on_over_the_next_line_is_left(self):
        text = "#check a\n  b\ntheorem a : 1 = 1 := rfl\n"
        self.assertEqual(sa.strip_print_commands(text), (text, []))

    def test_commands_that_run_code_are_not_touched(self):
        text = "#eval 1 + 1\n#reduce 1 + 1\n#guard 1 = 1\n#synth Inhabited Nat\n"
        self.assertEqual(sa.strip_print_commands(text), (text, []))

    def test_a_word_that_only_starts_like_the_command_is_not_one(self):
        text = "#printed x\n#checks x\n"
        self.assertEqual(sa.strip_print_commands(text), (text, []))

    def test_text_without_a_command_is_returned_as_it_was(self):
        text = "import X\n\ntheorem a : 1 = 1 := rfl\n"
        self.assertEqual(sa.strip_print_commands(text), (text, []))

    def test_a_command_on_the_last_line_without_a_newline(self):
        self.assertEqual(sa.strip_print_commands("theorem a : 1 = 1 := rfl\n#print axioms a"), ("theorem a : 1 = 1 := rfl", ["#print axioms a"]))


class Note(unittest.TestCase):
    def test_the_note_names_the_command_and_is_one_short_line(self):
        n = bundle.print_note("#print axioms NavierStokes.Comparator.navier_stokes_breakdown_R3")
        self.assertEqual(n, "/-! Tengoku repair: removed `#print axioms NavierStokes.Comparator.navier_stokes_breakdown_R3` (it only prints; the queue checks the axioms of every declaration). -/")
        self.assertNotIn("\n", n)

    def test_the_notes_go_right_after_the_last_import(self):
        out = bundle.add_repair_notes("import A\nimport B\n\n/-! doc -/\n\ntheorem t : 1 = 1 := rfl\n", ["/-! one -/", "/-! two -/"])
        self.assertEqual(out.split("\n")[:7], ["import A", "import B", "", "/-! one -/", "/-! two -/", "", "/-! doc -/"])

    def test_a_module_without_an_import_gets_none(self):
        text = "theorem t : 1 = 1 := rfl\n"
        self.assertEqual(bundle.add_repair_notes(text, ["/-! one -/"]), text)


class Compose(unittest.TestCase):
    """The toy library, with a `#print axioms` at the end of B."""

    B = "import Toy.A\n\nnamespace Toy\n\nvariable (n : Nat)\n\ntheorem unrelated : n = n := rfl\n\nopen Nat in\ntheorem uses_one_pos : 0 < one := one_pos\n\nend Toy\n\n#print axioms Toy.uses_one_pos\n"

    def compose(self, text=None):
        text = text or self.B
        lines = text.split("\n")
        ln = lambda needle: next(i + 1 for i, x in enumerate(lines) if needle in x)  # noqa: E731
        rows = [["Toy.uses_one_pos", ln("open Nat in"), ln("theorem uses_one_pos")]]
        return tfi.Compose("compose").compose("--imports", "faithful", extra_modules={"Toy/B": (text, rows)})

    def read(self, d, rel="Toy/B.lean"):
        return (d / "bundle-proposed" / "Tengoku" / "ToyLib" / rel).read_text()

    def test_the_module_ships_without_the_command_and_says_so_once(self):
        d, r = self.compose()
        self.assertEqual(r.returncode, 0, r.stderr)
        b = self.read(d)
        self.assertNotIn("#print", b.replace("`#print axioms Toy.uses_one_pos`", ""))
        self.assertEqual(b.count("/-! Tengoku repair: removed `#print axioms Toy.uses_one_pos`"), 1)
        self.assertIn("theorem uses_one_pos", b)

    def test_the_repair_note_follows_the_faithful_imports_note(self):
        d, r = self.compose()
        self.assertEqual(r.returncode, 0, r.stderr)
        lines = self.read(d).split("\n")
        i = next(k for k, ln in enumerate(lines) if ln.startswith("/-! Tengoku: the imports"))
        self.assertTrue(lines[i + 2].startswith("/-! Tengoku repair: removed"), lines[i : i + 3])  # one blank line between the two

    def test_the_theorem_is_in_the_manifest_and_the_report_counts_the_repair(self):
        d, r = self.compose()
        self.assertEqual(r.returncode, 0, r.stderr)
        names = [json.loads(ln)["name"] for ln in (d / "bundle-proposed" / "manifest.jsonl").read_text().splitlines()]
        self.assertEqual(names, ["Toy.uses_one_pos"])
        rep = json.loads((d / "bundle-proposed" / "report.json").read_text())
        self.assertEqual(rep["stripped_attributes"], {"#print/#check command": 1})

    def test_the_source_copy_keeps_the_text_as_the_library_wrote_it_apart_from_the_note(self):
        d, r = self.compose()
        self.assertEqual(r.returncode, 0, r.stderr)
        self.assertNotIn("#print axioms Toy.uses_one_pos\n", (d / "src-proposed" / "Toy" / "B.lean").read_text().replace("`#print axioms Toy.uses_one_pos`", ""))

    def test_a_module_without_the_command_is_as_before(self):
        d, r = self.compose(self.B.replace("\n#print axioms Toy.uses_one_pos\n", "\n"))
        self.assertEqual(r.returncode, 0, r.stderr)
        self.assertNotIn("Tengoku repair", self.read(d))
        self.assertEqual(json.loads((d / "bundle-proposed" / "report.json").read_text())["stripped_attributes"], {})

    def test_a_command_that_runs_code_still_drops_the_module(self):
        d, r = self.compose(self.B.replace("#print axioms Toy.uses_one_pos", "#eval 1 + 1"))
        self.assertEqual(r.returncode, 0, r.stderr)
        self.assertFalse((d / "bundle-proposed" / "Tengoku" / "ToyLib" / "Toy" / "B.lean").exists())


if __name__ == "__main__":
    unittest.main()
