"""notation_census.py: the global notation of a library that leaks into the tree, read from its sources. On 22 modules of lean-pool and equational-theories it found exactly the
commands the compiled scan (TengokuLeak.lean) reported for them (52 of the 53 the compiled scan found over both libraries; the 53rd is in a module that was not compared)."""

import json
import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import notation_census as nc  # noqa: E402

SEED = {"keys": ["leading -", "trailing ∈", "trailing ∘", "leading √", "trailing ⁻¹", "leading ("], "idents": ["at", "with", "fun"]}


def found(text):
    return [(r["line"], r["why"]) for r in nc.census(text, SEED)]


class Census(unittest.TestCase):
    def test_a_token_of_core_at_the_same_position_is_a_leak(self):
        self.assertEqual(found('namespace A\nprefix:80 "-" => complement\nend A\n'), [(2, ["token: leading -"])])
        self.assertEqual(found('infix : 120 " ∈ " => mem\n'), [(1, ["token: trailing ∈"])])
        self.assertEqual(found('infixr:80 " ∘ " => comp\n'), [(1, ["token: trailing ∘"])])
        self.assertEqual(found('postfix:max " ⁻¹ " => inv\n'), [(1, ["token: trailing ⁻¹"])])
        self.assertEqual(found('notation "√" => square_roots\n'), [(1, ["token: leading √"])])

    def test_the_same_token_at_the_other_position_is_not(self):
        self.assertEqual(found('infixl:65 " - " => sub\n'), [])  # core has a LEADING `-`; a trailing one is another parser
        self.assertEqual(found('notation "⁻¹" x => inv x\n'), [])
        self.assertEqual(found('prefix:80 " ∈ " => mem\n'), [])

    def test_a_variable_before_the_first_atom_makes_it_trailing(self):
        self.assertEqual(found('notation:80 φ "⟦" s "⟧" => subst s φ\n'), [])
        self.assertEqual(found('notation:80 a " ∘ " b => comp a b\n'), [(1, ["token: trailing ∘"])])

    def test_a_word_that_looks_like_an_identifier_is_a_leak_unless_core_has_it(self):
        self.assertEqual(found('notation "v" => x\n'), [(1, ["word: v"])])
        self.assertEqual(found('prefix:76 "diaDot" => diadot\n'), [(1, ["word: diaDot"])])
        self.assertEqual(found('notation "at" => x\n'), [])
        self.assertEqual(found('elab "superpose " a:term:arg b:term:arg : term => do pure a\n'), [(1, ["word: superpose"])])
        self.assertEqual(found('macro "Facts " G:term:max "[" sat:num,* "]" : term => `(G)\n'), [(1, ["word: Facts"])])

    def test_the_first_atom_of_a_tactic_is_no_token_the_others_are(self):
        self.assertEqual(found('syntax "toytac" : tactic\n'), [])
        self.assertEqual(found('syntax "quux " "zork" : tactic\n'), [(1, ["word: zork"])])
        self.assertEqual(found('macro "foo" x:term : tactic => `(tactic| skip)\n'), [])

    def test_scoped_and_local_commands_and_rules_are_not_leaks(self):
        for src in ('scoped prefix:80 "-" => f\n', 'local notation "v" => x\n', 'namespace A\nscoped notation "v" => x\nend A\n', 'macro_rules | `(foo) => `(1)\n'):
            self.assertEqual(found(src), [], src)

    def test_attributes_and_modifiers_in_front(self):
        self.assertEqual(found('@[inherit_doc X] infix : 120 " ∈ " => f\n'), [(1, ["token: trailing ∈"])])
        self.assertEqual(found('private notation "v" => x\n'), [(1, ["word: v"])])

    def test_comments_and_docstrings_do_not_count_and_a_dash_in_a_string_does_not_start_one(self):
        self.assertEqual(found('-- prefix:80 "-" => f\n/- notation "v" => x -/\n/-- notation "w" -/\n'), [])
        self.assertEqual(found('notation "√" => x -- trailing comment\n'), [(1, ["token: leading √"])])
        self.assertEqual(found('notation "--" => x\n'), [])  # not a seed token, not a word

    def test_a_command_over_several_lines(self):
        self.assertEqual(found('notation "(" k " ↦ "v"; "m")"\n    => TMap.put k v m\n'), [(1, ["token: leading ("])])

    def test_a_command_without_a_string_is_skipped(self):
        self.assertEqual(found("notation => x\nsyntax foo : term\n"), [])


class Tree(unittest.TestCase):
    def test_the_report_lines_are_the_ones_of_the_compiled_scan_and_the_seed_is_left_alone(self):
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            (root / "Tengoku/Lib/Modal").mkdir(parents=True)
            (root / "Tengoku/Seed/Mathlib").mkdir(parents=True)
            (root / "Tengoku/Lib/Modal/Complement.lean").write_text('namespace A\n/-- doc -/\nprefix:80 "-" => c\nend A\n')
            (root / "Tengoku/Seed/Mathlib/Neg.lean").write_text('prefix:80 "-" => Neg.neg\n')
            (root / "seed.json").write_text(json.dumps(SEED))
            import subprocess

            r = subprocess.run(
                [sys.executable, "-I", str(Path(nc.__file__)), "--tree", d, "--seed", str(root / "seed.json"), "--out", str(root / "leaks.txt")],
                capture_output=True,
                text=True,
            )
            self.assertEqual(r.returncode, 0, r.stderr)
            self.assertEqual((root / "leaks.txt").read_text(), "leak: notation src@3 registered in Tengoku.Lib.Modal.Complement (declared at line 3)\n")


if __name__ == "__main__":
    unittest.main()
