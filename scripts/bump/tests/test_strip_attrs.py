import sys
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(HERE))
import strip_attrs  # noqa: E402


class Strip(unittest.TestCase):
    def test_only_the_refused_attributes_go(self):
        t = "@[simp, circuit_norm] theorem a : True := trivial\n\n@[circuit_norm]\ndef b : Nat := 1\n\n@[reducible] def c : Nat := 2\n"
        out, n = strip_attrs.strip_attributes(t)
        self.assertEqual(out, "@[simp] theorem a : True := trivial\n\ndef b : Nat := 1\n\n@[reducible] def c : Nat := 2\n")
        self.assertEqual(dict(n), {"circuit_norm": 2})

    def test_an_attribute_command_with_nothing_left_goes_whole(self):
        t = "namespace X\n\nattribute [circuit_norm] foo bar\n  baz\n\ntheorem a : True := trivial\nattribute [simp, circuit_norm] foo\nend X\n"
        out, _ = strip_attrs.strip_attributes(t)
        self.assertEqual(out, "namespace X\n\ntheorem a : True := trivial\nattribute [simp] foo\nend X\n")

    def test_comments_and_strings_are_left_alone(self):
        t = '-- @[circuit_norm] in a comment\n/- @[circuit_norm] block -/\ndef s : String := "@[circuit_norm]"\n'
        self.assertEqual(strip_attrs.strip_attributes(t), (t, {}))

    def test_aesop_tactic_rules_and_arguments(self):
        t = "@[aesop safe apply] theorem a : True := trivial\n@[aesop norm tactic] def f := 1\n@[simp ←, field_simps] theorem g : True := trivial\n@[to_additive (attr := circuit_norm)] theorem h : True := trivial\n"
        out, n = strip_attrs.strip_attributes(t)
        self.assertIn("@[aesop safe apply] theorem a", out)
        self.assertNotIn("aesop norm tactic", out)
        self.assertIn("@[simp ←, field_simps] theorem g", out)
        self.assertIn("@[to_additive (attr := circuit_norm)] theorem h", out)  # to_additive is allowed, its argument is its business
        self.assertEqual(dict(n), {"aesop": 1})

    def test_idempotent_and_plain_lean_untouched(self):
        t = "@[simp, circuit_norm, implicit_reducible] theorem a : True := trivial\n"
        once, _ = strip_attrs.strip_attributes(t)
        self.assertEqual(once, "@[simp, implicit_reducible] theorem a : True := trivial\n")
        self.assertEqual(strip_attrs.strip_attributes(once), (once, {}))


class PortfolioTraces(unittest.TestCase):
    BLOCK = (
        "theorem t : x = y := by\n  first\n"
        '    | (all_goals grind; done; trace "PORTFOLIO-OK grind")\n'
        '    | (all_goals aesop; done; trace "PORTFOLIO-OK aesop")\n'
    )

    def test_the_traces_go_and_the_block_stays(self):
        out, n = strip_attrs.strip_portfolio_traces(self.BLOCK)
        self.assertEqual(n, 2)
        self.assertIn("    | (all_goals grind; done)\n", out)
        self.assertIn("    | (all_goals aesop; done)\n", out)
        self.assertEqual(out.count("\n"), self.BLOCK.count("\n"))  # no line moves

    def test_a_trace_in_a_comment_or_a_string_is_left_alone(self):
        text = '-- x; trace "PORTFOLIO-OK grind"\ndef s := "a; trace \\"PORTFOLIO-OK x\\""\n/- y; trace "PORTFOLIO-OK aesop" -/\n'
        out, n = strip_attrs.strip_portfolio_traces(text)
        self.assertEqual((out, n), (text, 0))


if __name__ == "__main__":
    unittest.main()
