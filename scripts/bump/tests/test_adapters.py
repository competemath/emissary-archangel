import sys
import tempfile
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(HERE))
import adapters  # noqa: E402

SAMPLE = """/-
Copyright (c) 2023 David Renshaw.
-/

module

public import Mathlib.Tactic
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Algebra] }

/-!
# Title

problem statement in prose: determine the answer. snip begin
-/

namespace Bulgaria1998P3

snip begin

lemma helper (n : ℕ) : n = n := rfl

snip end

-- problem in a comment
problem bulgaria1998_p3
    (f : ℝ → ℝ) : False := by
  have := "problem foo"
  sorry

determine solution_set : Set ℝ := {1}

@[simp] private problem other (x : ℕ) : x = x := rfl

end Bulgaria1998P3
"""


class Compfiles(unittest.TestCase):
    def test_the_commands_become_their_plain_meaning(self):
        out, n = adapters.adapt_compfiles(SAMPLE)
        self.assertNotIn("ProblemExtraction", out)
        self.assertNotIn("problem_file", out)
        self.assertNotIn("snip begin\n\nlemma", out)
        self.assertIn("lemma helper (n : ℕ) : n = n := rfl", out)  # what the snip held stays
        self.assertIn("\ntheorem bulgaria1998_p3\n    (f : ℝ → ℝ) : False := by", out)
        self.assertIn("abbrev solution_set : Set ℝ := {1}", out)
        self.assertIn("@[simp] private theorem other (x : ℕ) : x = x := rfl", out)
        self.assertGreaterEqual(n, 7)

    def test_prose_comments_and_strings_are_left_alone(self):
        out, _ = adapters.adapt_compfiles(SAMPLE)
        self.assertIn("problem statement in prose: determine the answer. snip begin", out)  # inside a block comment
        self.assertIn("-- problem in a comment", out)
        self.assertIn('"problem foo"', out)

    def test_it_is_idempotent_and_plain_lean_is_untouched(self):
        once, _ = adapters.adapt_compfiles(SAMPLE)
        twice, n = adapters.adapt_compfiles(once)
        self.assertEqual(once, twice)
        self.assertEqual(n, 0)
        plain = "import Mathlib\n\ntheorem a : True := trivial\n"
        self.assertEqual(adapters.adapt_compfiles(plain), (plain, 0))

    def test_a_multiline_problem_file_goes_whole(self):
        src = "import Mathlib\nproblem_file {\n  tags := [.Algebra],\n  solutionImportedFrom := \"x}y\"\n}\n\ntheorem a : True := trivial\n"
        out, _ = adapters.adapt_compfiles(src)
        self.assertEqual(out, "import Mathlib\n\ntheorem a : True := trivial\n")

    def test_the_library_entry_point_rewrites_only_registered_libraries(self):
        d = Path(tempfile.mkdtemp())
        (d / "Compfiles").mkdir()
        (d / "Compfiles" / "A.lean").write_text(SAMPLE)
        self.assertEqual(adapters.adapt_library("other-lib", d, ["Compfiles"]), (0, 0))
        self.assertIn("problem_file", (d / "Compfiles" / "A.lean").read_text())
        files, n = adapters.adapt_library("compfiles", d, ["Compfiles"])
        self.assertEqual(files, 1)
        self.assertGreater(n, 0)
        self.assertNotIn("problem_file", (d / "Compfiles" / "A.lean").read_text())


PHYS = """module

public import Mathlib.Algebra.Order.Field.Basic
public import Physlib.Meta.TODO.Basic
public import Physlib.Mathematics.Foo

/-! TODO "inside a comment stays" -/

namespace Physlib

TODO "Prove injectivity of `f` and construct the
  full isomorphism, with an escaped \\" quote."

theorem a : True := trivial

TODO "second"
-- TODO "also a comment"
def s : String := "TODO \\"not a command\\""

end Physlib
"""


class Physlib(unittest.TestCase):
    def test_todo_commands_and_their_import_go(self):
        out, n = adapters.adapt_physlib(PHYS)
        self.assertNotIn("Physlib.Meta.TODO.Basic", out)
        self.assertIn("public import Physlib.Mathematics.Foo", out)
        self.assertNotIn("Prove injectivity", out)
        self.assertNotIn('TODO "second"', out)
        self.assertIn('/-! TODO "inside a comment stays" -/', out)
        self.assertIn('-- TODO "also a comment"', out)
        self.assertIn('def s : String := "TODO', out)
        self.assertIn("theorem a : True := trivial", out)
        self.assertEqual(n, 3)

    def test_idempotent(self):
        once, _ = adapters.adapt_physlib(PHYS)
        self.assertEqual(adapters.adapt_physlib(once), (once, 0))


if __name__ == "__main__":
    unittest.main()
