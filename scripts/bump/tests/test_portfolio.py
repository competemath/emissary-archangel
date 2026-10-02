import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parents[1]

SRC = """import Mathlib

namespace T

/-- fine -/
theorem ok_one : 1 = 1 := rfl

/-- the proof broke -/
theorem broken (a b : Nat) (h : a ≤ b) : a < b + 1 := by
  simp at h
  linarith

theorem pattern : ∀ n : Nat, n = n
  | 0 => rfl
  | n + 1 => rfl

theorem bad_statement (a : Nat) : foo a = a := by
  simp

theorem term_proof (a : Nat) : a = a := by
  exact (Eq.refl a)

end T
"""


def run(src, log):
    d = tempfile.mkdtemp()
    lib = Path(d)
    (lib / "T.lean").write_text(src)
    (lib / "build.log").write_text(log)
    r = subprocess.run([sys.executable, str(HERE / "portfolio.py"), "apply", "--lib", d, "--log", str(lib / "build.log"), "--out", str(lib / "r.json")], capture_output=True, text=True, check=True)
    return (lib / "T.lean").read_text(), json.loads((lib / "r.json").read_text())


class Portfolio(unittest.TestCase):
    def test_rewrites_only_proof_errors(self):
        log = "\n".join(
            [
                "error: T.lean:11:2: unsolved goals",
                "⊢ a < b + 1",
                "error: T.lean:19:0: Unknown identifier `foo`",  # statement error: not a hammer's business
                "error: T.lean:22:2: type mismatch",
            ]
        )
        out, rep = run(SRC, log)
        self.assertIn("theorem broken (a b : Nat) (h : a ≤ b) : a < b + 1 := by\n  first\n  | (grind; done; trace \"PORTFOLIO grind\")", out)
        self.assertNotIn("simp at h", out)
        self.assertIn("theorem ok_one : 1 = 1 := rfl", out)  # untouched
        self.assertIn("theorem bad_statement (a : Nat) : foo a = a := by\n  simp", out)  # untouched
        self.assertIn("theorem term_proof (a : Nat) : a = a := by\n  exact (Eq.refl a)", out)  # type mismatch: untouched
        self.assertEqual(rep["theorems_rewritten"], 1)
        self.assertTrue(out.rstrip().endswith("end T"))

    def test_pattern_matching_theorem_is_left_alone(self):
        out, rep = run(SRC, "error: T.lean:14:2: unsolved goals")
        self.assertIn("  | 0 => rfl", out)
        self.assertEqual(rep["theorems_rewritten"], 0)


class NoGoals(unittest.TestCase):
    SRC = "import Mathlib\n\ntheorem a (x : Nat) : x + 0 = x := by\n  simp\n  rfl\n\ntheorem b (x : Nat) : x = x := by\n  simp; rfl\n\ntheorem c (x : Nat) : x = x := by\n  skip\n  rfl\n"

    def test_deletes_the_superfluous_tactic(self):
        log = "error: T.lean:5:2: no goals to be solved\nerror: T.lean:8:8: no goals to be solved\n"
        out, rep = run(self.SRC, log)
        self.assertEqual(rep.get("superfluous_tactics_deleted"), 2)
        self.assertIn("theorem a (x : Nat) : x + 0 = x := by\n  simp\n\ntheorem b", out)
        self.assertIn("theorem b (x : Nat) : x = x := by\n  simp\n\ntheorem c", out)
        self.assertEqual(rep["theorems_rewritten"], 0)  # not rewritten by the hammer in the same round


if __name__ == "__main__":
    unittest.main()
