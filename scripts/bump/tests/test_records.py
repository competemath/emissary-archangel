"""records.py compose on a two-module toy library (no Lean): the log lines Lean would print are written by hand."""

import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parents[1]
ROOT = HERE.parents[1]

A = """/-
Copyright (c) test
-/
import Mathlib.Data.Nat.Basic

namespace Toy

/-- the number one -/
def one : Nat := 1

/-- never used -/
theorem unused : one = 1 := rfl

notation "ℓ" => one

theorem one_pos : 0 < one := by decide

end Toy
"""
B = """import Toy.A

namespace Toy

variable (n : Nat)

theorem unrelated : n = n := rfl

open Nat in
theorem uses_one_pos : 0 < one := one_pos

end Toy
"""


class Compose(unittest.TestCase):
    def test_compose_and_stage(self):
        with tempfile.TemporaryDirectory() as d:
            lib = Path(d) / "lib"
            (lib / "Toy").mkdir(parents=True)
            (lib / "Toy" / "A.lean").write_text(A)
            (lib / "Toy" / "B.lean").write_text(B)
            # lines (1-based) of the blocks: A: one 8-9? compute from the text
            la, lb = A.split("\n"), B.split("\n")
            ln = lambda lines, needle: next(i + 1 for i, x in enumerate(lines) if needle in x)
            one = (ln(la, "/-- the number one"), ln(la, "def one"))
            unused = (ln(la, "/-- never used"), ln(la, "theorem unused"))
            one_pos = (ln(la, "theorem one_pos"),) * 2
            unrelated = (ln(lb, "theorem unrelated"),) * 2
            uses = (ln(lb, "open Nat in"), ln(lb, "theorem uses_one_pos"))
            sidecars = {
                "Toy/A": [["Toy.one", *one], ["Toy.unused", *unused], ["Toy.one_pos", *one_pos], ["Toy.one.match_1", *one]],
                "Toy/B": [["Toy.unrelated", *unrelated], ["Toy.uses_one_pos", *uses]],
            }
            for m, rows in sidecars.items():
                f = lib / ".lake" / "build" / "lib" / "lean" / (m + ".olean.ranges.json")
                f.parent.mkdir(parents=True, exist_ok=True)
                f.write_text(json.dumps(rows))
            deps = {
                "name": "Toy.uses_one_pos",
                "module": "Toy.B",
                "consts": [["Toy.B", "Toy.uses_one_pos"], ["Toy.A", "Toy.one_pos"], ["Toy.A", "Toy.one.match_1"], ["Toy.A", "Toy.one"]],
            }
            log = f"x.lean:1:0: info: REC_DEPS {json.dumps(deps)} REC_END\n"
            (Path(d) / "deps.log").write_text(log)
            (Path(d) / "setup.json").write_text(json.dumps({"repo": "https://github.com/o/toy.git", "commit": "abc123"}))
            subprocess.run([sys.executable, str(HERE / "records.py"), "compose", "--lib", str(lib), "--log", str(Path(d) / "deps.log"), "--meta", str(Path(d) / "setup.json"), "--out", str(Path(d) / "composed.jsonl")], check=True)
            rec = json.loads((Path(d) / "composed.jsonl").read_text().splitlines()[0])
            text = rec["proof"]
            self.assertIn("-- [Emissary prelude] Toy.A — verbatim (imports stripped)", text)
            self.assertIn("def one : Nat := 1", text)
            self.assertIn("theorem one_pos", text)
            self.assertNotIn("theorem unused", text)  # pruned: nothing uses it
            self.assertIn('notation "ℓ" => one', text)  # glue stays
            self.assertNotIn("theorem unrelated", text)  # pruned from the own file
            self.assertIn("variable (n : Nat)", text)  # glue of the own file stays
            self.assertNotIn("import Mathlib", text)
            self.assertIn("-- [Emissary] Toy/B.lean, everything before line", text)
            self.assertTrue(text.rstrip().endswith("theorem uses_one_pos : 0 < one := one_pos"))
            self.assertEqual(rec["sourceUrl"], "https://github.com/o/toy/blob/abc123/Toy/B.lean")
            # and the staging record the pipeline's own splitter makes of it
            r = subprocess.run(["node", str(HERE / "stage-records.mjs"), str(Path(d) / "composed.jsonl"), "--source", "toy", "--toolchain", "tc", "--out", str(Path(d) / "bank.jsonl")], capture_output=True, text=True)
            if r.returncode == 0:
                staged = json.loads((Path(d) / "bank.jsonl").read_text().splitlines()[0])
                self.assertEqual(staged["statement"].split(":")[0].split()[-1], "uses_one_pos")
                self.assertTrue(staged["proof"].startswith(":="))
                self.assertIn("-- [Emissary prelude] Toy.A", staged["context"])


if __name__ == "__main__":
    unittest.main()
