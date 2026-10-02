import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parents[1]


class Normalize(unittest.TestCase):
    def run_on(self, text: str) -> str:
        d = Path(tempfile.mkdtemp())
        (d / "Lib").mkdir()
        (d / "Lib" / "A.lean").write_text(text)
        subprocess.run([sys.executable, str(HERE / "engine.py"), "normalize-imports", "--lib", str(d), "--roots", "Lib"], check=True, capture_output=True)
        return (d / "Lib" / "A.lean").read_text()

    def test_mathlib_imports_become_the_umbrellas_and_own_imports_stay(self):
        out = self.run_on("/-\nCopyright\n-/\nimport Mathlib.Data.Nat.Basic\nimport Lib.Other\nimport Mathlib.Tactic.Ring\nimport Batteries.Data.List.Basic\n\nnamespace A\nimport Mathlib.NotAHeader\n")
        self.assertIn("import Mathlib\nimport Batteries\nimport Aesop\nimport Qq\nimport ProofWidgets\nimport Lib.Other", out)
        self.assertNotIn("Mathlib.Data.Nat.Basic", out)
        self.assertNotIn("Batteries.Data.List.Basic", out)
        self.assertIn("import Mathlib.NotAHeader", out)  # not in the header: untouched
        self.assertTrue(out.startswith("/-\nCopyright\n-/\n"))

    def test_module_files_keep_public(self):
        out = self.run_on("module\n\npublic import Mathlib.Algebra.Group.Defs\nimport Foo.Bar\n\n@[expose] public section\n")
        self.assertIn("module\n\npublic import Mathlib\npublic import Batteries", out)
        self.assertIn("import Foo.Bar", out)

    def test_module_files_get_public_umbrellas_even_when_the_first_import_was_private(self):
        out = self.run_on("module\n\nimport Mathlib.Tactic.Ring\npublic import Mathlib.Logic.Basic\n\npublic section\n")
        self.assertIn("public import Mathlib\npublic import Batteries", out)
        self.assertNotIn("\nimport Mathlib\n", out)

    def test_nothing_to_do(self):
        text = "import Lib.Other\n\ntheorem x : True := trivial\n"
        self.assertEqual(self.run_on(text), text)


class Available(unittest.TestCase):
    def test_umbrella_without_a_root_olean_is_not_imported(self):
        d = Path(tempfile.mkdtemp())
        (d / "Lib").mkdir()
        (d / "Lib" / "A.lean").write_text("import Mathlib.Data.Nat.Basic\nimport ProofWidgets.Component.Basic\n\ntheorem x : True := trivial\n")
        lp = d / "oleans"
        lp.mkdir()
        for m in ("Mathlib", "Batteries", "Aesop", "Qq"):  # no ProofWidgets.olean
            (lp / f"{m}.olean").write_text("")
        subprocess.run([sys.executable, str(HERE / "engine.py"), "normalize-imports", "--lib", str(d), "--roots", "Lib", "--lean-path", str(lp)], check=True, capture_output=True)
        out = (d / "Lib" / "A.lean").read_text()
        self.assertIn("import Mathlib\nimport Batteries\nimport Aesop\nimport Qq\n", out)
        self.assertNotIn("import ProofWidgets", out)


if __name__ == "__main__":
    unittest.main()
