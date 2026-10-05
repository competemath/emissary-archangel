import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import bundle_rehead as br  # noqa: E402

OLD = "import Tengoku\nimport Tengoku.Std\nimport Tengoku.Tactic.Aesop\nimport Tengoku.Meta.Qq\n\ntheorem a : True := trivial\n"
NEW = "import Tengoku\n\ntheorem a : True := trivial\n"


class Rehead(unittest.TestCase):
    def test_the_four_umbrellas_become_one_import(self):
        self.assertEqual(br.rehead(OLD), NEW)

    def test_a_module_system_header_keeps_public(self):
        old = "module\n\npublic import Tengoku\npublic import Tengoku.Std\npublic import Tengoku.Tactic.Aesop\npublic import Tengoku.Meta.Qq\n\npublic section\n"
        self.assertEqual(br.rehead(old), "module\n\npublic import Tengoku\n\npublic section\n")

    def test_specific_seeded_modules_collapse_too(self):
        old = "public import Tengoku\npublic import Tengoku.NumberTheory.NumberField.InfinitePlace.Basic\npublic import Tengoku.Analysis.Quaternion\n\nx\n"
        self.assertEqual(br.rehead(old), "public import Tengoku\n\nx\n")
        both = "public import Tengoku\npublic import Tengoku.Analysis.Quaternion\nimport Tengoku.RingTheory.SimpleModule.WedderburnArtin\n\nx\n"
        self.assertEqual(br.rehead(both), "public import Tengoku\n\nx\n")
        self.assertEqual(br.rehead("import Tengoku.RingTheory.SimpleModule.WedderburnArtin\n\nx\n"), "import Tengoku\n\nx\n")

    def test_a_public_copy_makes_the_one_import_public(self):
        old = "module\n\nimport Tengoku.Std\npublic import Tengoku\nprivate import Tengoku.Meta.Qq\n\nx\n"
        self.assertEqual(br.rehead(old), "module\n\npublic import Tengoku\n\nx\n")
        self.assertEqual(br.rehead("meta import Tengoku.Std\npublic import Tengoku\n"), "public meta import Tengoku\n")

    def test_import_all_becomes_a_plain_import(self):
        self.assertEqual(br.rehead("import all Tengoku.Logic.Basic\n\nx\n"), "import Tengoku\n\nx\n")

    def test_the_library_and_other_libraries_are_not_touched(self):
        old = "import Tengoku\nimport Tengoku.Pfr.Entropy.Basic\nimport Tengoku.Vcvio\nimport Lean.Elab\n\nx\n"
        self.assertEqual(br.rehead(old), old)

    def test_only_the_header_is_rewritten(self):
        old = "/-!\n```lean\nimport Tengoku.Std\n```\n-/\nimport Tengoku.Std\n\n/-- import Tengoku.Std -/\ntheorem a : True := trivial\n\nimport Tengoku.Std\n"
        got = br.rehead(old)
        self.assertEqual(got, "/-!\n```lean\nimport Tengoku.Std\n```\n-/\nimport Tengoku\n\n/-- import Tengoku.Std -/\ntheorem a : True := trivial\n\nimport Tengoku.Std\n")

    def test_idempotent(self):
        for text in (OLD, NEW, "module\n\npublic import Tengoku\n\nx\n", ""):
            self.assertEqual(br.rehead(br.rehead(text)), br.rehead(text))

    def test_other_bytes_stay(self):
        old = "import Tengoku.Std\r\nimport Tengoku\r\n\r\ntheorem a : True := trivial -- ünï\r\n"
        self.assertEqual(br.rehead(old), "import Tengoku\r\n\r\ntheorem a : True := trivial -- ünï\r\n")

    def test_a_bundle_directory(self):
        with tempfile.TemporaryDirectory() as t:
            d = Path(t) / "bundle"
            (d / "Tengoku" / "Lib").mkdir(parents=True)
            (d / "Tengoku" / "Lib" / "A.lean").write_text(OLD)
            (d / "Tengoku" / "Lib" / "B.lean").write_text(NEW)
            (d / "Tengoku" / "Lib" / "Deps.lean").write_text("-- Lib: marker\n")
            (d / "Tengoku" / "Lib.lean").write_text("import Tengoku.Lib.A\nimport Tengoku.Lib.B\n")
            self.assertEqual(br.rehead_dir(d), {"files": 3, "changed": 1})
            self.assertEqual((d / "Tengoku/Lib/A.lean").read_text(), NEW)
            self.assertEqual((d / "Tengoku/Lib.lean").read_text(), "import Tengoku.Lib.A\nimport Tengoku.Lib.B\n")
            self.assertEqual(br.rehead_dir(d), {"files": 3, "changed": 0})


if __name__ == "__main__":
    unittest.main()
