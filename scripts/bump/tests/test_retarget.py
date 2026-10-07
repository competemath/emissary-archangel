import importlib.util
import sys
import unittest
from pathlib import Path

spec = importlib.util.spec_from_file_location("tlb", Path(__file__).resolve().parents[2] / "trial-library-build.py")
tlb = importlib.util.module_from_spec(spec)
sys.modules["tlb"] = tlb
spec.loader.exec_module(tlb)

SLT = '''import Lake
open Lake DSL

package «SLT» where
  leanOptions := #[]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.32.0"

@[default_target]
lean_lib «SLT» where
  globs := #[.submodules `SLT]

meta if get_config? env = some "dev" then
require «doc-gen4» from git
  "https://github.com/leanprover/doc-gen4" @ "v4.32.0"
'''


class RetargetLean(unittest.TestCase):
    def test_dev_require_and_its_meta_if_guard_go_together(self):
        out = tlb.retarget_lean(SLT, "v4.34.0-rc2")
        self.assertIn('@ "v4.34.0-rc2"', out)
        self.assertNotIn("doc-gen4", out)
        self.assertNotIn("meta if", out)
        # what the bump workflow appends afterwards is a top-level target again
        self.assertTrue((out + "\nlean_lib Vendor\n").rstrip().endswith("lean_lib Vendor"))
        self.assertNotIn("then\n\nlean_lib Vendor", out + "\nlean_lib Vendor\n")

    def test_reservoir_spelling(self):
        out = tlb.retarget_lean('require "leanprover-community" / "mathlib" @ git "v4.1.0"\n', "v9")
        self.assertIn('@ git "v9"', out)


CL = """name = "complexitylib"

[[require]]
name = "mathlib"
scope = "leanprover-community"
rev = "728a93eeff833da3173895bb0575752fdc24edb0"

[[require]]
name = "cslib"
git = "https://github.com/leanprover/cslib"
rev = "311d27ad8458b61e9b7461fc83a480e4be97aef2"

[[lean_lib]]
name = "Complexitylib"
"""


class MathlibLast(unittest.TestCase):
    """Lake: `mismatched dependencies … Try putting `require mathlib` last` (the shards of complexitylib, which requires cslib, 2026-10-07)"""

    def requires(self, text):
        return [ln.split('"')[1] for ln in text.splitlines() if ln.startswith("name =")]

    def test_mathlib_goes_behind_the_other_requires_and_the_libs(self):
        out = tlb.mathlib_last(CL)
        self.assertEqual(self.requires(out), ["complexitylib", "cslib", "Complexitylib", "mathlib"])
        self.assertTrue(out.rstrip().endswith('rev = "728a93eeff833da3173895bb0575752fdc24edb0"'))
        self.assertIn('git = "https://github.com/leanprover/cslib"', out)
        self.assertEqual(out.count("[[require]]"), 2)

    def test_a_file_that_has_it_last_or_not_at_all_is_unchanged(self):
        last = tlb.mathlib_last(CL)
        self.assertEqual(tlb.mathlib_last(last), last)
        nomath = 'name = "x"\n\n[[require]]\nname = "linters"\nrev = "main"\n'
        self.assertEqual(tlb.mathlib_last(nomath), nomath)

    def test_retarget_leaves_mathlib_last_with_the_new_revision(self):
        import tempfile

        d = Path(tempfile.mkdtemp())
        (d / "lakefile.toml").write_text(CL)
        tlb.retarget(str(d), "v4.34.0-rc2", "leanprover/lean4:v4.34.0-rc2")
        out = (d / "lakefile.toml").read_text()
        self.assertEqual(self.requires(out)[-1], "mathlib")
        self.assertTrue(out.rstrip().endswith('rev = "v4.34.0-rc2"'))
        self.assertNotIn("728a93eeff", out)


class InheritedMathlib(unittest.TestCase):
    def test_toml_without_a_mathlib_require_gets_one(self):
        import tempfile

        d = Path(tempfile.mkdtemp())
        (d / "lakefile.toml").write_text('name = "Seymour"\n\n[[require]]\nname = "linters"\ngit = "https://github.com/madvorak/leanters"\nrev = "main"\n\n[[lean_lib]]\nname = "Seymour"\n')
        tlb.retarget(str(d), "v4.34.0-rc2", "leanprover/lean4:v4.34.0-rc2")
        out = (d / "lakefile.toml").read_text()
        self.assertIn('name = "mathlib"', out)
        self.assertIn('rev = "v4.34.0-rc2"', out)
        self.assertIn('name = "linters"', out)

    def test_lean_without_a_mathlib_require_gets_one(self):
        out = tlb.retarget_lean("import Lake\nopen Lake DSL\npackage x\nrequire linters from git \"https://x/y\"\n", "v9")
        self.assertIn('require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "v9"', out)


if __name__ == "__main__":
    unittest.main()
