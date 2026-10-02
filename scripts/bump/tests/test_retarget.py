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


if __name__ == "__main__":
    unittest.main()
