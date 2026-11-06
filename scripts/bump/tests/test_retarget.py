import importlib.util
import json
import re
import sys
import unittest
from pathlib import Path

spec = importlib.util.spec_from_file_location("tlb", Path(__file__).resolve().parents[2] / "trial-library-build.py")
tlb = importlib.util.module_from_spec(spec)
sys.modules["tlb"] = tlb
spec.loader.exec_module(tlb)

REAL = json.loads((Path(__file__).resolve().parent / "fixtures" / "real-lakefiles.json").read_text())  # lakefile.lean of the registered libraries, at the commits sources.json pins

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


MATHLIB_REQUIRE = re.compile(r'^\s*require\s+(?:«?mathlib»?\b|"[^"]+"\s*/\s*(?:«?mathlib»?\b|"mathlib"))', re.M)


class EveryMathlibSpelling(unittest.TestCase):
    """compply and polyfun write `require "leanprover-community" / mathlib @ git "v4.35.0"` (the name not in quotes): retarget_lean did not know the spelling, appended a SECOND require, and
    every shard of the bump died with "`mathlib` has already been declared" (2026-11-06). Every way Lake accepts a Mathlib require, with and without other requires around it."""

    def spellings(self):
        out = []
        for scope in ("leanprover-community", "leanprover"):
            for name in ("mathlib", '"mathlib"', "«mathlib»"):
                for tail in (' @ git "v1.2.3"', ' @ "v1.2.3"', ""):
                    out.append(f'require "{scope}" / {name}{tail}')
        for name in ("mathlib", "«mathlib»"):
            out.append(f'require {name} from git "https://github.com/leanprover-community/mathlib4.git" @ "v1.2.3"')
            out.append(f'require {name} from git\n  "https://github.com/leanprover-community/mathlib4.git" @ "v1.2.3"')
            out.append(f'require {name} @ git "v1.2.3"')
        return out

    def test_grid(self):
        cases = 0
        for req in self.spellings():
            for before in ("", 'require batteries from git "https://github.com/leanprover-community/batteries" @ "main"\n'):
                for after in ("", '\nrequire aesop from git "https://github.com/leanprover-community/aesop" @ "master"\n'):
                    for tail in ("", "\n", "\n\n@[default_target]\nlean_lib X\n"):
                        text = f"import Lake\nopen Lake DSL\n\npackage X\n\n{before}{req}\n{after}{tail}"
                        out = tlb.retarget_lean(text, "v9.9.9")
                        cases += 1
                        self.assertEqual(len(MATHLIB_REQUIRE.findall(out)), 1, f"exactly one Mathlib require, not a second one appended:\n{req}\n---\n{out}")
                        self.assertIn('"v9.9.9"', out, req)
                        self.assertNotIn('"v1.2.3"', out, req)
                        self.assertEqual(out.count("require"), text.count("require"), f"no require added or lost:\n{req}")
                        self.assertEqual(tlb.retarget_lean(out, "v9.9.9"), out, f"retargeting twice changes nothing:\n{req}")
        self.assertGreaterEqual(cases, 288)  # 24 spellings x 2 x 2 x 3 surroundings

    def test_the_real_compply_lakefile(self):
        text = REAL["compply"]
        self.assertRegex(text, r'require "leanprover-community" / mathlib @ git "v4\.33\.1"')
        out = tlb.retarget_lean(text, "v4.34.0-rc2")
        self.assertEqual(len(MATHLIB_REQUIRE.findall(out)), 1)
        self.assertIn('/ mathlib @ git "v4.34.0-rc2"', out)

    def test_every_real_lakefile_of_the_registry(self):
        """The lakefile.lean of every registered library that has one (35, at the commits sources.json pins): after the retarget there is exactly one Mathlib require, with the target revision,
        and retargeting again changes nothing."""
        self.assertGreaterEqual(len(REAL), 30)
        for key, text in REAL.items():
            out = tlb.retarget_lean(text, "v4.34.0-rc2")
            self.assertEqual(len(MATHLIB_REQUIRE.findall(out)), 1, f"{key}:\n{out[-600:]}")
            self.assertEqual(tlb.retarget_lean(out, "v4.34.0-rc2"), out, key)


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


class ForkedMathlib(unittest.TestCase):
    """grothendieck-riemann-roch requires Mathlib from vaca22/mathlib4 @ a commit: on the tree's Mathlib it is the official repository at the tree's tag."""

    def test_lean_fork_url_becomes_the_official_one(self):
        out = tlb.retarget_lean('require mathlib from git\n  "https://github.com/vaca22/mathlib4" @ "38ddc37712cd"\n', "v4.34.0-rc2")
        self.assertIn('"https://github.com/leanprover-community/mathlib4.git" @ "v4.34.0-rc2"', out)
        self.assertNotIn("vaca22", out)

    def test_toml_fork_url_becomes_the_official_one(self):
        import tempfile

        d = Path(tempfile.mkdtemp())
        (d / "lakefile.toml").write_text('name = "X"\n\n[[require]]\nname = "mathlib"\ngit = "https://github.com/someone/mathlib4"\nrev = "abc"\n')
        tlb.retarget(str(d), "v4.34.0-rc2", "leanprover/lean4:v4.34.0-rc2")
        out = (d / "lakefile.toml").read_text()
        self.assertIn(tlb.MATHLIB_URL, out)
        self.assertNotIn("someone", out)

    def test_other_packages_with_mathlib_in_the_name_are_left(self):
        self.assertEqual(tlb.official_url("https://github.com/x/mathlib4-extras"), "https://github.com/x/mathlib4-extras")


if __name__ == "__main__":
    unittest.main()
