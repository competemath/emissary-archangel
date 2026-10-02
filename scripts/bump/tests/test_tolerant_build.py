"""Header parsing of scripts/bump/tolerant_build.py: the scheduler orders modules by these imports, so a missed import
starts a module before its dependency (zkevm-clean: a multi-line copyright block hid every import below it)."""

import importlib.util
import sys
import unittest
from pathlib import Path

spec = importlib.util.spec_from_file_location("tolerant_build", Path(__file__).resolve().parents[1] / "tolerant_build.py")
tb = importlib.util.module_from_spec(spec)
sys.modules["tolerant_build"] = tb
spec.loader.exec_module(tb)


class HeaderImports(unittest.TestCase):
    def test_copyright_block_then_imports(self):
        text = "/-\nCopyright (c) 2024 X. All rights reserved.\nReleased under Apache 2.0 license.\nAuthors: Y\n-/\nimport Mathlib.Data.Nat.Basic\nimport Clean.Utils.Misc\n\nnamespace A\n"
        self.assertEqual(tb.header_imports(text), ["Mathlib.Data.Nat.Basic", "Clean.Utils.Misc"])

    def test_module_keyword_public_imports_and_comments(self):
        text = "module\n\n-- a comment\npublic import Mathlib.Algebra.Group.Defs -- trailing\nmeta import Lean.Elab.Command\nimport all Foo.Bar\n/-! module doc\nimport NotAnImport\n-/\nimport After.Doc\ntheorem x : True := trivial\nimport Too.Late\n"
        self.assertEqual(tb.header_imports(text), ["Mathlib.Algebra.Group.Defs", "Lean.Elab.Command", "Foo.Bar", "After.Doc"])

    def test_nested_comment_and_prelude(self):
        text = "prelude\n/- outer /- inner -/ still outer\nimport Hidden -/\nimport Init.Core\n"
        self.assertEqual(tb.header_imports(text), ["Init.Core"])

    def test_no_imports(self):
        self.assertEqual(tb.header_imports("namespace Foo\nimport NotAHeader\n"), [])
        self.assertEqual(tb.header_imports(""), [])

    def test_guillemets_and_dotted_names(self):
        self.assertEqual(tb.header_imports("import Foo.«1102.4662».C\nimport «weird name».B\n"), ["Foo.«1102.4662».C", "«weird name».B"])


if __name__ == "__main__":
    unittest.main()
