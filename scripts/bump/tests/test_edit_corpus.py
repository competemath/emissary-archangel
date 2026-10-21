"""The corpus of edit_corpus.py, without Lean: every pattern yields the edited texts the real-Lean run builds, and the edits keep their text-level promises.

The metamorphic test itself (original and edited libraries built by a real `lean`, fingerprints compared) runs in CI (bundle-keep-tests.yml, step 'The edits keep the meaning of every Lean scoping
construct of the corpus'). Here: the corpus is well-formed, so that a pattern added later cannot be silently skipped.
"""

import re
import sys
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(HERE / "tests"))
import edit_corpus as ec  # noqa: E402
import tree_dups as td  # noqa: E402


class Corpus(unittest.TestCase):
    def test_every_pattern_has_a_reason_a_unique_name_and_three_modules_that_import_each_other_in_a_chain(self):
        names = [p.name for p in ec.PATTERNS]
        self.assertEqual(len(names), len(set(names)))
        for p in ec.PATTERNS:
            self.assertTrue(p.why.strip(), p.name)
            self.assertNotIn("import", p.base, f"{p.name}: Base imports nothing")
            self.assertIn("import Tengoku.{lib}.Base", p.x, p.name)
            self.assertIn("import Tengoku.{lib}.X", p.user, p.name)
            self.assertEqual(p.module_system, p.base.startswith("module"), f"{p.name}: all three modules are of the module system or none is")
            self.assertEqual(p.module_system, p.x.startswith("module") and p.user.startswith("module"), p.name)

    def test_the_corpus_covers_the_constructs_the_edits_have_broken_on(self):
        text = "\n".join(p.name for p in ec.PATTERNS)
        for must in ("reopened_namespace_bare_name", "namespace_no_import_declares", "open_namespace_both_sides", "module_system", "instances_across_modules"):
            self.assertIn(must, text)

    def test_every_pattern_gets_a_fork_variant_with_the_namespace_and_an_alias_variant_with_the_trees_module_and_the_kept_imports(self):
        for p in ec.PATTERNS:
            fk = ec.fork_variant(p)
            self.assertEqual(sorted(fk), ["User", "X"])
            for m, text in fk.items():
                self.assertIn(f"namespace {ec.FORK_NS}\n", text, f"{p.name}/{m}")
            self.assertIn("Tengoku.EF.X", fk["User"], p.name)  # the importer imports the wrapped copy
            self.assertIn("Tengoku.E.Base", fk["X"], p.name)  # and the copy still imports the unwrapped base
            tree, imp = ec.alias_variant(p)
            self.assertEqual(tree["X"], ec.files_for(p, "E")["X"], p.name)  # the tree's module is an identical copy
            self.assertIn("Tengoku.ET.X", imp["User"], p.name)
            self.assertIn("Tengoku.E.Base", imp["User"], f"{p.name}: the importer keeps what the aliased copy imported")
            self.assertNotIn("Tengoku.E.X", imp["User"], p.name)

    def test_the_edit_is_the_one_the_factory_makes(self):
        """the corpus uses tree_dups' own functions, never a copy of them"""
        p = ec.PATTERNS[0]
        self.assertEqual(ec.fork_variant(p)["X"], td.apply_fork_text(ec.files_for(p, "E", user_imports="Tengoku.EF.X")["X"], ec.FORK_NS))

    def test_an_open_command_in_a_comment_is_prose_and_one_in_code_opens_both_namespaces(self):
        out = td.apply_fork_text("import Tengoku.A\n\n/-- open the door\nopen Foo\n-/\nopen Set Nat\nopen scoped Topology\nopen A in\ndef x := 1\n", "ToyFork")
        self.assertIn("/-- open the door\nopen Foo\n-/", out)
        self.assertIn("open Set _root_.Set Nat _root_.Nat\n", out)
        self.assertIn("open scoped Topology _root_.Topology\n", out)
        self.assertIn("open A _root_.A in\ndef x := 1", out)
        self.assertEqual(len(re.findall(r"^namespace Foo$", out, re.M)), 0, "a namespace named in a comment is not registered")

    def test_an_open_with_hiding_renaming_or_a_list_is_left_alone(self):
        text = "import Tengoku.A\nopen B hiding c\nopen C (d e)\nopen D renaming f → g\n"
        out = td.apply_fork_text(text, "ToyFork")
        for line in ("open B hiding c", "open C (d e)", "open D renaming f → g"):
            self.assertIn(line + "\n", out)
        self.assertNotIn("_root_", out)


if __name__ == "__main__":
    unittest.main()
