"""lean_names.names: the Lean names a module declares, as the tree's single environment sees them."""

import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import lean_names  # noqa: E402


class Names(unittest.TestCase):
    def test_namespaces_sections_and_root_names(self):
        text = """namespace Foo

theorem a : True := trivial

section Bar
def b : Nat := 1
end Bar

namespace Baz
theorem _root_.Elsewhere.c : True := trivial
end Baz

end Foo

theorem top : True := trivial
"""
        self.assertEqual(lean_names.names(text), {"Foo.a", "Foo.b", "Elsewhere.c", "top"})

    def test_private_declarations_comments_and_strings_do_not_count(self):
        text = """namespace N
private theorem hidden : True := trivial
/- theorem in_a_block_comment : True := trivial -/
-- theorem in_a_line_comment : True := trivial
def s : String := "theorem in_a_string"
@[simp] theorem shown : True := trivial
protected def mk : Nat := 0
end N
"""
        self.assertEqual(lean_names.names(text), {"N.s", "N.shown", "N.mk"})

    def test_instance_structure_and_class_names(self):
        self.assertEqual(lean_names.names("namespace X\nstructure S where\n  a : Nat\nclass C (a : Type) where\ninductive I where\n  | a\nend X\n"), {"X.S", "X.C", "X.I"})


if __name__ == "__main__":
    unittest.main()
