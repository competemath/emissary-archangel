"""The copy of tengoku's isnad_tag.py that the factory tags bundles with names a theorem written `theorem _root_.A.b` as `A.b` (tengoku's tests have the grid; the pin in test_canonicalise_bundle.py ties this
copy to that file)."""
import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import isnad_tag as tg  # noqa: E402


class RootPrefixedNames(unittest.TestCase):
    def test_a_root_prefixed_theorem_is_found_under_its_own_name_only(self):
        for name in ("A.c", "A.B.c", "AlgebraicGeometry.GeometricallyIntegral.of_isPullback_of_geometricallyIntegral", "Foo.α_β"):
            self.assertTrue(tg.declared_name_matches(name, "_root_." + name), name)
            self.assertFalse(tg.declared_name_matches("X." + name, "_root_." + name), name)
            self.assertFalse(tg.declared_name_matches(name, "_root_." + name + "x"), name)
            self.assertTrue(tg.declared_name_matches("X." + name, name), name)  # the old rule: the last components, without _root_


if __name__ == "__main__":
    unittest.main()
