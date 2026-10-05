import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import autonames as an  # noqa: E402


class Rewrite(unittest.TestCase):
    """Regression of 2026-10-05: flt's merge-queue ejection. Every line below is from the real failure (modules of the FLT library, root `FLT`)."""

    REAL = [
        ("attribute [local instance] instAlgebraForall_fLT", "attribute [local instance] instAlgebraForall_tengoku"),
        ("attribute [local instance] MeasureTheory.instMeasurableAddSubtypeMemAddSubgroup_fLT", "attribute [local instance] MeasureTheory.instMeasurableAddSubtypeMemAddSubgroup_tengoku"),
        ("attribute [local instance] WeierstrassCurve.instIsEllipticBaseChange_fLT", "attribute [local instance] WeierstrassCurve.instIsEllipticBaseChange_tengoku"),
        ("example : IsScalarTower A B C := @instIsScalarTowerUnits_fLT A B C _ _ _", "example : IsScalarTower A B C := @instIsScalarTowerUnits_tengoku A B C _ _ _"),
    ]

    def test_the_real_failures(self):
        for old, new in self.REAL:
            self.assertEqual(an.rewrite(old, "FLT"), (new, 1), old)

    def test_the_suffix_follows_the_library_root(self):
        self.assertEqual(an.suffix_of("FLT"), "fLT")
        self.assertEqual(an.suffix_of("PrimeNumberTheoremAnd"), "primeNumberTheoremAnd")
        self.assertEqual(an.suffix_of("Tengoku"), "tengoku")
        self.assertEqual(an.rewrite("open X in instFoo_primeNumberTheoremAnd", "PrimeNumberTheoremAnd")[0], "open X in instFoo_tengoku")

    def test_only_this_librarys_suffix_and_only_instance_names(self):
        for text in (
            "instFoo_pFR",  # another library's suffix
            "instFoo",  # no suffix: no clash
            "instFoo_fLTx",  # a longer name
            "foo_fLT",  # not an instance name
            "Mathlib.instFoo_tengoku",  # already the tree's
            "instFoo_fLT'",  # a different name (prime)
        ):
            self.assertEqual(an.rewrite(text, "FLT"), (text, 0), text)

    def test_the_name_must_start_with_inst_in_its_last_component(self):
        self.assertEqual(an.rewrite("xinstFoo_fLT", "FLT"), ("xinstFoo_fLT", 0))
        self.assertEqual(an.rewrite("Foo.xinst_fLT", "FLT"), ("Foo.xinst_fLT", 0))
        self.assertEqual(an.rewrite("Foo.inst_fLT", "FLT"), ("Foo.inst_tengoku", 1))

    def test_several_on_a_line_and_idempotent(self):
        text = "attribute [local instance] instA_fLT, B.instB_fLT\n"
        once, n = an.rewrite(text, "FLT")
        self.assertEqual((once, n), ("attribute [local instance] instA_tengoku, B.instB_tengoku\n", 2))
        self.assertEqual(an.rewrite(once, "FLT"), (once, 0))

    def test_a_library_rooted_tengoku_is_left_alone(self):
        self.assertEqual(an.rewrite("instFoo_tengoku", "Tengoku"), ("instFoo_tengoku", 0))

    def test_unicode_and_primes_in_names(self):
        self.assertEqual(an.rewrite("instFoo'_fLT", "FLT"), ("instFoo'_tengoku", 1))
        self.assertEqual(an.rewrite("instΦ_fLT", "FLT"), ("instΦ_tengoku", 1))


class Directory(unittest.TestCase):
    def test_each_file_uses_its_own_root(self):
        with tempfile.TemporaryDirectory() as t:
            b = Path(t) / "bundle"
            (b / "Tengoku" / "Flt" / "FLT" / "A").mkdir(parents=True)
            (b / "Tengoku" / "Flt" / "FLT" / "A" / "B.lean").write_text("attribute [local instance] instX_fLT\n")
            (b / "Tengoku" / "Flt" / "Other").mkdir()
            (b / "Tengoku" / "Flt" / "Other" / "C.lean").write_text("attribute [local instance] instX_fLT instY_other\n")  # root Other: its suffix is `other`
            (b / "Tengoku" / "Flt" / "Solo.lean").write_text("instZ_solo\n")  # a file at the top: its own stem is the root
            (b / "Tengoku" / "Flt" / "Deps.lean").write_text("instD_deps\n")  # the marker is never touched
            (b / "Tengoku" / "Flt.lean").write_text("import Tengoku.Flt.Solo\n")
            r = an.rewrite_dir(b)
            self.assertEqual(r, {"files": 3, "changed": 3, "names": 3})
            self.assertEqual((b / "Tengoku/Flt/FLT/A/B.lean").read_text(), "attribute [local instance] instX_tengoku\n")
            self.assertEqual((b / "Tengoku/Flt/Other/C.lean").read_text(), "attribute [local instance] instX_fLT instY_tengoku\n")
            self.assertEqual((b / "Tengoku/Flt/Solo.lean").read_text(), "instZ_tengoku\n")
            self.assertEqual((b / "Tengoku/Flt/Deps.lean").read_text(), "instD_deps\n")
            self.assertEqual(an.rewrite_dir(b), {"files": 3, "changed": 0, "names": 0})


if __name__ == "__main__":
    unittest.main()
