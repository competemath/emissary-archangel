"""p2m_util.py writes the shortcuts of the library's `P2M/Util.lean` out as plain Lean, on the REAL files of flt-anthropic (commit aa2d8b34, fixtures/p2m-real/*.lean, whole files, unchanged).

The real case: 59,022 of the library's 60,478 modules import P2M.Util; its `elab` commands run the library's code while a module compiles, which the tree's lint refuses; 15,006 declarations that
passed Gate 2 stayed out because of it (bump run 43686274801). Over the whole library, measured when this was written (every .lean file, `rewrite_module`): 29,510 of the 29,511 Theorems modules
are written out (the one left has a header this does not read); 37,086 + 5,621 opens, 38,429 exports (247 of them without a namespace, dropped), 66,150 reactivations; 250 modules keep the import
(233 with `p2m_alias`, 20 with `p2m_export_all`, the one theorem, Util.lean itself).

Invariants: no statement is touched (a Theorems module is the same text up to `:= by`); no line is added or moved (except the import line and a `#p2m_type_eq*` line, which go); a comment or a string
that names a shortcut is not code and is not touched; a module with something this cannot write out is returned exactly as it was; rewriting the result changes nothing; the import goes only when no
shortcut is left. The Lean side (same types, same values as the shortcuts) is p2m_util_probe.py, run by .github/workflows/p2m-util-tests.yml.
Mutants (each must fail a check): the hidden names of `p2m_open` dropped, `p2m_open` written as `open scoped`, the binder names dropped from the exact term, the import kept, comments rewritten.
"""

from __future__ import annotations

import inspect
import re
import sys
import unittest
from collections import Counter
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))

import p2m_util as pu  # noqa: E402

FX = HERE / "fixtures" / "p2m-real"


def real(name: str) -> str:
    return (FX / name).read_text(encoding="utf-8")


def lines(text: str) -> list[str]:
    return text.split("\n")


class TheTheoremsModules(unittest.TestCase):
    def test_the_fermat_five_wrapper_is_written_out(self):
        t = real("Thm_fermatLastTheoremFive.lean")
        new, done, left = pu.rewrite_module(t)
        self.assertEqual(
            new,
            "import Mathlib\nimport P2M.Sol.S_fermatLastTheoremFive\n\ntheorem fermatLastTheoremFive : FermatLastTheoremFor 5 := by exact @_root_.P2MW.S_fermatLastTheoremFive.solution\n",
        )
        self.assertEqual((dict(done), dict(left)), ({"p2m_exact_reverting": 1}, {}))

    def test_binders_of_every_kind_become_the_arguments_of_the_solution(self):
        new, _, _ = pu.rewrite_module(real("Thm_CuspForm_stableT.lean"))
        self.assertTrue(new.rstrip("\n").endswith("by exact @_root_.P2MW.S_CuspForm_stableT.solution M _ H k ℓ hℓ hℓM"))  # (M) [NeZero M] (H) (k) {ℓ} (hℓ) (hℓM): an instance with no name is `_`

    def test_the_header_may_put_its_name_on_the_next_line(self):
        t = real("Thm_LanglandsTunnell_CubicInduction_isOpen_congruenceK1.lean")
        self.assertRegex(t, r"theorem\n")
        new, done, _ = pu.rewrite_module(t)
        self.assertTrue(new.rstrip("\n").endswith("solution R K _ _ _ _ _ v c"), new[-120:])
        self.assertEqual(dict(done), {"p2m_exact_reverting": 1})

    def test_a_hypothesis_with_no_name_is_found_by_its_type(self):
        t = real("Thm_CuspForm_exists_isNewform_descent.lean")
        new, _, _ = pu.rewrite_module(t)
        self.assertTrue(new.rstrip("\n").endswith("solution N _ f hf"))
        anon = pu.rewrite_module("import P2M.Util\ntheorem T (K : Type) (_ : CommRing K) (n : ℕ) : n = n := by p2m_exact_reverting @_root_.P2MW.S_T.solution")[0]
        self.assertTrue(anon.rstrip("\n").endswith("solution K ‹CommRing K› n"), anon)

    def test_the_statement_is_the_same_text(self):
        """everything from `theorem` to the `:= by` is the same text, character for character: the rewrite touches the proof and the commands before it"""
        for f in ("Thm_CuspForm_stableT.lean", "Thm_fermatLastTheoremFive.lean", "Thm_CuspForm_exists_isNewform_descent.lean", "Thm_LanglandsTunnell_CubicInduction_isOpen_congruenceK1.lean"):
            t = real(f)
            new, _, _ = pu.rewrite_module(t)
            statement = lambda s: s[s.index("theorem") :].split(":= by")[0]  # noqa: E731
            self.assertEqual(statement(new), statement(t), f)
            self.assertNotIn("P2M.Util", new)

    def test_the_one_header_that_is_not_read_leaves_the_module_as_it_was(self):
        t = real("Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_AnnulusDatumLevel_den_circleDeg_eq_one_and_den_depthMoment_eq_one_of_inertiaStable.lean")
        new, done, left = pu.rewrite_module(t)
        self.assertEqual(new, t)
        self.assertEqual((dict(done), dict(left)), ({}, {"p2m_exact_reverting": 1}))


class SeveralTheorems(unittest.TestCase):
    """the probe's toy module has three theorems; the library's Theorems modules have one each, but a module with several must not be left half done (found by the first real Lean run, p2m-util-tests)"""

    def test_every_theorem_of_a_module_is_written_out(self):
        t = (
            "import P2M.Util\ntheorem a (n : ℕ) : n = n := by p2m_exact_reverting @_root_.P2MW.S_a.solution\n"
            "theorem\nb : True := by p2m_exact_reverting @_root_.P2MW.S_b.solution\n"
            "theorem c.{u} {β : Sort u}\n    (x : β) :\n    x = x := by p2m_exact_reverting @_root_.P2MW.S_c.solution\n"
        )
        new, done, left = pu.rewrite_module(t)
        self.assertEqual(
            new,
            "theorem a (n : ℕ) : n = n := by exact @_root_.P2MW.S_a.solution n\ntheorem\nb : True := by exact @_root_.P2MW.S_b.solution\n"
            "theorem c.{u} {β : Sort u}\n    (x : β) :\n    x = x := by exact @_root_.P2MW.S_c.solution β x\n",
        )
        self.assertEqual((dict(done), dict(left)), ({"p2m_exact_reverting": 3}, {}))

    def test_one_that_cannot_be_written_out_leaves_the_module_as_it_was(self):
        t = "import P2M.Util\ntheorem a : True := by p2m_exact_reverting @_root_.P2MW.S_a.solution\ntheorem b (x := 1) : True := by p2m_exact_reverting @_root_.P2MW.S_b.solution\n"
        new, done, left = pu.rewrite_module(t)
        self.assertEqual((new, dict(done)), (t, {}))
        self.assertEqual(dict(left), {"p2m_exact_reverting": 1})

    def test_a_comment_that_names_the_tactic_is_not_one(self):
        t = "import P2M.Util\n/- the proof is `by p2m_exact_reverting @_root_.P2MW.S_a.solution` in the library -/\ntheorem a : True := by p2m_exact_reverting @_root_.P2MW.S_a.solution\n"
        new, done, left = pu.rewrite_module(t)
        self.assertTrue(new.rstrip("\n").endswith("by exact @_root_.P2MW.S_a.solution"))
        self.assertIn("`by p2m_exact_reverting @_root_", new)  # the comment is untouched
        self.assertEqual((dict(done), dict(left)), ({"p2m_exact_reverting": 1}, {}))


class TheEdges(unittest.TestCase):
    """what cubic found on #203: forms of the same things this had not looked at"""

    def test_reactivate_takes_every_word_verbatim_open_scoped_reads_the_tilde(self):
        self.assertEqual(pu.scoped_commands("A.B C~x", False, tilde=False), "open scoped A.B C~x")
        self.assertEqual(pu.scoped_commands("A.B C~x", False), "open scoped A.B C")
        new, _, _ = pu.rewrite_module('import P2M.Util\np2m_reactivate "A~b C"\np2m_open_scoped "A~b C"\n')
        self.assertEqual(new, "open scoped A~b C\nopen scoped A C\n")

    def test_import_all_is_an_import_of_the_util_too(self):
        for line in ("import all P2M.Util", "public import all P2M.Util", "meta import P2M.Util", "import P2M.Util"):
            new, done, left = pu.rewrite_module(f"{line}\np2m_open \"A\"\n")
            self.assertEqual(new, "open A\n", line)
        self.assertIsNone(pu.IMPORT_UTIL.search("-- import P2M.Util\n"))  # a comment is not an import

    def test_an_escaped_identifier_in_a_print_only_check_is_not_guessed_at(self):
        t = "import P2M.Util\n#p2m_type_eq_warn «A b» C\n"
        new, done, left = pu.rewrite_module(t)
        self.assertEqual((new, dict(left)), (t, {"#p2m_type_eq_warn": 1}))
        t2 = "import P2M.Util\n#p2m_type_eq_warn A B extra\n"
        self.assertEqual(pu.rewrite_module(t2)[0], t2)  # more than two words: left too

    def test_a_module_changed_by_two_passes_is_counted_by_both_notices(self):
        import grind_sets as gs

        text = "import X\n" + gs.notice("lib@aa", "A.lean", ["removed 2 tag(s) of the custom grind set(s) `s` from declarations"]) + "\n" + gs.notice("lib@aa", "A.lean", ["wrote out 5 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 5 `p2m_open`"]) + "\n"
        counted = gs.shipped_changes([text])
        self.assertEqual(counted["modules changed"], 1)  # one module
        self.assertEqual(counted["set tags removed"], 2)  # the first notice
        self.assertEqual(counted["P2M.Util shortcuts written out"], 5)  # and the second


class TheMoreEdges(unittest.TestCase):
    """the second round of cubic on #203"""

    def test_an_import_line_inside_a_comment_or_a_string_is_not_an_import(self):
        t = 'import P2M.Util\n/-\nimport P2M.Util\n-/\ndef s := "\nimport P2M.Util\n"\np2m_open "A"\n'
        new, done, left = pu.rewrite_module(t)
        self.assertEqual(new, '/-\nimport P2M.Util\n-/\ndef s := "\nimport P2M.Util\n"\nopen A\n')  # only the real import goes; the comment and the string keep their lines
        self.assertEqual(len(pu.util_imports(t)), 1)

    def test_in_on_the_next_line_belongs_to_the_command(self):
        for sep in ("\n in", "\n    in", " \t in"):
            new, _, _ = pu.rewrite_module(f'import P2M.Util\np2m_open "A"{sep}\ntheorem t : True := trivial\n')
            self.assertEqual(new, "open A in\ntheorem t : True := trivial\n", repr(sep))

    def test_in_is_a_word_not_the_start_of_one(self):
        new, _, _ = pu.rewrite_module('import P2M.Util\np2m_open "A"\ninvariant_x\n')
        self.assertEqual(new, "open A\ninvariant_x\n")

    def test_two_anonymous_hypotheses_of_one_type_cannot_be_told_apart(self):
        """cubic on #203: `‹T›` finds a hypothesis by its type: with two of that type (anonymous or named) it could hand the solution the wrong one"""
        for header in ("(_ : P) (_ : P)", "(_ : P) (h : P)", "(h : P) (_ : P)"):
            t = f"import P2M.Util\ntheorem T {header} : True := by p2m_exact_reverting @_root_.P2MW.S_T.solution\n"
            new, done, left = pu.rewrite_module(t)
            self.assertEqual((new, dict(done), dict(left)), (t, {}, {"p2m_exact_reverting": 1}), header)
        t = "import P2M.Util\ntheorem T (_ : P) (_ : Q) (h : R) : True := by p2m_exact_reverting @_root_.P2MW.S_T.solution\n"
        self.assertTrue(pu.rewrite_module(t)[0].rstrip("\n").endswith("solution ‹P› ‹Q› h"))  # distinct types: unambiguous


class TheSolModules(unittest.TestCase):
    def test_export_and_open_with_a_second_namespace(self):
        new, done, left = pu.rewrite_module(real("S_ModularCurve_legendreJ_one_sub.lean"))
        self.assertIn('export ModularCurve (legendreJ)', new)
        self.assertIn("open ModularCurve open P2MW.S_ModularCurve_legendreJ_one_sub.ModularCurve", new)
        self.assertNotIn("p2m_", new)
        self.assertEqual((dict(done), dict(left)), ({"p2m_export": 1, "p2m_open": 2}, {}))

    def test_several_commands_on_one_line_stay_on_that_line(self):
        line = 'namespace FreyPackage p2m_export "FreyPackage" "freyCurve c p a hc0 ha0 b hFLT hb0" end FreyPackage'  # the real line of S_FreyPackage_frey_no_cofixed_eleven
        new, done, _ = pu.rewrite_module(f"import P2M.Util\n{line}\np2m_open_scoped \"FreyPackage\" in\n")
        self.assertEqual(new, "namespace FreyPackage export FreyPackage (freyCurve c p a hc0 ha0 b hFLT hb0) end FreyPackage\nopen scoped FreyPackage in\n")
        self.assertEqual(dict(done), {"p2m_export": 1, "p2m_open_scoped": 1})

    def test_an_export_with_no_namespace_leaves_the_module_as_it_was(self):
        """cubic on #203: the alias `<current>.A.b` for `A.b` has no plain form, and dropping it could change what a name resolves to without an error: the real module (283 such uses in 135 files) stays behind the import"""
        t = real("S_FreyPackage_frey_no_cofixed_eleven.lean")
        self.assertIn('p2m_export "" "FreyPackage.p_ne_of_fermatLastTheoremFor_K"', t)
        new, done, left = pu.rewrite_module(t)
        self.assertEqual((new, dict(done), dict(left)), (t, {}, {"p2m_export (no namespace)": 1}))

    def test_reactivate_is_open_scoped(self):
        new, _, _ = pu.rewrite_module(real("S_GaloisRep_isFractionRing_ratLocalizedAt.lean"))
        self.assertIn("open scoped P2MW.S_GaloisRep_isFractionRing_ratLocalizedAt.SolB0C", new)

    def test_all_four_in_one_module(self):
        t = real("S_AlgebraicGeometry_Scheme_Modules_IsLocallyFreeOfRank_pullback.lean")
        new, done, left = pu.rewrite_module(t)
        self.assertEqual(dict(done), {"p2m_open": 2, "p2m_export": 4, "p2m_open_scoped": 1, "p2m_reactivate": 3})
        self.assertNotIn("p2m_", new)
        self.assertNotIn("P2M.Util", new)

    def test_a_module_that_imports_the_util_and_uses_nothing_only_loses_the_import(self):
        t = real("S_ModularCurve_UVCrossingModel_chartHom_C.lean")
        new, done, left = pu.rewrite_module(t)
        self.assertEqual(new, t.replace("import P2M.Util\n", ""))
        self.assertEqual((dict(done), dict(left)), ({}, {}))

    def test_a_module_with_p2m_alias_is_returned_exactly_as_it_was(self):
        t = real("S_AlgebraicCurve_IsFrobeniusEndo_restrictAlong_injective.lean")
        new, done, left = pu.rewrite_module(t)
        self.assertEqual(new, t)
        self.assertIn("import P2M.Util", new)
        self.assertEqual((dict(done), dict(left)), ({}, {"p2m_alias": 1}))

    def test_export_all_and_ns_are_left(self):
        for cmd, key in (('p2m_export_all "" "Ideal.IsHopfIdeal\'"', "p2m_export_all"), ('p2m_ns "X"', "p2m_ns")):
            t = f"import P2M.Util\n{cmd}\n"
            new, done, left = pu.rewrite_module(t)
            self.assertEqual((new, dict(left)), (t, {key: 1}))

    def test_the_two_commands_that_only_print_go_with_their_line(self):
        t = "import P2M.Util\nlemma a : True := trivial\n#p2m_type_eq_warn P2M.Dup.A.b A.b\n#p2m_type_eq A.b A.b\nlemma c : True := trivial\n"
        new, done, left = pu.rewrite_module(t)
        self.assertEqual(new, "lemma a : True := trivial\nlemma c : True := trivial\n")
        self.assertEqual(dict(done), {"#p2m_type_eq_warn": 1, "#p2m_type_eq": 1})

    def test_the_real_dup_line_of_the_library(self):
        line = "#p2m_type_eq_warn P2M.Dup.AlgebraicCurve.IsFrobeniusEndo.restrictAlong_injective AlgebraicCurve.IsFrobeniusEndo.restrictAlong_injective"
        new, done, _ = pu.rewrite_module(f"import P2M.Util\nnamespace X\n{line}\nend X\n")
        self.assertEqual(new, "namespace X\nend X\n")


class TheForms(unittest.TestCase):
    def test_p2m_open(self):
        self.assertEqual(pu.open_commands("Toy", False), "open Toy")
        self.assertEqual(pu.open_commands("Toy~foo", False), "open Toy hiding foo")
        self.assertEqual(pu.open_commands("scoped MatrixGroups ModularForm~a~b", False), "open MatrixGroups open ModularForm hiding a b")
        self.assertEqual(pu.open_commands("A B", True), "open A in open B in")
        self.assertEqual(pu.open_commands("scoped", False), "")

    def test_p2m_open_scoped_and_reactivate(self):
        self.assertEqual(pu.scoped_commands("A B", False), "open scoped A B")
        self.assertEqual(pu.scoped_commands("A B~x", True), "open scoped A B in")
        self.assertEqual(pu.scoped_commands("", False), "")

    def test_p2m_export(self):
        self.assertEqual(pu.export_command("Toy", "foo bar"), "export Toy (foo bar)")
        self.assertEqual(pu.export_command("", "A.b"), "")
        self.assertEqual(pu.export_command("Toy", ""), "")


class TheInvariants(unittest.TestCase):
    ALL = sorted(FX.glob("*.lean"))

    def test_no_line_is_added_or_moved(self):
        for f in self.ALL:
            t = f.read_text(encoding="utf-8")
            new, done, left = pu.rewrite_module(t)
            if left:
                self.assertEqual(new, t)
                continue
            gone = len(re.findall(r"(?m)^[ \t]*import P2M\.Util[ \t]*\n", t)) + len(re.findall(r"(?m)^[ \t]*#p2m_type_eq\w*[^\n]*\n", t))
            self.assertEqual(len(lines(new)), len(lines(t)) - gone, f.name)

    def test_no_shortcut_is_left_in_code_when_the_import_goes(self):
        for f in self.ALL:
            new, _, left = pu.rewrite_module(f.read_text(encoding="utf-8"))
            if not left:
                self.assertNotIn("P2M.Util", new, f.name)
                self.assertIsNone(re.search(r"(?<![\w.'])#?p2m_[a-z_]+", new), f.name)

    def test_the_result_is_a_fixed_point(self):
        for f in self.ALL:
            new, _, _ = pu.rewrite_module(f.read_text(encoding="utf-8"))
            again, done, left = pu.rewrite_module(new)
            self.assertEqual(again, new, f.name)
            self.assertEqual(dict(done), {}, f.name)

    def test_comments_and_strings_that_name_a_shortcut_are_not_code(self):
        t = 'import P2M.Util\n-- p2m_open "A" is how it was written\n/- p2m_export "A" "b" -/\ndef s := "p2m_reactivate \\"A\\""\np2m_open "A"\n'
        new, done, _ = pu.rewrite_module(t)
        self.assertEqual(new, '-- p2m_open "A" is how it was written\n/- p2m_export "A" "b" -/\ndef s := "p2m_reactivate \\"A\\""\nopen A\n')
        self.assertEqual(dict(done), {"p2m_open": 1})

    def test_a_name_inside_another_name_is_not_a_shortcut_and_an_unknown_p2m_word_leaves_the_module(self):
        t = "import P2M.Util\nopen A.p2m_open in\ndef x := B.p2m_export\n"
        new, done, left = pu.rewrite_module(t)
        self.assertEqual(new, "open A.p2m_open in\ndef x := B.p2m_export\n")  # dotted: part of another name
        self.assertEqual((dict(done), dict(left)), ({}, {}))
        odd = "import P2M.Util\ndef p2m_open_x := 1\n"  # a word this does not know (`p2m_restate_check` is in one real module): not guessed at
        new, done, left = pu.rewrite_module(odd)
        self.assertEqual((new, dict(left)), (odd, {"p2m_open_x": 1}))

    def test_a_module_with_no_shortcut_and_no_import_is_untouched(self):
        t = "import Mathlib\ntheorem a : True := trivial\n"
        self.assertEqual(pu.rewrite_module(t), (t, Counter(), Counter()))


class TheLibrary(unittest.TestCase):
    def test_the_util_file_itself_is_the_source_of_the_names(self):
        util = (HERE / "fixtures" / "real-p2m-util-aa2d8b34.lean").read_text(encoding="utf-8")
        defined = set(re.findall(r'(?:elab|macro|syntax)[^"\n]*"(#?p2m_[a-z_]+)', util))
        handled = {"p2m_exact_reverting", "p2m_open", "p2m_open_scoped", "p2m_export", "p2m_reactivate", "#p2m_type_eq", "#p2m_type_eq_warn", "p2m_alias", "p2m_export_all", "p2m_ns"}
        self.assertEqual(defined, handled, "a command of the library's Util that this does not know (or know to leave)")
        self.assertEqual(set(pu.UNSUPPORTED) | set(pu.INERT) | {"p2m_exact_reverting", "p2m_open", "p2m_open_scoped", "p2m_export", "p2m_reactivate"}, handled)

    def test_the_util_module_itself_is_left(self):
        util = (HERE / "fixtures" / "real-p2m-util-aa2d8b34.lean").read_text(encoding="utf-8")
        new, done, left = pu.rewrite_module(util)
        self.assertEqual(new, util)  # it defines the commands: no shortcut of its own is a use (and `p2m_alias`, `p2m_export_all` are defined there, so it is left)


def mutated(old: str, new: str, fn: str = "rewrite_module"):
    src = inspect.getsource(getattr(pu, fn))
    assert src.count(old) == 1, (old, src.count(old))
    ns = dict(vars(pu))
    exec(src.replace(old, new), ns)
    return ns[fn]


class TheMutants(unittest.TestCase):
    def test_hidden_names_dropped(self):
        src = inspect.getsource(pu.open_commands).replace('" hiding " + " ".join(hidden) if hidden else ""', '""')
        ns = dict(vars(pu))
        exec(src, ns)
        self.assertEqual(ns["open_commands"]("Toy~foo", False), "open Toy")  # what the real check (test_p2m_open) refuses

    def test_open_as_open_scoped(self):
        src = inspect.getsource(pu.open_commands).replace('f"open {head}"', 'f"open scoped {head}"')
        ns = dict(vars(pu))
        exec(src, ns)
        self.assertEqual(ns["open_commands"]("Toy", False), "open scoped Toy")  # test_p2m_open refuses this

    def test_binder_names_dropped(self):
        f = mutated('"".join(" " + a for a in args)', '""', "expand_exact")
        text = "theorem T (n : ℕ) : n = n := by p2m_exact_reverting @_root_.P2MW.S_T.solution"
        self.assertTrue(f(text, pu.code_mask(text))[0].endswith("solution"))  # the binder names are gone: test_binders_of_every_kind_become_the_arguments_of_the_solution refuses this

    def test_import_kept(self):
        f = mutated("return drop_util_imports(out), done, left", "return out, done, left")
        new, _, _ = f("import P2M.Util\np2m_open \"A\"\n")
        self.assertIn("import P2M.Util", new)  # the invariant test_no_shortcut_is_left_in_code_when_the_import_goes refuses this

    def test_comments_rewritten(self):
        f = mutated("if not mask[m.start()]:\n            continue", "if False:\n            continue")
        new, done, _ = f('-- p2m_open "A"\nimport P2M.Util\n')
        self.assertIn("open A", new)  # the comment is rewritten: test_comments_and_strings_that_name_a_shortcut_are_not_code refuses this


class TheComposePass(unittest.TestCase):
    """bundle.py compose calls `rewrite` on the pruned modules right after grind_sets.rewrite and before the lint: the lint then never sees `P2M.Util`."""

    TEXTS = {
        "P2M.Util": (HERE / "fixtures" / "real-p2m-util-aa2d8b34.lean").read_text(encoding="utf-8"),
        "P2M.Sol.S_fermatLastTheoremFive": "import Mathlib\nimport P2M.Util\nnamespace P2MW.S_fermatLastTheoremFive\ntheorem solution : FermatLastTheoremFor 5 := sorry\nend P2MW.S_fermatLastTheoremFive\n",
        "Theorems.Thm_fermatLastTheoremFive": real("Thm_fermatLastTheoremFive.lean"),
        "P2M.Sol.S_alias": real("S_AlgebraicCurve_IsFrobeniusEndo_restrictAlong_injective.lean"),
    }
    IMPORTS = {
        "P2M.Util": [],
        "P2M.Sol.S_fermatLastTheoremFive": ["P2M.Util"],
        "Theorems.Thm_fermatLastTheoremFive": ["P2M.Util", "P2M.Sol.S_fermatLastTheoremFive"],
        "P2M.Sol.S_alias": ["P2M.Util"],
    }

    def test_what_it_changes_and_what_it_says(self):
        out, changes, stats, imports = pu.rewrite(self.TEXTS, self.IMPORTS)
        self.assertNotIn("P2M.Util", out["Theorems.Thm_fermatLastTheoremFive"])
        self.assertEqual(imports["Theorems.Thm_fermatLastTheoremFive"], ["P2M.Sol.S_fermatLastTheoremFive"])
        self.assertEqual(imports["P2M.Sol.S_fermatLastTheoremFive"], [])
        self.assertEqual(out["P2M.Sol.S_alias"], self.TEXTS["P2M.Sol.S_alias"])  # p2m_alias: as it was, and still importing the Util
        self.assertNotIn("P2M.Sol.S_alias", changes)
        self.assertEqual(changes["Theorems.Thm_fermatLastTheoremFive"], ["wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`", "removed the import of `P2M.Util`"])
        self.assertEqual(changes["P2M.Sol.S_fermatLastTheoremFive"], ["removed the import of `P2M.Util`"])
        self.assertEqual(stats["modules changed"], 2)
        self.assertEqual(stats["modules kept as they were"], 2)  # the alias module, and the Util itself (it defines p2m_alias)

    def test_the_util_module_leaves_only_when_nothing_imports_it(self):
        out, _, stats, _ = pu.rewrite(self.TEXTS, self.IMPORTS)
        self.assertIn("P2M.Util", out)  # S_alias still imports it
        texts = {k: v for k, v in self.TEXTS.items() if k != "P2M.Sol.S_alias"}
        imports = {k: v for k, v in self.IMPORTS.items() if k != "P2M.Sol.S_alias"}
        out, _, stats, _ = pu.rewrite(texts, imports)
        self.assertNotIn("P2M.Util", out)
        self.assertEqual(stats["util module left out"], 1)

    def test_a_library_without_the_util_is_untouched(self):
        texts = {"A": "import Mathlib\ntheorem a : True := trivial\n", "B": "import A\ntheorem b : True := a\n"}
        out, changes, stats, imports = pu.rewrite(texts, {"A": [], "B": ["A"]})
        self.assertEqual((out, changes, stats, imports), (texts, {}, {}, {}))

    def test_the_notice_is_counted_in_what_the_pr_says(self):
        import grind_sets as gs

        out, changes, _, _ = pu.rewrite(self.TEXTS, self.IMPORTS)
        shipped = [out[m] + "\n\n" + gs.notice("lib@aa2d8b34", m, w) + "\n" for m, w in changes.items()]
        counted = gs.shipped_changes(shipped)
        self.assertEqual(counted["modules changed"], 2)
        self.assertEqual(counted["P2M.Util shortcuts written out"], 1)

    def test_compose_calls_it_after_the_grind_sets_and_before_the_lint(self):
        src = (HERE.parent / "bundle.py").read_text(encoding="utf-8")
        a = src.index("grind_sets.rewrite(pruned")
        b = src.index("p2m_util.rewrite(pruned")
        c = src.index("lint[mod] = allowlist.violations")
        self.assertTrue(a < b < c)
        self.assertIn("imports[mod] = deps", src)  # a module that no longer imports the Util is no longer blocked by it in the cascade


class TheMutantsOfThePass(unittest.TestCase):
    def test_the_imports_not_updated(self):
        src = inspect.getsource(pu.rewrite).replace("new_imports[mod] = [d for d in imports.get(mod, []) if d != UTIL]", "pass")
        ns = dict(vars(pu))
        exec(src, ns)
        _, _, _, imports = ns["rewrite"](TheComposePass.TEXTS, TheComposePass.IMPORTS)
        self.assertEqual(imports, {})  # TheComposePass.test_what_it_changes_and_what_it_says expects the edges to go

    def test_the_util_module_always_kept(self):
        src = inspect.getsource(pu.rewrite).replace("        del out[UTIL]\n", "        pass\n")
        ns = dict(vars(pu))
        exec(src, ns)
        texts = {k: v for k, v in TheComposePass.TEXTS.items() if k != "P2M.Sol.S_alias"}
        imports = {k: v for k, v in TheComposePass.IMPORTS.items() if k != "P2M.Sol.S_alias"}
        out, *_ = ns["rewrite"](texts, imports)
        self.assertIn("P2M.Util", out)  # the real test expects it gone


if __name__ == "__main__":
    unittest.main()
