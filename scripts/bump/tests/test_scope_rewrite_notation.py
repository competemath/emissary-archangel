"""scope_rewrite.py for NOTATION leaks: a global `prefix:80 "-" => complement` (lean-pool, `LO.Modal.Formula`) is a second reading of every `-(…)` in the tree, and a
global `notation "v" => …` reserves `v` as a word in every file (2026-10-17). The command becomes `scoped` in a namespace and `local` in the root namespace."""

import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import scope_rewrite as sr  # noqa: E402

MODAL = """module

public import Tengoku.Lib.Base

@[expose] public section

namespace LO
namespace Modal
namespace Formula

/-- doc -/
def complement : Formula α → Formula α := fun φ => φ

/-- the complement -/
prefix:80 "-" => complement

lemma neg_def : -φ = φ := rfl

end Formula

namespace FormulaFinset

lemma uses (h : -φ = ψ) : True := trivial

end FormulaFinset

end Modal
end LO
"""

REPORT = 'leak: notation LO.Modal.Formula.«term-_» registered in Tengoku.Lib.Lib.Modal.Complement (declared at line 15)'


class Parse(unittest.TestCase):
    def test_a_name_with_brackets_and_a_semicolon_is_one_name(self):
        leaks = sr.parse("leak: notation «term(_↦_;_)» registered in Tengoku.L.L.Map (declared at line 96);leak: notation LO.Axioms.termKAx registered in Tengoku.L.L.Ax (declared at line 33)")
        self.assertEqual([(x["kind"], x["name"], x["line"]) for x in leaks], [("notation", "«term(_↦_;_)»", 96), ("notation", "LO.Axioms.termKAx", 33)])

    def test_an_instance_line_is_read_as_before(self):
        leaks = sr.parse("leak: instance A.inst registered in Tengoku.L.L.M (priority 5) (declared at line 3)")
        self.assertEqual((leaks[0]["kind"], leaks[0]["name"], leaks[0]["prio"]), ("instance", "A.inst", 5))


class Edit(unittest.TestCase):
    def edit(self, text, line):
        f = sr.Lines(text)
        r, info = sr.edit_notation(f, line)
        return r, info, f.text

    def test_in_a_namespace_it_becomes_scoped(self):
        r, info, lines = self.edit(MODAL, 14)  # the doc comment of the command
        self.assertEqual(r, "edited")
        self.assertEqual((info["mode"], info["ns"]), ("scoped", "LO.Modal.Formula"))
        self.assertIn('scoped prefix:80 "-" => complement', lines)

    def test_in_the_root_namespace_it_becomes_local_and_keeps_its_command(self):
        r, info, lines = self.edit('import X\n\nnotation "Gal("K ", "F")" => K ≃ₐ[F] K -- Galois group\n', 3)
        self.assertEqual(r, "edited")
        self.assertEqual((info["mode"], info["cmd"]), ("local", 'notation "Gal("K ", "F")" => K ≃ₐ[F] K'))
        self.assertEqual(lines[2], 'local notation "Gal("K ", "F")" => K ≃ₐ[F] K -- Galois group')

    def test_attributes_and_modifiers_stay_in_front(self):
        for src, want in (
            ('namespace A\n@[inherit_doc X] infix : 120 " ∈ " => f\nend A\n', '@[inherit_doc X] scoped infix : 120 " ∈ " => f'),
            ('namespace A\nprivate postfix:max " ⁻¹ " => inv\nend A\n', "private scoped postfix:max \" ⁻¹ \" => inv"),
            ('namespace A\nelab "superpose " a:term : term => do pure a\nend A\n', 'scoped elab "superpose " a:term : term => do pure a'),
            ('namespace A\nmacro "Facts " G:term:max : term => pure G\nend A\n', 'scoped macro "Facts " G:term:max : term => pure G'),
            ('namespace A\nsyntax "foo" term : term\nend A\n', 'scoped syntax "foo" term : term'),
        ):
            r, _, lines = self.edit(src, 2)
            self.assertEqual((r, lines[1]), ("edited", want), src)

    def test_scoped_or_local_already_is_left_alone(self):
        for src in ('namespace A\nscoped notation "x" => 1\nend A\n', 'local prefix:80 "-" => f\n'):
            r, info, lines = self.edit(src, 1 if src.startswith("local") else 2)
            self.assertEqual((r, info), ("already", None), src)

    def test_a_rule_command_and_a_docstring_that_says_notation_are_not_edited(self):
        text = "namespace A\n/-- the notation\nprefix:80 \"-\" is used -/\ndef x := 1\nmacro_rules | `(foo) => `(1)\nend A\n"
        r, _, lines = self.edit(text, 2)
        self.assertEqual(r, "missing")
        self.assertEqual(lines, text.split("\n"))

    def test_a_root_command_of_several_lines_is_left_alone_and_reported(self):
        r, info, lines = self.edit('notation "Foo(" a ", "\n    b ")" => bar a b\n', 1)
        self.assertEqual(r, "unsupported")
        self.assertIn("several lines", info["why"])
        self.assertEqual(lines[0], 'notation "Foo(" a ", "')

    def test_a_scoped_command_of_several_lines_is_fine(self):
        r, info, _ = self.edit('namespace A\nnotation "Foo(" a ", "\n    b ")" => bar a b\nend A\n', 2)
        self.assertEqual((r, info["mode"]), ("edited", "scoped"))

    def test_a_root_command_after_an_open_is_left_alone_and_reported(self):
        for src in ('open Real\nnotation "π" => pi\n', 'section S\nopen Real\nnotation "π" => pi\nend S\n', 'open Real in\nnotation "π" => pi\n'):
            r, info, _ = self.edit(src, src.count("\n") - 1 if "section" in src else 2)
            if "in\n" in src:
                self.assertEqual(r, "edited", src)  # `open … in` applies to the next command only, and that is not this one
            else:
                self.assertEqual(r, "unsupported", src)
                self.assertIn("`open`", info["why"])

    def test_an_open_that_has_ended_does_not_count(self):
        r, _, _ = self.edit('section S\nopen Real\nend S\nnotation "π" => pi\n', 4)
        self.assertEqual(r, "edited")

    def test_a_scoped_command_ignores_the_opens_it_stands_after(self):
        r, info, _ = self.edit('open Real\nnamespace A\nnotation "π" => pi\nend A\n', 3)
        self.assertEqual((r, info["mode"]), ("edited", "scoped"))

    def test_a_namespace_that_core_or_mathlib_have_scoped_entries_in_is_refused(self):
        sr.FORBIDDEN_NS.update({"Real"})
        try:
            r, info, lines = self.edit('namespace Real\nnotation "√√" => f\nend Real\n', 2)
        finally:
            sr.FORBIDDEN_NS.clear()
        self.assertEqual(r, "unsupported")
        self.assertIn("`Real`", info["why"])
        self.assertEqual(lines[1], 'notation "√√" => f')


class ForbiddenNamespace(unittest.TestCase):
    """core or Mathlib have scoped entries in `ZFSet`: `open scoped ZFSet` would turn those on, so a notation there is scoped only when nothing has to open it"""

    def test_nothing_after_the_namespace_and_no_importer_means_nothing_to_open(self):
        sr.FORBIDDEN_NS.add("ZFSet")
        try:
            f = sr.Lines('namespace ZFSet\n\nnotation "ω" => omega\n\nend ZFSet\n\nend\n')
            r, info = sr.edit_notation(f, 3, has_importers=False)
            self.assertEqual((r, info["mode"]), ("edited", "scoped"))
            f = sr.Lines('namespace ZFSet\n\nnotation "ω" => omega\n\nend ZFSet\n\nlemma later : True := trivial\n')
            self.assertEqual(sr.edit_notation(f, 3, has_importers=False)[0], "unsupported")  # code after the namespace would have to open it again
            f = sr.Lines('namespace ZFSet\n\nnotation "ω" => omega\n\nend ZFSet\n')
            self.assertEqual(sr.edit_notation(f, 3, has_importers=True)[0], "unsupported")  # an importer would have to open it
        finally:
            sr.FORBIDDEN_NS.clear()

    def test_through_a_bundle_the_importers_decide(self):
        sr.FORBIDDEN_NS.add("ZFSet")
        try:
            with tempfile.TemporaryDirectory() as d:
                base = Path(d) / "Tengoku" / "Lib"
                base.mkdir(parents=True)
                (base / "Def.lean").write_text('namespace ZFSet\nnotation "ω" => omega\nend ZFSet\n')
                (base / "Alone.lean").write_text("import Tengoku\n\ntheorem a : True := trivial\n")
                leaks = sr.parse("leak: notation ZFSet.«termω» registered in Tengoku.Lib.Def (declared at line 2)")
                rep = sr.apply_bundle(Path(d), leaks)
                self.assertEqual(rep["rewritten"], 1, rep)  # nothing imports Def: scoped, nothing to open
                (base / "Def.lean").write_text('namespace ZFSet\nnotation "ω" => omega\nend ZFSet\n')
                (base / "Use.lean").write_text("import Tengoku.Lib.Def\n\ntheorem u : True := trivial\n")
                rep = sr.apply_bundle(Path(d), leaks)
                self.assertEqual(rep["rewritten"], 0, rep)  # Use imports it: it would need `open scoped ZFSet`
                self.assertIn("open scoped ZFSet", rep["skipped"][0])
        finally:
            sr.FORBIDDEN_NS.clear()


class File(unittest.TestCase):
    def rewrite(self, text, leaks):
        with tempfile.TemporaryDirectory() as d:
            p = Path(d) / "M.lean"
            p.write_text(text)
            done, skipped = sr.rewrite_file(p, leaks)
            return done, skipped, p.read_text()

    def test_scoped_notation_is_opened_again_after_the_namespace_that_closes_it_and_a_note_says_so(self):
        done, skipped, new = self.rewrite(MODAL, sr.parse(REPORT))
        self.assertEqual((done, skipped), (1, []))
        self.assertIn('scoped prefix:80 "-" => complement', new)
        # the namespace Formula ends, `FormulaFinset` (in Modal) uses the notation: it is opened again, once
        self.assertIn("end Formula\nopen scoped LO.Modal.Formula\n", new)
        self.assertEqual(new.count("open scoped LO.Modal.Formula"), 1)
        self.assertTrue(new.endswith("-- Tengoku: 1 notation(s) of this module made scoped so they do not change other libraries (generated)\n"))

    def test_nothing_is_added_after_a_block_that_has_only_ends_after_it(self):
        _, _, new = self.rewrite(MODAL, sr.parse(REPORT))
        self.assertNotIn("end Modal\nopen scoped", new)
        self.assertNotIn("end LO\nopen scoped", new)

    def test_a_local_notation_in_a_section_is_declared_again_after_it(self):
        text = 'section Foo\nnotation "Gal("K ", "F")" => K ≃ₐ[F] K\nlemma a : Gal(K, F) = x := rfl\nend Foo\n\nlemma b : Gal(K, F) = y := rfl\n'
        done, _, new = self.rewrite(text, sr.parse('leak: notation «termGal(_,_)» registered in Tengoku.L.L.M (declared at line 2)'))
        self.assertEqual(done, 1)
        self.assertIn('end Foo\nlocal notation "Gal("K ", "F")" => K ≃ₐ[F] K\n', new)

    def test_an_unsupported_notation_is_reported_with_its_reason_and_the_file_is_not_touched(self):
        text = 'open Real\nnotation "π" => pi\n'
        done, skipped, new = self.rewrite(text, sr.parse("leak: notation «termπ» registered in Tengoku.L.L.M (declared at line 2)"))
        self.assertEqual(done, 0)
        self.assertEqual(len(skipped), 1)
        self.assertIn("after an `open`", skipped[0])
        self.assertEqual(new, text)

    def test_a_leak_without_a_position_is_reported_not_guessed(self):
        done, skipped, new = self.rewrite(MODAL, sr.parse("leak: notation LO.Modal.Formula.«term-_» registered in Tengoku.Lib.Lib.Modal.Complement"))
        self.assertEqual(done, 0)
        self.assertEqual(skipped, ["notation LO.Modal.Formula.«term-_»"])
        self.assertEqual(new, MODAL)

    def test_instances_and_notations_in_one_file_get_both_notes(self):
        text = "namespace A\ninstance : Foo := x\nprefix:80 \"-\" => f\nend A\nlemma z : True := trivial\n"
        done, _, new = self.rewrite(text, sr.parse("leak: instance A.instFoo registered in Tengoku.L.L.M (declared at line 2);leak: notation A.«term-_» registered in Tengoku.L.L.M (declared at line 3)"))
        self.assertEqual(done, 2)
        self.assertIn("local instance : Foo := x", new)
        self.assertIn('scoped prefix:80 "-" => f', new)
        self.assertIn("-- Tengoku: 1 registration(s) of this module made local so they do not change other libraries (generated)\n", new)
        self.assertIn("-- Tengoku: 1 notation(s) of this module made scoped so they do not change other libraries (generated)\n", new)


class Importers(unittest.TestCase):
    def library(self, d, files):
        for rel, text in files.items():
            p = Path(d) / "Tengoku" / "Lib" / rel
            p.parent.mkdir(parents=True, exist_ok=True)
            p.write_text(text)
        return Path(d)

    def test_every_importer_inside_the_library_activates_the_notation_and_nothing_outside_does(self):
        with tempfile.TemporaryDirectory() as d:
            root = self.library(
                d,
                {
                    "Modal/Complement.lean": 'import Tengoku.Lib.Base\n\nnamespace LO.Modal.Formula\nprefix:80 "-" => complement\nend LO.Modal.Formula\n',
                    "Modal/Use.lean": "import Tengoku.Lib.Modal.Complement\n\ntheorem u : -φ = φ := rfl\n",
                    "Modal/Deep.lean": "import Tengoku.Lib.Modal.Use\n\ntheorem d : True := trivial\n",
                    "Other.lean": "import Tengoku.Lib.Base\n\ntheorem o : True := trivial\n",
                    "Base.lean": "theorem b : True := trivial\n",
                },
            )
            leaks = sr.parse("leak: notation LO.Modal.Formula.«term-_» registered in Tengoku.Lib.Modal.Complement (declared at line 4)")
            rep = sr.apply_bundle(root, leaks)
            rep.update(sr.reexport(root, leaks))
            self.assertEqual(rep["rewritten"], 1)
            base = root / "Tengoku" / "Lib"
            self.assertIn('scoped prefix:80 "-" => complement', (base / "Modal/Complement.lean").read_text())
            for rel in ("Modal/Use.lean", "Modal/Deep.lean"):
                self.assertIn("open scoped LO.Modal.Formula", (base / rel).read_text(), rel)
            self.assertNotIn("open scoped", (base / "Other.lean").read_text())
            self.assertNotIn("open scoped", (base / "Base.lean").read_text())
            # the header stays first: the line goes after the imports
            use = (base / "Modal/Use.lean").read_text().split("\n")
            self.assertLess(use.index("import Tengoku.Lib.Modal.Complement"), use.index("open scoped LO.Modal.Formula"))

    def test_a_local_notation_is_declared_again_in_the_importers(self):
        with tempfile.TemporaryDirectory() as d:
            root = self.library(
                d,
                {
                    "Gal.lean": 'import Tengoku.Lib.Base\n\nnotation "Gal("K ", "F")" => K ≃ₐ[F] K\n',
                    "Use.lean": "import Tengoku.Lib.Gal\n\ntheorem u : Gal(K, F) = x := rfl\n",
                    "Base.lean": "theorem b : True := trivial\n",
                },
            )
            leaks = sr.parse("leak: notation «termGal(_,_)» registered in Tengoku.Lib.Gal (declared at line 3)")
            sr.apply_bundle(root, leaks)
            sr.reexport(root, leaks)
            base = root / "Tengoku" / "Lib"
            self.assertIn('local notation "Gal("K ", "F")" => K ≃ₐ[F] K', (base / "Gal.lean").read_text())
            self.assertIn('local notation "Gal("K ", "F")" => K ≃ₐ[F] K\n', (base / "Use.lean").read_text())


if __name__ == "__main__":
    unittest.main()
