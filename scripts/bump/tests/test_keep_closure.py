"""keep_closure: what the text of a kept declaration names is kept too (the compose-level cases are in test_bundle.AutoDrops)."""

import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import bundle  # noqa: E402
import keep_closure  # noqa: E402


class VisibleName(unittest.TestCase):
    def test_a_private_declaration_is_known_by_the_name_a_proof_writes(self):
        self.assertEqual(keep_closure.visible_name("_private.OAI.Combinatorics.PerfectMatching.Polytope.0.OAI.MatchingEntropy.LooplessGraph.aux_step"), "OAI.MatchingEntropy.LooplessGraph.aux_step")
        self.assertEqual(keep_closure.visible_name("Toy.plain_name"), "Toy.plain_name")

    def test_the_compilers_own_constants_are_not_declarations_a_proof_names(self):
        for n in ("Toy.foo.eq_1", "Toy.foo.match_1", "Toy.foo.proof_2", "Toy._auxLemma.3", "Toy.S.rec", "Toy.S.casesOn", "Toy.foo.eq_def"):
            self.assertIsNone(keep_closure.visible_name(n), n)

    def test_only_a_distinctive_last_component_matches_by_itself(self):
        for n in ("pathLpOperator_apply", "polytope_eq_constraints", "sobolevBound"):
            self.assertTrue(keep_closure.distinctive(n), n)
        for n in ("mul", "h", "foo", "aux_h", "short_1"):
            self.assertFalse(keep_closure.distinctive(n), n)


class FakeModule:
    """The three things keep_closure.close asks of records.Module: the lines, the block a line is in, the blocks a set of ranges keeps."""

    def __init__(self, lines, blocks):
        self.lines, self.blocks = lines, blocks

    def block_of(self, line):
        return next(((s, e) for s, e in self.blocks if s <= line <= e), None)

    def kept_blocks(self, keep):
        return {b for b in self.blocks if any(b[0] <= s <= b[1] for s, _ in keep)}


class FailedDeclarations(unittest.TestCase):
    """A declaration that had an error in the factory's build is closed with a sorry that is not in its text: it must never be kept for the text of another (2026-10-11)."""

    def setup(self):
        # block (1,2): a kept theorem whose text names `helper_lemma` (full name Toy.helper_lemma) and `side_lemma` (Toy.Sub.side_lemma) ; (4,5): Toy.helper_lemma ; (7,8): Toy.Sub.side_lemma
        a = FakeModule(["theorem kept_one : True := by", "  simp only [Toy.helper_lemma, side_lemma]", "", "theorem Toy.helper_lemma : True := by", "  trivial", "", "theorem Toy.Sub.side_lemma : True := by", "  trivial"], [(1, 2), (4, 5), (7, 8)])
        modules = {"Toy.A": a}
        sidecars = {"Toy.A": {"Toy.kept_one": (1, 2), "Toy.helper_lemma": (4, 5), "Toy.Sub.side_lemma": (7, 8)}}
        return modules, sidecars, {"Toy.A": {(1, 2)}}

    def test_without_failures_both_are_kept(self):
        modules, sidecars, keep = self.setup()
        added, unresolved = keep_closure.close(modules, sidecars, keep)
        self.assertEqual((added, unresolved), (2, {}))

    def test_a_failed_declaration_named_in_full_is_not_kept_and_the_naming_module_goes(self):
        modules, sidecars, keep = self.setup()
        added, unresolved = keep_closure.close(modules, sidecars, keep, failed={"Toy.A": {(4, 5)}})
        self.assertEqual(unresolved, {"Toy.A": {"Toy.helper_lemma"}})
        self.assertNotIn((4, 5), {b for b in modules["Toy.A"].kept_blocks(keep["Toy.A"])})
        self.assertEqual(added, 1)  # side_lemma is still kept

    def test_a_failed_declaration_matched_by_its_last_component_alone_is_a_guess_and_drops_nothing(self):
        modules, sidecars, keep = self.setup()
        added, unresolved = keep_closure.close(modules, sidecars, keep, failed={"Toy.A": {(7, 8)}})
        self.assertEqual(unresolved, {})  # `side_lemma` is written without its namespace: not a certain reference
        self.assertEqual(added, 1)  # only helper_lemma
        self.assertNotIn((7, 8), modules["Toy.A"].kept_blocks(keep["Toy.A"]))

    def test_the_declarations_gate_2_rejected_for_sorry_are_read_from_its_log(self):
        import tempfile

        log = Path(tempfile.mkdtemp()) / "gate2.log"
        log.write_text(
            "GATE2B_FAIL old=A.b new=A.b reason=uses_sorry\nGATE2B_PASS old=A.c new=A.c via=equal\nGATE2B_FAIL old=A.d new=A.d reason=nonstandard_axiom axioms=[x]\nGATE2B_FAIL old=A.e new=A.e reason=uses_sorry\n"
        )
        self.assertEqual(bundle.sorry_users(str(log)), {"A.b", "A.e"})
        self.assertEqual(bundle.sorry_users(""), set())

    def test_a_failed_block_that_a_passed_term_really_needs_stays_but_is_reported(self):
        modules, sidecars, keep = self.setup()
        keep["Toy.A"].add((4, 5))  # Toy.helper_lemma failed in the build and the term of a passed theorem needs it (not only a compiler-made sub-proof of it)
        seeds = []
        added, unresolved = keep_closure.close(modules, sidecars, keep, failed={"Toy.A": {(4, 5)}}, failed_seeds=seeds)
        self.assertEqual(seeds, [("Toy.A", (4, 5))])  # accounted for: the caller puts it in the report
        self.assertIn((4, 5), keep["Toy.A"])  # and it stays (a hard drop would lose every module that has one)
        self.assertEqual(unresolved, {})  # a full-name mention of a kept block is no problem

    def test_a_failed_declaration_needed_only_through_a_compiler_made_sub_proof_is_dropped_from_the_seed_quietly(self):
        modules, sidecars, keep = self.setup()
        keep["Toy.A"].add((4, 5))  # kept because a passed theorem's term names `Toy.helper_lemma._proof_1`, which maps onto the whole declaration
        added, unresolved = keep_closure.close(modules, sidecars, keep, failed={"Toy.A": {(4, 5)}}, aux_only={"Toy.A": {(4, 5)}})
        self.assertNotIn((4, 5), keep["Toy.A"])  # the pruner will not keep its text
        # the kept theorem still names it in full: that module is unresolved, as before (the seed itself no longer is)
        self.assertEqual(unresolved, {"Toy.A": {"Toy.helper_lemma"}})

    def test_which_ranges_are_there_only_for_compiler_made_constants(self):
        ranges = {("Toy.A", "Toy.f._proof_1"): (4, 5), ("Toy.A", "Toy.f"): (4, 5), ("Toy.A", "Toy.g.match_1"): (7, 8), ("Toy.A", "Toy.h"): (10, 11)}
        out = keep_closure.aux_only_ranges(list(ranges), lambda mod, c: ranges.get((mod, c)))
        self.assertEqual(dict(out), {"Toy.A": {(7, 8)}})  # (4,5) is also needed by the declaration itself, (10,11) is a plain declaration

    def test_a_seed_block_the_parser_stopped_in_makes_the_module_unshippable(self):
        modules, sidecars, keep = self.setup()
        keep["Toy.A"].add((4, 5))
        seeds = []
        added, unresolved = keep_closure.close(modules, sidecars, keep, failed={"Toy.A": {(4, 5)}}, fatal={"Toy.A": {(4, 5)}}, failed_seeds=seeds)
        self.assertIn("<block at line 4 does not parse>", unresolved["Toy.A"])
        self.assertEqual(seeds, [])  # not a failed seed that stays: a parse error cannot be shipped

    def test_the_parser_messages_are_told_from_the_elaborators(self):
        import bundle

        for m in ("unexpected token 'end'; expected '⟩'", "unterminated comment", "expected term"):
            self.assertTrue(bundle.PARSE_ERROR.match(m), m)
        for m in ("unknown identifier x", "unsolved goals", "Application type mismatch", "Tactic `tauto` failed"):
            self.assertFalse(bundle.PARSE_ERROR.match(m), m)


class NamespaceResolution(unittest.TestCase):
    """A name written short is the declaration the file's namespace and `open`s say, however many declarations in the library end in it (tauceti `pointsFunctor_map`, 2026-10-11)."""

    LINES = [
        "namespace TauCeti",  # 1
        "namespace HopfAlgebra",  # 2
        "lemma pointsFunctor_map : True := trivial",  # 3
        "theorem uses_it : True := by",  # 4
        "  simp [pointsFunctor_map]",  # 5
        "end HopfAlgebra",  # 6
        "namespace Other",  # 7
        "lemma pointsFunctor_map : True := trivial",  # 8
        "lemma pointsFunctor_map_one : True := trivial",  # 9 (a different name: not a candidate)
        "end Other",  # 10
        "namespace Third",  # 11
        "lemma pointsFunctor_map : True := trivial",  # 12
        "theorem in_third : True := by",  # 13
        "  simp [pointsFunctor_map]",  # 14
        "end Third",  # 15
        "namespace Fourth",  # 16
        "lemma pointsFunctor_map : True := trivial",  # 17
        "end Fourth",  # 18
        "section",  # 19
        "open TauCeti.HopfAlgebra",  # 20
        "theorem opens_it : True := by",  # 21
        "  simp [pointsFunctor_map]",  # 22
        "end",  # 23
        "theorem bare : True := by",  # 24
        "  simp [pointsFunctor_map]",  # 25
        "end TauCeti",  # 26
    ]
    BLOCKS = [(3, 3), (4, 5), (8, 8), (9, 9), (12, 12), (13, 14), (17, 17), (21, 22), (24, 25)]

    def setup(self):
        mod = FakeModule(self.LINES, self.BLOCKS)
        sidecars = {
            "M": {
                "TauCeti.HopfAlgebra.pointsFunctor_map": (3, 3),
                "TauCeti.Other.pointsFunctor_map": (8, 8),
                "TauCeti.Third.pointsFunctor_map": (12, 12),
                "TauCeti.Fourth.pointsFunctor_map": (17, 17),
                "TauCeti.HopfAlgebra.uses_it": (4, 5),
                "TauCeti.Third.in_third": (13, 14),
                "opens_it": (21, 22),
                "bare": (24, 25),
            }
        }
        return {"M": mod}, sidecars

    def kept_after(self, seed):
        modules, sidecars, keep = (*self.setup()[:2], {"M": {seed}})
        keep_closure.close(modules, sidecars, keep)
        return {b for b in modules["M"].kept_blocks(keep["M"])}

    def test_the_contexts_of_the_blocks(self):
        modules, _ = self.setup()
        ctx = keep_closure.block_contexts(modules["M"])
        self.assertEqual(ctx[(4, 5)], ("TauCeti.HopfAlgebra", ()))
        self.assertEqual(ctx[(21, 22)], ("TauCeti", ("TauCeti.HopfAlgebra",)))  # the `open` of the section
        self.assertEqual(ctx[(24, 25)], ("TauCeti", ()))  # and it ended with the section

    def test_a_short_name_is_the_declaration_of_the_namespace_it_is_written_in_even_when_four_end_in_it(self):
        kept = self.kept_after((4, 5))
        self.assertIn((3, 3), kept)  # HopfAlgebra.pointsFunctor_map
        self.assertNotIn((8, 8), kept)
        self.assertNotIn((12, 12), kept)
        self.assertNotIn((17, 17), kept)

    def test_an_open_namespace_resolves_it_too(self):
        kept = self.kept_after((21, 22))
        self.assertIn((3, 3), kept)
        self.assertNotIn((8, 8), kept)

    def test_a_name_that_no_namespace_of_the_place_makes_a_declaration_is_not_guessed(self):
        kept = self.kept_after((24, 25))  # namespace TauCeti only: TauCeti.pointsFunctor_map does not exist, four others end in it
        self.assertEqual(kept & {(3, 3), (8, 8), (12, 12), (17, 17)}, set())

    def test_the_innermost_namespace_wins(self):
        kept = self.kept_after((13, 14))  # in TauCeti.Third, which has its own
        self.assertIn((12, 12), kept)
        self.assertNotIn((3, 3), kept)

    def test_a_root_declaration_is_found_from_inside_a_namespace(self):
        lines = ["lemma root_helper_name : True := trivial", "namespace A", "theorem t : True := by", "  simp [root_helper_name]", "end A", "namespace B", "lemma root_helper_name : True := trivial", "end B"]
        mod = FakeModule(lines, [(1, 1), (3, 4), (7, 7)])
        sidecars = {"M": {"root_helper_name": (1, 1), "A.t": (3, 4), "B.root_helper_name": (7, 7), "C.root_helper_name": (7, 7), "D.root_helper_name": (7, 7)}}
        keep = {"M": {(3, 4)}}
        keep_closure.close({"M": mod}, sidecars, keep)
        kept = mod.kept_blocks(keep["M"])
        self.assertIn((1, 1), kept)  # the root level: four end in the name, so only the namespace reading finds it

    def test_commands_inside_a_block_comment_do_not_change_the_namespace(self):
        """CodeRabbit on #34: a column-0 `end` inside a `/- … -/` comment popped the real namespace, and the next declaration got the wrong context."""
        lines = [
            "namespace TauCeti",  # 1
            "/-",  # 2
            "end",  # 3 (comment text)
            "namespace Fake",  # 4 (comment text)
            "open Elsewhere",  # 5 (comment text)
            "-/",  # 6
            "theorem inside : True := trivial",  # 7
            "end TauCeti",  # 8
        ]
        ctx = keep_closure.block_contexts(FakeModule(lines, [(7, 7)]))
        self.assertEqual(ctx[(7, 7)], ("TauCeti", ()))


class GlueMentions(unittest.TestCase):
    """A command outside every declaration (`attribute [fun_prop] foo`, a `variable` over a library structure, a local notation) stays in the pruned file whatever is kept, so what it names must
    be kept too (openai-math `ProjectionMoments/BallMoments.lean`, 2026-10-12: `attribute [fun_prop] measurable_polarRows` stayed, the lemma was cut from `Polar.lean`, and the tree
    stopped at 'Unknown constant'. The closure started from declarations only and never read the glue)."""

    def setup(self, glue):
        # module A: the glue line (line 2, inside `namespace Toy`) and a kept theorem (line 3); module B: the lemma the glue names
        a = FakeModule(["namespace Toy", glue, "theorem kept_one : True := trivial", "end Toy"], [(3, 3)])
        b = FakeModule(["namespace Toy", "lemma measurable_polarRows : True := trivial", "end Toy"], [(2, 2)])
        sidecars = {"A": {"Toy.kept_one": (3, 3)}, "B": {"Toy.measurable_polarRows": (2, 2)}}
        return {"A": a, "B": b}, sidecars, {"A": {(3, 3)}, "B": set()}

    def test_an_attribute_command_keeps_the_declaration_it_names(self):
        modules, sidecars, keep = self.setup("attribute [fun_prop] measurable_polarRows")
        added, unresolved = keep_closure.close(modules, sidecars, keep)
        self.assertEqual((added, unresolved), (1, {}))
        self.assertEqual(modules["B"].kept_blocks(keep["B"]), {(2, 2)})

    def test_the_name_is_read_in_the_namespace_the_glue_is_in(self):
        modules, sidecars, keep = self.setup("attribute [fun_prop] measurable_polarRows")
        # three more declarations end in the name (out of reach of the last-component guess): only the namespace of the glue says which one it means
        modules["B"] = FakeModule(
            ["namespace Toy", "lemma measurable_polarRows : True := trivial", "end Toy"] + [f"lemma Other{i}.measurable_polarRows : True := trivial" for i in range(3)],
            [(2, 2), (4, 4), (5, 5), (6, 6)],
        )
        sidecars["B"].update({f"Other{i}.measurable_polarRows": (4 + i, 4 + i) for i in range(3)})
        added, _ = keep_closure.close(modules, sidecars, keep)
        self.assertEqual((added, modules["B"].kept_blocks(keep["B"])), (1, {(2, 2)}))

    def test_a_comment_or_a_string_in_the_glue_names_nothing(self):
        for glue in ("-- attribute [fun_prop] measurable_polarRows", '/- attribute [fun_prop] measurable_polarRows -/', 'set_option trace.x "measurable_polarRows"'):
            modules, sidecars, keep = self.setup(glue)
            self.assertEqual(keep_closure.close(modules, sidecars, keep), (0, {}), glue)

    def test_a_namespace_or_import_line_is_not_a_mention(self):
        for glue in ("import Toy.measurable_polarRows", "namespace measurable_polarRows", "open measurable_polarRows"):
            modules, sidecars, keep = self.setup(glue)
            self.assertEqual(keep_closure.close(modules, sidecars, keep)[0], 0, glue)

    def test_glue_naming_a_declaration_that_failed_makes_the_module_unshippable(self):
        modules, sidecars, keep = self.setup("attribute [fun_prop] Toy.measurable_polarRows")
        added, unresolved = keep_closure.close(modules, sidecars, keep, failed={"B": {(2, 2)}})
        self.assertEqual((added, unresolved), (0, {"A": {"Toy.measurable_polarRows"}}))

    def test_the_glue_of_a_module_with_nothing_kept_is_not_read(self):
        modules, sidecars, keep = self.setup("attribute [fun_prop] measurable_polarRows")
        keep["A"] = set()  # the module ships nothing: its glue goes with it
        self.assertEqual(keep_closure.close(modules, sidecars, keep), (0, {}))


class GlueNamesAndSameFileFailures(unittest.TestCase):
    """lean-pool 2026-10-12 (part 6): `infixl:90 "⨀₂" => mdp₂!` names a lemma `mdp₂!` (five characters: not distinctive) by the namespace it is written in; and
    `x.predictorStep_wide` names a declaration of the same file that failed in the build, by its last component only."""

    def test_a_short_name_in_glue_is_read_by_the_namespace_of_the_glue(self):
        a = FakeModule(["namespace Toy", 'infixl:90 "⨀₂" => mdp₂!', "theorem kept_one : True := trivial", "end Toy"], [(3, 3)])
        b = FakeModule(["namespace Toy", "lemma mdp₂! : True := trivial", "end Toy"], [(2, 2)])
        sidecars = {"A": {"Toy.kept_one": (3, 3)}, "B": {"Toy.mdp₂!": (2, 2)}}
        keep = {"A": {(3, 3)}, "B": set()}
        added, unresolved = keep_closure.close({"A": a, "B": b}, sidecars, keep)
        self.assertEqual((added, unresolved), (1, {}))
        self.assertEqual(b.kept_blocks(keep["B"]), {(2, 2)})

    def test_the_same_short_name_in_a_block_is_still_not_guessed(self):
        a = FakeModule(["namespace Toy", "theorem kept_one : True := by", "  exact mdp₂!", "end Toy"], [(2, 3)])
        b = FakeModule(["namespace Toy", "lemma mdp₂! : True := trivial", "end Toy"], [(2, 2)])
        sidecars = {"A": {"Toy.kept_one": (2, 3)}, "B": {"Toy.mdp₂!": (2, 2)}}
        keep = {"A": {(2, 3)}, "B": set()}
        self.assertEqual(keep_closure.close({"A": a, "B": b}, sidecars, keep)[0], 0)

    def test_a_failed_declaration_of_the_same_file_named_by_its_last_component_drops_the_module(self):
        a = FakeModule(
            ["theorem Toy.Alg.predictorStep_wide : True := trivial", "theorem kept_one : True := by", "  exact x.predictorStep_wide"],
            [(1, 1), (2, 3)],
        )
        sidecars = {"A": {"Toy.Alg.predictorStep_wide": (1, 1), "kept_one": (2, 3)}}
        added, unresolved = keep_closure.close({"A": a}, sidecars, {"A": {(2, 3)}}, failed={"A": {(1, 1)}})
        self.assertEqual(unresolved, {"A": {"x.predictorStep_wide"}})

    def test_a_qualified_name_is_read_by_the_namespace_whatever_its_length(self):
        """lean-pool `HilbertStyle/Context`, 2026-10-12: `FiniteContext.weakening` inside `namespace LO.Entailment`; `weakening` is one plain word, never distinctive."""
        a = FakeModule(["namespace LO.Entailment", "theorem kept_one : True := by", "  exact FiniteContext.weakening", "end LO.Entailment"], [(2, 3)])
        b = FakeModule(["namespace LO.Entailment.FiniteContext", "def weakening : Nat := 1", "end LO.Entailment.FiniteContext"], [(2, 2)])
        sidecars = {"A": {"LO.Entailment.kept_one": (2, 3)}, "B": {"LO.Entailment.FiniteContext.weakening": (2, 2)}}
        keep = {"A": {(2, 3)}, "B": set()}
        self.assertEqual(keep_closure.close({"A": a, "B": b}, sidecars, keep)[0], 1)
        self.assertEqual(b.kept_blocks(keep["B"]), {(2, 2)})

    def test_an_unqualified_plain_word_is_still_not_guessed(self):
        a = FakeModule(["namespace LO.Entailment", "theorem kept_one : True := by", "  exact weakening", "end LO.Entailment"], [(2, 3)])
        b = FakeModule(["namespace LO.Entailment", "def weakening : Nat := 1", "end LO.Entailment"], [(2, 2)])
        sidecars = {"A": {"LO.Entailment.kept_one": (2, 3)}, "B": {"LO.Entailment.weakening": (2, 2)}}
        self.assertEqual(keep_closure.close({"A": a, "B": b}, sidecars, {"A": {(2, 3)}, "B": set()})[0], 0)

    def test_a_variable_binder_is_no_mention(self):
        """BollobasNikiforov (43 modules, 2026-10-12): `variable {k : ℕ}` binds `k`; a declaration `Ns.k` that failed made it a mention."""
        a = FakeModule(["namespace Toy", "variable {k : ℕ}", "theorem kept_one : True := trivial", "end Toy"], [(3, 3)])
        b = FakeModule(["namespace Toy", "def k : Nat := 1", "end Toy"], [(2, 2)])
        sidecars = {"A": {"Toy.kept_one": (3, 3)}, "B": {"Toy.k": (2, 2)}}
        added, unresolved = keep_closure.close({"A": a, "B": b}, sidecars, {"A": {(3, 3)}, "B": set()}, failed={"B": {(2, 2)}})
        self.assertEqual((added, unresolved), (0, {}))

    def test_glue_tail_is_what_refers_to_declarations(self):
        self.assertEqual(keep_closure.glue_tail("attribute [fun_prop] foo bar").strip(), "foo bar")
        self.assertEqual(keep_closure.glue_tail('infixl:90 "⨀₂" => mdp₂!').strip(), "mdp₂!")
        self.assertEqual(keep_closure.glue_tail("alias or_cases! := or₃'!").strip(), "or₃'!")
        self.assertEqual(keep_closure.glue_tail("variable {k : ℕ} (h : k = 1)"), "")

    def test_only_field_notation_on_a_local_counts_as_a_same_file_reference(self):
        for tok in ("alg.predictorStep_wide", "φ₁.tensorMul_apply", "L.first_match"):
            self.assertTrue(keep_closure.field_notation(tok), tok)
        for tok in ("_root_.InnerProductSpace", "Finset.sum_comm_extra", "previous_transition", "x.mul"):
            self.assertFalse(keep_closure.field_notation(tok), tok)

    def test_a_failed_declaration_of_another_file_named_by_its_last_component_is_still_a_guess(self):
        a = FakeModule(["theorem kept_one : True := by", "  exact x.predictorStep_wide"], [(1, 2)])
        b = FakeModule(["theorem Toy.Alg.predictorStep_wide : True := trivial"], [(1, 1)])
        sidecars = {"A": {"kept_one": (1, 2)}, "B": {"Toy.Alg.predictorStep_wide": (1, 1)}}
        added, unresolved = keep_closure.close({"A": a, "B": b}, sidecars, {"A": {(1, 2)}, "B": set()}, failed={"B": {(1, 1)}})
        self.assertEqual((added, unresolved), (0, {}))


class TextKeptInstances(unittest.TestCase):
    """A declaration kept because a kept text NAMES it has no elaborated term in the keep step (that walks the passed theorems only), so the instances its proof resolves silently are not
    in the keep set (tauceti `AlbertAlgebra.finrank_traceZero`, 2026-10-12: it names `Octonion.finrank_eq_eight`, whose proof needs `Module.Free R (Octonion R)`, an anonymous instance
    of the module that was cut: 'failed to synthesize' in the tree). The instances of its module that come before it are kept with it."""

    def mods(self, instance_text="instance [CommRing R] : Module.Free R (Octonion R) := foo", later=False, fail_dep=False):
        # B: an instance (line 1), the lemma a text names (line 2), another instance (line 3); A: a kept theorem whose text names the lemma
        b = FakeModule([instance_text, "theorem finrank_eq_eight : True := trivial", "instance [CommRing R] : Module.Finite R (Octonion R) := bar", "theorem dep_one_here : True := trivial"], [(1, 1), (2, 2), (3, 3), (4, 4)])
        a = FakeModule(["theorem kept_one : True := by", "  simp [finrank_eq_eight]"], [(1, 2)])
        sidecars = {"A": {"kept_one": (1, 2)}, "B": {"Toy.instFree": (1, 1), "finrank_eq_eight": (2, 2), "Toy.instFinite": (3, 3), "dep_one_here": (4, 4)}}
        return {"A": a, "B": b}, sidecars, {"A": {(1, 2)}, "B": set()}

    def test_the_instances_before_a_text_kept_declaration_come_with_it(self):
        modules, sidecars, keep = self.mods()
        added, unresolved = keep_closure.close(modules, sidecars, keep)
        kept = modules["B"].kept_blocks(keep["B"])
        self.assertIn((2, 2), kept)  # the declaration the text names
        self.assertIn((1, 1), kept)  # the instance before it
        self.assertNotIn((3, 3), kept)  # an instance after it is not what its proof saw
        self.assertEqual(unresolved, {})

    def test_a_declaration_that_a_passed_term_needs_brings_no_extra_instances(self):
        modules, sidecars, keep = self.mods()
        keep["B"] = {(2, 2)}  # a seed: the keep step walked its term, which names every instance it needs
        keep["A"] = set()
        keep_closure.close(modules, sidecars, keep)
        self.assertNotIn((1, 1), modules["B"].kept_blocks(keep["B"]))

    def test_an_instance_that_names_a_failed_declaration_is_left_out_and_blames_nobody(self):
        modules, sidecars, keep = self.mods(instance_text="instance [CommRing R] : Module.Free R (Octonion R) := Toy.dep_one_here")
        sidecars["B"]["Toy.dep_one_here"] = (4, 4)
        added, unresolved = keep_closure.close(modules, sidecars, keep, failed={"B": {(4, 4)}})
        self.assertNotIn((1, 1), modules["B"].kept_blocks(keep["B"]))  # the optional instance is not worth a module
        self.assertIn((2, 2), modules["B"].kept_blocks(keep["B"]))
        self.assertEqual(unresolved, {})

    def test_an_instance_with_sorry_is_left_out(self):
        modules, sidecars, keep = self.mods(instance_text="instance [CommRing R] : Module.Free R (Octonion R) := sorry")
        added, unresolved = keep_closure.close(modules, sidecars, keep)
        self.assertNotIn((1, 1), modules["B"].kept_blocks(keep["B"]))
        self.assertEqual(unresolved, {})

    def test_an_instance_using_field_notation_of_a_failed_declaration_of_its_module_is_left_out(self):
        """tauceti `Quasicoherent/Monoidal`, 2026-10-12: `isQuasicoherent_tensorObj` writes `qM.tensor`, the declaration `Toy.Sub.tensor` of the same module had failed in the build, and
        the text closure cannot resolve a field name."""
        modules, sidecars, keep = self.mods(instance_text="instance [CommRing R] : Module.Free R (Octonion R) := qM.tensor qN")
        sidecars["B"]["Toy.Sub.tensor"] = (4, 4)
        added, unresolved = keep_closure.close(modules, sidecars, keep, failed={"B": {(4, 4)}})
        self.assertNotIn((1, 1), modules["B"].kept_blocks(keep["B"]))
        self.assertEqual(unresolved, {})

    def test_an_instance_that_names_another_instance_which_uses_a_failed_field_is_left_out_too(self):
        """The real chain (Monoidal): instance 2 names instance 1 by its name, instance 1 writes `qM.tensor`; keeping 2 would keep 1 through the closure."""
        b = FakeModule(
            ["instance isOne [CommRing R] : Foo := qM.tensor qN", "instance isTwo [CommRing R] : Bar := isOne", "theorem later_one : True := trivial", "theorem tensor : True := trivial"],
            [(1, 1), (2, 2), (3, 3), (4, 4)],
        )
        a = FakeModule(["theorem kept_one : True := by", "  simp [later_one]"], [(1, 2)])
        sidecars = {"A": {"kept_one": (1, 2)}, "B": {"isOne": (1, 1), "isTwo": (2, 2), "later_one": (3, 3), "Toy.Sub.tensor": (4, 4)}}
        keep = {"A": {(1, 2)}, "B": set()}
        keep_closure.close({"A": a, "B": b}, sidecars, keep, failed={"B": {(4, 4)}})
        self.assertEqual(b_kept := {x for x in b.kept_blocks(keep["B"])}, {(3, 3)}, b_kept)

    def test_a_module_with_a_failed_declaration_drags_no_instance(self):
        """Monoidal again: `isMonoidal_isQuasicoherent` names nothing that failed, but `inferInstanceAs` finds the instance that uses it."""
        modules, sidecars, keep = self.mods()
        sidecars["B"]["unrelated_failed"] = (4, 4)
        keep_closure.close(modules, sidecars, keep, failed={"B": {(4, 4)}})
        self.assertNotIn((1, 1), modules["B"].kept_blocks(keep["B"]))
        self.assertIn((2, 2), modules["B"].kept_blocks(keep["B"]))  # the declaration the text names still stays

    def test_an_instance_whose_closure_reaches_a_module_with_a_failed_declaration_is_left_out(self):
        """The real chain: an instance of a clean module names an instance of a module that has a failed declaration (tauceti `Modules.Quasicoherent` -> `Monoidal`)."""
        b = FakeModule(["instance isOne : Foo := trivial", "theorem unrelated_failed : True := trivial", "theorem later_one : True := trivial"], [(1, 1), (2, 2), (3, 3)])
        c = FakeModule(["instance isTwo : Bar := isOne", "theorem later_two : True := trivial"], [(1, 1), (2, 2)])
        a = FakeModule(["theorem kept_one : True := by", "  simp [later_two]"], [(1, 2)])
        sidecars = {"A": {"kept_one": (1, 2)}, "B": {"isOne": (1, 1), "unrelated_failed": (2, 2), "later_one": (3, 3)}, "C": {"isTwo": (1, 1), "later_two": (2, 2)}}
        keep = {"A": {(1, 2)}, "B": set(), "C": set()}
        keep_closure.close({"A": a, "B": b, "C": c}, sidecars, keep, failed={"B": {(2, 2)}})
        self.assertNotIn((1, 1), c.kept_blocks(keep["C"]))  # isTwo would need isOne, whose module has a failed declaration
        self.assertEqual(b.kept_blocks(keep["B"]), set())

    def test_a_failed_declaration_of_another_module_does_not_stop_the_instance(self):
        modules, sidecars, keep = self.mods(instance_text="instance [CommRing R] : Module.Free R (Octonion R) := qM.tensor qN")
        modules["C"] = FakeModule(["theorem tensor : True := trivial"], [(1, 1)])
        sidecars["C"] = {"Other.tensor": (1, 1)}
        keep["C"] = set()
        keep_closure.close(modules, sidecars, keep, failed={"C": {(1, 1)}})
        self.assertIn((1, 1), modules["B"].kept_blocks(keep["B"]))

    def test_an_instance_that_names_a_declaration_keeps_that_too(self):
        modules, sidecars, keep = self.mods(instance_text="instance [CommRing R] : Module.Free R (Octonion R) := Toy.dep_one_here")
        sidecars["B"]["Toy.dep_one_here"] = (4, 4)
        keep_closure.close(modules, sidecars, keep)
        self.assertEqual({(1, 1), (2, 2), (4, 4)} - modules["B"].kept_blocks(keep["B"]), set())


if __name__ == "__main__":
    unittest.main()
