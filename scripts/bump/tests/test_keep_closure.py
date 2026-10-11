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


if __name__ == "__main__":
    unittest.main()
