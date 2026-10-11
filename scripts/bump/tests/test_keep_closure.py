"""keep_closure: what the text of a kept declaration names is kept too (the compose-level cases are in test_bundle.AutoDrops)."""

import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
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


if __name__ == "__main__":
    unittest.main()
