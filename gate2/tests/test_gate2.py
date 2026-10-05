"""The real Gate2.lean, run by a real Lean on small cases (no Tengoku tree needed: the Vendor modules import only Lean).

Regression, 2026-10-05: the original is replayed into the session as a STATEMENT-ONLY AXIOM (server.py), and nothing stopped the submitted proof of
`NewType → OldType` from citing it, so `fun _ => Old n` "proved" the entailment for any new statement: an unrelated translation got GATE2_PASS.

The Vendor modules are copied into a temporary Lake project without the tree dependency (gate2/lakefile.toml requires it) and built once; each case writes a
Lean file that imports them, stands in for the replay (the export loader is the one thing not exercised) and runs `#gate2_verify`.
"""

from __future__ import annotations

import re
import shutil
import subprocess
import tempfile
import unittest
from pathlib import Path

GATE2 = Path(__file__).resolve().parent.parent
HAVE_LEAN = shutil.which("lake") is not None

STAND_IN = """
open Lean Elab Command in
/-- What the replay leaves behind: the original's constants in `importedConstantsRef` as the export had them (a theorem), and in the environment as a
statement-only axiom. -/
run_cmd (do
  for n in [`Old] do
    let some ci := (← getEnv).find? n | throwError "no {n}"
    importedConstantsRef.modify (·.insert n (.thmInfo { toConstantVal := ci.toConstantVal, value := mkConst ``True.intro, all := [n] })) : CommandElabM Unit)
"""


@unittest.skipUnless(HAVE_LEAN, "needs a Lean toolchain (lake on PATH): run by the gate2-tests workflow")
class Gate2Lean(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.tmp = tempfile.TemporaryDirectory()
        cls.proj = Path(cls.tmp.name) / "proj"
        shutil.copytree(GATE2 / "Vendor", cls.proj / "Vendor")
        shutil.copy(GATE2 / "Vendor.lean", cls.proj / "Vendor.lean")
        shutil.copy(GATE2 / "lean-toolchain", cls.proj / "lean-toolchain")
        (cls.proj / "lakefile.toml").write_text('name = "gate2test"\ndefaultTargets = ["Vendor"]\n\n[[lean_lib]]\nname = "Vendor"\n')
        r = subprocess.run(["lake", "build", "Vendor"], cwd=cls.proj, capture_output=True, text=True, check=False)
        assert r.returncode == 0, r.stdout[-1500:] + r.stderr[-1500:]

    @classmethod
    def tearDownClass(cls):
        cls.tmp.cleanup()

    def verdict(self, declarations: str, call: str) -> str:
        f = self.proj / "Case.lean"
        f.write_text("import Vendor.Gate2\nopen Lean Elab Command\n" + declarations + STAND_IN + call + "\n")
        r = subprocess.run(["lake", "env", "lean", "Case.lean"], cwd=self.proj, capture_output=True, text=True, check=False)
        out = r.stdout + r.stderr
        m = re.search(r"GATE2_(PASS|FAIL)[^\n]*", out)
        self.assertIsNotNone(m, out[-1500:])
        return m.group(0)

    OLD = "axiom Old : ∀ n : Nat, n + 0 = n\n"

    def test_the_same_statement_passes_with_the_identity(self):
        v = self.verdict(self.OLD + "theorem NewSame : ∀ m : Nat, m + 0 = m := fun m => Nat.add_zero m\n", '#gate2_verify "NewSame" "Old" "Bridge" "fun h => h"')
        self.assertTrue(v.startswith("GATE2_PASS"), v)

    def test_a_proof_that_cites_the_original_does_not_certify_an_unrelated_statement(self):
        # the bug: the original is an axiom in the session, so `fun _ => Old n` proved `new → old` for ANY new
        v = self.verdict(self.OLD + "theorem NewUnrelated : ∀ n : Nat, n ≤ n + 1 := fun n => Nat.le_succ n\n", '#gate2_verify "NewUnrelated" "Old" "BridgeCheat" "fun _ => Old n"')
        self.assertTrue(v.startswith("GATE2_FAIL"), v)
        self.assertIn("bridge_cites_the_original", v)

    def test_citing_the_original_is_refused_even_for_a_statement_that_does_imply_it(self):
        v = self.verdict(self.OLD + "theorem NewSame : ∀ n : Nat, n + 0 = n := fun n => Nat.add_zero n\n", '#gate2_verify "NewSame" "Old" "Bridge" "fun _ => Old n"')
        self.assertTrue(v.startswith("GATE2_FAIL"), v)
        self.assertIn("bridge_cites_the_original", v)

    def test_a_weaker_translation_is_still_rejected(self):
        old = "axiom Old : ∀ n : Nat, 0 < n → n ≠ 0\n"
        v = self.verdict(old + "theorem NewWeak : ∀ n : Nat, 1 < n → n ≠ 0 := fun n h => Nat.ne_of_gt (by omega)\n", '#gate2_verify "NewWeak" "Old" "Bridge" "fun h => h"')
        self.assertTrue(v.startswith("GATE2_FAIL"), v)

    def test_a_real_bridge_through_a_tree_lemma_is_still_accepted(self):
        # the fix must not forbid helper lemmas that are not the original: `0 + n = n` gives `n + 0 = n` through Nat.add_zero and Nat.zero_add
        v = self.verdict(
            self.OLD + "theorem NewZeroAdd : ∀ n : Nat, 0 + n = n := fun n => Nat.zero_add n\n",
            '#gate2_verify "NewZeroAdd" "Old" "Bridge" "fun _ => Nat.add_zero n"',
        )
        self.assertTrue(v.startswith("GATE2_PASS"), v)

    def test_the_name_guards_still_hold(self):
        # the translation reusing the original's name is the v0.0.4 tautology
        v = self.verdict(self.OLD, '#gate2_verify "Old" "Old" "Bridge" "fun h => h"')
        self.assertIn("GATE2_FAIL", v)
        self.assertIn("new_name_is_an_export_name", v)


if __name__ == "__main__":
    unittest.main()
