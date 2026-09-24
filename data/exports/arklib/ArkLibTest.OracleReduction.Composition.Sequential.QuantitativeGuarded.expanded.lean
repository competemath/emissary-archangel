/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.OracleReduction.Composition.Sequential.GuardedCompleteness


-- @@ L9-14 verbatim
/-!
# Quantitative guarded composition with genuine rejection

Each stage samples one of four challenges, rejects zero, and adds an accepted challenge to the
statement. Both stages have error one quarter; their composition has error at most one half.
-/


-- @@ L16-16 verbatim
open OracleComp OracleSpec ProtocolSpec

-- @@ L17-17 verbatim
open scoped NNReal ENNReal


-- @@ L19-19 verbatim
namespace QuantitativeGuardedRegression


-- @@ L21-22 verbatim
/-- An ambient oracle, unused by these challenge-only reductions. -/
abbrev oracle : OracleSpec Unit := fun _ => Bool


-- @@ L24-25 verbatim
/-- Each stage receives a uniformly sampled challenge in `Fin 4`. -/
abbrev protocol : ProtocolSpec 1 := ⟨fun _ => .V_to_P, fun _ => Fin 4⟩


-- @@ L27-28 verbatim
instance : VerifierOnly protocol where
  verifier_first' := rfl


-- @@ L30-31 verbatim
instance : ∀ i, SampleableType (protocol.Challenge i) := fun _ => inferInstanceAs
  (SampleableType (Fin 4))


-- @@ L33-34 verbatim
local instance : ∀ i, SampleableType ((protocol ++ₚ protocol).Challenge i) :=
  ProtocolSpec.instSampleableTypeChallengeAppend (pSpec₁ := protocol) (pSpec₂ := protocol)


-- @@ L36-45 verbatim
/-- One guarded stage increments its statement by the sampled nonzero challenge. -/
def stage : Reduction oracle ℕ Unit ℕ Unit protocol where
  prover := {
    PrvState := fun _ => ℕ × Fin 4
    input := fun input => (input.1, 0)
    sendMessage := fun i _ => absurd i.2 (by simp)
    receiveChallenge := fun _ st => pure (fun c => (st.1, c))
    output := fun st => pure (st.1 + st.2.val, ()) }
  verifier := ⟨fun stmt tr =>
    if (tr 0 : Fin 4) != 0 then pure (stmt + (tr 0).val) else failure⟩


-- @@ L47-47 verbatim
instance : stage.prover.OutputIsPure := ⟨fun st => (st.1 + st.2.val, ()), fun _ => rfl⟩


-- @@ L49-51 verbatim
/-- The guard rejects exactly challenge zero; its verdict agrees with the prover's increment. -/
def guardedForm : stage.verifier.GuardedForm :=
  ⟨fun _ tr => (tr 0 : Fin 4) != 0, fun stmt tr => stmt + (tr 0).val, fun _ _ => rfl⟩


-- @@ L53-53 verbatim
variable {σ : Type} (impl : QueryImpl oracle (StateT σ ProbComp))


-- @@ L55-72 verbatim
/-- The actual simulated prover increments its output and retains the current oracle state. -/
theorem simulated_run (stmt : ℕ) (s : σ) :
    (simulateQ (impl.addLift (challengeQueryImpl (pSpec := protocol)) : QueryImpl _
      (StateT σ ProbComp)) (stage.prover.run stmt ())).run s = (do
        let c ← $ᵗ (Fin 4)
        pure ((fun _ => c, stmt + c.val, ()), s)) := by
  rw [Prover.run_of_verifier_first]
  simp only [stage, liftComp_pure, pure_bind, liftM_pure,
    bind_pure_comp, QueryImpl.addLift_def, PFunctor.Handler.liftTarget_self]
  change (fun c : Fin 4 =>
    ((fun i : Fin 1 => match i with | ⟨0, _⟩ => c, stmt + c.val, ()), s)) <$>
    ($ᵗ (Fin 4)) = _
  congr 1
  funext c
  congr 2
  funext i
  fin_cases i
  rfl


-- @@ L74-80 verbatim
/-- Exactly three of the four challenges pass the guard. -/
theorem nonzero_probability :
    Pr[fun c : Fin 4 => c ≠ 0 | $ᵗ (Fin 4)] = (3 / 4 : ℝ≥0∞) := by
  rw [probEvent_uniformSample]
  have hcard : (Finset.univ.filter fun c : Fin 4 => c ≠ 0).card = 3 := by decide
  simp only [hcard, Fintype.card_fin]
  norm_num


-- @@ L82-84 verbatim
/-- A zero challenge really makes the verifier reject. -/
theorem verifier_rejects_zero (stmt : ℕ) :
    stage.verifier.verify stmt (fun _ => 0) = failure := rfl


-- @@ L86-99 verbatim
/-- Rejection occurs with probability one quarter under the actual simulated prover. -/
theorem rejection_probability (stmt : ℕ) (s : σ) :
    Pr[fun q => guardedForm.check stmt q.1.1 = false |
      (simulateQ (impl.addLift (challengeQueryImpl (pSpec := protocol)) :
        QueryImpl _ (StateT σ ProbComp)) (stage.prover.run stmt ())).run s] =
      (1 / 4 : ℝ≥0∞) := by
  rw [simulated_run]
  simp only [bind_pure_comp, probEvent_map, Function.comp_def, guardedForm,
    bne_eq_false_iff_eq]
  change Pr[fun c : Fin 4 => c = 0 | $ᵗ (Fin 4)] = _
  rw [probEvent_uniformSample]
  have hcard : (Finset.univ.filter fun c : Fin 4 => c = 0).card = 1 := by decide
  simp only [hcard, Fintype.card_fin]
  norm_num


-- @@ L101-114 verbatim
/-- Each component is complete with error one quarter from every deterministic oracle state. -/
theorem stage_completeness (s : σ) :
    stage.completeness (pure s) impl Set.univ Set.univ (1 / 4) := by
  rw [Reduction.completeness_iff_of_guarded_verifier stage guardedForm]
  intro stmt wit _
  cases wit
  simp only [pure_bind, simulated_run, bind_pure_comp, probEvent_map,
    Function.comp_def, guardedForm, Set.mem_univ, true_and, and_true, bne_iff_ne]
  rw [nonzero_probability]
  have hratio : (3 / 4 : ℝ≥0∞) = ((3 / 4 : ℝ≥0) : ℝ≥0∞) := by
    rw [ENNReal.coe_div (by norm_num : (4 : ℝ≥0) ≠ 0)]
    norm_num
  rw [hratio]
  exact_mod_cast (show (1 : ℝ≥0) - 1 / 4 ≤ 3 / 4 by norm_num)


-- @@ L116-118 verbatim
/-- The intermediate statement is the incremented input, on every sampled challenge. -/
theorem output_agreement (stmt : ℕ) (c : Fin 4) :
    stage.prover.output (stmt, c) = pure (guardedForm.out stmt (fun _ => c), ()) := rfl


-- @@ L120-129 verbatim
/-- Two stages with error one quarter compose with error at most one half. -/
theorem append_completeness (init : ProbComp σ) :
    (stage.append stage).completeness init impl Set.univ Set.univ (1 / 2) := by
  have hfirst : stage.completeness init impl Set.univ Set.univ (1 / 4) :=
    Reduction.completeness_of_guarded_states stage guardedForm (stage_completeness impl)
  have h := Reduction.append_completeness_of_guarded_verifiers stage stage
    guardedForm guardedForm (fun _ => Or.inl inferInstance)
    hfirst (stage_completeness impl)
  norm_num at h ⊢
  exact h


-- @@ L131-131 verbatim
end QuantitativeGuardedRegression


-- @@ L133-137 verbatim
/--
info: 'QuantitativeGuardedRegression.simulated_run' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in

-- @@ L138-138 verbatim
#print axioms QuantitativeGuardedRegression.simulated_run


-- @@ L140-144 verbatim
/--
info: 'QuantitativeGuardedRegression.nonzero_probability' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in

-- @@ L145-145 verbatim
#print axioms QuantitativeGuardedRegression.nonzero_probability


-- @@ L147-151 verbatim
/--
info: 'QuantitativeGuardedRegression.verifier_rejects_zero' depends on axioms:
[propext]
-/
#guard_msgs (whitespace := lax) in

-- @@ L152-152 verbatim
#print axioms QuantitativeGuardedRegression.verifier_rejects_zero


-- @@ L154-158 verbatim
/--
info: 'QuantitativeGuardedRegression.rejection_probability' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in

-- @@ L159-159 verbatim
#print axioms QuantitativeGuardedRegression.rejection_probability


-- @@ L161-165 verbatim
/--
info: 'QuantitativeGuardedRegression.stage_completeness' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in

-- @@ L166-166 verbatim
#print axioms QuantitativeGuardedRegression.stage_completeness


-- @@ L168-172 verbatim
/--
info: 'QuantitativeGuardedRegression.output_agreement' depends on axioms:
[propext]
-/
#guard_msgs (whitespace := lax) in

-- @@ L173-173 verbatim
#print axioms QuantitativeGuardedRegression.output_agreement


-- @@ L175-179 verbatim
/--
info: 'QuantitativeGuardedRegression.append_completeness' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in

-- @@ L180-180 verbatim
#print axioms QuantitativeGuardedRegression.append_completeness
