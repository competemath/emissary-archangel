/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Richard Goodman, ArkLib Contributors
-/

import ArkLib.OracleReduction.Composition.Sequential.GuardedCompleteness
import ArkLibTest.OracleReduction.Composition.Sequential.RawExecutionCounterexample


-- @@ L10-21 verbatim
/-!
# Simulated factorization beyond the structural seam condition

A pure ambient implementation makes the simulated prover programs agree although their raw
programs have different query orders. The factorization completeness theorem therefore applies
without pure left output or a message-opening right protocol.

## References

* [Richard Goodman, factorization](https://github.com/Verified-zkEVM/ArkLib/pull/635).
* [Richard Goodman, raw query order](https://github.com/Verified-zkEVM/ArkLib/pull/643).
-/


-- @@ L23-23 verbatim
namespace ArkLib.AppendRunNecessity


-- @@ L25-25 verbatim
open OracleComp OracleSpec ProtocolSpec


-- @@ L27-27 verbatim
local instance : ∀ i, SampleableType (leftSpec.Challenge i) := fun ⟨i, _⟩ => Fin.elim0 i

-- @@ L28-29 verbatim
local instance : ∀ i, SampleableType (rightSpec.Challenge i) := fun ⟨⟨0, _⟩, _⟩ =>
  inferInstanceAs (SampleableType Bool)

-- @@ L30-31 verbatim
local instance : ∀ i, SampleableType ((leftSpec ++ₚ rightSpec).Challenge i) :=
  ProtocolSpec.instSampleableTypeChallengeAppend (pSpec₁ := leftSpec) (pSpec₂ := rightSpec)


-- @@ L33-33 verbatim
local instance : VerifierOnly rightSpec := { verifier_first' := rfl }

-- @@ L34-34 verbatim
local instance : VerifierOnly (leftSpec ++ₚ rightSpec) := { verifier_first' := rfl }


-- @@ L36-37 verbatim
/-- The ambient query has no simulated effect and always returns `false`. -/
def pureImpl : QueryImpl oracleSpec (StateT Unit ProbComp) := fun _ => pure false


-- @@ L39-87 verbatim
/-- The raw counterexample factors after this ambient simulation, including its full result. -/
theorem simulated_factorization :
    simulateQ (pureImpl.addLift (challengeQueryImpl (pSpec := leftSpec ++ₚ rightSpec)) :
      QueryImpl _ (StateT Unit ProbComp)) ((leftProver.append rightProver).run () ()) = (do
        let r₁ ← simulateQ (pureImpl.addLift (challengeQueryImpl (pSpec := leftSpec)) :
          QueryImpl _ (StateT Unit ProbComp)) (leftProver.run () ())
        let r₂ ← simulateQ (pureImpl.addLift (challengeQueryImpl (pSpec := rightSpec)) :
          QueryImpl _ (StateT Unit ProbComp)) (rightProver.run r₁.2.1 r₁.2.2)
        pure (r₁.1 ++ₜ r₂.1, r₂.2)) := by
  simp only [Prover.run_of_verifier_first]
  dsimp only [Prover.append, leftProver, rightProver]
  simp only [Prover.run, Prover.runToRound, pure_bind,
    liftM_pure, liftComp_eq_liftM, liftM_bind, bind_assoc]
  simp only [Fin.val_zero, Nat.not_lt_zero, dite_false, dite_true,
    Nat.reduceEqDiff, eq_mpr_eq_cast, cast_eq, Fin.reduceLast, Fin.induction, Fin.induction.go,
    liftM_pure, pure_bind]
  dsimp only [id]
  simp only [pure_bind, bind_assoc, simulateQ_bind, simulateQ_pure]
  simp only [QueryImpl.addLift_def, PFunctor.Handler.liftTarget_self,
    QueryImpl.simulateQ_add_liftM_left, QueryImpl.simulateQ_add_liftM_right]
  simp only [HasQuery.instOfMonadLift_query, getChallenge,
    simulateQ_spec_query, pureImpl]
  change (do
    let c ← (liftM ($ᵗ Bool) : StateT Unit ProbComp Bool)
    let _ ← simulateQ (pureImpl.addLift (challengeQueryImpl (pSpec := leftSpec ++ₚ rightSpec)) :
      QueryImpl _ (StateT Unit ProbComp))
      (liftM (do let _ ← (query (spec := oracleSpec) () : OracleComp oracleSpec Bool)
                 pure (fun _ : Bool => ())) : OracleComp _ (Bool → Unit))
    pure ((show (leftSpec ++ₚ rightSpec).FullTranscript from fun ⟨0, _⟩ => c), (), ())) =
      (do
        let _ ← (pure false : StateT Unit ProbComp Bool)
        let c ← (liftM ($ᵗ Bool) : StateT Unit ProbComp Bool)
        pure (FullTranscript.append (pSpec₁ := leftSpec) (pSpec₂ := rightSpec)
          default (fun i => match i with | ⟨0, _⟩ => c), (), ()))
  simp only [QueryImpl.addLift_def, PFunctor.Handler.liftTarget_self,
    QueryImpl.simulateQ_add_liftM_left, simulateQ_bind, simulateQ_pure,
    HasQuery.instOfMonadLift_query, simulateQ_spec_query, pureImpl, pure_bind]
  congr 1
  funext c
  change (pure ((show (leftSpec ++ₚ rightSpec).FullTranscript from fun ⟨0, _⟩ => c), (), ()) :
    StateT Unit ProbComp _) = pure
      (FullTranscript.append (pSpec₁ := leftSpec) (pSpec₂ := rightSpec)
        default (fun i => match i with | ⟨0, _⟩ => c), (), ())
  congr 1
  apply Prod.ext
  · funext i
    fin_cases i
    rfl
  · rfl


-- @@ L89-91 verbatim
/-- Pure verification of the effectful-output first prover. -/
def firstReduction : Reduction oracleSpec Unit Unit Unit Unit leftSpec :=
  ⟨leftProver, ⟨fun _ _ => pure ()⟩⟩


-- @@ L93-95 verbatim
/-- Pure verification of the challenge-opening second prover. -/
def secondReduction : Reduction oracleSpec Unit Unit Unit Unit rightSpec :=
  ⟨rightProver, ⟨fun _ _ => pure ()⟩⟩


-- @@ L97-98 verbatim
/-- Deterministic verifier data for the first stage. -/
def firstVerifierForm : firstReduction.verifier.PureForm := ⟨fun _ _ => (), fun _ _ => rfl⟩


-- @@ L100-101 verbatim
/-- Deterministic verifier data for the second stage. -/
def secondVerifierForm : secondReduction.verifier.PureForm := ⟨fun _ _ => (), fun _ _ => rfl⟩


-- @@ L103-109 verbatim
/-- The supplied program equality holds for every input and starting state. -/
theorem beyond_seam_factorization :
    leftProver.SimulatedAppendFactorization rightProver pureImpl := by
  intro stmt wit s
  cases stmt
  cases wit
  exact congrArg (fun x => x.run s) simulated_factorization


-- @@ L111-117 verbatim
/-- The first stage is perfectly complete from every initial-state distribution. -/
theorem first_complete (start : ProbComp Unit) :
    firstReduction.perfectCompleteness start pureImpl Set.univ Set.univ := by
  rw [Reduction.perfectCompleteness,
    Reduction.completeness_iff_of_pure_verifier firstReduction firstVerifierForm]
  intro stmt wit h
  simp


-- @@ L119-125 verbatim
/-- The second stage is perfectly complete from every initial-state distribution. -/
theorem second_complete (start : ProbComp Unit) :
    secondReduction.perfectCompleteness start pureImpl Set.univ Set.univ := by
  rw [Reduction.perfectCompleteness,
    Reduction.completeness_iff_of_pure_verifier secondReduction secondVerifierForm]
  intro stmt wit h
  simp


-- @@ L127-132 verbatim
/-- The factorization interface proves completeness outside the structural seam restriction. -/
theorem beyond_seam_complete (start : ProbComp Unit) :
    (firstReduction.append secondReduction).perfectCompleteness start pureImpl Set.univ Set.univ :=
  Reduction.append_perfectCompleteness_of_prover_factorization
    firstReduction secondReduction firstVerifierForm secondVerifierForm
    beyond_seam_factorization (first_complete start) second_complete


-- @@ L134-139 verbatim
/-- The handoff output issues an ambient query and cannot have a pure-output certificate. -/
theorem output_not_pure : ¬ leftProver.OutputIsPure := by
  rintro ⟨out, hout⟩
  have h := hout ()
  change PFunctor.FreeM.liftBind _ _ = PFunctor.FreeM.pure _ at h
  cases h


-- @@ L141-147 verbatim
/-- Neither disjunct of the structural seam condition applies to this pair. -/
theorem seam_fails : ¬ (∀ hn : 0 < 1,
    leftProver.OutputIsPure ∨ rightSpec.dir ⟨0, hn⟩ = .P_to_V) := by
  intro h
  rcases h (by decide) with hp | hm
  · exact output_not_pure hp
  · cases hm


-- @@ L149-149 verbatim
end ArkLib.AppendRunNecessity


-- @@ L151-155 verbatim
/--
info: 'ArkLib.AppendRunNecessity.simulated_factorization' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in

-- @@ L156-156 verbatim
#print axioms ArkLib.AppendRunNecessity.simulated_factorization


-- @@ L158-162 verbatim
/--
info: 'ArkLib.AppendRunNecessity.beyond_seam_factorization' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in

-- @@ L163-163 verbatim
#print axioms ArkLib.AppendRunNecessity.beyond_seam_factorization


-- @@ L165-169 verbatim
/--
info: 'ArkLib.AppendRunNecessity.first_complete' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in

-- @@ L170-170 verbatim
#print axioms ArkLib.AppendRunNecessity.first_complete


-- @@ L172-176 verbatim
/--
info: 'ArkLib.AppendRunNecessity.second_complete' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in

-- @@ L177-177 verbatim
#print axioms ArkLib.AppendRunNecessity.second_complete


-- @@ L179-183 verbatim
/--
info: 'ArkLib.AppendRunNecessity.beyond_seam_complete' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in

-- @@ L184-184 verbatim
#print axioms ArkLib.AppendRunNecessity.beyond_seam_complete


-- @@ L186-190 verbatim
/--
info: 'ArkLib.AppendRunNecessity.output_not_pure' depends on axioms:
[propext]
-/
#guard_msgs (whitespace := lax) in

-- @@ L191-191 verbatim
#print axioms ArkLib.AppendRunNecessity.output_not_pure


-- @@ L193-197 verbatim
/--
info: 'ArkLib.AppendRunNecessity.seam_fails' depends on axioms:
[propext]
-/
#guard_msgs (whitespace := lax) in

-- @@ L198-198 verbatim
#print axioms ArkLib.AppendRunNecessity.seam_fails


-- @@ L200-204 verbatim
/--
info: 'Prover.simulatedAppendFactorization_of_seam' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in

-- @@ L205-205 verbatim
#print axioms Prover.simulatedAppendFactorization_of_seam


-- @@ L207-211 verbatim
/--
info: 'Reduction.append_completeness_of_prover_factorization' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in

-- @@ L212-212 verbatim
#print axioms Reduction.append_completeness_of_prover_factorization


-- @@ L214-218 verbatim
/--
info: 'Reduction.append_perfectCompleteness_of_prover_factorization' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in

-- @@ L219-219 verbatim
#print axioms Reduction.append_perfectCompleteness_of_prover_factorization


-- @@ L221-225 verbatim
/--
info: 'Reduction.append_completeness_of_guarded_prover_factorization' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in

-- @@ L226-226 verbatim
#print axioms Reduction.append_completeness_of_guarded_prover_factorization
