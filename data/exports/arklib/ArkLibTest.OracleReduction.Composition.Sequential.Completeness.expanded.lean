/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.OracleReduction.Composition.Sequential.GuardedCompleteness
import ArkLibTest.OracleReduction.Composition.Sequential.SharedStateCounterexample


-- @@ L10-15 verbatim
/-!
# Completeness boundaries for sequential composition

Empty protocols preserve arbitrary initialization mixtures. A state-mutating first stage can
compose with a suffix that is correct from every state, while rejection counts as failed mass.
-/


-- @@ L17-17 verbatim
open OracleComp OracleSpec ProtocolSpec


-- @@ L19-19 verbatim
namespace AppendSecurityRegression


-- @@ L21-22 verbatim
/-- A Boolean ambient oracle. -/
abbrev oracle : OracleSpec Unit := fun _ => Bool


-- @@ L24-24 verbatim
section PureCompleteness


-- @@ L26-27 verbatim
local instance : ∀ i, SampleableType ((!p[] ++ₚ !p[]).Challenge i) :=
  ProtocolSpec.instSampleableTypeChallengeAppend (pSpec₁ := !p[]) (pSpec₂ := !p[])


-- @@ L29-38 verbatim
/-- Appending identity reductions preserves completeness for every initial-state distribution. -/
theorem empty_identity_complete {ι : Type} {spec : OracleSpec ι} {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl spec (StateT σ ProbComp)) :
    ((Reduction.id : Reduction spec Bool Unit Bool Unit !p[]).append
      (Reduction.id : Reduction spec Bool Unit Bool Unit !p[])).perfectCompleteness
      init impl Set.univ Set.univ := by
  exact Reduction.append_perfectCompleteness_of_pure_verifiers _ _
    ⟨fun s _ => s, fun _ _ => rfl⟩ ⟨fun s _ => s, fun _ _ => rfl⟩
    (fun hn => by omega) (Reduction.id_perfectCompleteness init impl)
    (fun s => Reduction.id_perfectCompleteness (pure s) impl)


-- @@ L40-40 verbatim
end PureCompleteness


-- @@ L42-42 verbatim
section StateMutation


-- @@ L44-44 verbatim
open AppendStateCounterexample


-- @@ L46-53 verbatim
/-- A state-mutating prefix composes perfectly with an identity suffix. -/
theorem state_mutation_complete :
    (first.append (Reduction.id : Reduction spec Bool Unit Bool Unit !p[])).perfectCompleteness
      (pure false) impl Set.univ Set.univ := by
  exact Reduction.append_perfectCompleteness_of_pure_verifiers _ _
    ⟨fun _ _ => false, fun _ _ => rfl⟩ ⟨fun s _ => s, fun _ _ => rfl⟩
    (fun hn => by omega) first_perfectCompleteness
    (fun s => Reduction.id_perfectCompleteness (pure s) impl)


-- @@ L55-55 verbatim
end StateMutation


-- @@ L57-57 verbatim
section RejectingVerifier


-- @@ L59-60 verbatim
local instance : ∀ i, SampleableType ((!p[] ++ₚ !p[]).Challenge i) :=
  ProtocolSpec.instSampleableTypeChallengeAppend (pSpec₁ := !p[]) (pSpec₂ := !p[])


-- @@ L62-65 verbatim
/-- An identity prover paired with an always-rejecting verifier. -/
def rejecting : Reduction oracle Bool Unit Bool Unit !p[] :=
  { (Reduction.id : Reduction oracle Bool Unit Bool Unit !p[]) with
    verifier := ⟨fun _ _ => failure⟩ }


-- @@ L67-69 verbatim
/-- The constant-false guard for the rejecting verifier. -/
def rejectingForm : rejecting.verifier.GuardedForm :=
  ⟨fun _ _ => false, fun stmt _ => stmt, fun _ _ => rfl⟩


-- @@ L71-80 verbatim
/-- Appending an always-rejecting suffix gives completeness error one. -/
theorem rejecting_complete_error_one {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl oracle (StateT σ ProbComp)) :
    ((Reduction.id : Reduction oracle Bool Unit Bool Unit !p[]).append rejecting).completeness
      init impl Set.univ Set.univ 1 := by
  simpa only [zero_add] using Reduction.append_completeness_of_guarded_verifiers
    (Reduction.id : Reduction oracle Bool Unit Bool Unit !p[]) rejecting
    ⟨fun _ _ => true, fun stmt _ => stmt, fun _ _ => rfl⟩ rejectingForm
    (fun hn => by omega) (Reduction.id_perfectCompleteness init impl)
    (fun _ => by simp [Reduction.completeness])


-- @@ L82-89 verbatim
/-- An always-rejecting verifier is not perfectly complete. -/
theorem rejecting_not_perfect {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl oracle (StateT σ ProbComp)) :
    ¬ rejecting.perfectCompleteness init impl Set.univ Set.univ := by
  intro h
  have hfalse := (Reduction.completeness_iff_of_guarded_verifier
    rejecting rejectingForm Set.univ Set.univ 0).mp h false () (by trivial)
  simp [rejectingForm] at hfalse


-- @@ L91-91 verbatim
end RejectingVerifier


-- @@ L93-93 verbatim
end AppendSecurityRegression


-- @@ L95-99 verbatim
/--
info: 'AppendSecurityRegression.empty_identity_complete' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in

-- @@ L100-100 verbatim
#print axioms AppendSecurityRegression.empty_identity_complete


-- @@ L102-106 verbatim
/--
info: 'AppendSecurityRegression.state_mutation_complete' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in

-- @@ L107-107 verbatim
#print axioms AppendSecurityRegression.state_mutation_complete


-- @@ L109-113 verbatim
/--
info: 'AppendSecurityRegression.rejecting_complete_error_one' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in

-- @@ L114-114 verbatim
#print axioms AppendSecurityRegression.rejecting_complete_error_one


-- @@ L116-120 verbatim
/--
info: 'AppendSecurityRegression.rejecting_not_perfect' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in

-- @@ L121-121 verbatim
#print axioms AppendSecurityRegression.rejecting_not_perfect
