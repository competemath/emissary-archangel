/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.OracleReduction.Composition.Sequential.NoAmbient
import ArkLib.OracleReduction.Composition.Sequential.OracleCompleteness
import ArkLib.OracleReduction.LiftContext.Purity


-- @@ L11-16 verbatim
/-!
# Guarded composition certificates and empty-oracle boundary cases

These checks audit the composition declarations and show that a guarded fallback can preserve an
arbitrary oracle family from input without assuming it is inhabited.
-/


-- @@ L18-18 verbatim
open OracleSpec ProtocolSpec


-- @@ L20-20 verbatim
namespace CompositionRetirementRegression


-- @@ L22-25 expanded
/-- The fallback preserves an arbitrary oracle value supplied in the input. -/
def preserveArbitraryFamily {α : Type} (V : Verifier []ₒ (Unit × α) (Bool × α) empty) :
    V.GuardedForm :=
  Verifier.GuardedForm.ofEmpty V (fun input => (false, input.2))


-- @@ L27-32 expanded
/-- A rejecting verifier with empty output does not admit a total guarded verdict function. -/
theorem no_guarded_form_for_empty_output :
    ¬Nonempty
        (Verifier.GuardedForm (show Verifier []ₒ Unit Empty empty from ⟨fun _ _ => failure⟩)) :=
  by
  rintro ⟨G⟩
  exact (G.out () default).elim


-- @@ L34-34 verbatim
end CompositionRetirementRegression


-- @@ L36-40 verbatim
/--
info: 'OracleComp.runEmpty' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms OracleComp.runEmpty


-- @@ L42-46 verbatim
/--
info: 'OracleComp.eq_pure_runEmpty' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms OracleComp.eq_pure_runEmpty


-- @@ L48-53 verbatim
/--
info: 'Prover.instOutputIsPureEmpty' depends on axioms:
[propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms Prover.instOutputIsPureEmpty


-- @@ L55-60 verbatim
/--
info: 'Verifier.GuardedForm.ofEmpty' depends on axioms:
[propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms Verifier.GuardedForm.ofEmpty


-- @@ L62-67 verbatim
/--
info: 'Prover.instOutputIsPureLiftContext' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Prover.instOutputIsPureLiftContext


-- @@ L69-74 verbatim
/--
info: 'Verifier.GuardedForm.liftContext' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Verifier.GuardedForm.liftContext


-- @@ L76-81 verbatim
/--
info: 'Verifier.GuardedForm.seqCompose' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Verifier.GuardedForm.seqCompose


-- @@ L83-88 verbatim
/--
info: 'Reduction.seqCompose_completeness_of_guarded_verifiers' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Reduction.seqCompose_completeness_of_guarded_verifiers


-- @@ L90-95 verbatim
/--
info: 'Reduction.seqCompose_perfectCompleteness_of_guarded_verifiers' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Reduction.seqCompose_perfectCompleteness_of_guarded_verifiers


-- @@ L97-102 verbatim
/--
info: 'OracleReduction.append_completeness_of_guarded_verifiers' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms OracleReduction.append_completeness_of_guarded_verifiers


-- @@ L104-109 verbatim
/--
info: 'OracleReduction.append_perfectCompleteness_of_guarded_verifiers' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms OracleReduction.append_perfectCompleteness_of_guarded_verifiers


-- @@ L111-116 verbatim
/--
info: 'OracleReduction.seqCompose_completeness_of_guarded_verifiers' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms OracleReduction.seqCompose_completeness_of_guarded_verifiers


-- @@ L118-123 verbatim
/--
info: 'OracleReduction.seqCompose_perfectCompleteness_of_guarded_verifiers' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms OracleReduction.seqCompose_perfectCompleteness_of_guarded_verifiers


-- @@ L125-130 verbatim
/--
info: 'CompositionRetirementRegression.preserveArbitraryFamily' depends on axioms:
[propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms CompositionRetirementRegression.preserveArbitraryFamily


-- @@ L132-137 verbatim
/--
info: 'CompositionRetirementRegression.no_guarded_form_for_empty_output' depends on axioms:
[Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CompositionRetirementRegression.no_guarded_form_for_empty_output
