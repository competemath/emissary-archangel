/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Richard Goodman, ArkLib Contributors
-/
module

public import ArkLib.OracleReduction.Composition.Sequential.Append.Completeness


-- @@ L10-20 verbatim
/-!
# Completeness of two one-message reductions

Each prover may perform arbitrary oracle queries, including in its output. Pure verification
and suffix completeness from every shared state imply perfect completeness of the composition.
The opening message supplies the execution seam condition.

## References

* [Richard Goodman, one-message composition](https://github.com/Verified-zkEVM/ArkLib/pull/636).
-/


-- @@ L22-22 verbatim
@[expose] public section


-- @@ L24-24 verbatim
open OracleComp OracleSpec ProtocolSpec


-- @@ L26-26 verbatim
namespace ProtocolSpec


-- @@ L28-29 verbatim
/-- A protocol consisting of one message from the prover. -/
abbrev oneMessage (Msg : Type) : ProtocolSpec 1 := ⟨!v[.P_to_V], !v[Msg]⟩


-- @@ L31-32 verbatim
instance {Msg : Type} : ∀ i, SampleableType ((oneMessage Msg).Challenge i) :=
  fun ⟨0, h⟩ => nomatch h


-- @@ L34-36 verbatim
instance {Msg₁ Msg₂ : Type} :
    ∀ i, SampleableType (((oneMessage Msg₁) ++ₚ (oneMessage Msg₂)).Challenge i) :=
  instSampleableTypeChallengeAppend (pSpec₁ := oneMessage Msg₁) (pSpec₂ := oneMessage Msg₂)


-- @@ L38-38 verbatim
end ProtocolSpec


-- @@ L40-40 verbatim
namespace Reduction


-- @@ L42-43 verbatim
variable {ι σ Stmt₁ Wit₁ Stmt₂ Wit₂ Stmt₃ Wit₃ Msg₁ Msg₂ : Type}
  {oSpec : OracleSpec ι} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}


-- @@ L45-56 verbatim
/-- Two one-message reductions compose perfectly under pure verifier forms and suffix
completeness from every deterministic shared state. No prover purity premise is needed. -/
theorem append_perfectCompleteness_of_oneMessage
    (R₁ : Reduction oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ (oneMessage Msg₁))
    (R₂ : Reduction oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ (oneMessage Msg₂))
    (V₁ : R₁.verifier.PureForm) (V₂ : R₂.verifier.PureForm)
    {rel₁ : Set (Stmt₁ × Wit₁)} {rel₂ : Set (Stmt₂ × Wit₂)}
    {rel₃ : Set (Stmt₃ × Wit₃)}
    (h₁ : R₁.perfectCompleteness init impl rel₁ rel₂)
    (h₂ : ∀ s : σ, R₂.perfectCompleteness (pure s) impl rel₂ rel₃) :
    (R₁.append R₂).perfectCompleteness init impl rel₁ rel₃ :=
  append_perfectCompleteness_of_pure_verifiers R₁ R₂ V₁ V₂ (fun _ => Or.inr rfl) h₁ h₂


-- @@ L58-58 verbatim
end Reduction
