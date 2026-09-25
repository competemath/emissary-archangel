/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.AlgebraicFramework.Measurement.Postprocessing


-- @@ L10-26 verbatim
/-!

# Compatible measurements

Two measurements are compatible when a single joint measurement, on the classical *product* of
their outcome types, marginalizes — via postprocessing along the two coordinate projections — to
both. Compatibility of measurements is exactly this classical-output specialization of channel
compatibility (a joint channel into a composite system, marginalized by the two partial-trace
channels); the classical product `ι × κ → ℝ` needs no composite-system theory to build, since
`ι × κ` is already an ordinary product type.

## Main definitions

- `Measurement.IsCompatible`
- `Measurement.isCompatible_self`, `Measurement.isCompatible_comm`

-/


-- @@ L28-28 verbatim
@[expose] public section


-- @@ L30-32 verbatim
variable {E ι κ : Type*} [AddCommGroup E] [PartialOrder E] [IsOrderedAddMonoid E]
  [Module ℝ E] [PosSMulMono ℝ E] [One E] [IsOrderUnit E]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]


-- @@ L34-34 verbatim
namespace Measurement


-- @@ L36-41 expanded
/-- Two measurements are compatible when there is a joint measurement on the classical product of
their outcome types marginalizing, via the coordinate projections, to both. -/
def IsCompatible (M₁ : UnitalPositiveLinearMap ℝ (ι → ℝ) E)
    (M₂ : UnitalPositiveLinearMap ℝ (κ → ℝ) E) : Prop :=
  ∃ J : UnitalPositiveLinearMap ℝ (ι × κ → ℝ) E,
    postprocess J (classicalPullback Prod.fst) = M₁ ∧
      postprocess J (classicalPullback Prod.snd) = M₂


-- @@ L43-51 expanded
omit [IsOrderedAddMonoid E] [PosSMulMono ℝ E] [IsOrderUnit E] [Fintype ι] [DecidableEq ι] in
/-- Every measurement is compatible with itself: the joint measurement pulled back along the
diagonal `i ↦ (i, i)` marginalizes to the original measurement along either coordinate. -/
lemma isCompatible_self (M : UnitalPositiveLinearMap ℝ (ι → ℝ) E) : IsCompatible M M :=
  by
  refine ⟨postprocess M (classicalPullback fun i => (i, i)), ?_, ?_⟩
  ·
    rw [postprocess_postprocess, classicalPullback_comp,
      show Prod.fst ∘ (fun i : ι => (i, i)) = id from rfl, classicalPullback_id, postprocess_id]
  ·
    rw [postprocess_postprocess, classicalPullback_comp,
      show Prod.snd ∘ (fun i : ι => (i, i)) = id from rfl, classicalPullback_id, postprocess_id]


-- @@ L53-63 expanded
omit [IsOrderedAddMonoid E] [PosSMulMono ℝ E] [IsOrderUnit E] [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] in
/-- Compatibility is symmetric: swap the two coordinates of the joint measurement. -/
lemma isCompatible_comm {M₁ : UnitalPositiveLinearMap ℝ (ι → ℝ) E}
    {M₂ : UnitalPositiveLinearMap ℝ (κ → ℝ) E} (h : IsCompatible M₁ M₂) : IsCompatible M₂ M₁ :=
  by
  obtain ⟨J, h1, h2⟩ := h
  refine ⟨postprocess J (classicalPullback (Prod.swap : ι × κ → κ × ι)), ?_, ?_⟩
  ·
    rw [postprocess_postprocess, classicalPullback_comp,
      show Prod.fst ∘ (Prod.swap : ι × κ → κ × ι) = Prod.snd from rfl, h2]
  ·
    rw [postprocess_postprocess, classicalPullback_comp,
      show Prod.snd ∘ (Prod.swap : ι × κ → κ × ι) = Prod.fst from rfl, h1]


-- @@ L65-65 verbatim
end Measurement
