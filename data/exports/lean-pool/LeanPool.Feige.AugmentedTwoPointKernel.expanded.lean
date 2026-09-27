/-
Copyright (c) 2026 Zhengqing Zhou and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhengqing Zhou, GPT-5.6 Pro
-/
module

public import LeanPool.Feige.MeasurableTwoPointKernel


-- @@ L10-16 verbatim
/-!
# An augmented latent kernel

The extra `Unit` branch records the atom at one.  The other branch records a
strict below/above pair.  Thus a single latent parameter always determines a
mean-one law supported on at most two points.
-/


-- @@ L18-18 verbatim
@[expose] public section


-- @@ L20-20 verbatim
open MeasureTheory ProbabilityTheory Set


-- @@ L22-22 verbatim
namespace Feige


-- @@ L24-24 verbatim
noncomputable section


-- @@ L26-28 verbatim
/-- A latent coordinate is either the distinguished atom at one or a genuine
strict two-point parameter. -/
abbrev AugmentedTwoPointParams := Unit ⊕ TwoPointParams


-- @@ L30-35 verbatim
/-- The conditional coordinate kernel attached to an augmented parameter. -/
noncomputable def augmentedTwoPointKernel : Kernel AugmentedTwoPointParams ℝ where
  toFun := Sum.elim (fun _ ↦ Measure.dirac 1) twoPointKernel
  measurable' := by
    refine Measure.measurable_of_measurable_coe _ fun B hB ↦ ?_
    exact measurable_const.sumElim (twoPointKernel.measurable_coe hB)


-- @@ L37-40 verbatim
@[simp]
theorem augmentedTwoPointKernel_atom :
    augmentedTwoPointKernel (Sum.inl ()) = Measure.dirac 1 :=
  by simp [augmentedTwoPointKernel]


-- @@ L42-45 verbatim
@[simp]
theorem augmentedTwoPointKernel_pair (p : TwoPointParams) :
    augmentedTwoPointKernel (Sum.inr p) = twoPointMeasure p.1.1 p.1.2 :=
  by simp [augmentedTwoPointKernel]


-- @@ L47-56 verbatim
instance : IsMarkovKernel augmentedTwoPointKernel where
  isProbabilityMeasure p := by
    cases p with
    | inl u =>
        cases u
        rw [augmentedTwoPointKernel_atom]
        infer_instance
    | inr p =>
        rw [augmentedTwoPointKernel_pair]
        exact twoPointMeasure_isProbability p.2.1 p.2.2.1 p.2.2.2


-- @@ L58-67 verbatim
/-- Every conditional law selected by an augmented parameter has mean one. -/
theorem augmentedTwoPointKernel_mean (p : AugmentedTwoPointParams) :
    (∫ x : ℝ, x ∂(augmentedTwoPointKernel p)) = 1 := by
  cases p with
  | inl u =>
      cases u
      simp
  | inr p =>
      rw [augmentedTwoPointKernel_pair]
      exact twoPointMeasure_mean p.2.1 p.2.2.1 p.2.2.2


-- @@ L69-86 verbatim
/-- Every conditional law is concentrated on either one point or the two
points encoded by its latent parameter. -/
theorem augmentedTwoPointKernel_support
    (p : AugmentedTwoPointParams) :
    augmentedTwoPointKernel p
        (match p with
          | Sum.inl _ => ({1} : Set ℝ)ᶜ
          | Sum.inr q => ({q.1.1, q.1.2} : Set ℝ)ᶜ) = 0 := by
  cases p with
  | inl u =>
      cases u
      simp
  | inr p =>
      rw [augmentedTwoPointKernel_pair, twoPointMeasure]
      simp only [Measure.add_apply, Measure.smul_apply,
        Measure.dirac_apply' _
          (measurableSet_insert.mpr (measurableSet_singleton _)).compl]
      simp


-- @@ L88-93 verbatim
/-- The complete latent law: its left branch carries the atom at one, and its
right branch carries the nondegenerate parameter measure. -/
noncomputable def augmentedLatentMeasure (μ : Measure ℝ) (M : ℝ) :
    Measure AugmentedTwoPointParams :=
  μ {1} • Measure.dirac (Sum.inl ()) +
    (latentParamsMeasure μ M).map Sum.inr


-- @@ L95-100 verbatim
theorem augmentedLatentMeasure_apply_atom
    (μ : Measure ℝ) (M : ℝ) :
    augmentedLatentMeasure μ M (Set.range Sum.inl) = μ {1} := by
  rw [augmentedLatentMeasure, Measure.add_apply,
    Measure.smul_apply, Measure.map_apply measurable_inr measurableSet_range_inl]
  simp


-- @@ L102-121 verbatim
/-- Binding the augmented latent law against its conditional kernel gives
exactly the full one-coordinate mixture. -/
theorem augmentedTwoPointKernel_comp_latent
    (μ : Measure ℝ) (M : ℝ) :
    augmentedTwoPointKernel ∘ₘ augmentedLatentMeasure μ M =
      fullKernelMixture μ M := by
  ext B hB
  rw [Measure.bind_apply hB augmentedTwoPointKernel.aemeasurable]
  rw [augmentedLatentMeasure, lintegral_add_measure]
  · rw [lintegral_smul_measure]
    rw [lintegral_dirac' _ (augmentedTwoPointKernel.measurable_coe hB)]
    rw [lintegral_map' (by
      exact (augmentedTwoPointKernel.measurable_coe hB).aemeasurable)
      measurable_inr.aemeasurable]
    simp only [augmentedTwoPointKernel_atom, augmentedTwoPointKernel_pair]
    change μ {1} * Measure.dirac 1 B +
        ∫⁻ p, twoPointMeasure p.1.1 p.1.2 B ∂latentParamsMeasure μ M =
      fullKernelMixture μ M B
    rw [← kernelTwoPointMixture_apply (latentParamsMeasure μ M) hB]
    rfl


-- @@ L123-147 verbatim
/-- Under the hypotheses of the decomposition, the complete latent law is
itself a probability measure. -/
theorem augmentedLatentMeasure_isProbability
    {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x : ℝ ↦ x) μ)
    (hmean : (∫ x : ℝ, x ∂μ) = 1)
    (hM : 0 < belowMoment μ) :
    IsProbabilityMeasure
      (augmentedLatentMeasure μ (belowMoment μ)) := by
  constructor
  have hfull :
      fullKernelMixture μ (belowMoment μ) Set.univ = 1 :=
    (fullKernelMixture_isProbability hμ hmean hM).measure_univ
  rw [← augmentedTwoPointKernel_comp_latent μ (belowMoment μ),
    Measure.bind_apply MeasurableSet.univ
      augmentedTwoPointKernel.aemeasurable] at hfull
  have hpoint :
      (fun p : AugmentedTwoPointParams ↦
        augmentedTwoPointKernel p Set.univ) = fun _ ↦ (1 : ENNReal) := by
    funext p
    let : IsProbabilityMeasure (augmentedTwoPointKernel p) :=
      inferInstance
    exact measure_univ
  rw [hpoint, lintegral_one] at hfull
  exact hfull


-- @@ L149-159 verbatim
/-- The bind/Tonelli identity for the complete one-coordinate latent
decomposition. -/
theorem lintegral_augmentedTwoPointKernel_comp
    (μ : Measure ℝ) (M : ℝ) (f : ℝ → ENNReal)
    (hf : Measurable f) :
    (∫⁻ x, f x ∂fullKernelMixture μ M) =
      ∫⁻ p, ∫⁻ x, f x ∂augmentedTwoPointKernel p
        ∂augmentedLatentMeasure μ M := by
  rw [← augmentedTwoPointKernel_comp_latent μ M]
  exact Measure.lintegral_bind
    augmentedTwoPointKernel.aemeasurable hf.aemeasurable


-- @@ L161-161 verbatim
end


-- @@ L163-163 verbatim
end Feige
