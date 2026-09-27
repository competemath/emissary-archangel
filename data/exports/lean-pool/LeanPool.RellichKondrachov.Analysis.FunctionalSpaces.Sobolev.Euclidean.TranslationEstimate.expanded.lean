/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module

public import LeanPool.RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.H1
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff


-- @@ L14-24 verbatim
/-!
# `RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.TranslationEstimate`

Pointwise translation estimates for `C¹_c` functions on Euclidean spaces.

This file provides the key analytic inequality used later in the Euclidean Rellich step:
translation differences are controlled by the `L²`-gradient.

At this stage we only prove *pointwise* inequalities along the segment `t ↦ x + t • a`.
The measure-theoretic lifting to `L²` is tracked separately under `lean-103.5.2.26.5.3.2.3`.
-/


-- @@ L26-26 verbatim
@[expose] public section


-- @@ L28-28 verbatim
namespace RellichKondrachov

-- @@ L29-29 verbatim
namespace Analysis

-- @@ L30-30 verbatim
namespace FunctionalSpaces

-- @@ L31-31 verbatim
namespace Sobolev

-- @@ L32-32 verbatim
namespace Euclidean


-- @@ L34-34 verbatim
open scoped ENNReal MeasureTheory Topology

-- @@ L35-35 verbatim
open MeasureTheory Set


-- @@ L37-37 verbatim
section


-- @@ L39-39 verbatim
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]


-- @@ L41-43 verbatim
/-- Borel σ-algebra on the model space `E`. -/
local instance instMeasurableSpaceTranslationEstimate :
    MeasurableSpace E := borel E

-- @@ L44-45 verbatim
local instance instBorelSpaceTranslationEstimate :
    BorelSpace E := ⟨rfl⟩

-- @@ L46-48 verbatim
local instance instOpensMeasurableSpaceTranslationEstimate :
    OpensMeasurableSpace E := by
  infer_instance


-- @@ L50-50 verbatim
/-! ## Derivative along a translated line -/


-- @@ L52-54 verbatim
/-- The affine line `t ↦ x + t • a`. -/
def line (x a : E) (t : ℝ) : E :=
  x + t • a


-- @@ L56-61 verbatim
lemma hasDerivAt_line (x a : E) (t : ℝ) :
    HasDerivAt (line (x := x) (a := a)) a t := by
  -- `t ↦ t • a` has derivative `a`, and adding the constant `x` preserves the derivative.
  have hsmul : HasDerivAt (fun t : ℝ => t • a) a t := by
    simpa [one_smul] using (hasDerivAt_id t).smul_const a
  exact HasDerivAt.const_add x hsmul


-- @@ L63-65 verbatim
lemma deriv_line (x a : E) (t : ℝ) :
    deriv (line (x := x) (a := a)) t = a :=
  (hasDerivAt_line (x := x) (a := a) t).deriv


-- @@ L67-74 verbatim
lemma hasDerivAt_comp_line
    {f : E → ℝ} (hf : ContDiff ℝ 1 f) (x a : E) (t : ℝ) :
    HasDerivAt (fun t => f (line (x := x) (a := a) t))
      (fderiv ℝ f (line (x := x) (a := a) t) a) t := by
  have hf' : HasFDerivAt f (fderiv ℝ f (line (x := x) (a := a) t)) (line (x := x) (a := a) t) :=
    (hf.differentiable one_ne_zero).differentiableAt.hasFDerivAt
  exact
    HasFDerivAt.comp_hasDerivAt_of_eq t hf' (hasDerivAt_line (x := x) (a := a) t) rfl


-- @@ L76-79 verbatim
lemma deriv_comp_line {f : E → ℝ} (hf : ContDiff ℝ 1 f) (x a : E) (t : ℝ) :
    deriv (fun t => f (line (x := x) (a := a) t)) t =
      fderiv ℝ f (line (x := x) (a := a) t) a :=
  (hasDerivAt_comp_line (hf := hf) (x := x) (a := a) t).deriv


-- @@ L81-81 verbatim
/-! ## Pointwise translation bound via the gradient -/


-- @@ L83-83 verbatim
section


-- @@ L85-85 verbatim
variable [CompleteSpace E]


-- @@ L87-101 verbatim
lemma enorm_fderiv_apply_le_enorm_grad_mul (f : E → ℝ) (x a : E) :
    ‖fderiv ℝ f x a‖ₑ ≤ ‖grad (E := E) f x‖ₑ * ‖a‖ₑ := by
  -- Use the operator norm bound, then identify `‖fderiv‖` with `‖grad‖` via the Riesz isometry.
  have h₁ :
      ‖fderiv ℝ f x a‖ₑ ≤ ‖fderiv ℝ f x‖ₑ * ‖a‖ₑ :=
    (ContinuousLinearMap.le_opENorm (f := fderiv ℝ f x) a)
  have h₂ : ‖grad (E := E) f x‖ₑ = ‖fderiv ℝ f x‖ₑ := by
    -- `grad f x = (toDual).symm (fderiv f x)` and `toDual.symm` is an isometry.
    simp only [grad]
    exact
      (LinearIsometry.enorm_map
        (f := (InnerProductSpace.toDual ℝ E).symm.toLinearIsometry)
        (fderiv ℝ f x))
  -- Replace the operator norm by the gradient norm.
  simpa [h₂, mul_assoc, mul_left_comm, mul_comm] using h₁


-- @@ L103-112 verbatim
lemma enorm_deriv_comp_line_le (x a : E) {f : E → ℝ} (hf : ContDiff ℝ 1 f) (t : ℝ) :
    ‖deriv (fun t => f (line (x := x) (a := a) t)) t‖ₑ ≤
      ‖a‖ₑ * ‖grad (E := E) f (line (x := x) (a := a) t)‖ₑ := by
  -- Reduce to the `fderiv` bound.
  have :=
    enorm_fderiv_apply_le_enorm_grad_mul
      (E := E) (f := f) (x := line (x := x) (a := a) t) (a := a)
  -- Rewrite `deriv` and commute the product.
  simpa [deriv_comp_line (hf := hf) (x := x) (a := a) t,
    mul_comm, mul_left_comm, mul_assoc] using this


-- @@ L114-163 verbatim
lemma enorm_sub_le_enorm_mul_lintegral_grad (x a : E) {f : E → ℝ} (hf : ContDiff ℝ 1 f) :
    ‖f (x + a) - f x‖ₑ ≤
      ‖a‖ₑ * ∫⁻ t in Icc (0 : ℝ) 1, ‖grad (E := E) f (x + t • a)‖ₑ := by
  -- Apply FTC along the segment `t ↦ x + t • a`, then bound the derivative pointwise.
  have hCont :
      ContDiffOn ℝ 1 (fun t : ℝ => f (x + t • a)) (Icc (0 : ℝ) 1) := by
    -- `t ↦ x + t • a` is `C^∞`; compose with `f`.
    have hInner : ContDiff ℝ ⊤ (fun t : ℝ => x + t • a) := by
      simpa [line] using
        (contDiff_const.add (contDiff_id.smul (contDiff_const : ContDiff ℝ ⊤ (fun _ : ℝ => a))))
    have hInner' : ContDiff ℝ 1 (fun t : ℝ => x + t • a) := hInner.of_le (by simp)
    exact (hf.comp hInner').contDiffOn
  have hFTC :
      ‖f (x + a) - f x‖ₑ ≤ ∫⁻ t in Icc (0 : ℝ) 1, ‖deriv (fun t : ℝ => f (x + t • a)) t‖ₑ := by
    simpa using
      (enorm_sub_le_lintegral_deriv_of_contDiffOn_Icc (f := fun t : ℝ => f (x + t • a))
        (a := (0 : ℝ)) (b := 1) hCont (by exact zero_le_one))
  refine hFTC.trans ?_
  have hDerivBound :
      (fun t : ℝ => ‖deriv (fun t : ℝ => f (x + t • a)) t‖ₑ)
        ≤ᵐ[Measure.restrict volume (Icc (0 : ℝ) 1)]
          fun t : ℝ => ‖a‖ₑ * ‖grad (E := E) f (x + t • a)‖ₑ := by
    -- Pointwise bound holds everywhere.
    refine (ae_of_all _ fun t => ?_)
    -- `deriv` along `t ↦ x + t•a` is controlled by the gradient.
    simpa [line, mul_assoc, mul_left_comm, mul_comm] using
      (enorm_deriv_comp_line_le (x := x) (a := a) (f := f) hf (t := t))
  -- Pull out the constant `‖a‖ₑ`.
  have :
      (∫⁻ t in Icc (0 : ℝ) 1, ‖deriv (fun t : ℝ => f (x + t • a)) t‖ₑ) ≤
        ∫⁻ t in Icc (0 : ℝ) 1, ‖a‖ₑ * ‖grad (E := E) f (x + t • a)‖ₑ := by
    exact lintegral_mono_ae hDerivBound
  refine this.trans ?_
  -- Pull out the constant factor.
  have hMeas :
      Measurable fun t : ℝ => ‖grad (E := E) f (x + t • a)‖ₑ := by
    -- `grad f` is continuous when `f` is `C¹`.
    have hgradCont : Continuous (grad (E := E) f) := continuous_grad (E := E) (f := f) (by
      -- `ContDiff` gives continuity of `grad`.
      exact hf)
    -- hence `t ↦ grad f (x + t•a)` is measurable; take `enorm`.
    exact (hgradCont.comp (by
      have : Continuous (fun t : ℝ => x + t • a) := by
        fun_prop
      exact this)).measurable.enorm
  -- Now finish: `∫⁻ t in Icc, ‖a‖ * g t = ‖a‖ * ∫⁻ t in Icc, g t`.
  exact le_of_eq <| by
    simpa [mul_assoc] using
      (MeasureTheory.lintegral_const_mul (μ := volume.restrict (Icc (0 : ℝ) 1)) (r := ‖a‖ₑ)
        (f := fun t : ℝ => ‖grad (E := E) f (x + t • a)‖ₑ) hMeas)


-- @@ L165-165 verbatim
end


-- @@ L167-167 verbatim
end


-- @@ L169-169 verbatim
end Euclidean

-- @@ L170-170 verbatim
end Sobolev

-- @@ L171-171 verbatim
end FunctionalSpaces

-- @@ L172-172 verbatim
end Analysis

-- @@ L173-173 verbatim
end RellichKondrachov
