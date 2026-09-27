/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.ParentPacketLabelData
import LeanPool.NavierStokesAndEuler.ForMathlib.SmoothnessOrder


-- @@ L12-14 verbatim
/-! Keeping the physical label scale in the coefficient bounds gives one
factor ell for each normalized spatial derivative. This factor is needed
in the neighboring-label estimates of the induction. -/


-- @@ L16-16 verbatim
@[expose] public section



-- @@ L19-19 verbatim
noncomputable section


-- @@ L21-21 verbatim
namespace EulerOperatorGevreyCalculus


-- @@ L23-23 verbatim
open EulerGevrey

-- @@ L24-24 verbatim
open scoped ContDiff


-- @@ L26-27 verbatim
variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]


-- @@ L29-37 verbatim
theorem scalar_precomp_bound (f : E → V) (hf : ContDiff ℝ ∞ f)
    (C R ell : ℝ) (hell : 0 ≤ ell)
    (hb : ∀ n x, ‖iteratedFDeriv ℝ n f x‖ ≤ C * majorant R 0 n) (n : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ n (fun y => f (ell • y)) x‖ ≤ C*majorant (ell*R) 0 n := by
  rw [iteratedFDeriv_comp_const_smul ell (hf.of_le (by simp)),norm_smul,
    Real.norm_eq_abs,abs_of_nonneg (pow_nonneg hell n)]
  calc
    _ ≤ ell^n*(C*majorant R 0 n) := mul_le_mul_of_nonneg_left (hb n (ell • x)) (pow_nonneg hell n)
    _ = _ := by simp only [majorant,Nat.add_zero,mul_pow]; ring


-- @@ L39-39 verbatim
end EulerOperatorGevreyCalculus


-- @@ L41-41 verbatim
namespace EulerParentPacketFrames.LabelData


-- @@ L43-44 verbatim
open Set ContinuousLinearMap EulerSmoothLimit EulerMeanCoefficients EulerLpTranslation
  EulerPacketParentLabelBounds EulerPacketCofactor EulerGevrey EulerOperatorGevreyCalculus

-- @@ L45-45 verbatim
open scoped ContDiff BoundedContinuousFunction


-- @@ L47-47 verbatim
variable {G : Parent} (L : LabelData G)


-- @@ L49-50 verbatim
/-- Scaled radius, given by `G.ell*coefficientRadius L.K`. -/
def scaledRadius : ℝ := G.ell*coefficientRadius L.K


-- @@ L52-53 verbatim
theorem scaledRadius_nonneg : 0 ≤ L.scaledRadius :=
  mul_nonneg G.ell_pos.le (coefficientRadius_nonneg L.K)


-- @@ L55-64 verbatim
theorem scaled_gradient_bound (A : SmoothL2Field Space) (hA : HasLabelBound L.K A)
    (n : ℕ) (x : Space) :
    ‖iteratedFDeriv ℝ n (fun y => fderiv ℝ A.field (G.ell • y)) x‖ ≤
      gradientAmplitude L.K*majorant L.scaledRadius 0 n := by
  apply scalar_precomp_bound (fderiv ℝ A.field) (A.smooth.fderiv_right (m := ∞) (by simp))
    (gradientAmplitude L.K) (coefficientRadius L.K) G.ell G.ell_pos.le
  intro j y
  have h := source_gradient_bound A.toLp A.translation_contDiff A.field A.smooth A.toLp_ae
    L.K (zero_le_one.trans L.K_one) hA (ContinuousLinearMap.id ℝ Space) norm_id_le j y
  simpa only [ContinuousLinearMap.id_apply] using h


-- @@ L66-82 verbatim
theorem frame_scaled_bound (n : ℕ) (t : Icc (0 : ℝ) G.T) (x : Space) :
    ‖iteratedFDeriv ℝ n (G.frame.field t : Space → EndSpace) x‖ ≤
      frameAmplitude L.K*majorant L.scaledRadius 0 n := by
  have he : (G.frame.field t : Space → EndSpace) =
      fun y => ContinuousLinearMap.id ℝ Space+fderiv ℝ (L.displacement t).field (G.ell • y) :=
    funext (L.frame_match t)
  rw [he]
  apply scalar_precomp_bound (fun y => ContinuousLinearMap.id ℝ Space+fderiv ℝ (L.displacement
      t).field y)
    (contDiff_const.add ((L.displacement t).smooth.fderiv_right (m := ∞) (by simp)))
    (frameAmplitude L.K) (coefficientRadius L.K) G.ell G.ell_pos.le
  intro j y
  have h := source_deformation_bound (L.displacement t).toLp (L.displacement t).translation_contDiff
    (L.displacement t).field (L.displacement t).smooth (L.displacement t).toLp_ae
    L.K (zero_le_one.trans L.K_one) (L.displacement_bound t)
    (ContinuousLinearMap.id ℝ Space) norm_id_le j y
  simpa only [ContinuousLinearMap.id_apply] using h


-- @@ L84-90 verbatim
theorem first_scaled_bound (n : ℕ) (t : Icc (0 : ℝ) G.T) (x : Space) :
    ‖iteratedFDeriv ℝ n (G.first.field t : Space → EndSpace) x‖ ≤
      gradientAmplitude L.K*majorant L.scaledRadius 0 n := by
  have he : (G.first.field t : Space → EndSpace) =
      fun y => fderiv ℝ (L.velocity t).field (G.ell • y) := funext (L.first_match t)
  rw [he]
  exact L.scaled_gradient_bound (L.velocity t) (L.velocity_bound t) n x


-- @@ L92-98 verbatim
theorem second_scaled_bound (n : ℕ) (t : Icc (0 : ℝ) G.T) (x : Space) :
    ‖iteratedFDeriv ℝ n (G.second.field t : Space → EndSpace) x‖ ≤
      gradientAmplitude L.K*majorant L.scaledRadius 0 n := by
  have he : (G.second.field t : Space → EndSpace) =
      fun y => fderiv ℝ (L.acceleration t).field (G.ell • y) := funext (L.second_match t)
  rw [he]
  exact L.scaled_gradient_bound (L.acceleration t) (L.acceleration_bound t) n x


-- @@ L100-106 verbatim
theorem inverse_scaled_bound (n : ℕ) (t : Icc (0 : ℝ) G.T) (x : Space) :
    ‖iteratedFDeriv ℝ n (G.inverse.field t : Space → EndSpace) x‖ ≤
      (9*(frameAmplitude L.K)^2)*majorant L.scaledRadius 0 n :=
  coefficientInverse_bound G.frame.toSmoothCoefficientPath G.inverse.field G.frame_det
      G.inverse_left
    L.scaledRadius (frameAmplitude L.K) L.scaledRadius_nonneg (frameAmplitude_nonneg L.K)
    L.frame_scaled_bound n t x


-- @@ L108-115 verbatim
theorem strain_scaled_bound (n : ℕ) (t : Icc (0 : ℝ) G.T) (x : Space) :
    ‖iteratedFDeriv ℝ n (G.strain.field t : Space → EndSpace) x‖ ≤
      (27*(frameAmplitude L.K)^2*gradientAmplitude L.K)*majorant L.scaledRadius 0 n :=
  coefficientStrain_bound G.frame.toSmoothCoefficientPath G.first.toSmoothCoefficientPath
    G.strain.toSmoothCoefficientPath G.frame_det G.strain_equation L.scaledRadius
    (frameAmplitude L.K) (gradientAmplitude L.K) L.scaledRadius_nonneg
    (frameAmplitude_nonneg L.K) (gradientAmplitude_nonneg L.K)
    L.frame_scaled_bound L.first_scaled_bound n t x


-- @@ L117-124 verbatim
theorem curvature_scaled_bound (n : ℕ) (t : Icc (0 : ℝ) G.T) (x : Space) :
    ‖iteratedFDeriv ℝ n (G.curvature.field t : Space → EndSpace) x‖ ≤
      (27*(frameAmplitude L.K)^2*gradientAmplitude L.K)*majorant L.scaledRadius 0 n :=
  coefficientCurvature_bound G.frame.toSmoothCoefficientPath G.second.toSmoothCoefficientPath
    G.curvature.toSmoothCoefficientPath G.frame_det G.second_equation L.scaledRadius
    (frameAmplitude L.K) (gradientAmplitude L.K) L.scaledRadius_nonneg
    (frameAmplitude_nonneg L.K) (gradientAmplitude_nonneg L.K)
    L.frame_scaled_bound L.second_scaled_bound n t x


-- @@ L126-126 verbatim
end EulerParentPacketFrames.LabelData
