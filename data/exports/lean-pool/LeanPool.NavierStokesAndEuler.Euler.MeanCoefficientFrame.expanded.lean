/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.MeanCoefficientTime


-- @@ L11-11 verbatim
/-! Genuine matrix-frame identities induce the operator identities used by the mean inverse. -/


-- @@ L13-13 verbatim
@[expose] public section



-- @@ L16-16 verbatim
noncomputable section


-- @@ L18-18 verbatim
namespace EulerMeanCoefficients


-- @@ L20-21 verbatim
open MeasureTheory InnerProductSpace Set EulerSmoothLimit EulerMeanSolenoidal
  EulerLiftedPressure

-- @@ L22-22 verbatim
open scoped BoundedContinuousFunction NNReal


-- @@ L24-25 verbatim
/-- Cache the standard `NormedAddCommGroup Field` instance to shorten typeclass synthesis. -/
local instance instMeanCoefficientFrame1 : NormedAddCommGroup Field := inferInstance

-- @@ L26-27 verbatim
/-- Cache the standard `NormedSpace ℝ Field` instance to shorten typeclass synthesis. -/
local instance instMeanCoefficientFrame2 : NormedSpace ℝ Field := inferInstance


-- @@ L29-32 verbatim
/-- Adjoint field as an element of `Field`. -/
def adjointField (A : Field) : Field :=
  (ContinuousLinearMap.adjoint.toContinuousLinearEquiv.toContinuousLinearMap
    : (Space →L[ℝ] Space) →L[ℝ] (Space →L[ℝ] Space)).compLeftContinuousBounded Space A


-- @@ L34-35 verbatim
@[simp] theorem adjointField_apply (A : Field) (x : Space) :
    adjointField A x = (A x).adjoint := rfl


-- @@ L37-39 verbatim
theorem multiplier_adjointField (A : Field) : multiplier (adjointField A) = (multiplier A).adjoint
    :=
  multiplier_adjoint A (adjointField A) (fun _ => rfl)


-- @@ L41-49 verbatim
theorem operatorPath_comp (T : ℝ) (A B C : C(Icc (0 : ℝ) T, Field))
    (hABC : ∀ t x v, C t x v = A t x (B t x v)) :
    ∀ t (u : L2), operatorPath T C t u = operatorPath T A t (operatorPath T B t u) := by
  intro t u
  apply Lp.ext
  filter_upwards [multiplier_ae (C t) u, multiplier_ae (A t) (multiplier (B t) u),
    multiplier_ae (B t) u] with x hc ha hb
  change (multiplier (C t) u) x = (multiplier (A t) (multiplier (B t) u)) x
  rw [hc, ha, hb, hABC]


-- @@ L51-62 verbatim
theorem operatorPath_neg_comp (T : ℝ) (A B C : C(Icc (0 : ℝ) T, Field))
    (hABC : ∀ t x v, C t x v = -(A t x (B t x v))) :
    ∀ t (u : L2), operatorPath T C t u = -(operatorPath T A t (operatorPath T B t u)) := by
  intro t u
  apply Lp.ext
  filter_upwards [multiplier_ae (C t) u, multiplier_ae (A t) (multiplier (B t) u),
    multiplier_ae (B t) u, Lp.coeFn_neg (multiplier (A t) (multiplier (B t) u))]
    with x hc ha hb hn
  change (multiplier (C t) u) x = (-(multiplier (A t) (multiplier (B t) u))) x
  rw [hc, hn]
  simp only [Pi.neg_apply]
  rw [ha, hb, hABC]


-- @@ L64-70 verbatim
theorem operatorPath_identity_at (T : ℝ) (A : C(Icc (0 : ℝ) T, Field)) (t : Icc (0 : ℝ) T)
    (hA : ∀ x v, A t x v = v) : operatorPath T A t = ContinuousLinearMap.id ℝ L2 := by
  apply ContinuousLinearMap.ext
  intro u
  apply Lp.ext
  filter_upwards [multiplier_ae (A t) u] with x hx
  exact hx.trans (hA x (u x))


-- @@ L72-80 verbatim
theorem operatorPath_initial_coefficient (T : ℝ) (hT : 0 ≤ T)
    (A : C(Icc (0 : ℝ) T, Field)) (M : Field)
    (hAM : ∀ x, A ⟨0, le_rfl, hT⟩ x = M x) (C : ℝ≥0) (hC : ∀ x, ‖M x‖ ≤ C) :
    operatorPath T A ⟨0, le_rfl, hT⟩ =
      coefficientOperator M M.continuous.aestronglyMeasurable C hC := by
  have he : A ⟨0, le_rfl, hT⟩ = M := BoundedContinuousFunction.ext hAM
  change multiplier (A ⟨0, le_rfl, hT⟩) = _
  rw [he]
  exact multiplier_eq_coefficientOperator M C hC


-- @@ L82-86 verbatim
theorem operatorPath_norm_le (T : ℝ) (A : C(Icc (0 : ℝ) T, Field)) :
    ‖operatorPath T A‖ ≤ ‖A‖ := by
  apply (ContinuousMap.norm_le (operatorPath T A) (norm_nonneg A)).2
  intro t
  exact (multiplier_norm_le (A t)).trans (A.norm_coe_le_norm t)


-- @@ L88-93 verbatim
theorem operatorPath_norm_le_of_pointwise (T : ℝ) (A : C(Icc (0 : ℝ) T, Field))
    (C : ℝ) (hC : 0 ≤ C) (hA : ∀ t x, ‖A t x‖ ≤ C) : ‖operatorPath T A‖ ≤ C := by
  apply (operatorPath_norm_le T A).trans
  apply (ContinuousMap.norm_le A hC).2
  intro t
  exact (BoundedContinuousFunction.norm_le hC).2 (hA t)


-- @@ L95-95 verbatim
end EulerMeanCoefficients
