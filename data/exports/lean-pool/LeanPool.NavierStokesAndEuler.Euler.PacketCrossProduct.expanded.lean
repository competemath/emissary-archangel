/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.Foundations.SmoothLimit
public import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.Geometry.Euclidean.Angle.Unoriented.CrossProduct


-- @@ L13-13 verbatim
/-! The ordinary Euclidean cross product as an actual bounded linear operator. -/


-- @@ L15-15 verbatim
@[expose] public section



-- @@ L18-18 verbatim
noncomputable section


-- @@ L20-20 verbatim
namespace EulerPacketCrossProduct


-- @@ L22-22 verbatim
open EulerSmoothLimit InnerProductSpace Matrix WithLp


-- @@ L24-25 verbatim
/-- Cross, given by `toLp 2 (crossProduct (ofLp a) (ofLp b))`. -/
def cross (a b : Space) : Space := toLp 2 (crossProduct (ofLp a) (ofLp b))


-- @@ L27-30 verbatim
theorem cross_norm_le (a b : Space) : ‖cross a b‖ ≤ ‖a‖*‖b‖ := by
  rw [cross, InnerProductGeometry.norm_ofLp_crossProduct]
  exact mul_le_of_le_one_right (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    (Real.sin_le_one _)


-- @@ L32-36 verbatim
/-- Cross linear, bundling `toFun`, `map_add`, `map_smul`. -/
def crossLinear (a : Space) : Space →ₗ[ℝ] Space where
  toFun := cross a
  map_add' b c := by simp [cross, map_add]
  map_smul' c b := by simp [cross, map_smul]


-- @@ L38-40 verbatim
/-- Cross left, given by `(crossLinear a).mkContinuous ‖a‖ (cross_norm_le a)`. -/
def crossLeft (a : Space) : Space →L[ℝ] Space :=
  (crossLinear a).mkContinuous ‖a‖ (cross_norm_le a)


-- @@ L42-42 verbatim
theorem crossLeft_apply (a b : Space) : crossLeft a b=cross a b := rfl


-- @@ L44-45 verbatim
theorem crossLeft_norm_le (a : Space) : ‖crossLeft a‖ ≤ ‖a‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) (cross_norm_le a)


-- @@ L47-49 verbatim
theorem dot_eq_inner (a b : Space) : ofLp a ⬝ᵥ ofLp b=⟪a,b⟫_ℝ := by
  simp only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
  exact dotProduct_comm _ _


-- @@ L51-54 verbatim
theorem cross_cross (m a : Space) :
    cross m (cross m a)=⟪m,a⟫_ℝ • m-‖m‖^2 • a := by
  simp only [cross, ofLp_toLp, cross_cross_eq_smul_sub_smul', toLp_sub, toLp_smul,
    toLp_ofLp, dot_eq_inner, real_inner_self_eq_norm_sq]


-- @@ L56-62 verbatim
theorem cross_negative_normalized (m a : Space) (hm : m ≠ 0)
    (ha : ⟪m, a⟫_ℝ = 0) : cross m (-((‖m‖^2)⁻¹) • cross m a)=a := by
  change crossLeft m (-((‖m‖^2)⁻¹) • cross m a)=a
  rw [map_smul, crossLeft_apply, cross_cross, ha, zero_smul, zero_sub, smul_neg,
    smul_smul]
  have hnorm : ‖m‖^2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hm)
  simp only [neg_mul, inv_mul_cancel₀ hnorm, neg_smul, one_smul, neg_neg]


-- @@ L64-66 verbatim
/-- Its normalization is exactly the linear map used inside the angular primitive for Q. -/
def potentialMultiplier (m : Space) : Space →L[ℝ] Space :=
  (-((‖m‖^2)⁻¹)) • crossLeft m


-- @@ L68-69 verbatim
theorem potentialMultiplier_apply (m a : Space) :
    potentialMultiplier m a=(-((‖m‖^2)⁻¹)) • cross m a := rfl


-- @@ L71-73 verbatim
theorem cross_potentialMultiplier (m a : Space) (hm : m ≠ 0)
    (ha : ⟪m, a⟫_ℝ = 0) : cross m (potentialMultiplier m a)=a :=
  cross_negative_normalized m a hm ha


-- @@ L75-75 verbatim
end EulerPacketCrossProduct
