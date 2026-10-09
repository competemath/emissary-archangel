import OAI.Geometry.Zonotope.Support
import OAI.Geometry.Zonotope.Determinant
import Mathlib.LinearAlgebra.Determinant


-- @@ L5-5 verbatim
namespace OAI


-- @@ L7-7 verbatim
noncomputable section

-- @@ L8-8 verbatim
open Set


-- @@ L10-10 verbatim
namespace DiagonalZonotope

-- @@ L11-11 verbatim
variable {ι : Type*} [Fintype ι] [DecidableEq ι]


-- @@ L13-25 verbatim
/-- The determinant-one shear that supplies the linear part of a facet extrusion. -/
def shear (i : ι) : (ι → ℝ) →ₗ[ℝ] (ι → ℝ) where
  toFun s j := if j = i then s i else s j + s i
  map_add' x y := by
    funext j
    by_cases h : j = i
    · simp [h]
    · simp [h, add_left_comm, add_comm]
  map_smul' c x := by
    funext j
    by_cases h : j = i
    · simp [h]
    · simp [h, mul_add]


-- @@ L27-39 verbatim
lemma shear_matrix (i : ι) :
    LinearMap.toMatrix' (shear i) =
      (1 : Matrix ι ι ℝ).updateCol i (fun _ => 1) := by
  ext k j
  by_cases hji : j = i
  · subst j
    by_cases hki : k = i <;>
      simp [LinearMap.toMatrix'_apply, shear, Matrix.updateCol, hki]
  · by_cases hki : k = i
    · subst k
      simp [LinearMap.toMatrix'_apply, shear, Matrix.updateCol, hji, Ne.symm hji]
    · simp [LinearMap.toMatrix'_apply, shear, Matrix.updateCol, hji, hki,
        Ne.symm hji, Pi.single_apply, Matrix.one_apply]


-- @@ L41-43 verbatim
/-- No absolute determinant factor is lost in the extrusion parameterization. -/
theorem shear_det (i : ι) : LinearMap.det (shear i) = 1 := by
  rw [← LinearMap.det_toMatrix', shear_matrix, det_identity_updateCol_ones]


-- @@ L45-52 verbatim
omit [Fintype ι] in
lemma extrusionMap_eq (i : ι) (s : ι → ℝ) :
    extrusionMap i s = Pi.single i 1 + shear i s := by
  funext j
  by_cases hji : j = i
  · subst j
    simp [extrusionMap, shear]
  · simp [extrusionMap, shear, hji]


-- @@ L54-54 verbatim
end DiagonalZonotope


-- @@ L56-56 verbatim
end


-- @@ L58-58 verbatim
end OAI
