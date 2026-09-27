/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Setting.Examples.ShearFlow


-- @@ L10-10 verbatim
/-! # Pointwise energy calculus for the viscous shear -/


-- @@ L12-12 verbatim
@[expose] public section


-- @@ L14-14 verbatim
open MeasureTheory Set

-- @@ L15-15 verbatim
open CKN.Foundation.Parabolic

-- @@ L16-16 verbatim
open CKN.ShearCalculus



-- @@ L19-19 verbatim
namespace CKN


-- @@ L21-22 verbatim
/-- The kinetic-energy density of the shear. -/
noncomputable def shearEnergy (z : Vec3 × ℝ) : ℝ := shearAmplitude z * shearAmplitude z


-- @@ L24-25 verbatim
/-- The cubic scalar transport factor. -/
noncomputable def shearTransport (z : Vec3 × ℝ) : ℝ := shearEnergy z * shearAmplitude z


-- @@ L27-29 verbatim
/-- Smoothness of the energy density. -/
theorem shearEnergy_smooth : ContDiff ℝ (⊤ : ℕ∞) shearEnergy :=
  shearAmplitude_smooth.mul shearAmplitude_smooth


-- @@ L31-33 verbatim
/-- Smoothness of the cubic transport factor. -/
theorem shearTransport_smooth : ContDiff ℝ (⊤ : ℕ∞) shearTransport :=
  shearEnergy_smooth.mul shearAmplitude_smooth


-- @@ L35-45 verbatim
/-- The energy has no derivative along the flow direction. -/
theorem shearEnergy_spatial (z : Vec3 × ℝ) (j : Fin 3) :
    spatialPartial shearEnergy j z =
      if j = 1 then 2 * (shearAmplitude z * shearSlope z) else 0 := by
  change spatialPartial (fun w : Vec3 × ℝ => shearAmplitude w * shearAmplitude w) j z = _
  rw [spatial_mul shearAmplitude_smooth shearAmplitude_smooth]
  rw [shearAmplitude_spatial]
  by_cases hj : j = 1
  · simp only [hj, ite_true]
    ring
  · simp [hj]


-- @@ L47-53 verbatim
/-- Time derivative of the energy density. -/
theorem shearEnergy_time (z : Vec3 × ℝ) :
    timePartial shearEnergy z = -2 * shearEnergy z := by
  change timePartial (fun w : Vec3 × ℝ => shearAmplitude w * shearAmplitude w) z = _
  rw [time_mul shearAmplitude_smooth shearAmplitude_smooth, shearAmplitude_time]
  unfold shearEnergy
  ring


-- @@ L55-61 verbatim
/-- The cubic transport also has zero flow-direction derivative. -/
theorem shearTransport_spatial_zero (z : Vec3 × ℝ) :
    spatialPartial shearTransport 0 z = 0 := by
  change spatialPartial (fun w : Vec3 × ℝ => shearEnergy w * shearAmplitude w) 0 z = _
  rw [spatial_mul shearEnergy_smooth shearAmplitude_smooth,
    shearEnergy_spatial, shearAmplitude_spatial]
  norm_num


-- @@ L63-82 verbatim
/-- Second spatial derivatives of the energy density. -/
theorem shearEnergy_second (z : Vec3 × ℝ) (j : Fin 3) :
    spatialPartial (fun w : Vec3 × ℝ => spatialPartial shearEnergy j w) j z =
      if j = 1 then 2 * (shearSlope z * shearSlope z - shearEnergy z) else 0 := by
  have he : (fun w : Vec3 × ℝ => spatialPartial shearEnergy j w) =
      (fun w : Vec3 × ℝ => if j = 1 then 2 * (shearAmplitude w * shearSlope w) else 0) := by
    funext w
    exact shearEnergy_spatial w j
  rw [he]
  by_cases hj : j = 1
  · subst j
    simp only [ite_true]
    rw [spatial_mul contDiff_const (shearAmplitude_smooth.mul shearSlope_smooth),
      spatial_mul shearAmplitude_smooth shearSlope_smooth,
      shearAmplitude_spatial, shearSlope_spatial]
    simp only [spatialPartial, fderiv_const_apply, zero_apply, zero_mul,
      zero_add, ite_true]
    unfold shearEnergy
    ring
  · simp [hj, spatialPartial]


-- @@ L84-89 verbatim
/-- The squared Euclidean speed is the scalar energy. -/
theorem shearFlow_energy (z : ParabolicPoint) :
    vec3EuclideanNorm (shearFlow z) ^ 2 = shearEnergy z := by
  unfold vec3EuclideanNorm
  rw [Real.sq_sqrt (Finset.sum_nonneg fun i _hi => sq_nonneg _)]
  simp [shearFlow, shearEnergy, shearAmplitude, pow_two]


-- @@ L91-94 verbatim
/-- The squared gradient density is the squared transverse slope. -/
theorem shearFlow_gradientSq (z : ParabolicPoint) :
    spatialGradientSq shearFlow shearFlowGrad z = shearSlope z * shearSlope z := by
  simp [spatialGradientSq, shearFlowGrad, Fin.sum_univ_three, shearSlope, pow_two]


-- @@ L96-96 verbatim
end CKN
