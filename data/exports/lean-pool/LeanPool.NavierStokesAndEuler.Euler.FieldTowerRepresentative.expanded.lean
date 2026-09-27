/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.AllOrderCorrectionData
public import LeanPool.NavierStokesAndEuler.Euler.SobolevPointEvaluation
import LeanPool.NavierStokesAndEuler.Euler.ClassicalPressureCurl
import LeanPool.NavierStokesAndEuler.Euler.Foundations.SmoothPressureRepresentative
import LeanPool.NavierStokesAndEuler.Euler.SobolevJointEvaluation


-- @@ L15-16 verbatim
/-! Canonical smooth pointwise representatives of any genuine all-order
field tower. All spatial regularity follows from its actual Sobolev jets. -/


-- @@ L18-18 verbatim
@[expose] public section



-- @@ L21-21 verbatim
noncomputable section


-- @@ L23-23 verbatim
namespace EulerAllOrderCorrectionData.FieldTower


-- @@ L25-28 verbatim
open Set MeasureTheory EulerLiftedGradientSpace EulerCylinderSobolevSpace
  EulerCylinderSobolev EulerSpatialSobolevInverse EulerSobolevPointEvaluation
  EulerSobolevJointEvaluation EulerSmoothPressureRepresentative EulerMetricTransport
  EulerVolterraConvolution

-- @@ L29-29 verbatim
open scoped ContDiff


-- @@ L31-31 verbatim
variable {P T : ℝ} [Fact (0 < P)] (A : EulerAllOrderCorrectionData.FieldTower P T)


-- @@ L33-36 verbatim
/-- Spatial jet, given by `A.value_eq q t ▸ toJet P (A.realization q t)`. -/
def spatialJet (q : ℕ) (t : Icc (0 : ℝ) T) :
    SpatialJet P standardDirection q (A.field t) :=
  A.value_eq q t ▸ toJet P (A.realization q t)


-- @@ L38-40 verbatim
/-- Point field, given by `pointEvaluation P x (A.realization 3 t)`. -/
def pointField (t : Icc (0 : ℝ) T) (x : LiftDomain P) : Vector3 :=
  pointEvaluation P x (A.realization 3 t)


-- @@ L42-46 verbatim
theorem pointField_ae (t : Icc (0 : ℝ) T) :
    (A.field t : LiftDomain P → Vector3) =ᵐ[liftMeasure P] A.pointField t := by
  have h := representative_ae P (A.realization 3 t)
  rw [A.value_eq] at h
  exact h


-- @@ L48-49 verbatim
theorem pointField_joint_continuous : Continuous A.pointField.uncurry :=
  path_representative_joint_continuous P (A.realization 3)


-- @@ L51-56 verbatim
theorem pointField_unique (t : Icc (0 : ℝ) T) (g : LiftDomain P → Vector3)
    (hg : Continuous g)
    (ha : (A.field t : LiftDomain P → Vector3) =ᵐ[liftMeasure P] g) :
    A.pointField t = g :=
  Measure.eq_of_ae_eq ((A.pointField_ae t).symm.trans ha)
    (Continuous.uncurry_left t A.pointField_joint_continuous) hg


-- @@ L58-62 verbatim
theorem pointField_smooth (t : Icc (0 : ℝ) T) (x : LiftDomain P) :
    ContDiff ℝ ∞ (localFieldLift P (A.pointField t) x) := by
  obtain ⟨g,hg,ha⟩ := exists_smooth_representative P (A.field t) (fun q => A.spatialJet q t)
  rw [A.pointField_unique t g (smoothField_continuous P g hg) ha]
  exact hg x


-- @@ L64-67 verbatim
theorem restrict_realization {p q : ℕ} (h : q ≤ p) (t : Icc (0 : ℝ) T) :
    restrictOperator P h (A.realization p t) = A.realization q t := by
  apply value_injective P
  simp only [value_restrictOperator,A.value_eq]


-- @@ L69-72 verbatim
theorem pointField_eq_high (q : ℕ) (hq : 3 ≤ q) (t : Icc (0 : ℝ) T)
    (x : LiftDomain P) :
    A.pointField t x = pointEvaluation P x (restrictOperator P hq (A.realization q t)) :=
  congrArg (pointEvaluation P x) (A.restrict_realization hq t).symm


-- @@ L74-80 verbatim
theorem pointField_hasDerivWithinAt (B : EulerAllOrderCorrectionData.FieldTower P T)
    (hT : 0 ≤ T) (t : Icc (0 : ℝ) T)
    (hd : HasDerivWithinAt (extendPath T hT (A.realization 3))
      (B.realization 3 t) (Icc (0 : ℝ) T) t) (x : LiftDomain P) :
    HasDerivWithinAt (fun r => A.pointField (projIcc 0 T hT r) x)
      (B.pointField t x) (Icc (0 : ℝ) T) t :=
  (pointEvaluation P x).hasFDerivAt.comp_hasDerivWithinAt (t : ℝ) hd


-- @@ L82-82 verbatim
end EulerAllOrderCorrectionData.FieldTower
