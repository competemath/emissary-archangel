/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CylinderDirichletTranslation
import LeanPool.NavierStokesAndEuler.Euler.CylinderDirichletNaturality
import LeanPool.NavierStokesAndEuler.Euler.FixedEvolutionRegularity


-- @@ L13-20 verbatim
/-!
# Actual mixed-translation smoothness of the cylinder history

The translated variational problems live on one fixed Hilbert space.
Smoothness follows from their genuine coercive inverses, and exact covariance
identifies that family with the translation orbit of the constructed field.
No regularity assumption is imposed on a solved history field.
-/


-- @@ L22-22 verbatim
@[expose] public section



-- @@ L25-25 verbatim
noncomputable section


-- @@ L27-27 verbatim
namespace EulerCylinderDirichlet.Coefficients


-- @@ L29-31 verbatim
open Set MeasureTheory ContinuousLinearMap InnerProductSpace EulerSmoothLimit
  EulerLiftedGradientSpace EulerLpCylinderTranslation EulerLpCylinderRectangular
  EulerTimeLp EulerTimeLpBoundedMap EulerVolterraConvolution EulerMeanCoefficients

-- @@ L32-32 verbatim
open scoped BoundedContinuousFunction ContDiff


-- @@ L34-37 verbatim
variable (P : ℝ) [Fact (0 < P)] {T : ℝ} {U E : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  (D : Coefficients T U E)


-- @@ L39-42 verbatim
/-- Cache the standard `NormedAddCommGroup (CylinderL2 P U)` instance to shorten typeclass
synthesis. -/
local instance instCylinderDirichletRegularity1 : NormedAddCommGroup (CylinderL2 P U) :=
    inferInstance

-- @@ L43-44 verbatim
/-- Cache the standard `NormedSpace ℝ (CylinderL2 P U)` instance to shorten typeclass synthesis. -/
local instance instCylinderDirichletRegularity2 : NormedSpace ℝ (CylinderL2 P U) := inferInstance

-- @@ L45-48 verbatim
/-- Cache the standard `NormedAddCommGroup (CylinderL2 P E)` instance to shorten typeclass
synthesis. -/
local instance instCylinderDirichletRegularity3 : NormedAddCommGroup (CylinderL2 P E) :=
    inferInstance

-- @@ L49-50 verbatim
/-- Cache the standard `NormedSpace ℝ (CylinderL2 P E)` instance to shorten typeclass synthesis. -/
local instance instCylinderDirichletRegularity4 : NormedSpace ℝ (CylinderL2 P E) := inferInstance

-- @@ L51-54 verbatim
/-- Cache the standard `NormedAddCommGroup (CylinderL2 P U →L[ℝ] CylinderL2 P E)` instance to
shorten typeclass synthesis. -/
local instance instCylinderDirichletRegularity5 : NormedAddCommGroup (CylinderL2 P U →L[ℝ]
    CylinderL2 P E) := inferInstance

-- @@ L55-58 verbatim
/-- Cache the standard `NormedSpace ℝ (CylinderL2 P U →L[ℝ] CylinderL2 P E)` instance to shorten
typeclass synthesis. -/
local instance instCylinderDirichletRegularity6 : NormedSpace ℝ (CylinderL2 P U →L[ℝ] CylinderL2 P
    E) := inferInstance

-- @@ L59-62 verbatim
/-- Cache the standard `NormedAddCommGroup (CylinderL2 P E →L[ℝ] CylinderL2 P E)` instance to
shorten typeclass synthesis. -/
local instance instCylinderDirichletRegularity7 : NormedAddCommGroup (CylinderL2 P E →L[ℝ]
    CylinderL2 P E) := inferInstance

-- @@ L63-66 verbatim
/-- Cache the standard `NormedSpace ℝ (CylinderL2 P E →L[ℝ] CylinderL2 P E)` instance to shorten
typeclass synthesis. -/
local instance instCylinderDirichletRegularity8 : NormedSpace ℝ (CylinderL2 P E →L[ℝ] CylinderL2 P
    E) := inferInstance

-- @@ L67-71 verbatim
/-- Cache the standard `NormedAddCommGroup C(Icc (0 : ℝ) T,CylinderL2 P U →L[ℝ] CylinderL2 P E)`
instance to shorten typeclass synthesis. -/
local instance instCylinderDirichletRegularity9 : NormedAddCommGroup C(Icc (0 : ℝ) T,CylinderL2 P U
    →L[ℝ] CylinderL2 P E) :=
    inferInstance

-- @@ L72-76 verbatim
/-- Cache the standard `NormedSpace ℝ C(Icc (0 : ℝ) T,CylinderL2 P U →L[ℝ] CylinderL2 P E)`
instance to shorten typeclass synthesis. -/
local instance instCylinderDirichletRegularity10 : NormedSpace ℝ C(Icc (0 : ℝ) T,CylinderL2 P U
    →L[ℝ] CylinderL2 P E) :=
    inferInstance

-- @@ L77-81 verbatim
/-- Cache the standard `NormedAddCommGroup C(Icc (0 : ℝ) T,CylinderL2 P E →L[ℝ] CylinderL2 P E)`
instance to shorten typeclass synthesis. -/
local instance instCylinderDirichletRegularity11 : NormedAddCommGroup C(Icc (0 : ℝ) T,CylinderL2 P
    E →L[ℝ] CylinderL2 P E) :=
    inferInstance

-- @@ L82-86 verbatim
/-- Cache the standard `NormedSpace ℝ C(Icc (0 : ℝ) T,CylinderL2 P E →L[ℝ] CylinderL2 P E)`
instance to shorten typeclass synthesis. -/
local instance instCylinderDirichletRegularity12 : NormedSpace ℝ C(Icc (0 : ℝ) T,CylinderL2 P E
    →L[ℝ] CylinderL2 P E) :=
    inferInstance


-- @@ L88-92 verbatim
omit [CompleteSpace U] [CompleteSpace E] in
theorem frameOrbit_contDiff (hQ : ContDiff ℝ ∞ (translateCoefficientPath D.Q)) :
    ContDiff ℝ ∞ (fun a : LiftTangent => (D.shifted a.1).frame P) :=
  (fullPathMap (K := Icc (0 : ℝ) T) (E := U) (F := E) P).contDiff.comp
    (hQ.comp contDiff_fst)


-- @@ L94-98 verbatim
omit [CompleteSpace U] [CompleteSpace E] in
theorem frameDerivativeOrbit_contDiff (hQ₁ : ContDiff ℝ ∞ (translateCoefficientPath D.Q₁)) :
    ContDiff ℝ ∞ (fun a : LiftTangent => (D.shifted a.1).frameDerivative P) :=
  (fullPathMap (K := Icc (0 : ℝ) T) (E := U) (F := E) P).contDiff.comp
    (hQ₁.comp contDiff_fst)


-- @@ L100-104 verbatim
omit [CompleteSpace U] [CompleteSpace E] in
theorem hessianOrbit_contDiff (hH : ContDiff ℝ ∞ (translateCoefficientPath D.H)) :
    ContDiff ℝ ∞ (fun a : LiftTangent => (D.shifted a.1).hessian P) :=
  (fullPathMap (K := Icc (0 : ℝ) T) (E := E) (F := E) P).contDiff.comp
    (hH.comp contDiff_fst)


-- @@ L106-112 verbatim
theorem accelerationLp_translation (a : LiftTangent) (f : TimeLp T (CylinderL2 P E)) :
    (D.shifted a.1).accelerationLp P (timeLift T (translate P a).toContinuousLinearMap f) =
      timeLift T (translate P a).toContinuousLinearMap (D.accelerationLp P f) :=
  D.accelerationLp_intertwines P (D.shifted a.1)
    (translate P a).toContinuousLinearMap (translate P a).toContinuousLinearMap
    (D.shifted_frame P a) (D.shifted_frameDerivative P a)
    (D.shifted_frame_back P a) (D.shifted_frameDerivative_back P a) (D.shifted_hessian P a) f


-- @@ L114-116 verbatim
variable (hQ : ContDiff ℝ ∞ (translateCoefficientPath D.Q))
  (hQ₁ : ContDiff ℝ ∞ (translateCoefficientPath D.Q₁))
  (hH : ContDiff ℝ ∞ (translateCoefficientPath D.H))


-- @@ L118-118 verbatim
include hQ hQ₁ hH


-- @@ L120-140 verbatim
theorem velocityLp_orbit_contDiff (f : TimeLp T (CylinderL2 P E))
    (hf : ContDiff ℝ ∞ (fun a => timeLift T (translate P a).toContinuousLinearMap f)) :
    ContDiff ℝ ∞ (fun a => timeLift T (translate P a).toContinuousLinearMap (D.velocityLp P f)) :=
        by
  let g : LiftTangent → TimeLp T (CylinderL2 P E) :=
    fun a => timeLift T (translate P a).toContinuousLinearMap f
  change ContDiff ℝ ∞ g at hf
  have hs := EulerTransverseFixedEvolution.velocityLp_contDiff
    (X := LiftTangent) (U := CylinderL2 P U) (E := CylinderL2 P E) (n := ∞) T D.time_pos.le
    (fun a : LiftTangent => (D.shifted a.1).frame P)
    (fun a : LiftTangent => (D.shifted a.1).frameDerivative P)
    (fun a : LiftTangent => (D.shifted a.1).hessian P)
    D.lower D.lower_pos (fun a => (D.shifted a.1).frame_lower P)
    (fun a => (D.shifted a.1).frame_derivative P)
    D.potential D.potential_nonneg (fun a => (D.shifted a.1).hessian_upper P) D.small
    (D.frameOrbit_contDiff P hQ) (D.frameDerivativeOrbit_contDiff P hQ₁) (D.hessianOrbit_contDiff P
        hH)
    g hf
  convert hs using 1
  funext a
  exact (D.velocityLp_translation P a f).symm


-- @@ L142-162 verbatim
theorem accelerationLp_orbit_contDiff (f : TimeLp T (CylinderL2 P E))
    (hf : ContDiff ℝ ∞ (fun a => timeLift T (translate P a).toContinuousLinearMap f)) :
    ContDiff ℝ ∞ (fun a => timeLift T (translate P a).toContinuousLinearMap (D.accelerationLp P f))
        := by
  let g : LiftTangent → TimeLp T (CylinderL2 P E) :=
    fun a => timeLift T (translate P a).toContinuousLinearMap f
  change ContDiff ℝ ∞ g at hf
  have hs := EulerTransverseFixedEvolution.accelerationLp_contDiff
    (X := LiftTangent) (U := CylinderL2 P U) (E := CylinderL2 P E) (n := ∞) T D.time_pos.le
    (fun a : LiftTangent => (D.shifted a.1).frame P)
    (fun a : LiftTangent => (D.shifted a.1).frameDerivative P)
    (fun a : LiftTangent => (D.shifted a.1).hessian P)
    D.lower D.lower_pos (fun a => (D.shifted a.1).frame_lower P)
    (fun a => (D.shifted a.1).frame_derivative P)
    D.potential D.potential_nonneg (fun a => (D.shifted a.1).hessian_upper P) D.small
    (D.frameOrbit_contDiff P hQ) (D.frameDerivativeOrbit_contDiff P hQ₁) (D.hessianOrbit_contDiff P
        hH)
    g hf
  convert hs using 1
  funext a
  exact (D.accelerationLp_translation P a f).symm


-- @@ L164-181 verbatim
theorem velocityPath_orbit_contDiff (f : C(Icc (0 : ℝ) T, CylinderL2 P E))
    (hf : ContDiff ℝ ∞ (fun a => pathTranslate P a f)) :
    ContDiff ℝ ∞ (fun a => pathTranslate P a (D.velocityPath P (pathLp T D.time_pos.le f))) := by
  have hs := EulerTransverseFixedEvolution.continuousVelocity_contDiff T D.time_pos.le
    (fun a : LiftTangent => (D.shifted a.1).frame P)
    (fun a : LiftTangent => (D.shifted a.1).frameDerivative P)
    (fun a : LiftTangent => (D.shifted a.1).hessian P)
    D.lower D.lower_pos (fun a => (D.shifted a.1).frame_lower P)
    (fun a => (D.shifted a.1).frame_derivative P)
    D.potential D.potential_nonneg (fun a => (D.shifted a.1).hessian_upper P) D.small
    (D.frameOrbit_contDiff P hQ) (D.frameDerivativeOrbit_contDiff P hQ₁) (D.hessianOrbit_contDiff P
        hH)
    (fun a => pathTranslate P a f) hf
  convert hs using 1
  funext a
  apply ContinuousMap.ext
  intro t
  exact (D.continuousVelocity_translation P a f t).symm


-- @@ L183-200 verbatim
theorem accelerationPath_orbit_contDiff (f : C(Icc (0 : ℝ) T, CylinderL2 P E))
    (hf : ContDiff ℝ ∞ (fun a => pathTranslate P a f)) :
    ContDiff ℝ ∞ (fun a => pathTranslate P a (D.accelerationPath P f)) := by
  have hs := EulerTransverseFixedEvolution.classicalAcceleration_contDiff T D.time_pos.le
    (fun a : LiftTangent => (D.shifted a.1).frame P)
    (fun a : LiftTangent => (D.shifted a.1).frameDerivative P)
    (fun a : LiftTangent => (D.shifted a.1).hessian P)
    D.lower D.lower_pos (fun a => (D.shifted a.1).frame_lower P)
    (fun a => (D.shifted a.1).frame_derivative P)
    D.potential D.potential_nonneg (fun a => (D.shifted a.1).hessian_upper P) D.small
    (D.frameOrbit_contDiff P hQ) (D.frameDerivativeOrbit_contDiff P hQ₁) (D.hessianOrbit_contDiff P
        hH)
    (fun a => pathTranslate P a f) hf
  convert hs using 1
  funext a
  apply ContinuousMap.ext
  intro t
  exact (D.accelerationPath_translation P a f t).symm


-- @@ L202-219 verbatim
theorem physicalVelocity_orbit_contDiff (f : C(Icc (0 : ℝ) T, CylinderL2 P E))
    (hf : ContDiff ℝ ∞ (fun a => pathTranslate P a f)) :
    ContDiff ℝ ∞ (fun a => pathTranslate P a (D.physicalVelocity P f)) := by
  have hs := EulerTransverseFixedEvolution.physicalVelocity_contDiff T D.time_pos.le
    (fun a : LiftTangent => (D.shifted a.1).frame P)
    (fun a : LiftTangent => (D.shifted a.1).frameDerivative P)
    (fun a : LiftTangent => (D.shifted a.1).hessian P)
    D.lower D.lower_pos (fun a => (D.shifted a.1).frame_lower P)
    (fun a => (D.shifted a.1).frame_derivative P)
    D.potential D.potential_nonneg (fun a => (D.shifted a.1).hessian_upper P) D.small
    (D.frameOrbit_contDiff P hQ) (D.frameDerivativeOrbit_contDiff P hQ₁) (D.hessianOrbit_contDiff P
        hH)
    (fun a => pathTranslate P a f) hf
  convert hs using 1
  funext a
  apply ContinuousMap.ext
  intro t
  exact (D.physicalVelocity_translation P a f t).symm


-- @@ L221-238 verbatim
theorem physicalDerivative_orbit_contDiff (f : C(Icc (0 : ℝ) T, CylinderL2 P E))
    (hf : ContDiff ℝ ∞ (fun a => pathTranslate P a f)) :
    ContDiff ℝ ∞ (fun a => pathTranslate P a (D.physicalDerivative P f)) := by
  have hs := EulerTransverseFixedEvolution.physicalDerivative_contDiff T D.time_pos.le
    (fun a : LiftTangent => (D.shifted a.1).frame P)
    (fun a : LiftTangent => (D.shifted a.1).frameDerivative P)
    (fun a : LiftTangent => (D.shifted a.1).hessian P)
    D.lower D.lower_pos (fun a => (D.shifted a.1).frame_lower P)
    (fun a => (D.shifted a.1).frame_derivative P)
    D.potential D.potential_nonneg (fun a => (D.shifted a.1).hessian_upper P) D.small
    (D.frameOrbit_contDiff P hQ) (D.frameDerivativeOrbit_contDiff P hQ₁) (D.hessianOrbit_contDiff P
        hH)
    (fun a => pathTranslate P a f) hf
  convert hs using 1
  funext a
  apply ContinuousMap.ext
  intro t
  exact (D.physicalDerivative_translation P a f t).symm


-- @@ L240-240 verbatim
end EulerCylinderDirichlet.Coefficients
