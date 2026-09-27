/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketTimeData
public import LeanPool.NavierStokesAndEuler.Euler.CylinderSlowCurlTime
public import LeanPool.NavierStokesAndEuler.Euler.CylinderPotentialTime
public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketForcing
import LeanPool.NavierStokesAndEuler.Euler.TransversePacketProvider


-- @@ L15-16 verbatim
/-! The potential and slow curl of the actual transverse solution, with their genuine time
derivatives. -/


-- @@ L18-18 verbatim
@[expose] public section



-- @@ L21-21 verbatim
noncomputable section


-- @@ L23-23 verbatim
namespace EulerTransversePacketProvider


-- @@ L25-28 verbatim
open Set ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace EulerMeanCoefficients
  EulerLpCylinderTranslation EulerLpCylinderPaths EulerCylinderSmoothOrbit
      EulerSourcePotentialCoefficient
  EulerPacketProfileRecursion EulerVolterraConvolution EulerMetricTransport

-- @@ L29-29 verbatim
open scoped ContDiff BoundedContinuousFunction


-- @@ L31-31 verbatim
namespace Data


-- @@ L33-33 verbatim
variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] (D : Data U)


-- @@ L35-38 verbatim
/-- Cache the standard `NormedAddCommGroup (Space →L[ℝ] Space)` instance to shorten typeclass
synthesis. -/
local instance instTransversePacketCorrector1 : NormedAddCommGroup (Space →L[ℝ] Space) :=
    inferInstance

-- @@ L39-41 verbatim
/-- Cache the standard `NormedSpace ℝ (Space →L[ℝ] Space)` instance to shorten typeclass
synthesis. -/
local instance instTransversePacketCorrector2 : NormedSpace ℝ (Space →L[ℝ] Space) := inferInstance

-- @@ L42-44 verbatim
/-- Cache the standard `NormedAddCommGroup PotentialField` instance to shorten typeclass
synthesis. -/
local instance instTransversePacketCorrector3 : NormedAddCommGroup PotentialField := inferInstance

-- @@ L45-46 verbatim
/-- Cache the standard `NormedSpace ℝ PotentialField` instance to shorten typeclass synthesis. -/
local instance instTransversePacketCorrector4 : NormedSpace ℝ PotentialField := inferInstance

-- @@ L47-50 verbatim
/-- Cache the standard `NormedAddCommGroup C(Icc (0 : ℝ) D.T,PotentialField)` instance to
shorten typeclass synthesis. -/
local instance instTransversePacketCorrector5 : NormedAddCommGroup C(Icc (0 : ℝ)
    D.T,PotentialField) := inferInstance

-- @@ L51-54 verbatim
/-- Cache the standard `NormedSpace ℝ C(Icc (0 : ℝ) D.T,PotentialField)` instance to shorten
typeclass synthesis. -/
local instance instTransversePacketCorrector6 : NormedSpace ℝ C(Icc (0 : ℝ) D.T,PotentialField) :=
    inferInstance


-- @@ L56-59 verbatim
/-- Potential coefficient path: an abbreviation for `potentialCoefficient D.normal D.normalLower
D.normalLower_pos D.normal_lower`. -/
abbrev potentialCoefficientPath :=
  potentialCoefficient D.normal D.normalLower D.normalLower_pos D.normal_lower


-- @@ L61-63 verbatim
theorem potentialCoefficientPath_orbit :
    ContDiff ℝ ∞ (translateCoefficientPath D.potentialCoefficientPath) :=
  potentialCoefficient_translation_contDiff D.normal D.normalLower D.normalLower_pos D.normal_lower


-- @@ L65-70 verbatim
theorem potentialCoefficientPath_time (t : ℝ) (ht : t ∈ Icc (0 : ℝ) D.T) (x : Space) :
    HasDerivWithinAt (fun r => extendPath D.T D.T_pos.le D.potentialCoefficientPath r x)
      (extendPath D.T D.T_pos.le D.potentialDerivative t x) (Icc (0 : ℝ) D.T) t := by
  exact (D.potential_hasDerivWithinAt ⟨t, ht⟩ x).congr_deriv
    (congrArg (fun s : Icc (0 : ℝ) D.T => D.potentialDerivative s x)
      (projIcc_of_mem D.T_pos.le ht).symm)


-- @@ L72-72 verbatim
end Data


-- @@ L74-74 verbatim
namespace Forcing


-- @@ L76-78 verbatim
variable {P : ℝ} [Fact (0 < P)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} {raw : VectorField} (G : Forcing P D raw) (I : InitialData P D)


-- @@ L80-81 verbatim
/-- Cache the standard `NormedAddCommGroup (LiftL2 P)` instance to shorten typeclass synthesis. -/
local instance instTransversePacketCorrector7 : NormedAddCommGroup (LiftL2 P) := inferInstance

-- @@ L82-83 verbatim
/-- Cache the standard `NormedSpace ℝ (LiftL2 P)` instance to shorten typeclass synthesis. -/
local instance instTransversePacketCorrector8 : NormedSpace ℝ (LiftL2 P) := inferInstance

-- @@ L84-88 verbatim
/-- Cache the standard `NormedAddCommGroup (Supported P Space D.support D.support_measurable)`
instance to shorten typeclass synthesis. -/
local instance instTransversePacketCorrector9 : NormedAddCommGroup (Supported P Space D.support
    D.support_measurable) :=
    inferInstance

-- @@ L89-93 verbatim
/-- Cache the standard `NormedSpace ℝ (Supported P Space D.support D.support_measurable)`
instance to shorten typeclass synthesis. -/
local instance instTransversePacketCorrector10 : NormedSpace ℝ (Supported P Space D.support
    D.support_measurable) :=
    inferInstance

-- @@ L94-97 verbatim
/-- Cache the standard `NormedAddCommGroup C(Icc (0 : ℝ) D.T,LiftL2 P)` instance to shorten
typeclass synthesis. -/
local instance instTransversePacketCorrector11 : NormedAddCommGroup C(Icc (0 : ℝ) D.T,LiftL2 P) :=
    inferInstance

-- @@ L98-101 verbatim
/-- Cache the standard `NormedSpace ℝ C(Icc (0 : ℝ) D.T,LiftL2 P)` instance to shorten typeclass
synthesis. -/
local instance instTransversePacketCorrector12 : NormedSpace ℝ C(Icc (0 : ℝ) D.T,LiftL2 P) :=
    inferInstance


-- @@ L103-105 verbatim
/-- Full velocity path: an abbreviation for `includePath P D.support D.support_measurable
(G.velocityPath I)`. -/
abbrev fullVelocityPath := includePath P D.support D.support_measurable (G.velocityPath I)

-- @@ L106-108 verbatim
/-- Full derivative path: an abbreviation for `includePath P D.support D.support_measurable
(G.derivativePath I)`. -/
abbrev fullDerivativePath := includePath P D.support D.support_measurable (G.derivativePath I)


-- @@ L110-114 verbatim
theorem fullVelocityPath_time (t : Icc (0 : ℝ) D.T) :
    HasDerivWithinAt (extendPath D.T D.T_pos.le (G.fullVelocityPath I))
      (G.fullDerivativePath I t) (Icc (0 : ℝ) D.T) t :=
  (Supported P Space D.support D.support_measurable).subtypeL.hasFDerivAt.comp_hasDerivWithinAt
    (t : ℝ) (G.velocityPath_time I t)


-- @@ L116-119 verbatim
/-- Potential path, given by `EulerCylinderPotential.potentialPath P D.potentialCoefficientPath
(G.fullVelocityPath I)`. -/
def potentialPath : C(Icc (0 : ℝ) D.T,LiftL2 P) :=
  EulerCylinderPotential.potentialPath P D.potentialCoefficientPath (G.fullVelocityPath I)


-- @@ L121-124 verbatim
/-- Potential time path, constructed using `EulerCylinderPotential.potentialDerivative`. -/
def potentialTimePath : C(Icc (0 : ℝ) D.T,LiftL2 P) :=
  EulerCylinderPotential.potentialDerivative P D.T D.potentialCoefficientPath D.potentialDerivative
    (G.fullVelocityPath I) (G.fullDerivativePath I)


-- @@ L126-130 verbatim
theorem potentialPath_orbit :
    ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a (G.potentialPath I)) :=
  EulerCylinderPotential.potentialPath_orbit P D.potentialCoefficientPath
      D.potentialCoefficientPath_orbit
    (G.fullVelocityPath I) (G.velocityPath_orbit I)


-- @@ L132-138 verbatim
theorem potentialTimePath_orbit :
    ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a (G.potentialTimePath I)) :=
  EulerCylinderPotential.potentialDerivative_orbit P D.T D.potentialCoefficientPath
      D.potentialDerivative
    D.potentialCoefficientPath_orbit D.potentialDerivative_orbit
    (G.fullVelocityPath I) (G.fullDerivativePath I) (G.velocityPath_orbit I)
        (G.derivativePath_orbit I)


-- @@ L140-145 verbatim
theorem potentialPath_time (t : Icc (0 : ℝ) D.T) :
    HasDerivWithinAt (extendPath D.T D.T_pos.le (G.potentialPath I))
      (G.potentialTimePath I t) (Icc (0 : ℝ) D.T) t :=
  EulerCylinderPotential.potentialPath_hasDerivWithinAt P D.T D.T_pos.le
    D.potentialCoefficientPath D.potentialDerivative (G.fullVelocityPath I) (G.fullDerivativePath I)
    D.potentialCoefficientPath_time (G.fullVelocityPath_time I) t


-- @@ L147-149 verbatim
/-- Corrector path, given by `EulerCylinderSlowCurl.path P D.FInv.field (G.potentialPath I)`. -/
def correctorPath : C(Icc (0 : ℝ) D.T,LiftL2 P) :=
  EulerCylinderSlowCurl.path P D.FInv.field (G.potentialPath I)


-- @@ L151-155 verbatim
/-- Corrector time path, given by `EulerCylinderSlowCurl.derivative P D.T D.FInv.field
D.inverseDerivative (G.potentialPath I) (G.potentialTimePath I)`. -/
def correctorTimePath : C(Icc (0 : ℝ) D.T,LiftL2 P) :=
  EulerCylinderSlowCurl.derivative P D.T D.FInv.field D.inverseDerivative
    (G.potentialPath I) (G.potentialTimePath I)


-- @@ L157-160 verbatim
theorem correctorPath_orbit :
    ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a (G.correctorPath I)) :=
  EulerCylinderSlowCurl.path_orbit P D.FInv.field D.FInv.translation_contDiff
    (G.potentialPath I) (G.potentialPath_orbit I)


-- @@ L162-167 verbatim
theorem correctorTimePath_orbit :
    ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a (G.correctorTimePath I)) :=
  EulerCylinderSlowCurl.derivative_orbit P D.T D.FInv.field D.inverseDerivative
    D.FInv.translation_contDiff D.inverseDerivative_orbit (G.potentialPath I) (G.potentialTimePath
        I)
    (G.potentialPath_orbit I) (G.potentialTimePath_orbit I)


-- @@ L169-175 verbatim
theorem correctorPath_time (t : Icc (0 : ℝ) D.T) :
    HasDerivWithinAt (extendPath D.T D.T_pos.le (G.correctorPath I))
      (G.correctorTimePath I t) (Icc (0 : ℝ) D.T) t :=
  EulerCylinderSlowCurl.path_hasDerivWithinAt P D.T D.T_pos.le D.FInv.field D.inverseDerivative
    (G.potentialPath I) (G.potentialTimePath I) (G.potentialPath_orbit I)
        (G.potentialTimePath_orbit I)
    D.inverse_hasDerivWithinAt (G.potentialPath_time I) t


-- @@ L177-181 verbatim
/-- Corrector, defined pointwise by `pointField P (G.correctorPath I) (G.correctorPath_orbit I)
(D.clamp z.1) (z.2.1,(z.2.2 : AddCircle P))`. -/
def corrector : VectorField := fun z =>
  pointField P (G.correctorPath I) (G.correctorPath_orbit I)
    (D.clamp z.1) (z.2.1,(z.2.2 : AddCircle P))


-- @@ L183-187 verbatim
/-- Corrector derivative, defined pointwise by `pointField P (G.correctorTimePath I)
(G.correctorTimePath_orbit I) (D.clamp z.1) (z.2.1,(z.2.2 : AddCircle P))`. -/
def correctorDerivative : VectorField := fun z =>
  pointField P (G.correctorTimePath I) (G.correctorTimePath_orbit I)
    (D.clamp z.1) (z.2.1,(z.2.2 : AddCircle P))


-- @@ L189-196 verbatim
theorem corrector_hasDerivWithinAt (t : Icc (0 : ℝ) D.T) (x : Space) (θ : ℝ) :
    HasDerivWithinAt (fun r => G.corrector I (r,(x,θ)))
      (G.correctorDerivative I (t,(x,θ))) (Icc (0 : ℝ) D.T) t := by
  have h := pointField_hasDerivWithinAt P D.T D.T_pos.le (G.correctorPath I) (G.correctorTimePath I)
    (G.correctorPath_orbit I) (G.correctorTimePath_orbit I) (G.correctorPath_time I) t (x,(θ :
        AddCircle P))
  simpa only [corrector, correctorDerivative, Data.clamp, projIcc_of_mem D.T_pos.le t.property]
      using h


-- @@ L198-202 verbatim
theorem fullVelocityPath_mean_zero (t : Icc (0 : ℝ) D.T) (x : Space) :
    (∫ θ in (0 : ℝ)..P, pointField P (G.fullVelocityPath I) (G.velocityPath_orbit I)
      t (x,(θ : AddCircle P))) = 0 := by
  simpa only [vector, EulerSourceCylinderClassical.field, Data.clamp_coe] using G.vector_mean_zero
      I t x


-- @@ L204-212 verbatim
/-- This potential is exactly the manuscript's normalized angular integral of −m×A/|m|². -/
theorem potentialPath_eq_periodic (t : Icc (0 : ℝ) D.T) :
    pointField P (G.potentialPath I) (G.potentialPath_orbit I) t =
      EulerPacketPeriodicPotential.field P (fun x => D.normal.field t x)
        (pointField P (G.fullVelocityPath I) (G.velocityPath_orbit I) t) :=
  EulerCylinderPotential.potentialField_eq_periodic P D.potentialCoefficientPath
    D.potentialCoefficientPath_orbit (G.fullVelocityPath I) (G.velocityPath_orbit I)
    (G.fullVelocityPath_mean_zero I) (fun t x => D.normal.field t x)
    (potentialCoefficient_apply D.normal D.normalLower D.normalLower_pos D.normal_lower) t


-- @@ L214-225 verbatim
/-- The stored corrector is the literal slow curl with the actual inverse deformation. -/
theorem corrector_formula (t : Icc (0 : ℝ) D.T) (x : Space) (θ : ℝ) :
    G.corrector I (t,(x,θ)) =
      EulerMeanBoundary.curlMatrix
        ((EulerLiftedWeakDerivative.fieldFDeriv P
          (pointField P (G.potentialPath I) (G.potentialPath_orbit I) t) (x,(θ : AddCircle P))).comp
          ((ContinuousLinearMap.inl ℝ Space ℝ).comp (D.FInv.field t x))) := by
  change EulerCylinderSlowCurl.field P D.FInv.field D.FInv.translation_contDiff
    (G.potentialPath I) (G.potentialPath_orbit I) (D.clamp t) (x,(θ : AddCircle P)) = _
  rw [Data.clamp_coe]
  exact EulerCylinderSlowCurl.field_formula P D.FInv.field D.FInv.translation_contDiff
    (G.potentialPath I) (G.potentialPath_orbit I) t (x,(θ : AddCircle P))


-- @@ L227-227 verbatim
end Forcing

-- @@ L228-228 verbatim
end EulerTransversePacketProvider
