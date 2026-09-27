/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.CylinderPotentialPath
import LeanPool.NavierStokesAndEuler.Euler.LpCylinderFullTime
public import LeanPool.NavierStokesAndEuler.Euler.CylinderTimeRegularity
public import LeanPool.NavierStokesAndEuler.Euler.PacketPiolaPair
import LeanPool.NavierStokesAndEuler.Euler.CylinderTimeGradient
import LeanPool.NavierStokesAndEuler.Euler.PacketPotentialRegularity


-- @@ L15-15 verbatim
/-! Genuine time derivatives of the constructed vector potential and its slow curl. -/


-- @@ L17-17 verbatim
section


-- @@ L19-19 verbatim
/-! Actual one-sided time differentiation of the packet's spatial curl corrector. -/


-- @@ L21-21 verbatim
@[expose] public section


-- @@ L23-23 verbatim
noncomputable section


-- @@ L25-25 verbatim
namespace EulerPacketPiola


-- @@ L27-29 verbatim
open Set MeasureTheory ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace
  EulerMetricTransport EulerTransportDerivatives EulerCylinderSmoothOrbit
  EulerLpCylinderTranslation EulerVolterraConvolution EulerLiftedWeakDerivative EulerMeanBoundary

-- @@ L30-30 verbatim
open scoped ContDiff


-- @@ L32-36 verbatim
variable (P : ℝ) [Fact (0 < P)]
  (T : ℝ) (hT : 0 ≤ T) (p f : C(Icc (0 : ℝ) T, LiftL2 P))
  (hp : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a p))
  (hf : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a f))
  (hd : ∀ t : Icc (0 : ℝ) T, HasDerivWithinAt (extendPath T hT p) (f t) (Icc (0 : ℝ) T) t)


-- @@ L38-38 verbatim
include hd


-- @@ L40-60 verbatim
/-- The two product-rule terms are derived from the genuine L² evolution and actual inverse frame
derivative. -/
theorem matrixSlowCurl_hasDerivWithinAt (t : Icc (0 : ℝ) T) (x : LiftDomain P)
    (G : ℝ → Space →L[ℝ] Space) (G₁ : Space →L[ℝ] Space)
    (hG : HasDerivWithinAt G G₁ (Icc (0 : ℝ) T) t) :
    HasDerivWithinAt
      (fun r => curlMatrix ((fieldFDeriv P (pointField P p hp (projIcc 0 T hT r)) x).comp
        ((ContinuousLinearMap.inl ℝ Space ℝ).comp (G r))))
      (curlMatrix ((fieldFDeriv P (pointField P f hf t) x).comp
          ((ContinuousLinearMap.inl ℝ Space ℝ).comp (G t))) +
        curlMatrix ((fieldFDeriv P (pointField P p hp t) x).comp
          ((ContinuousLinearMap.inl ℝ Space ℝ).comp G₁)))
      (Icc (0 : ℝ) T) t := by
  have hL : HasDerivWithinAt (fun r => (ContinuousLinearMap.inl ℝ Space ℝ).comp (G r))
      ((ContinuousLinearMap.inl ℝ Space ℝ).comp G₁) (Icc (0 : ℝ) T) t := by
    have h := ((hasDerivAt_const (t : ℝ) (ContinuousLinearMap.inl ℝ Space
        ℝ)).hasDerivWithinAt).clm_comp hG
    simpa only [ContinuousLinearMap.zero_comp, zero_add] using h
  have hD := pointField_fderiv_hasDerivWithinAt P T hT p f hp hf hd t x
  have h := curlOperator.hasFDerivAt.comp_hasDerivWithinAt (t : ℝ) (hD.clm_comp hL)
  simpa only [Function.comp_def, map_add, curlOperator_apply, projIcc_of_mem hT t.property] using h


-- @@ L62-75 verbatim
/-- This is the literal lifted curl in the Piola packet construction, including both time endpoints.
-/
theorem liftedSlowCurl_hasDerivWithinAt (t : Icc (0 : ℝ) T) (x : LiftDomain P)
    (F : ℝ → Space → Space ≃L[ℝ] Space) (G₁ : Space →L[ℝ] Space)
    (hG : HasDerivWithinAt (fun r => (F r x.1).symm.toContinuousLinearMap) G₁
      (Icc (0 : ℝ) T) t) :
    HasDerivWithinAt
      (fun r => liftedSlowCurl P (F r) (pointField P p hp (projIcc 0 T hT r)) x)
      (liftedSlowCurl P (F t) (pointField P f hf t) x +
        curlMatrix ((fieldFDeriv P (pointField P p hp t) x).comp
          ((ContinuousLinearMap.inl ℝ Space ℝ).comp G₁)))
      (Icc (0 : ℝ) T) t :=
  matrixSlowCurl_hasDerivWithinAt P T hT p f hp hf hd t x
    (fun r => (F r x.1).symm.toContinuousLinearMap) G₁ hG


-- @@ L77-77 verbatim
end EulerPacketPiola


-- @@ L79-79 verbatim
end

-- @@ L80-80 verbatim
end


-- @@ L82-82 verbatim
end


-- @@ L84-84 verbatim
@[expose] public section


-- @@ L86-86 verbatim
noncomputable section


-- @@ L88-88 verbatim
namespace EulerCylinderPotential


-- @@ L90-93 verbatim
open Set MeasureTheory ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace
  EulerMetricTransport EulerLiftedWeakDerivative EulerCylinderSmoothOrbit
  EulerLpCylinderTranslation EulerLpCylinderRectangular EulerCylinderAnglePrimitive
  EulerMeanCoefficients EulerVolterraConvolution EulerMeanBoundary EulerPacketPiola

-- @@ L94-94 verbatim
open scoped ContDiff BoundedContinuousFunction


-- @@ L96-102 verbatim
variable (P : ℝ) [Fact (0 < P)] (T : ℝ) (hT : 0 ≤ T)
  (B B₁ : C(Icc (0 : ℝ) T, Space →ᵇ Space →L[ℝ] Space))
  (hB : ContDiff ℝ ∞ (translateCoefficientPath B))
  (hB₁ : ContDiff ℝ ∞ (translateCoefficientPath B₁))
  (p f : C(Icc (0 : ℝ) T, LiftL2 P))
  (hp : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a p))
  (hf : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a f))


-- @@ L104-106 verbatim
/-- Potential derivative, given by `potentialPath P B₁ p + potentialPath P B f`. -/
def potentialDerivative : C(Icc (0 : ℝ) T,LiftL2 P) :=
  potentialPath P B₁ p + potentialPath P B f


-- @@ L108-112 verbatim
include hB hB₁ hp hf in
theorem potentialDerivative_orbit :
    ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a (potentialDerivative P T B B₁ p f)) := by
  simp only [potentialDerivative, map_add]
  exact (potentialPath_orbit P B₁ hB₁ p hp).add (potentialPath_orbit P B hB f hf)


-- @@ L114-116 verbatim
/-- Cache the standard `NormedAddCommGroup (Space →L[ℝ] Space)` instance to shorten typeclass
synthesis. -/
local instance instCylinderPotentialTime1 : NormedAddCommGroup (Space →L[ℝ] Space) := inferInstance

-- @@ L117-119 verbatim
/-- Cache the standard `NormedSpace ℝ (Space →L[ℝ] Space)` instance to shorten typeclass
synthesis. -/
local instance instCylinderPotentialTime2 : NormedSpace ℝ (Space →L[ℝ] Space) := inferInstance

-- @@ L120-123 verbatim
/-- Cache the standard `NormedAddCommGroup (Space →ᵇ Space →L[ℝ] Space)` instance to shorten
typeclass synthesis. -/
local instance instCylinderPotentialTime3 : NormedAddCommGroup (Space →ᵇ Space →L[ℝ] Space) :=
    inferInstance

-- @@ L124-127 verbatim
/-- Cache the standard `NormedSpace ℝ (Space →ᵇ Space →L[ℝ] Space)` instance to shorten
typeclass synthesis. -/
local instance instCylinderPotentialTime4 : NormedSpace ℝ (Space →ᵇ Space →L[ℝ] Space) :=
    inferInstance


-- @@ L129-133 verbatim
variable
  (hBt : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : Space,
    HasDerivWithinAt (fun s => extendPath T hT B s x)
      (extendPath T hT B₁ t x) (Icc (0 : ℝ) T) t)
  (hd : ∀ t : Icc (0 : ℝ) T, HasDerivWithinAt (extendPath T hT p) (f t) (Icc (0 : ℝ) T) t)


-- @@ L135-135 verbatim
include hBt hd


-- @@ L137-141 verbatim
theorem potentialPath_hasDerivWithinAt (t : Icc (0 : ℝ) T) :
    HasDerivWithinAt (extendPath T hT (potentialPath P B p))
      (potentialDerivative P T B B₁ p f t) (Icc (0 : ℝ) T) t :=
  fullProduct_hasDerivWithinAt P T hT B B₁ hBt (pathPrimitive P p) (pathPrimitive P f)
    (pathPrimitive_time_derivative P T hT p f hd) t


-- @@ L143-149 verbatim
theorem potentialField_hasDerivWithinAt (t : Icc (0 : ℝ) T) (x : LiftDomain P) :
    HasDerivWithinAt (fun r => potentialField P B hB p hp (projIcc 0 T hT r) x)
      (pointField P (potentialDerivative P T B B₁ p f)
        (potentialDerivative_orbit P T B B₁ hB hB₁ p f hp hf) t x) (Icc (0 : ℝ) T) t :=
  pointField_hasDerivWithinAt P T hT (potentialPath P B p) (potentialDerivative P T B B₁ p f)
    (potentialPath_orbit P B hB p hp) (potentialDerivative_orbit P T B B₁ hB hB₁ p f hp hf)
    (potentialPath_hasDerivWithinAt P T hT B B₁ p f hBt hd) t x


-- @@ L151-167 verbatim
/-- The actual curl derivative is obtained from the constructed potential, not assumed as a profile
jet. -/
theorem potentialCurl_hasDerivWithinAt (t : Icc (0 : ℝ) T) (x : LiftDomain P)
    (F : ℝ → Space → Space ≃L[ℝ] Space) (G₁ : Space →L[ℝ] Space)
    (hG : HasDerivWithinAt (fun r => (F r x.1).symm.toContinuousLinearMap) G₁
      (Icc (0 : ℝ) T) t) :
    HasDerivWithinAt
      (fun r => liftedSlowCurl P (F r) (potentialField P B hB p hp (projIcc 0 T hT r)) x)
      (liftedSlowCurl P (F t)
          (pointField P (potentialDerivative P T B B₁ p f)
            (potentialDerivative_orbit P T B B₁ hB hB₁ p f hp hf) t) x +
        curlMatrix ((fieldFDeriv P (potentialField P B hB p hp t) x).comp
          ((ContinuousLinearMap.inl ℝ Space ℝ).comp G₁)))
      (Icc (0 : ℝ) T) t :=
  liftedSlowCurl_hasDerivWithinAt P T hT (potentialPath P B p) (potentialDerivative P T B B₁ p f)
    (potentialPath_orbit P B hB p hp) (potentialDerivative_orbit P T B B₁ hB hB₁ p f hp hf)
    (potentialPath_hasDerivWithinAt P T hT B B₁ p f hBt hd) t x F G₁ hG


-- @@ L169-169 verbatim
end EulerCylinderPotential
