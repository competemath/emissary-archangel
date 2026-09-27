/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderFieldProducts
public import LeanPool.NavierStokesAndEuler.Euler.BoundedFieldCalculus


-- @@ L12-12 verbatim
/-! Actual bounded coefficient paths identified with the raw packet coefficients. -/


-- @@ L14-14 verbatim
@[expose] public section



-- @@ L17-17 verbatim
noncomputable section


-- @@ L19-19 verbatim
namespace EulerPacketCylinderField


-- @@ L21-22 verbatim
open Set ContinuousLinearMap EulerSmoothLimit EulerMeanCoefficients EulerBoundedFieldCalculus
  EulerPacketPointJets EulerPacketProfileRecursion

-- @@ L23-23 verbatim
open scoped ContDiff BoundedContinuousFunction


-- @@ L25-28 verbatim
/-- Cache the standard `NormedAddCommGroup (Space →L[ℝ] Space)` instance to shorten typeclass
synthesis. -/
local instance instPacketCylinderCoefficientData1 : NormedAddCommGroup (Space →L[ℝ] Space) :=
    inferInstance

-- @@ L29-32 verbatim
/-- Cache the standard `NormedSpace ℝ (Space →L[ℝ] Space)` instance to shorten typeclass
synthesis. -/
local instance instPacketCylinderCoefficientData2 : NormedSpace ℝ (Space →L[ℝ] Space) :=
    inferInstance

-- @@ L33-36 verbatim
/-- Cache the standard `NormedAddCommGroup (Space →ᵇ Space →L[ℝ] Space)` instance to shorten
typeclass synthesis. -/
local instance instPacketCylinderCoefficientData3 : NormedAddCommGroup (Space →ᵇ Space →L[ℝ] Space)
    := inferInstance

-- @@ L37-40 verbatim
/-- Cache the standard `NormedSpace ℝ (Space →ᵇ Space →L[ℝ] Space)` instance to shorten
typeclass synthesis. -/
local instance instPacketCylinderCoefficientData4 : NormedSpace ℝ (Space →ᵇ Space →L[ℝ] Space) :=
    inferInstance


-- @@ L42-48 verbatim
/-- Matrix coefficient data, collecting `path`, `orbit`, `raw_eq`. -/
structure MatrixCoefficient (T : ℝ) (raw : Domain → Space →L[ℝ] Space) where
  /-- Time-dependent path of `MatrixCoefficient`, of type `C(Icc (0 : ℝ) T,Space →ᵇ Space →L[ℝ]
  Space)`. -/
  path : C(Icc (0 : ℝ) T,Space →ᵇ Space →L[ℝ] Space)
  orbit : ContDiff ℝ ∞ (translateCoefficientPath path)
  raw_eq : ∀ (t : Icc (0 : ℝ) T) x θ, raw (t,(x,θ)) = path t x


-- @@ L50-55 verbatim
/-- Vector coefficient data, collecting `path`, `orbit`, `raw_eq`. -/
structure VectorCoefficient (T : ℝ) (raw : VectorField) where
  /-- Time-dependent path of `VectorCoefficient`, of type `C(Icc (0 : ℝ) T,Space →ᵇ Space)`. -/
  path : C(Icc (0 : ℝ) T,Space →ᵇ Space)
  orbit : ContDiff ℝ ∞ (translateCoefficientPath path)
  raw_eq : ∀ (t : Icc (0 : ℝ) T) x θ, raw (t,(x,θ)) = path t x


-- @@ L57-57 verbatim
namespace MatrixCoefficient


-- @@ L59-59 verbatim
variable {P T : ℝ} [Fact (0 < P)] {coef : Domain → Space →L[ℝ] Space} {raw : VectorField}


-- @@ L61-64 verbatim
/-- Multiply, given by `G.multiply A.path A.orbit coef A.raw_eq`. -/
def multiply (A : MatrixCoefficient T coef) (G : Field P T raw) :
    Field P T (fun z => coef z (raw z)) :=
  G.multiply A.path A.orbit coef A.raw_eq


-- @@ L66-84 verbatim
/-- Adjoint, bundling `path`, `orbit`, `translateCoefficientPath`, `exact` and the required
compatibility proofs. -/
def adjoint (A : MatrixCoefficient T coef) :
    MatrixCoefficient T (fun z => (coef z).adjoint) where
  path := pathAdjointMap A.path
  orbit := by
    have he : translateCoefficientPath (pathAdjointMap A.path) =
        (pathAdjointMap (α := Space) (K := Icc (0 : ℝ) T) (U := Space) (E := Space)) ∘
          translateCoefficientPath A.path := by
      funext a
      apply ContinuousMap.ext
      intro t
      apply BoundedContinuousFunction.ext
      intro x
      rfl
    rw [he]
    exact (pathAdjointMap (α := Space) (K := Icc (0 : ℝ) T) (U := Space) (E :=
        Space)).contDiff.comp A.orbit
  raw_eq t x θ := by rw [A.raw_eq]; rfl


-- @@ L86-86 verbatim
end MatrixCoefficient


-- @@ L88-97 verbatim
/-- This data is only regularity and literal identification of the three source coefficients. -/
structure CoefficientData (P T : ℝ) (O : Operators) where
  period_eq : O.period = P
  interval_eq : O.interval = Icc (0 : ℝ) T
  /-- Inverse of `CoefficientData`, of type `MatrixCoefficient T O.inverseFrame`. -/
  inverse : MatrixCoefficient T O.inverseFrame
  /-- Strain of `CoefficientData`, of type `MatrixCoefficient T O.strain`. -/
  strain : MatrixCoefficient T O.strain
  /-- Normal of `CoefficientData`, of type `VectorCoefficient T O.normal`. -/
  normal : VectorCoefficient T O.normal


-- @@ L99-99 verbatim
end EulerPacketCylinderField
