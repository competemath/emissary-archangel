/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.SourceCylinderPressureField
public import LeanPool.NavierStokesAndEuler.Euler.SourceNormalResidualBounds
public import LeanPool.NavierStokesAndEuler.Euler.SourceCylinderForwardSobolev
import LeanPool.NavierStokesAndEuler.Euler.LpCylinderTimeWeight
import LeanPool.NavierStokesAndEuler.Euler.SourceCylinderWeight


-- @@ L15-20 verbatim
/-!
# The pressure estimate is for the actual normalized PDE pressure

All identities are algebraic identities of genuine continuous L² paths.
They use no derivative, extremum, or reciprocal bound for the time profile.
-/


-- @@ L22-22 verbatim
@[expose] public section



-- @@ L25-25 verbatim
noncomputable section


-- @@ L27-27 verbatim
namespace EulerSourceNormalResidualBounds


-- @@ L29-31 verbatim
open Set ContinuousLinearMap EulerSmoothLimit EulerMeanCoefficients
  EulerLiftedGradientSpace EulerLpCylinderTranslation EulerLpCylinderRectangular
  EulerSourceNormalCoefficient EulerCylinderScalarPrimitive EulerContinuousTimeWeight

-- @@ L32-32 verbatim
open scoped BoundedContinuousFunction


-- @@ L34-38 verbatim
variable (P : ℝ) [Fact (0 < P)]
  {K : Type*} [TopologicalSpace K] [CompactSpace K]
  (M : SmoothCoefficientPath K (Space →L[ℝ] Space)) (m : SmoothCoefficientPath K Space)
  (cm : ℝ) (hcm : 0 < cm) (hm : ∀ t x, cm ≤ ‖m.field t x‖ ^ 2)
  (g : C(K, ℝ)) (f v : C(K, CylinderL2 P Space))


-- @@ L40-50 verbatim
theorem sourceResidual_weight :
    sourceResidual P M m cm hcm hm (weight g f) (weight g v) =
      weight g (sourceResidual P M m cm hcm hm f v) := by
  apply ContinuousMap.ext
  intro t
  change fullOperatorMap P (normalFunctional m cm hcm hm t)
      (g t • f t - (2 : ℝ) • fullOperatorMap P (M.field t) (g t • v t)) =
    g t • fullOperatorMap P (normalFunctional m cm hcm hm t)
      (f t - (2 : ℝ) • fullOperatorMap P (M.field t) (v t))
  simp only [map_sub, map_smul, smul_sub, smul_smul]
  rw [mul_comm (2 : ℝ) (g t)]


-- @@ L52-59 verbatim
theorem sourcePressure_weight :
    sourcePressure P M m cm hcm hm (weight g f) (weight g v) =
      weight g (sourcePressure P M m cm hcm hm f v) := by
  unfold sourcePressure
  rw [sourceResidual_weight]
  apply ContinuousMap.ext
  intro t
  exact (primitive P).map_smul (g t) (sourceResidual P M m cm hcm hm f v t)


-- @@ L61-61 verbatim
end EulerSourceNormalResidualBounds


-- @@ L63-63 verbatim
namespace EulerSourceCylinderEquation


-- @@ L65-68 verbatim
open Set ContinuousLinearMap EulerSmoothLimit EulerMeanCoefficients
  EulerLiftedGradientSpace EulerLpCylinderTranslation EulerLpCylinderPaths
  EulerLpCylinderRectangular EulerSourceCylinderForwardSobolev
  EulerSourceNormalResidualBounds EulerContinuousTimeWeight

-- @@ L69-69 verbatim
open scoped BoundedContinuousFunction


-- @@ L71-79 verbatim
variable (P : ℝ) [Fact (0 < P)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (S : Set Space) (hS : MeasurableSet S) (T : ℝ) (hT : 0 ≤ T)
  (Q Q₁ : SmoothCoefficientPath (Icc (0 : ℝ) T) (U →L[ℝ] Space))
  (c : ℝ) (hc : 0 < c) (hQ : ∀ t x v, c * ‖v‖ ^ 2 ≤ ‖Q.field t x v‖ ^ 2)
  (f : C(Icc (0 : ℝ) T, Supported P Space S hS)) (a₀ : Supported P U S hS)
  (M : SmoothCoefficientPath (Icc (0 : ℝ) T) (Space →L[ℝ] Space))
  (m : SmoothCoefficientPath (Icc (0 : ℝ) T) Space)
  (cm : ℝ) (hcm : 0 < cm) (hm : ∀ t x, cm ≤ ‖m.field t x‖ ^ 2)


-- @@ L81-85 verbatim
/-- The bounded pressure used in the coefficient estimate is exactly the PDE pressure. -/
theorem pressurePath_eq_sourcePressure :
    pressurePath P S hS T hT Q Q₁ c hc hQ f a₀ M m cm hcm hm =
      sourcePressure P M m cm hcm hm (includePath P S hS f)
        (includePath P S hS (velocity P S hS T hT Q Q₁ c hc hQ f a₀)) := rfl


-- @@ L87-87 verbatim
variable (g : C(Icc (0 : ℝ) T, ℝ)) (hg : ∀ t, 0 < g t)


-- @@ L89-93 verbatim
/-- The actual pressure path divided by g, written in terms of the normalized
physical forcing and the already constructed normalized physical velocity. -/
def normalizedPressure : C(Icc (0 : ℝ) T,CylinderL2 P ℝ) :=
  sourcePressure P M m cm hcm hm (includePath P S hS f)
    (includePath P S hS (normalizedVelocity P T hT S hS Q Q₁ c hc hQ g hg f a₀))


-- @@ L95-99 verbatim
theorem pressurePath_weight_eq :
    pressurePath P S hS T hT Q Q₁ c hc hQ (weight g f) a₀ M m cm hcm hm =
      weight g (normalizedPressure P S hS T hT Q Q₁ c hc hQ f a₀ M m cm hcm hm g hg) := by
  rw [pressurePath_eq_sourcePressure, velocity_weight_eq, include_weight, include_weight]
  exact sourcePressure_weight P M m cm hcm hm g _ _


-- @@ L101-104 verbatim
theorem normalized_full_pressure_eq :
    normalize g hg (pressurePath P S hS T hT Q Q₁ c hc hQ (weight g f) a₀ M m cm hcm hm) =
      normalizedPressure P S hS T hT Q Q₁ c hc hQ f a₀ M m cm hcm hm g hg := by
  rw [pressurePath_weight_eq, normalize_weight]


-- @@ L106-106 verbatim
end EulerSourceCylinderEquation
