/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.SobolevWordBlocks
public import LeanPool.NavierStokesAndEuler.Euler.H6Pressure
import LeanPool.NavierStokesAndEuler.Euler.Foundations.StrongSmoothJet


-- @@ L13-14 verbatim
/-! Actual derivative words at any lower Sobolev level, with exact representative and norm
identities. -/


-- @@ L16-16 verbatim
@[expose] public section



-- @@ L19-19 verbatim
noncomputable section


-- @@ L21-21 verbatim
namespace EulerSobolevWordLevel


-- @@ L23-25 verbatim
open MeasureTheory EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerCylinderSobolev
  EulerSpatialSobolevInverse EulerMetricTransport EulerSobolevWordBlocks EulerH6Pressure
      EulerStrongSmoothJet


-- @@ L27-27 verbatim
open scoped ContDiff Topology


-- @@ L29-29 verbatim
variable (period : ℝ) [Fact (0 < period)]


-- @@ L31-34 verbatim
/-- A genuine derivative word followed by restriction to its prescribed target Sobolev level. -/
def wordAtLevel {s : ℕ} (q n : ℕ) (w : Fin n → Fin 4) (h : n + q ≤ s) :
    SobolevSpace period s →L[ℝ] SobolevSpace period q :=
  (wordBlock period q n w).comp (restrictOperator period (by omega : q+n ≤ s))


-- @@ L36-42 verbatim
/-- The underlying L² value is the literal strong derivative coordinate of the original field. -/
theorem wordAtLevel_value {s : ℕ} (q n : ℕ) (w : Fin n → Fin 4) (h : n + q ≤ s)
    (u : SobolevSpace period s) :
    value period (wordAtLevel period q n w h u) = (toJet period u).word w := by
  change value period (wordBlock period q n w (restrictOperator period (by omega : q+n ≤ s) u)) = _
  rw [wordBlock_value, toJet_word period u (by omega)]
  rfl


-- @@ L44-53 verbatim
/-- Every actual smooth representative has the expected classical word after this operation. -/
theorem wordAtLevel_ae {s : ℕ} (q n : ℕ) (w : Fin n → Fin 4) (h : n + q ≤ s)
    (u : SobolevSpace period s) (f : LiftDomain period → Vector3)
    (hu : (value period u : LiftDomain period → Vector3) =ᵐ[liftMeasure period] f)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x)) :
    (value period (wordAtLevel period q n w h u) : LiftDomain period → Vector3) =ᵐ[liftMeasure
        period]
      iteratedFieldDerivative period w f := by
  rw [wordAtLevel_value]
  exact jet_word_ae period (by omega) (value period u) (toJet period u) w f hu hf


-- @@ L55-59 verbatim
/-- The derivative-sum Sobolev norm is continuous on its complete finite-array space. -/
theorem continuous_sumNorm (q : ℕ) : Continuous (sumNorm period (q := q)) := by
  apply continuous_finsetSum
  intro w _
  exact (wordOperator period w).continuous.norm


-- @@ L61-67 verbatim
/-- The word-at-level norm equals the corresponding genuine derivative-jet norm. -/
theorem sumNorm_wordAtLevel {s q n : ℕ} (w : Fin n → Fin 4) (h : n + q ≤ s)
    (u : SobolevSpace period s) :
    sumNorm period (wordAtLevel period q n w h u) =
      (EulerH6Pressure.SpatialJet.derivativeJet (toJet period u) w h).sobolevNorm := by
  rw [sumNorm_eq_jet]
  exact EulerH6Pressure.SpatialJet.norm_unique _ _ (wordAtLevel_value period q n w h u)


-- @@ L69-69 verbatim
end EulerSobolevWordLevel
