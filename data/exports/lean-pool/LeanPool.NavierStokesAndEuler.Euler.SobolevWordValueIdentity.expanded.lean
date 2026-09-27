/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.RegularizedTopBlocks
public import LeanPool.NavierStokesAndEuler.Euler.TimeLp
import LeanPool.NavierStokesAndEuler.Euler.SobolevMaximalRegularity


-- @@ L13-14 verbatim
/-! Genuine Sobolev derivative words and time fields are independent of harmless order reindexing.
-/


-- @@ L16-16 verbatim
@[expose] public section



-- @@ L19-19 verbatim
noncomputable section


-- @@ L21-21 verbatim
namespace EulerSobolevWordValueIdentity


-- @@ L23-24 verbatim
open MeasureTheory Set EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerMildTopWord
  EulerTimeLp EulerVolterraConvolution EulerRegularizedTopBlocks EulerSobolevMaximalRegularity


-- @@ L26-26 verbatim
variable (period : ℝ) [Fact (0 < period)]


-- @@ L28-33 verbatim
/-- Equal actual L² fields have identical strong derivative words at every shared Sobolev order. -/
theorem word_of_value_eq {p q n : ℕ} (u : SobolevSpace period p) (v : SobolevSpace period q)
    (huv : value period u = value period v) (hp : n ≤ p) (hq : n ≤ q) (w : Fin n → Fin 4) :
    word period u hp w = word period v hq w := by
  rw [← toJet_word period u hp w, ← toJet_word period v hq w]
  exact EulerPressureJetIdentities.SpatialJet.word_unique _ _ huv hp hq w


-- @@ L35-43 verbatim
/-- Every actual bounded derivative block depends only on its underlying field when the required
derivatives exist. -/
theorem boundedWordBlock_of_value_eq {p q r n : ℕ} (u : SobolevSpace period p) (v : SobolevSpace
    period q)
    (huv : value period u = value period v) (hp : r + n ≤ p) (hq : r + n ≤ q) (w : Fin n → Fin 4) :
    boundedWordBlock period r n hp w u = boundedWordBlock period r n hq w v := by
  apply value_injective period
  rw [boundedWordBlock_value, boundedWordBlock_value]
  exact word_of_value_eq period u v huv (by omega) (by omega) w


-- @@ L45-48 verbatim
/-- The genuine maximal-regularity time field reindexed from H^(2+q) to H^((q+1)+1). -/
def reindexMaximalTime (q : ℕ) (T : ℝ) (U : TimeLp T (SobolevSpace period (2 + q))) :
    TimeLp T (SobolevSpace period ((q+1)+1)) :=
  (restrictOperator period (by omega : (q+1)+1 ≤ 2+q)).compLpL 2 (timeMeasure T) U


-- @@ L50-55 verbatim
/-- This actual reindexing preserves the represented L² field almost everywhere in time. -/
theorem reindexMaximalTime_value (q : ℕ) (T : ℝ) (U : TimeLp T (SobolevSpace period (2 + q))) :
    (fun t => value period (reindexMaximalTime period q T U t)) =ᵐ[timeMeasure T]
      fun t => value period (U t) := by
  filter_upwards [(restrictOperator period (by omega : (q+1)+1 ≤ 2+q)).coeFn_compLpL U] with t ht
  exact congrArg (value period) ht


-- @@ L57-67 verbatim
/-- The reindexed genuine maximal-regularity field restricts to the original continuous solution. -/
theorem reindexMaximalTime_restriction {q : ℕ} (T : ℝ) (hT : 0 ≤ T)
    (u : C(Icc (0 : ℝ) T, SobolevSpace period (q + 1))) (U : TimeLp T (SobolevSpace period (2 + q)))
    (hU : Filter.Tendsto (fun n => pathLp T hT (maximalApproximation period q T n u)) Filter.atTop
        (nhds U)) :
    (fun t => truncateOperator period (q+1) (reindexMaximalTime period q T U t)) =ᵐ[timeMeasure T]
      extendPath T hT u := by
  filter_upwards [reindexMaximalTime_value period q T U,
    maximal_limit_restriction period T hT u U hU] with t hv hu
  apply value_injective period
  exact hv.trans (congrArg (value period) hu)


-- @@ L69-69 verbatim
end EulerSobolevWordValueIdentity
