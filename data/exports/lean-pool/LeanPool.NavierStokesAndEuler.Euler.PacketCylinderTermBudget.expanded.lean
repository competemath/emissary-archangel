/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderFieldWeight
public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderJetOperations
import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderWeightedAdvection


-- @@ L13-13 verbatim
/-! A single coefficient cost bounds every elementary nonlinear packet term. -/


-- @@ L15-15 verbatim
@[expose] public section



-- @@ L18-18 verbatim
noncomputable section


-- @@ L20-20 verbatim
namespace EulerPacketCylinderField


-- @@ L22-23 verbatim
open Set EulerSmoothLimit EulerPacketPointJets EulerPacketProfileRecursion
  EulerMeanCoefficients EulerParameterWordGevrey EulerGevrey EulerCylinderPathProduct

-- @@ L24-24 verbatim
open scoped ContDiff


-- @@ L26-26 verbatim
variable {P T : ℝ} [Fact (0 < P)] {O : Operators}


-- @@ L28-42 verbatim
/-- Coefficient budget data, collecting `Rc`, `amplitude`, `Rc_nonneg`, `amplitude_nonneg`,
`inverse_bound`, `strain_bound` and their compatibility conditions. -/
structure CoefficientBudget (C : CoefficientData P T O) where
  /-- Rc of `CoefficientBudget`, of type `ℝ`. -/
  Rc : ℝ
  /-- Amplitude of `CoefficientBudget`, of type `ℝ`. -/
  amplitude : ℝ
  Rc_nonneg : 0 ≤ Rc
  amplitude_nonneg : 0 ≤ amplitude
  inverse_bound : ∀ n a, ‖iteratedFDeriv ℝ n (translateCoefficientPath C.inverse.path) a‖ ≤
    amplitude*majorant Rc 0 n
  strain_bound : ∀ n a, ‖iteratedFDeriv ℝ n (translateCoefficientPath C.strain.path) a‖ ≤
    amplitude*majorant Rc 0 n
  normal_bound : ∀ n a, ‖iteratedFDeriv ℝ n (translateCoefficientPath C.normal.path) a‖ ≤
    amplitude*majorant Rc 0 n


-- @@ L44-44 verbatim
namespace CoefficientBudget


-- @@ L46-46 verbatim
variable {C : CoefficientData P T O} (B : CoefficientBudget C)


-- @@ L48-49 verbatim
/-- Multiplier cost, given by `3*sobolevCoefficientAmplitude (Fin 4) 6 B.Rc B.amplitude`. -/
def multiplierCost : ℝ := 3*sobolevCoefficientAmplitude (Fin 4) 6 B.Rc B.amplitude

-- @@ L50-51 verbatim
/-- Slow cost, given by `9*productBlockConstant P*B.multiplierCost`. -/
def slowCost : ℝ := 9*productBlockConstant P*B.multiplierCost

-- @@ L52-53 verbatim
/-- Fast cost, given by `3*productBlockConstant P*B.multiplierCost`. -/
def fastCost : ℝ := 3*productBlockConstant P*B.multiplierCost

-- @@ L54-55 verbatim
/-- Linear cost, given by `1+B.multiplierCost`. -/
def linearCost : ℝ := 1+B.multiplierCost

-- @@ L56-57 verbatim
/-- Term cost, given by `2*(1+B.multiplierCost+B.slowCost)`. -/
def termCost : ℝ := 2*(1+B.multiplierCost+B.slowCost)


-- @@ L59-62 verbatim
omit [Fact (0 < P)] in
theorem multiplierCost_nonneg : 0 ≤ B.multiplierCost :=
  mul_nonneg (by norm_num) (sobolevCoefficientAmplitude_nonneg 6 B.Rc B.amplitude
    B.Rc_nonneg B.amplitude_nonneg)


-- @@ L64-65 verbatim
theorem slowCost_nonneg : 0 ≤ B.slowCost :=
  mul_nonneg (mul_nonneg (by norm_num) (productBlockConstant_nonneg P)) B.multiplierCost_nonneg


-- @@ L67-68 verbatim
theorem fastCost_nonneg : 0 ≤ B.fastCost :=
  mul_nonneg (mul_nonneg (by norm_num) (productBlockConstant_nonneg P)) B.multiplierCost_nonneg


-- @@ L70-74 verbatim
theorem fastCost_le_slowCost : B.fastCost ≤ B.slowCost := by
  unfold fastCost slowCost
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (by norm_num : (3 : ℝ) ≤ 9) (productBlockConstant_nonneg P))
    B.multiplierCost_nonneg


-- @@ L76-77 verbatim
omit [Fact (0 < P)] in
theorem linearCost_nonneg : 0 ≤ B.linearCost := add_nonneg zero_le_one B.multiplierCost_nonneg


-- @@ L79-83 verbatim
theorem termCost_nonneg : 0 ≤ B.termCost := by
  have hm := B.multiplierCost_nonneg
  have hs := B.slowCost_nonneg
  unfold termCost
  positivity


-- @@ L85-89 verbatim
theorem one_le_termCost : 1 ≤ B.termCost := by
  have hm := B.multiplierCost_nonneg
  have hs := B.slowCost_nonneg
  unfold termCost
  linarith


-- @@ L91-94 verbatim
theorem twice_slowCost_le : 2*B.slowCost ≤ B.termCost := by
  have hm := B.multiplierCost_nonneg
  unfold termCost
  linarith


-- @@ L96-97 verbatim
theorem twice_fastCost_le : 2*B.fastCost ≤ B.termCost :=
  (mul_le_mul_of_nonneg_left B.fastCost_le_slowCost (by norm_num)).trans B.twice_slowCost_le


-- @@ L99-102 verbatim
theorem twice_linearCost_le : 2*B.linearCost ≤ B.termCost := by
  have hs := B.slowCost_nonneg
  unfold termCost linearCost
  linarith


-- @@ L104-107 verbatim
theorem twice_multiplierCost_le : 2*B.multiplierCost ≤ B.termCost := by
  have hs := B.slowCost_nonneg
  unfold termCost
  linarith


-- @@ L109-111 verbatim
variable {J K : Domain → VectorJet} (G : SpatialJetField P T J) (H : SpatialJetField P T K)
  (hT : 0 ≤ T) (g h b : C(Icc (0 : ℝ) T, ℝ))
  (hg : ∀ t, 0 < g t) (hh : ∀ t, 0 < h t) (hb : ∀ t, 0 < b t)


-- @@ L113-125 verbatim
theorem slow_bound {R : ℝ} {d e : ℕ}
    (hG : (G.field.normalized hT g hg).WordBound 6 R 1 d)
    (hH : (H.field.normalized hT h hh).WordBound 6 R 1 e)
    (hR : 0 ≤ R) (hRc : sobolevCoefficientRadius (Fin 4) B.Rc ≤ R)
    (hp : ∀ t, g t * h t ≤ b t) :
    ((SpatialJetField.slowAdvection C.inverse G H).normalized hT b hb).WordBound 6 R
      B.slowCost (d+e+1) := by
  have hbound := G.slowAdvection_normalized_bound H hT g h b hg hh hb C.inverse hG hH
    hR zero_le_one zero_le_one B.Rc B.amplitude B.Rc_nonneg B.amplitude_nonneg hRc
    B.inverse_bound 1 zero_le_one
    (productProfileRatio_abs_le g h b (fun t => (hg t).le) (fun t => (hh t).le) hb 1
      (by simpa only [one_mul] using hp))
  simpa only [one_mul,mul_one,slowCost,multiplierCost] using hbound


-- @@ L127-139 verbatim
theorem fast_bound {R : ℝ} {d e : ℕ}
    (hG : (G.field.normalized hT g hg).WordBound 6 R 1 d)
    (hH : (H.field.normalized hT h hh).WordBound 6 R 1 e)
    (hR : 0 ≤ R) (hRc : sobolevCoefficientRadius (Fin 4) B.Rc ≤ R)
    (hp : ∀ t, g t * h t ≤ b t) :
    ((SpatialJetField.fastAdvection C.normal G H).normalized hT b hb).WordBound 6 R
      B.fastCost (d+e+1) := by
  have hbound := G.fastAdvection_normalized_bound H hT g h b hg hh hb C.normal hG hH
    hR zero_le_one zero_le_one B.Rc B.amplitude B.Rc_nonneg B.amplitude_nonneg hRc
    B.normal_bound 1 zero_le_one
    (productProfileRatio_abs_le g h b (fun t => (hg t).le) (fun t => (hh t).le) hb 1
      (by simpa only [one_mul] using hp))
  simpa only [one_mul,mul_one,fastCost,multiplierCost] using hbound


-- @@ L141-141 verbatim
end CoefficientBudget

-- @@ L142-142 verbatim
end EulerPacketCylinderField
