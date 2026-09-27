/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CorrectionDifference


-- @@ L11-11 verbatim
/-! Fixed, actual coefficient budgets for L² viscosity stability. -/


-- @@ L13-13 verbatim
@[expose] public section



-- @@ L16-16 verbatim
noncomputable section


-- @@ L18-18 verbatim
namespace EulerCorrectionStabilityConstants


-- @@ L20-21 verbatim
open MeasureTheory EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerCorrectionOperators
  EulerCorrectionDifference EulerSobolevL2Product

-- @@ L22-22 verbatim
open scoped Topology


-- @@ L24-26 verbatim
/-- The fixed L² Lipschitz coefficient of all non-top-transport difference terms. -/
def lowerConstant (period : ℝ) [Fact (0 < period)] (q : ℕ) (A0 A2 Z R : ℝ) : ℝ :=
  A0+(4+2*A2)*sobolevEmbeddingConstant period q*(Z+R)


-- @@ L28-30 verbatim
/-- A fixed pointwise bound for the actual background-plus-error advecting velocity. -/
def velocityBound (period : ℝ) [Fact (0 < period)] (q : ℕ) (Z R : ℝ) : ℝ :=
  sobolevEmbeddingConstant period q*(Z+R)


-- @@ L32-34 verbatim
/-- The squared-metric growth coefficient after the genuine transport and heat cancellations. -/
def growthConstant (c Kb Kx Kt V L : ℝ) : ℝ :=
  (Kt+2*Kx*V+4*Kx^2/c^2+2*Kb*L+1)/c^2


-- @@ L36-37 verbatim
/-- The fixed coefficient of the squared viscosity difference. -/
def defectConstant (Kb R : ℝ) : ℝ := (Kb*(4*R))^2


-- @@ L39-39 verbatim
variable (period : ℝ) [Fact (0 < period)]


-- @@ L41-48 verbatim
/-- Nonnegative actual coefficient and norm budgets give a nonnegative lower-order Lipschitz
constant. -/
theorem lowerConstant_nonneg (q : ℕ) (A0 A2 Z R : ℝ)
    (hA0 : 0 ≤ A0) (hA2 : 0 ≤ A2) (hZ : 0 ≤ Z) (hR : 0 ≤ R) :
    0 ≤ lowerConstant period q A0 A2 Z R := by
  unfold lowerConstant
  have := sobolevEmbeddingConstant_nonneg period q
  positivity


-- @@ L50-53 verbatim
/-- The actual pointwise velocity budget is nonnegative. -/
theorem velocityBound_nonneg (q : ℕ) (Z R : ℝ) (hZ : 0 ≤ Z) (hR : 0 ≤ R) :
    0 ≤ velocityBound period q Z R :=
  mul_nonneg (sobolevEmbeddingConstant_nonneg period q) (add_nonneg hZ hR)


-- @@ L55-78 verbatim
/-- Actual higher Sobolev and coefficient bounds give the lower-order difference estimate in L². -/
theorem differenceRemainder_uniform {q : ℕ} {T : Type*} [TopologicalSpace T]
    (D : CorrectionData period q T) (hq : 6 ≤ q) (t : T)
    (u v : SobolevSpace period (q + 1)) (A0 A2 Z R : ℝ)
    (hA0 : ((D.linear.coefficient t).bound : ℝ) ≤ A0)
    (hA2 : (∑ i : Fin 3, (((D.quadratic i).coefficient t).bound : ℝ)) ≤ A2)
    (hZ : ‖D.approximation t‖ ≤ Z) (hu : ‖u‖ ≤ R) (hv : ‖v‖ ≤ R) :
    ‖value period (differenceRemainder period D hq t u v)‖ ≤
      lowerConstant period q A0 A2 Z R*‖value period (u-v)‖ := by
  have hz0 := (norm_nonneg (D.approximation t)).trans hZ
  have hr0 := (norm_nonneg u).trans hu
  have ha20 : 0 ≤ A2 := (Finset.sum_nonneg (fun i _ => ((D.quadratic i).coefficient
      t).bound.coe_nonneg)).trans hA2
  have hzu : ‖D.approximation t+u‖ ≤ Z+R := (norm_add_le _ _).trans (add_le_add hZ hu)
  have hzv : ‖D.approximation t+v‖ ≤ Z+R := (norm_add_le _ _).trans (add_le_add hZ hv)
  apply (differenceRemainder_norm period D hq t u v).trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  have h1 := mul_le_mul_of_nonneg_left hzv (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4)
    (sobolevEmbeddingConstant_nonneg period q))
  have h2 := mul_le_mul (mul_le_mul_of_nonneg_right hA2 (sobolevEmbeddingConstant_nonneg period q))
    (add_le_add hzu hzv) (add_nonneg (norm_nonneg _) (norm_nonneg _))
    (mul_nonneg ha20 (sobolevEmbeddingConstant_nonneg period q))
  unfold lowerConstant
  nlinarith


-- @@ L80-84 verbatim
omit [Fact (0 < period)] in
/-- The actual fixed growth coefficient is nonnegative. -/
theorem growthConstant_nonneg (c Kb Kx Kt V L : ℝ)
    (hKb : 0 ≤ Kb) (hKx : 0 ≤ Kx) (hKt : 0 ≤ Kt) (hV : 0 ≤ V) (hL : 0 ≤ L) :
    0 ≤ growthConstant c Kb Kx Kt V L := by unfold growthConstant; positivity


-- @@ L86-86 verbatim
end EulerCorrectionStabilityConstants
