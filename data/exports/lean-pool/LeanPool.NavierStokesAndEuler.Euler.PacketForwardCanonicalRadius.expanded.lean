/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketForwardRadiusPolynomial
import LeanPool.NavierStokesAndEuler.Euler.PacketTerminalEnvelope


-- @@ L12-12 verbatim
/-! Named direct-forward budgets at the literal canonical source radius. -/


-- @@ L14-14 verbatim
@[expose] public section



-- @@ L17-17 verbatim
noncomputable section


-- @@ L19-19 verbatim
namespace EulerPacketTerminalDatum


-- @@ L21-22 verbatim
open EulerPacketCylinderField EulerPacketProfileRecursion EulerParameterWordGevrey
  EulerPacketForwardCommonRadius


-- @@ L24-31 verbatim
variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : EulerTransversePacketProvider.Data U}
  {M : EulerMeanPacketProvider.Data} {Rm Tc : ℝ} {O : Operators}
  {C : CoefficientData period Tc O}
  (LM : EulerMeanPacketProvider.Budget M 6 Rm)
  (L : EulerTransversePacketForward.Budget D (Fin 4) 6)
  (NB : EulerTransversePacketJoin.NormalBudget D 6 L.R)
  (BC : CoefficientBudget C) (δ : ℝ) (ξ : U)


-- @@ L33-35 verbatim
/-- Forward initialized radius: an abbreviation for `EulerPacketForwardRadius.canonicalRadius L
LM NB BC δ ξ`. -/
abbrev forwardInitializedRadius : ℝ := EulerPacketForwardRadius.canonicalRadius L LM NB BC δ ξ


-- @@ L37-38 verbatim
theorem forward_le_initializedRadius : L.R ≤ forwardInitializedRadius LM L NB BC δ ξ :=
  (commonRadius_bounds LM L NB BC (wordCost (Fin 4) 6 δ*‖ξ‖) (wordRadius (Fin 4) δ)).2.1


-- @@ L40-41 verbatim
theorem mean_le_forwardInitializedRadius : Rm ≤ forwardInitializedRadius LM L NB BC δ ξ :=
  (commonRadius_bounds LM L NB BC (wordCost (Fin 4) 6 δ*‖ξ‖) (wordRadius (Fin 4) δ)).1


-- @@ L43-47 verbatim
/-- Forward initialized linear budget, given by `L.enlargeRadius (forwardInitializedRadius LM L
NB BC δ ξ) (forward_le_initializedRadius LM L NB BC δ ξ)`. -/
def forwardInitializedLinearBudget : EulerTransversePacketForward.Budget D (Fin 4) 6 :=
  L.enlargeRadius (forwardInitializedRadius LM L NB BC δ ξ)
    (forward_le_initializedRadius LM L NB BC δ ξ)


-- @@ L49-54 verbatim
/-- Forward initialized normal budget, given by `NB.enlargeRadius (forwardInitializedRadius LM L
NB BC δ ξ) (forward_le_initializedRadius LM L NB BC δ ξ)`. -/
def forwardInitializedNormalBudget : EulerTransversePacketJoin.NormalBudget D 6
    (forwardInitializedRadius LM L NB BC δ ξ) :=
  NB.enlargeRadius (forwardInitializedRadius LM L NB BC δ ξ)
    (forward_le_initializedRadius LM L NB BC δ ξ)


-- @@ L56-61 verbatim
/-- Forward initialized mean budget, given by `LM.enlargeRadius (forwardInitializedRadius LM L
NB BC δ ξ) (mean_le_forwardInitializedRadius LM L NB BC δ ξ)`. -/
def forwardInitializedMeanBudget : EulerMeanPacketProvider.Budget M 6
    (forwardInitializedRadius LM L NB BC δ ξ) :=
  LM.enlargeRadius (forwardInitializedRadius LM L NB BC δ ξ)
    (mean_le_forwardInitializedRadius LM L NB BC δ ξ)


-- @@ L63-79 verbatim
theorem forwardInitializedRadius_guards :
    EulerTransversePacketForward.Budget.GradeGuards (P := period)
      (forwardInitializedLinearBudget LM L NB BC δ ξ) (forwardInitializedNormalBudget LM L NB BC δ
          ξ) 1 ∧
    EulerMeanPacketProvider.Budget.GradeGuards (forwardInitializedMeanBudget LM L NB BC δ ξ) ∧
    EulerTransversePacketForward.Budget.GradeGuards (P := period)
      (forwardInitializedLinearBudget LM L NB BC δ ξ) (forwardInitializedNormalBudget LM L NB BC δ
          ξ)
      (wordCost (Fin 4) 6 δ*‖ξ‖) ∧
    wordRadius (Fin 4) δ ≤ forwardInitializedRadius LM L NB BC δ ξ ∧
    BC.termCost ≤ forwardInitializedRadius LM L NB BC δ ξ ∧
    sobolevCoefficientRadius (Fin 4) BC.Rc ≤ forwardInitializedRadius LM L NB BC δ ξ := by
  obtain ⟨_,_,hm,hf,hp,hc,hr,ht⟩ := commonRadius_guards LM L NB BC
    (wordCost (Fin 4) 6 δ*‖ξ‖) (wordRadius (Fin 4) δ)
    (mul_nonneg (wordCost_nonneg 6 δ) (norm_nonneg ξ))
    (forwardInitializedRadius LM L NB BC δ ξ) le_rfl
  exact ⟨hf,hm,hp,ht,hc,hr⟩


-- @@ L81-81 verbatim
end EulerPacketTerminalDatum
