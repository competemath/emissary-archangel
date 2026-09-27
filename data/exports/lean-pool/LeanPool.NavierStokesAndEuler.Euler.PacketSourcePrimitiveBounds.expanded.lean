/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketCorrectionPrimitiveBounds
public import LeanPool.NavierStokesAndEuler.Euler.PacketJoinedCoefficientBudgets
public import LeanPool.NavierStokesAndEuler.Euler.PacketForwardCoefficientBudgets


-- @@ L13-14 verbatim
/-! The actual joined and forward source budgets retain the polynomial
correction envelope. Only their original coefficient leaves enter it. -/


-- @@ L16-16 verbatim
@[expose] public section



-- @@ L19-19 verbatim
noncomputable section


-- @@ L21-21 verbatim
namespace EulerTransversePacketJoin.Budget


-- @@ L23-23 verbatim
open EulerTransversePacketProvider EulerPacketCorrectionPrimitive


-- @@ L25-29 verbatim
variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} {τ : ℝ} {hτ : 0 < τ} {hτT : τ < D.T}
  {B : HistoryData (D.initial τ hτ hτT.le)}
  (L : Budget D τ hτ hτT B (Fin 4) 6) (NB : NormalBudget D 6 L.R)
  (P : ℝ) [Fact (0 < P)]


-- @@ L31-41 verbatim
theorem correctionCoefficients_primitive_bound (X : ℝ) (hX : 1 ≤ X)
    (hLR : L.Rc ≤ X) (hNR : NB.Rc ≤ X) (hC0 : L.C₀ ≤ X)
    (hC1 : L.C₁ ≤ X) (hCI : NB.C ≤ X) :
    CorrectionBounds D P (L.correctionCoefficients NB P) (primitiveEnvelope P X) := by
  unfold correctionCoefficients
  apply correctionBudget_bounds
  · exact hX
  · exact max_le hLR hNR
  · exact hC0
  · exact hC1
  · exact hCI


-- @@ L43-48 verbatim
theorem correctionCoefficients_primitive_power (X : ℝ) (hX : 1 ≤ X)
    (hLR : L.Rc ≤ X) (hNR : NB.Rc ≤ X) (hC0 : L.C₀ ≤ X)
    (hC1 : L.C₁ ≤ X) (hCI : NB.C ≤ X) :
    CorrectionBounds D P (L.correctionCoefficients NB P) (primitiveConstant P*X^primitivePower P) :=
  (L.correctionCoefficients_primitive_bound NB P X hX hLR hNR hC0 hC1 hCI).mono D P
    (primitiveEnvelope_power P X hX)


-- @@ L50-50 verbatim
end EulerTransversePacketJoin.Budget


-- @@ L52-52 verbatim
namespace EulerTransversePacketForward.Budget


-- @@ L54-54 verbatim
open EulerTransversePacketProvider EulerPacketCorrectionPrimitive


-- @@ L56-59 verbatim
variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} (L : Budget D (Fin 4) 6)
  (NB : EulerTransversePacketJoin.NormalBudget D 6 L.R)
  (P : ℝ) [Fact (0 < P)]


-- @@ L61-71 verbatim
theorem correctionCoefficients_primitive_bound (X : ℝ) (hX : 1 ≤ X)
    (hLR : L.Rc ≤ X) (hNR : NB.Rc ≤ X) (hC0 : L.C₀ ≤ X)
    (hC1 : L.C₁ ≤ X) (hCI : NB.C ≤ X) :
    CorrectionBounds D P (L.correctionCoefficients NB P) (primitiveEnvelope P X) := by
  unfold correctionCoefficients
  apply correctionBudget_bounds
  · exact hX
  · exact max_le hLR hNR
  · exact hC0
  · exact hC1
  · exact hCI


-- @@ L73-78 verbatim
theorem correctionCoefficients_primitive_power (X : ℝ) (hX : 1 ≤ X)
    (hLR : L.Rc ≤ X) (hNR : NB.Rc ≤ X) (hC0 : L.C₀ ≤ X)
    (hC1 : L.C₁ ≤ X) (hCI : NB.C ≤ X) :
    CorrectionBounds D P (L.correctionCoefficients NB P) (primitiveConstant P*X^primitivePower P) :=
  (L.correctionCoefficients_primitive_bound NB P X hX hLR hNR hC0 hC1 hCI).mono D P
    (primitiveEnvelope_power P X hX)


-- @@ L80-80 verbatim
end EulerTransversePacketForward.Budget
