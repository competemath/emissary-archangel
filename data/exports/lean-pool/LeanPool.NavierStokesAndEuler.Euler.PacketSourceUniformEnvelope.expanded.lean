/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.ParentInitializedRadiusPolynomial
public import LeanPool.NavierStokesAndEuler.Euler.PacketInitializedOutputCosts
public import LeanPool.NavierStokesAndEuler.Euler.PacketForwardRadiusPolynomial
public import LeanPool.NavierStokesAndEuler.Euler.PacketGeometryJoinedBudget
public import LeanPool.NavierStokesAndEuler.Euler.ParentForwardGeometryInput
import LeanPool.NavierStokesAndEuler.Euler.PacketGeometryProfileEnvelope
import LeanPool.NavierStokesAndEuler.Euler.PacketInitializedParameterBounds


-- @@ L17-18 verbatim
/-! The chosen geometric profile contributes only another fixed
polynomial in the source primitives, including the target shear. -/


-- @@ L20-20 verbatim
@[expose] public section



-- @@ L23-23 verbatim
noncomputable section


-- @@ L25-25 verbatim
namespace EulerPacketUniformSource


-- @@ L27-27 verbatim
open EulerParentInitializedRadius EulerPolynomialCost


-- @@ L29-31 verbatim
/-- Profile envelope, given by `1+sourceEnvelope X+8*Real.exp 6*X*(1+sourceEnvelope X)`. -/
def profileEnvelope (X : ℝ) : ℝ :=
  1+sourceEnvelope X+8*Real.exp 6*X*(1+sourceEnvelope X)


-- @@ L33-36 verbatim
/-- Profile polynomial, given by `1+sourcePolynomial+Polynomial.C (8*Real.exp
6)*Polynomial.X*(1+sourcePolynomial)`. -/
def profilePolynomial : Polynomial ℝ :=
  1+sourcePolynomial+Polynomial.C (8*Real.exp 6)*Polynomial.X*(1+sourcePolynomial)


-- @@ L38-40 verbatim
theorem profilePolynomial_eval (X : ℝ) : profilePolynomial.eval X=profileEnvelope X := by
  simp only [profilePolynomial,profileEnvelope,Polynomial.eval_add,Polynomial.eval_mul,
    Polynomial.eval_C,Polynomial.eval_X,Polynomial.eval_one,sourcePolynomial_eval]


-- @@ L42-44 verbatim
theorem sourceEnvelope_one (X : ℝ) (hX : 1 ≤ X) : 1 ≤ sourceEnvelope X := by
  have hi := (inputEnvelope_bounds X X hX le_rfl).1
  exact hi.trans (EulerPacketSourceRadius.le_sourceRadiusEnvelope _ (zero_le_one.trans hi))


-- @@ L46-54 verbatim
theorem profileEnvelope_bounds (X : ℝ) (hX : 1 ≤ X) :
    1 ≤ profileEnvelope X ∧ sourceEnvelope X ≤ profileEnvelope X ∧
    8*Real.exp 6*X*(1+sourceEnvelope X) ≤ profileEnvelope X := by
  have hX0 := zero_le_one.trans hX
  have hS := zero_le_one.trans (sourceEnvelope_one X hX)
  have he := (Real.exp_pos (6 : ℝ)).le
  have hp : 0 ≤ 8*Real.exp 6*X*(1+sourceEnvelope X) := by positivity
  unfold profileEnvelope
  exact ⟨by linarith,by linarith,by linarith⟩


-- @@ L56-65 verbatim
theorem profile_amplitude_le (X δ h C : ℝ) (hX : 1 ≤ X)
    (_hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hh : 0 ≤ h) (hhX : h ≤ X)
    (hC : 0 ≤ C) (hCS : C ≤ sourceEnvelope X) :
    8*Real.exp 6*δ*h*(1+C) ≤ profileEnvelope X := by
  have hS := zero_le_one.trans (sourceEnvelope_one X hX)
  have he := (Real.exp_pos (6 : ℝ)).le
  calc
    _ ≤ 8*Real.exp 6*1*X*(1+sourceEnvelope X) := by gcongr
    _ = 8*Real.exp 6*X*(1+sourceEnvelope X) := by ring
    _ ≤ _ := (profileEnvelope_bounds X hX).2.2


-- @@ L67-72 verbatim
/-- Frequency polynomial, given by `Polynomial.C
EulerPacketInitializedOutputCost.uniformConstant *
profilePolynomial^EulerPacketInitializedOutputCost.uniformPower`. -/
def frequencyPolynomial : Polynomial ℝ :=
  Polynomial.C EulerPacketInitializedOutputCost.uniformConstant *
    profilePolynomial^EulerPacketInitializedOutputCost.uniformPower


-- @@ L74-75 verbatim
/-- Frequency constant, given by `coefficientCost frequencyPolynomial`. -/
def frequencyConstant : ℝ := coefficientCost frequencyPolynomial

-- @@ L76-77 verbatim
/-- Frequency power, given by `frequencyPolynomial.natDegree`. -/
def frequencyPower : ℕ := frequencyPolynomial.natDegree


-- @@ L79-79 verbatim
theorem frequencyConstant_pos : 0 < frequencyConstant := coefficientCost_pos _


-- @@ L81-86 verbatim
theorem frequencyPolynomial_eval (X : ℝ) :
    frequencyPolynomial.eval X=EulerPacketInitializedOutputCost.uniformConstant *
      (profileEnvelope X)^EulerPacketInitializedOutputCost.uniformPower := by
  unfold frequencyPolynomial
  simp only [Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,
    profilePolynomial_eval]


-- @@ L88-93 verbatim
theorem frequency_bound (X : ℝ) (hX : 1 ≤ X) :
    EulerPacketInitializedOutputCost.uniformConstant *
      (profileEnvelope X)^EulerPacketInitializedOutputCost.uniformPower ≤
      frequencyConstant*X^frequencyPower := by
  rw [← frequencyPolynomial_eval]
  exact (le_abs_self _).trans (eval_bound frequencyPolynomial X hX)


-- @@ L95-95 verbatim
end EulerPacketUniformSource


-- @@ L97-97 verbatim
namespace EulerPacketSourceGeometry.Guards


-- @@ L99-101 verbatim
open Set EulerSmoothLimit EulerTransversePacketProvider EulerPacketUniformSource
  EulerParentInitializedRadius EulerPacketProfileRecursion EulerPacketCylinderField
  EulerPacketTerminalDatum


-- @@ L103-114 verbatim
variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} {τ : ℝ} {hτ : 0 < τ} {hτT : τ < D.T} {P : ParentFrame D τ}
  {H : HistoryData (D.initial τ hτ hτT.le)} (J : Guards hτ hτT P H)
  (hball : (1 / 2 : ℝ) ≤ J.radius)
  (L : EulerTransversePacketJoin.Budget D τ hτ hτT H (Fin 4) 6)
  (hg : L.g = J.sourceGrowthProfile hball)
  {M : EulerMeanPacketProvider.Data} {Rm Tc : ℝ} {O : Operators}
  {C : CoefficientData period Tc O}
  (LM : EulerMeanPacketProvider.Budget M 6 Rm)
  (NB : EulerTransversePacketJoin.NormalBudget D 6 L.R) (BC : CoefficientBudget C)
  (ξ : U) (X : ℝ) (hX : 1 ≤ X) (hhX : J.hchild ≤ X) (hδ1 : J.δ ≤ 1)
  (hR : EulerPacketRadiusPolynomial.RadiusPrimitives LM L NB BC J.δ ξ (sourceEnvelope X))


-- @@ L116-124 verbatim
include hg hX hhX hδ1 hR in
theorem source_uniform_primitives :
    EulerPacketRadiusPolynomial.RadiusPrimitives LM L NB BC J.δ ξ (profileEnvelope X) ∧
    ∀ t, J.primaryAmplitude hball*L.fullProfile t ≤ profileEnvelope X := by
  refine ⟨hR.mono (profileEnvelope_bounds X hX).2.1,?_⟩
  intro t
  exact (J.budget_fullProfile_amplitude hball L hg t).trans
    (profile_amplitude_le X J.δ J.hchild L.C₀ hX J.delta_nonneg hδ1
      J.child_nonneg hhX L.C₀_nonneg hR.joined_frame)


-- @@ L126-126 verbatim
end EulerPacketSourceGeometry.Guards


-- @@ L128-128 verbatim
namespace EulerPacketForwardRadius.RadiusPrimitives


-- @@ L130-131 verbatim
open EulerTransversePacketProvider EulerPacketProfileRecursion EulerPacketCylinderField
  EulerPacketTerminalDatum


-- @@ L133-139 verbatim
variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} {L : EulerTransversePacketForward.Budget D (Fin 4) 6}
  {M : EulerMeanPacketProvider.Data} {Rm Tc : ℝ} {O : Operators}
  {C : CoefficientData period Tc O}
  {LM : EulerMeanPacketProvider.Budget M 6 Rm}
  {NB : EulerTransversePacketJoin.NormalBudget D 6 L.R} {BC : CoefficientBudget C}
  {δ : ℝ} {ξ : U} {X Y : ℝ}


-- @@ L141-163 verbatim
theorem mono (H : RadiusPrimitives L LM NB BC δ ξ X) (hXY : X ≤ Y) :
    RadiusPrimitives L LM NB BC δ ξ Y := {
  one := H.one.trans hXY
  total_time := H.total_time
  mean_time := H.mean_time
  mean_inverse_time := H.mean_inverse_time.trans hXY
  original_forward := H.original_forward.trans hXY
  original_mean := H.original_mean.trans hXY
  forward_radius := H.forward_radius.trans hXY
  forward_frame := H.forward_frame.trans hXY
  forward_first := H.forward_first.trans hXY
  forward_inverse := H.forward_inverse.trans hXY
  normal_radius := H.normal_radius.trans hXY
  normal_amplitude := H.normal_amplitude.trans hXY
  normal_inverse := H.normal_inverse.trans hXY
  mean_radius := H.mean_radius.trans hXY
  mean_frame := H.mean_frame.trans hXY
  mean_first := H.mean_first.trans hXY
  mean_forcing := H.mean_forcing.trans hXY
  coefficient_radius := H.coefficient_radius.trans hXY
  coefficient_cost := H.coefficient_cost.trans hXY
  delta_inverse := H.delta_inverse.trans hXY
  terminal := H.terminal.trans hXY }


-- @@ L165-165 verbatim
end EulerPacketForwardRadius.RadiusPrimitives


-- @@ L167-167 verbatim
namespace EulerPacketSourceGeometry.ForwardGuards


-- @@ L169-171 verbatim
open Set EulerSmoothLimit EulerTransversePacketProvider EulerPacketUniformSource
  EulerParentInitializedRadius EulerPacketProfileRecursion EulerPacketCylinderField
  EulerPacketTerminalDatum


-- @@ L173-183 verbatim
variable {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} {P : ParentFrame D 0} (J : ForwardGuards P)
  (hball : (1 / 2 : ℝ) ≤ J.radius)
  (L : EulerTransversePacketForward.Budget D (Fin 4) 6)
  (hg : L.g = J.sourceGrowthProfile hball)
  {M : EulerMeanPacketProvider.Data} {Rm Tc : ℝ} {O : Operators}
  {C : CoefficientData period Tc O}
  (LM : EulerMeanPacketProvider.Budget M 6 Rm)
  (NB : EulerTransversePacketJoin.NormalBudget D 6 L.R) (BC : CoefficientBudget C)
  (ξ : U) (X : ℝ) (hX : 1 ≤ X) (hhX : J.hchild ≤ X) (hδ1 : J.δ ≤ 1)
  (hR : EulerPacketForwardRadius.RadiusPrimitives L LM NB BC J.δ ξ (sourceEnvelope X))


-- @@ L185-194 verbatim
include hg hX hhX hδ1 hR in
theorem source_uniform_primitives :
    EulerPacketForwardRadius.RadiusPrimitives L LM NB BC J.δ ξ (profileEnvelope X) ∧
    ∀ t, J.primaryAmplitude hball*L.g t ≤ profileEnvelope X := by
  refine ⟨hR.mono (profileEnvelope_bounds X hX).2.1,?_⟩
  intro t
  apply (J.budget_profile_amplitude hball L hg t).trans
  simpa only [add_zero,mul_one] using
    profile_amplitude_le X J.δ J.hchild 0 hX J.delta_nonneg hδ1 J.child_nonneg hhX
      le_rfl (zero_le_one.trans (sourceEnvelope_one X hX))


-- @@ L196-196 verbatim
end EulerPacketSourceGeometry.ForwardGuards
