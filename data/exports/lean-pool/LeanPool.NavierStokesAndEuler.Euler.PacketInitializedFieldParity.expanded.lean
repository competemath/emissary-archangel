/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.PacketInitializedCorrectionData
public import LeanPool.NavierStokesAndEuler.Euler.PacketFieldParityAlgebra
public import LeanPool.NavierStokesAndEuler.Euler.PacketInitializedProfiles
import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderParity
import LeanPool.NavierStokesAndEuler.Euler.PacketFiniteParity
public import LeanPool.NavierStokesAndEuler.Euler.PacketProfileParity
public import LeanPool.NavierStokesAndEuler.Euler.PacketTerminalInitialData
public import LeanPool.NavierStokesAndEuler.Euler.PacketRecursiveBase
public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketCorrectorOperator
public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketPrimaryField
import LeanPool.NavierStokesAndEuler.Euler.TransversePacketPrimaryCorrector
import LeanPool.NavierStokesAndEuler.Euler.TransversePacketPrimaryPressure


-- @@ L21-22 verbatim
/-! The literal initialized packet and its exact residual tail are odd
as actual cylinder L² paths, before and after coordinate normalization. -/


-- @@ L24-24 verbatim
section


-- @@ L26-28 verbatim
/-! Joint parity of the actual terminal-history primary and its continuation.
The compact terminal wave supplies the odd input without an additional
assumption on the constructed solution. -/


-- @@ L30-30 verbatim
@[expose] public section


-- @@ L32-32 verbatim
noncomputable section


-- @@ L34-34 verbatim
namespace EulerTransversePacketPrimary


-- @@ L36-37 verbatim
open Set EulerSmoothLimit EulerTransversePacketProvider EulerPacketCylinderField
  EulerPacketProfileRecursion EulerLpCylinderTranslation EulerCylinderFieldReflection


-- @@ L39-48 verbatim
variable {P : ℝ} [Fact (0 < P)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T)
  (B : HistoryData (D.initial τ hτ hτT.le)) (Y : InitialData P D)
  (O : Operators) (hcorrector : O.curlCorrector = D.curlCorrector P)
  (hSym : ∀ x, -x ∈ D.support ↔ x ∈ D.support)
  (hF : ∀ t x, D.F.field t (-x) = D.F.field t x)
  (hM : ∀ t x, D.M.field t (-x) = D.M.field t x)
  (hH : ∀ t x, B.H.field t (-x) = B.H.field t x)
  (hY : reflection P (Y.value : CylinderL2 P U) = -(Y.value : CylinderL2 P U))


-- @@ L50-50 verbatim
include hcorrector hSym hF hM hH hY


-- @@ L52-64 verbatim
theorem profileParity :
    ProfileParity D.T (primaryProfile O (vector τ hτ hτT B Y) (scalar τ hτ hτT B Y)) where
  high := vector_odd τ hτ hτT B Y hSym hF hM hH hY
  mean := JointOdd.zero D.T
  corrector := by
    intro t x θ
    change O.curlCorrector (vector τ hτ hτT B Y) (t,(-x,-θ)) =
      -O.curlCorrector (vector τ hτ hτT B Y) (t,(x,θ))
    rw [hcorrector]
    exact curlCorrector_odd τ hτ hτT B Y hSym hF hM hH hY t x θ
  pressure := scalarGradient_odd τ hτ hτT B Y hSym hF hM hH hY
  highPressure := scalar_even τ hτ hτT B Y hSym hF hM hH hY
  meanPressure _ _ _ := rfl


-- @@ L66-66 verbatim
end EulerTransversePacketPrimary


-- @@ L68-68 verbatim
namespace EulerPacketTerminalDatum


-- @@ L70-71 verbatim
open Set EulerSmoothLimit EulerSpatialCutoffs EulerTransversePacketProvider
  EulerPacketCylinderField EulerPacketProfileRecursion EulerTransversePacketPrimary


-- @@ L73-81 verbatim
variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T)
  (B : HistoryData (D.initial τ hτ hτT.le))
  (δ : ℝ) (hδ : 0 < δ) (ξ : U) (hs : tsupport innerCutoff ⊆ D.support)
  (O : Operators) (hcorrector : O.curlCorrector = D.curlCorrector period)
  (hSym : ∀ x, -x ∈ D.support ↔ x ∈ D.support)
  (hF : ∀ t x, D.F.field t (-x) = D.F.field t x)
  (hM : ∀ t x, D.M.field t (-x) = D.M.field t x)
  (hH : ∀ t x, B.H.field t (-x) = B.H.field t x)


-- @@ L83-83 verbatim
include hcorrector hSym hF hM hH


-- @@ L85-90 verbatim
theorem primary_profile_parity :
    ProfileParity D.T (primaryProfile O
      (vector τ hτ hτT B (initialData D δ hδ ξ hs))
      (scalar τ hτ hτT B (initialData D δ hδ ξ hs))) :=
  profileParity τ hτ hτT B (initialData D δ hδ ξ hs) O hcorrector hSym hF hM hH
    (terminal_reflection δ hδ ξ)


-- @@ L92-92 verbatim
end EulerPacketTerminalDatum


-- @@ L94-94 verbatim
end

-- @@ L95-95 verbatim
end


-- @@ L97-97 verbatim
end


-- @@ L99-99 verbatim
section


-- @@ L101-102 verbatim
/-! Every initialized profile inherits reflection parity from the actual
terminal wave and the prescribed source coefficient symmetries. -/


-- @@ L104-104 verbatim
@[expose] public section


-- @@ L106-106 verbatim
noncomputable section


-- @@ L108-108 verbatim
namespace EulerPacketTerminalDatum


-- @@ L110-111 verbatim
open Set EulerSmoothLimit EulerSpatialCutoffs EulerTransversePacketProvider
  EulerPacketCylinderField EulerPacketProfileRecursion


-- @@ L113-117 verbatim
variable (M : EulerMeanPacketProvider.Data)
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (D : Data U) (hTime : M.T = D.T) (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T)
  (B : HistoryData (D.initial τ hτ hτT.le))
  (δ : ℝ) (hδ : 0 < δ) (ξ : U) (hs : tsupport innerCutoff ⊆ D.support) (α : ℝ)


-- @@ L119-135 verbatim
include hTime in
theorem initializedProfiles_parity (eM : EulerMeanPacketProvider.EvenData M)
    (hSym : ∀ x, -x ∈ D.support ↔ x ∈ D.support)
    (hF : ∀ t x, D.F.field t (-x) = D.F.field t x)
    (hDM : ∀ t x, D.M.field t (-x) = D.M.field t x)
    (hBH : ∀ t x, B.H.field t (-x) = B.H.field t x) (p : ℕ) :
    ProfileParity M.T (initializedProfiles M D τ hτ hτT B δ hδ ξ hs α p) := by
  have hp := primary_profile_parity τ hτ hτT B δ hδ (α • ξ) hs
    (joinedSourceOperators period M D τ hτ hτT B) rfl hSym hF hDM hBH
  have hpM : ProfileParity M.T
      (joinedTerminalPrimary period M D τ hτ hτT B (initialData D δ hδ (α • ξ) hs)) :=
    hp.changeTime hTime.symm
  exact joinedSourceProfiles_parity period M D hTime τ hτ hτT B
    (joinedTerminalPrimary period M D τ hτ hτT B (initialData D δ hδ (α • ξ) hs))
    (joinedTerminalPrimaryWitness period M D hTime τ hτ hτT B
      (initialData D δ hδ (α • ξ) hs))
    eM hSym hF hDM hBH hpM p


-- @@ L137-137 verbatim
end EulerPacketTerminalDatum


-- @@ L139-139 verbatim
end

-- @@ L140-140 verbatim
end


-- @@ L142-142 verbatim
end


-- @@ L144-144 verbatim
@[expose] public section


-- @@ L146-146 verbatim
noncomputable section


-- @@ L148-148 verbatim
namespace EulerPacketTerminalDatum


-- @@ L150-152 verbatim
open Set EulerSmoothLimit EulerSpatialCutoffs EulerTransversePacketProvider
  EulerPacketCylinderField EulerPacketProfileRecursion EulerPacketPointJets
  EulerCylinderFieldReflection


-- @@ L154-163 verbatim
variable (M : EulerMeanPacketProvider.Data)
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (D : Data U) (hTime : M.T = D.T) (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T)
  (B : HistoryData (D.initial τ hτ hτT.le))
  (δ : ℝ) (hδ : 0 < δ) (ξ : U) (hs : tsupport innerCutoff ⊆ D.support) (α : ℝ)
  (eM : EulerMeanPacketProvider.EvenData M)
  (hSym : ∀ x, -x ∈ D.support ↔ x ∈ D.support)
  (hF : ∀ t x, D.F.field t (-x) = D.F.field t x)
  (hDM : ∀ t x, D.M.field t (-x) = D.M.field t x)
  (hBH : ∀ t x, B.H.field t (-x) = B.H.field t x)


-- @@ L165-165 verbatim
include hTime eM hSym hF hDM hBH


-- @@ L167-172 verbatim
theorem initializedVelocity_odd (N : ℕ) (κ : ℝ) :
    JointOdd M.T (fieldSum (N+1) κ
      (assembledVelocity N (initializedProfiles M D τ hτ hτT B δ hδ ξ hs α))) :=
  ProfileParity.velocity_odd
    (fun i _ => initializedProfiles_parity M D hTime τ hτ hτT B δ hδ ξ hs α
      eM hSym hF hDM hBH i) κ


-- @@ L174-179 verbatim
theorem initializedPacketField_odd (N : ℕ) (κ : ℝ) :
    (initializedPacketField M D hTime τ hτ hτT B δ hδ ξ hs α N κ).ReflectionOdd := by
  apply Field.reflectionOdd_of_raw
  exact (initializedVelocity_odd M D hTime τ hτ hτT B δ hδ ξ hs α
    eM hSym hF hDM hBH N κ).matrix_apply _
    (joinedSourceCoefficientEven period M D τ hτ hτT B hF hDM).inverse


-- @@ L181-184 verbatim
theorem initializedNormalizedField_odd (N : ℕ) (k : ℝ) :
    (initializedNormalizedField M D hTime τ hτ hτT B δ hδ ξ hs α N k).ReflectionOdd :=
  ((initializedPacketField_odd M D hTime τ hτ hτT B δ hδ ξ hs α
    eM hSym hF hDM hBH N k⁻¹).smul k).changeTime hTime


-- @@ L186-202 verbatim
theorem initializedResidualField_odd (Cagree : SourceCoefficientAgreement M D)
    (N : ℕ) (hN : 1 ≤ N) (κ : ℝ) (hκ : κ ≠ 0) :
    (initializedResidualField M D hTime τ hτ hτT B δ hδ ξ hs α Cagree N hN κ hκ).ReflectionOdd := by
  let a := initializedProfiles M D τ hτ hτT B δ hδ ξ hs α
  let G := fun (i : ℕ) (_ : i ≤ N) =>
    initializedProfileWitness M D hTime τ hτ hτT B δ hδ ξ hs α i
  have H : ∀ i, i ≤ N → ProfileParity M.T (a i) :=
    fun i _ => initializedProfiles_parity M D hTime τ hτ hτT B δ hδ ξ hs α
      eM hSym hF hDM hBH i
  have ha : a 0 = 0 := profiles_zero _ _
  have htail := ProfileRegularity.residualTail_odd M.T_pos G H
    (joinedSourceCoefficientData period M D τ hτ hτT B hTime)
    (joinedSourceCoefficientEven period M D τ hτ hτT B hF hDM) ha κ
  intro t
  exact (ProfileRegularity.tailSumField M.T_pos G
    (joinedSourceCoefficientData period M D τ hτ hτT B hTime) ha κ).reflection_neg_of_raw_odd
    t (htail t)


-- @@ L204-211 verbatim
theorem initializedNormalizedResidualField_odd (Cagree : SourceCoefficientAgreement M D)
    (N : ℕ) (hN : 1 ≤ N) (k : ℝ) (hk : 4 ≤ k) :
    (initializedNormalizedResidualField M D hTime τ hτ hτT B δ hδ ξ hs α
      Cagree N hN k hk).ReflectionOdd := by
  have h := initializedResidualField_odd M D hTime τ hτ hτT B δ hδ ξ hs α
    eM hSym hF hDM hBH Cagree N hN k⁻¹ (inv_ne_zero (by linarith))
  exact ((h.multiply (joinedSourceCoefficientData period M D τ hτ hτT B hTime).inverse
    (joinedSourceCoefficientEven period M D τ hτ hτT B hF hDM).inverse).smul k).changeTime hTime


-- @@ L213-213 verbatim
end EulerPacketTerminalDatum
