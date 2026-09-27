/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketPrimarySourceRegularity
public import LeanPool.NavierStokesAndEuler.Euler.PacketJoinedSourceOperators
public import LeanPool.NavierStokesAndEuler.Euler.PacketPrimaryRegularity


-- @@ L13-13 verbatim
/-! The genuine endpoint primary supplies all qualitative inputs to the joined recursion. -/


-- @@ L15-15 verbatim
@[expose] public section



-- @@ L18-18 verbatim
noncomputable section


-- @@ L20-20 verbatim
namespace EulerPacketCylinderField


-- @@ L22-22 verbatim
open Set EulerSmoothLimit EulerPacketPointJets EulerPacketProfileRecursion

-- @@ L23-23 verbatim
open scoped ContDiff


-- @@ L25-30 verbatim
variable (P : ℝ) [Fact (0 < P)] (M : EulerMeanPacketProvider.Data)
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (D : EulerTransversePacketProvider.Data U) (hTime : M.T = D.T)
  (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T)
  (B : EulerTransversePacketProvider.HistoryData (D.initial τ hτ hτT.le))
  (Y : EulerTransversePacketProvider.InitialData P D)


-- @@ L32-36 verbatim
/-- Joined terminal primary, constructed using `primaryProfile`. -/
def joinedTerminalPrimary : Profile :=
  primaryProfile (joinedSourceOperators P M D τ hτ hτT B)
    (EulerTransversePacketPrimary.vector τ hτ hτT B Y)
    (EulerTransversePacketPrimary.scalar τ hτ hτT B Y)


-- @@ L38-43 verbatim
/-- Joined terminal primary witness as an element of `ProfileRegularity P M.T M.T_pos.le
D.support (joinedTerminalPrimary P M D τ hτ hτT B Y)`. -/
def joinedTerminalPrimaryWitness :
    ProfileRegularity P M.T M.T_pos.le D.support (joinedTerminalPrimary P M D τ hτ hτT B Y) :=
  (EulerTransversePacketPrimary.profileRegularity τ hτ hτT B Y
    (joinedSourceOperators P M D τ hτ hτT B) rfl).changeTime hTime.symm M.T_pos.le


-- @@ L45-45 verbatim
theorem joinedTerminalPrimary_mean : (joinedTerminalPrimary P M D τ hτ hτT B Y).mean=0 := rfl


-- @@ L47-52 verbatim
include hTime in
theorem joinedTerminalPrimary_tangent (t : Icc (0 : ℝ) M.T) (x : Space) (θ : ℝ) :
    inner ℝ (D.normalField (t,(x,θ))) ((joinedTerminalPrimary P M D τ hτ hτT B Y).high (t,(x,θ)))=0
        := by
  let td : Icc (0 : ℝ) D.T := ⟨t.val,by simpa only [← hTime] using t.property⟩
  exact EulerTransversePacketPrimary.vector_tangent τ hτ hτT B Y td x θ


-- @@ L54-57 verbatim
theorem joinedTerminalPrimary_pressure_smooth (t : ℝ) :
    ContDiff ℝ ∞ (fun y : Space × ℝ =>
      (joinedTerminalPrimary P M D τ hτ hτT B Y).highPressure (t,y)) :=
  EulerTransversePacketPrimary.scalar_smooth τ hτ hτT B Y t


-- @@ L59-74 verbatim
include hTime in
theorem joinedTerminalPrimary_equation (t : Icc (0 : ℝ) M.T) (x : Space) (θ : ℝ) :
    linearPart (D.strain (t,(x,θ)))
      (slicedJet (Icc (0 : ℝ) M.T) (joinedTerminalPrimary P M D τ hτ hτT B Y).high (t,(x,θ))) +
    fastPressure (D.normalField (t,(x,θ)))
      (pressureJet (joinedTerminalPrimary P M D τ hτ hτT B Y).highPressure (t,(x,θ)))=0 := by
  let td : Icc (0 : ℝ) D.T := ⟨t.val,by simpa only [← hTime] using t.property⟩
  change linearPart (D.strain (t,(x,θ)))
    (slicedJet (Icc (0 : ℝ) M.T) (EulerTransversePacketPrimary.vector τ hτ hτT B Y) (t,(x,θ))) +
    fastPressure (D.normalField (t,(x,θ)))
      (pressureJet (EulerTransversePacketPrimary.scalar τ hτ hτT B Y) (t,(x,θ)))=0
  have hjet := congrArg (fun I : Set ℝ => slicedJet I
    (EulerTransversePacketPrimary.vector τ hτ hτT B Y) (t.val,(x,θ)))
    (congrArg (fun s : ℝ => Icc (0 : ℝ) s) hTime)
  rw [hjet]
  exact EulerTransversePacketPrimary.jet_equation τ hτ hτT B Y td x θ


-- @@ L76-76 verbatim
end EulerPacketCylinderField
