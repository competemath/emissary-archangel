/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketForwardSuccessor
public import LeanPool.NavierStokesAndEuler.Euler.BaseInductionStage
import LeanPool.NavierStokesAndEuler.Euler.BaseFirstPacketSupport
import LeanPool.NavierStokesAndEuler.Euler.ParentChoiceInitialSupport


-- @@ L14-15 verbatim
/-! The finite initial base used by the limiting construction is the
actual first normal forward packet over the actual first packet state. -/


-- @@ L17-17 verbatim
@[expose] public section



-- @@ L20-20 verbatim
noncomputable section


-- @@ L22-22 verbatim
namespace EulerPacketInduction.Stage


-- @@ L24-26 verbatim
open Set EulerSmoothLimit EulerParentPacketFrames EulerPacketSupport
  EulerPacketInductionScales EulerPacketLowConstants EulerParentNeighborThreshold
  EulerPacketSourceScaleSequence


-- @@ L28-29 verbatim
variable {q : ℕ} {B : ℝ} {S : Scales (q : ℝ) B} (P : Stage S 0)
  (hq : requiredExponent ≤ q) (hB : commonThreshold gradientConstant hessianConstant ≤ B)


-- @@ L31-37 verbatim
theorem forwardNext_initial_support
    (hP : tsupport (fun x => P.state.evolution.velocity (0, x)) ⊆ Metric.closedBall 0 2) :
    tsupport (fun x => (P.forwardNext hq hB).state.evolution.velocity (0, x)) ⊆
      Metric.closedBall 0 2 :=
  GeometryForwardChoice.initial_support (P.forwardInput hq hB) P.restrictedState
    (frequency S.J S.X 0) (S.normal_frequency 0) (supportScale S.J S.X 1)
    (S.support_pos 1) (S.support_one 1) (P.chooseForward hq hB) symmetric hP


-- @@ L39-49 verbatim
theorem forwardNext_initial_field_support
    (hP : tsupport (fun x => P.state.evolution.velocity (0, x)) ⊆ Metric.closedBall 0 2) :
    tsupport ((P.forwardNext hq hB).state.regularity.velocity
      (P.forwardNext hq hB).parent.zeroTime).field ⊆ Metric.closedBall 0 2 := by
  have he : ((P.forwardNext hq hB).state.regularity.velocity
      (P.forwardNext hq hB).parent.zeroTime).field =
      fun x => (P.forwardNext hq hB).state.evolution.velocity (0,x) :=
    funext (fun x => ((P.forwardNext hq hB).state.regularity.velocity_match
      (P.forwardNext hq hB).parent.zeroTime x).symm)
  rw [he]
  exact P.forwardNext_initial_support hq hB hP


-- @@ L51-51 verbatim
end EulerPacketInduction.Stage


-- @@ L53-53 verbatim
namespace EulerPacketInductionScales.Scales


-- @@ L55-55 verbatim
open Set EulerSmoothLimit EulerPacketLowConstants EulerParentNeighborThreshold


-- @@ L57-58 verbatim
variable {q : ℕ} {B : ℝ} (S : Scales (q : ℝ) B)
  (hq : requiredExponent ≤ q) (hB : commonThreshold gradientConstant hessianConstant ≤ B)


-- @@ L60-63 verbatim
theorem firstForwardStage_initial_support :
    tsupport (fun x => (S.firstStage.forwardNext hq hB).state.evolution.velocity (0,x)) ⊆
      Metric.closedBall 0 2 :=
  S.firstStage.forwardNext_initial_support hq hB S.firstStage_initial_support


-- @@ L65-68 verbatim
theorem firstForwardStage_initial_field_support :
    tsupport ((S.firstStage.forwardNext hq hB).state.regularity.velocity
      (S.firstStage.forwardNext hq hB).parent.zeroTime).field ⊆ Metric.closedBall 0 2 :=
  S.firstStage.forwardNext_initial_field_support hq hB S.firstStage_initial_support


-- @@ L70-70 verbatim
end EulerPacketInductionScales.Scales
