/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketStageRestriction
import LeanPool.NavierStokesAndEuler.Euler.PacketInductionScaleBounds


-- @@ L12-12 verbatim
/-! Physical estimates on the actual shortened parent state. -/


-- @@ L14-14 verbatim
@[expose] public section



-- @@ L17-17 verbatim
noncomputable section


-- @@ L19-19 verbatim
namespace EulerPacketInduction.Stage


-- @@ L21-23 verbatim
open Set Real EulerSmoothLimit EulerParentPacketFrames EulerTimeIntervalRestriction
  EulerPacketInductionScales EulerPacketSourceScaleSequence EulerPacketLowConstants
  EulerPacketBaseGuardScales


-- @@ L25-25 verbatim
variable {c B : ℝ} {S : Scales c B} {n : ℕ} (P : Stage S n)


-- @@ L27-30 verbatim
theorem restricted_gradient_bound (t : Icc (0 : ℝ) P.restrictedParent.T) (x : Space) :
    ‖fderiv ℝ (fun y => P.restrictedState.evolution.velocity (t,y)) x‖ ≤
      gradientConstant*previousShear S.J S.X n :=
  P.gradient_bound (initialInclusion P.parent.T P.nextHorizon P.nextHorizon_le t) x


-- @@ L32-35 verbatim
theorem restricted_hessian_bound (t : Icc (0 : ℝ) P.restrictedParent.T) (x : Space) :
    ‖fderiv ℝ (P.restrictedState.evolution.force t) x‖ ≤
      hessianConstant*previousShear S.J S.X n*olderShear S.J S.X n :=
  P.hessian_bound (initialInclusion P.parent.T P.nextHorizon P.nextHorizon_le t) x


-- @@ L37-42 verbatim
theorem restricted_horizon_reciprocal :
    P.restrictedParent.T⁻¹ ≤ 12/baseHorizon S.J S.X := by
  have hp := div_pos (baseHorizon_pos S.J S.j_one S.x_pos) (by norm_num : (0 : ℝ) < 12)
  have h := one_div_le_one_div_of_le hp P.nextHorizon_common.le
  change P.nextHorizon⁻¹ ≤ 12/baseHorizon S.J S.X
  simpa only [one_div,inv_div] using h


-- @@ L44-44 verbatim
end EulerPacketInduction.Stage
