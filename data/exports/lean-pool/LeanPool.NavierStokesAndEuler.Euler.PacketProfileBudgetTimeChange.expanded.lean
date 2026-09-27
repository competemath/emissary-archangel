/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketBudgetTimeChange
public import LeanPool.NavierStokesAndEuler.Euler.PacketPrimaryRegularity
public import LeanPool.NavierStokesAndEuler.Euler.PacketProfileBudget


-- @@ L13-13 verbatim
/-! Profile budgets and their actual path witnesses transport across equal time endpoints. -/


-- @@ L15-15 verbatim
@[expose] public section



-- @@ L18-18 verbatim
noncomputable section


-- @@ L20-20 verbatim
namespace EulerPacketCylinderField.ProfileBudget


-- @@ L22-22 verbatim
open Set EulerSmoothLimit EulerPacketProfileRecursion EulerPacketTimeProfile


-- @@ L24-30 verbatim
theorem changeTime {P T T' : ℝ} [Fact (0 < P)] {hT : 0 ≤ T} {support : Set Space}
    {a : Profile} {G : ProfileRegularity P T hT support a}
    {S : Scales (Icc (0 : ℝ) T)} {R : ℝ} {p : ℕ}
    (B : ProfileBudget G S R p) (h : T = T') (hT' : 0 ≤ T') :
    ProfileBudget (G.changeTime h hT') (S.changeTime h) R p := by
  subst T'
  exact B


-- @@ L32-32 verbatim
end EulerPacketCylinderField.ProfileBudget


-- @@ L34-34 verbatim
namespace EulerPacketTimeProfile.Scales


-- @@ L36-36 verbatim
open Set EulerPacketCylinderField


-- @@ L38-41 verbatim
theorem growth_changeTime {T T' : ℝ} (S : Scales (Icc (0 : ℝ) T)) (h : T = T') :
    (S.changeTime h).growth = timeProfileChange S.growth h := by
  subst T'
  rfl


-- @@ L43-43 verbatim
end EulerPacketTimeProfile.Scales
