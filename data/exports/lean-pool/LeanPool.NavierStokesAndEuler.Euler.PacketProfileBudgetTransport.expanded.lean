/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketProfileBudget


-- @@ L11-11 verbatim
/-! Quantitative profile estimates do not depend on the particular regularity witness. -/


-- @@ L13-13 verbatim
@[expose] public section



-- @@ L16-16 verbatim
namespace EulerPacketCylinderField.ProfileBudget


-- @@ L18-18 verbatim
open Set EulerSmoothLimit EulerPacketProfileRecursion EulerPacketTimeProfile


-- @@ L20-22 verbatim
variable {P T : ℝ} [Fact (0 < P)] {hT : 0 ≤ T} {support support' : Set Space}
  {a b : Profile} {G : ProfileRegularity P T hT support a}
  {S : Scales (Icc (0 : ℝ) T)} {R : ℝ} {p : ℕ}


-- @@ L24-27 verbatim
theorem of_profile_eq (hG : ProfileBudget G S R p) (hTpos : 0 < T)
    (H : ProfileRegularity P T hT support' b) (he : a = b) : ProfileBudget H S R p := by
  subst b
  exact hG.transfer hTpos H


-- @@ L29-29 verbatim
end EulerPacketCylinderField.ProfileBudget
