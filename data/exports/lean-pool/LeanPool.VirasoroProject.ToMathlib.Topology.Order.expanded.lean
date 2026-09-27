/-
Copyright (c) 2026 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
module

public import Mathlib.Topology.Order


-- @@ L10-12 verbatim
/-!
# LeanPool.VirasoroProject.ToMathlib.Topology.Order
-/


-- @@ L14-14 verbatim
@[expose] public section


-- @@ L16-16 verbatim
section


-- @@ L18-18 verbatim
open Filter

-- @@ L19-19 verbatim
open scoped Topology


-- @@ L21-25 verbatim
lemma DiscreteTopology.tendsto_nhds_iff_eventually_eq
    {X : Type*} [TopologicalSpace X] [DiscreteTopology X] {ι : Type*} {F : Filter ι}
    (f : ι → X) (x : X) :
    F.Tendsto f (𝓝 x) ↔ F.Eventually (fun i ↦ f i = x) := by
  simp_all


-- @@ L27-27 verbatim
end
