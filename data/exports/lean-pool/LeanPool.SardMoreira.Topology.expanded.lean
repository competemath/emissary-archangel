/-
Copyright (c) 2026 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
module

public import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.NhdsWithin


-- @@ L11-13 verbatim
/-!
# LeanPool.SardMoreira.Topology
-/


-- @@ L15-15 verbatim
@[expose] public section


-- @@ L17-17 verbatim
open Filter

-- @@ L18-18 verbatim
open scoped Topology


-- @@ L20-25 verbatim
theorem eventually_nhdsWithin_nhds {X : Type*} [TopologicalSpace X] {U : Set X} (hU : IsOpen U)
    {p : X → Prop} {x : X} :
    (∀ᶠ y in 𝓝[U] x, ∀ᶠ z in 𝓝 y, p z) ↔ ∀ᶠ y in 𝓝[U] x, p y := by
  conv_rhs => rw [← eventually_eventually_nhdsWithin]
  refine eventually_congr <| eventually_mem_nhdsWithin.mono fun y hy ↦ ?_
  rw [hU.nhdsWithin_eq hy]
