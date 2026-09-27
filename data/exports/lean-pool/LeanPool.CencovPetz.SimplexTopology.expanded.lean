/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module

public import LeanPool.CencovPetz.Simplex
import Mathlib.Algebra.Order.Algebra
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Analysis.Complex.Order
import Mathlib.Tactic.ContinuousFunctionalCalculus



-- @@ L15-27 verbatim
/-!
# `CencovPetz.SimplexTopology`

Topology on the finite open simplex.

We use the topology induced by the coordinate map `p ↦ p.p : Simplex α → (α → ℝ)`.  Since the
proof fields of `Simplex` are propositions, this agrees with the usual subspace topology.

## Main results

- `CencovPetz.Simplex.continuous_p`
- `CencovPetz.Simplex.continuous_eval`
-/


-- @@ L29-29 verbatim
@[expose] public section


-- @@ L31-31 verbatim
namespace LeanPool.CencovPetz

-- @@ L32-32 verbatim
open scoped BigOperators


-- @@ L34-34 verbatim
universe u


-- @@ L36-36 verbatim
variable {α : Type u} [Fintype α]


-- @@ L38-38 verbatim
namespace Simplex


-- @@ L40-41 verbatim
instance : TopologicalSpace (Simplex α) :=
  TopologicalSpace.induced (fun p : Simplex α => p.p) inferInstance


-- @@ L43-44 verbatim
lemma continuous_p : Continuous fun p : Simplex α => p.p :=
  continuous_induced_dom


-- @@ L46-47 verbatim
lemma continuous_eval (a : α) : Continuous fun p : Simplex α => p.p a :=
  (continuous_apply a).comp continuous_p


-- @@ L49-49 verbatim
end Simplex

-- @@ L50-50 verbatim
end LeanPool.CencovPetz
