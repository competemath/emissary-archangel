/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module

public import LeanPool.CencovPetz.Simplex
public import LeanPool.CencovPetz.Uniform
import Mathlib.Algebra.Order.Algebra
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Analysis.Complex.Order
import Mathlib.Tactic.ContinuousFunctionalCalculus



-- @@ L16-20 verbatim
/-!
# `CencovPetz.UniformSimplex`

Package the uniform distribution on a finite type as a point of the open simplex.
-/


-- @@ L22-22 verbatim
@[expose] public section


-- @@ L24-24 verbatim
namespace LeanPool.CencovPetz

-- @@ L25-25 verbatim
open scoped BigOperators


-- @@ L27-27 verbatim
variable {α : Type*} [Fintype α] [Nonempty α]


-- @@ L29-29 verbatim
namespace Simplex


-- @@ L31-39 verbatim
/-- The uniform point of the open simplex. -/
noncomputable def uniform : Simplex α where
  p := uniformDistribution (α := α)
  pos := by
    intro a
    have hcard : 0 < (Fintype.card α : ℝ) := by exact_mod_cast Fintype.card_pos
    simpa [uniformDistribution] using (one_div_pos.2 hcard)
  sum_eq_one := by
    exact uniformDistribution_sum_one (α := α)


-- @@ L41-43 verbatim
@[simp] lemma uniform_apply (a : α) :
    (uniform (α := α)).p a = 1 / (Fintype.card α : ℝ) :=
  rfl


-- @@ L45-45 verbatim
end Simplex

-- @@ L46-46 verbatim
end LeanPool.CencovPetz
