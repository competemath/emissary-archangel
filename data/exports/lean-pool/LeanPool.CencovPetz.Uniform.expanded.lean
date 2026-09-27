/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module

public import Mathlib.Data.Fintype.Card
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic



-- @@ L14-27 verbatim
/-!
# `CencovPetz.Uniform`

Minimal facts about the uniform distribution on a finite type.

Mathlib already provides uniform distributions as probability measures / `PMF`s. This file keeps a
lightweight `α → ℝ` “density” version that is sometimes convenient in finite-dimensional
calculations.

## Main definitions

- `uniformDistribution`: the constant function `1 / |α|`.
- `IsUniform`: predicate asserting a function is uniform.
-/


-- @@ L29-29 verbatim
@[expose] public section


-- @@ L31-31 verbatim
namespace LeanPool.CencovPetz


-- @@ L33-33 verbatim
open scoped BigOperators


-- @@ L35-35 verbatim
universe u


-- @@ L37-39 verbatim
/-- Uniform distribution over a finite type `α`, defined as `1 / |α|` for all elements. -/
noncomputable abbrev uniformDistribution {α : Type u} [Fintype α] : α → ℝ :=
  Function.const α (1 / (Fintype.card α : ℝ))


-- @@ L41-43 verbatim
/-- Predicate asserting that a function agrees with `uniformDistribution`. -/
def IsUniform {α : Type u} [Fintype α] (p : α → ℝ) : Prop :=
  ∀ a : α, p a = uniformDistribution (α := α) a


-- @@ L45-48 verbatim
/-- The uniform distribution sums to `1`. -/
lemma uniformDistribution_sum_one {α : Type u} [Fintype α] [Nonempty α] :
    (∑ a : α, uniformDistribution (α := α) a) = 1 := by
  simp_all


-- @@ L50-50 verbatim
end LeanPool.CencovPetz
