/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module

public import LeanPool.CencovPetz.SplittingUniform
import Mathlib.Algebra.Order.Algebra
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Analysis.Complex.Order
import Mathlib.Tactic.ContinuousFunctionalCalculus



-- @@ L15-35 verbatim
/-!
# `CencovPetz.RationalPoint`

Common-denominator (“rational”) points of the finite open simplex.

The classical finite Čencov/Chentsov argument typically proves the scalar-multiple claim first at
the uniform point, then extends it to a dense family of points with rational coordinates by a
fiberwise splitting construction.

This file packages the notion of a common-denominator point and relates it to
`Simplex.IsSplitRepresentable`.

## Main definitions

- `CencovPetz.Simplex.IsRational`: `p(a) = m(a) / (∑ m)` for some `m : α → ℕ` with
  strictly positive coordinates.

## Main results

- `CencovPetz.Simplex.IsRational.isSplitRepresentable`
-/


-- @@ L37-37 verbatim
@[expose] public section


-- @@ L39-39 verbatim
namespace LeanPool.CencovPetz

-- @@ L40-40 verbatim
open scoped BigOperators


-- @@ L42-42 verbatim
universe u


-- @@ L44-44 verbatim
namespace MarkovMorphism


-- @@ L46-46 verbatim
variable {α : Type u} [Fintype α]


-- @@ L48-51 verbatim
lemma card_splitTarget (m : α → ℕ) :
    Fintype.card (SplitTarget (α := α) m) = ∑ a : α, m a := by
  classical
  simp [SplitTarget]


-- @@ L53-53 verbatim
end MarkovMorphism


-- @@ L55-55 verbatim
namespace Simplex


-- @@ L57-57 verbatim
variable {α : Type u} [Fintype α]


-- @@ L59-64 verbatim
/-- A simplex point whose coordinates have a finite common-denominator representation
`p(a) = m(a) / (∑ m)` for some strictly positive `m : α → ℕ`. -/
def IsRational (p : Simplex α) : Prop :=
  ∃ m : α → ℕ,
    (∀ a, 0 < m a) ∧
      ∀ a, p.p a = (m a : ℝ) / ((∑ a : α, m a : ℕ) : ℝ)


-- @@ L66-70 verbatim
lemma IsRational.isSplitRepresentable {p : Simplex α} (hp : IsRational (α := α) p) :
    IsSplitRepresentable (α := α) p := by
  rcases hp with ⟨m, hm, hp⟩
  refine ⟨m, hm, ?_⟩
  simp_all


-- @@ L72-72 verbatim
end Simplex

-- @@ L73-73 verbatim
end LeanPool.CencovPetz
