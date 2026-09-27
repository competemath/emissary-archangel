/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module

public import LeanPool.CencovPetz.Splitting
public import LeanPool.CencovPetz.UniformSimplex
import Mathlib.Algebra.Order.Algebra
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Analysis.Complex.Order
import Mathlib.Tactic.ContinuousFunctionalCalculus



-- @@ L16-28 verbatim
/-!
# `CencovPetz.SplittingUniform`

If a simplex point `p` has coordinates proportional to a fiber-multiplicity function `m : α → ℕ`,
then the fiberwise splitting Markov morphism `α → Σ a, Fin (m a)` pushes `p` forward to the
uniform distribution on the split target.

This is one of the standard reduction steps in finite Čencov/Chentsov uniqueness arguments.

## Main result

- `CencovPetz.MarkovMorphism.split_pushforward_eq_uniform_of_apply_eq_div_card`
-/


-- @@ L30-30 verbatim
@[expose] public section


-- @@ L32-32 verbatim
namespace LeanPool.CencovPetz

-- @@ L33-33 verbatim
open scoped BigOperators


-- @@ L35-35 verbatim
universe u


-- @@ L37-37 verbatim
namespace Simplex


-- @@ L39-39 verbatim
variable {α : Type u} [Fintype α]


-- @@ L41-51 verbatim
/-- A simplex point whose coordinates are proportional to a natural multiplicity function.

Such points become uniform after applying the fiberwise splitting Markov morphism
`α → Σ a, Fin (m a)`. This is the standard “rational-point” reduction step in finite Čencov/Chentsov
arguments.
-/
def IsSplitRepresentable (p : Simplex α) : Prop :=
  ∃ m : α → ℕ,
    (∀ a, 0 < m a) ∧
      ∀ a,
        p.p a = (m a : ℝ) / (Fintype.card (MarkovMorphism.SplitTarget (α := α) m) : ℝ)


-- @@ L53-53 verbatim
end Simplex


-- @@ L55-55 verbatim
namespace MarkovMorphism


-- @@ L57-57 verbatim
variable {α : Type u} [Fintype α] [Nonempty α]


-- @@ L59-73 verbatim
lemma split_pushforward_eq_uniform_of_apply_eq_div_card (m : α → ℕ) (hm : ∀ a, 0 < m a)
    (p : Simplex α)
    (hp : ∀ a, p.p a = (m a : ℝ) / (Fintype.card (SplitTarget (α := α) m) : ℝ)) :
    letI : Nonempty (SplitTarget (α := α) m) := by
      classical
      rcases (inferInstance : Nonempty α) with ⟨a0⟩
      exact ⟨⟨a0, ⟨0, hm a0⟩⟩⟩
    (split (α := α) m hm).pushforward p = Simplex.uniform (α := SplitTarget (α := α) m) := by
  classical
  ext b
  rcases b with ⟨a, i⟩
  have hm0 : (m a : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (hm a))
  rw [split_pushforward_apply (α := α) (m := m) (hm := hm) (p := p) (a := a) (i := i)]
  simp [Simplex.uniform_apply, hp a, hm0, div_eq_mul_inv, mul_comm]


-- @@ L75-75 verbatim
end MarkovMorphism

-- @@ L76-76 verbatim
end LeanPool.CencovPetz
