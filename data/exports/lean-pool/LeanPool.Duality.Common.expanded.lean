/-
Copyright (c) 2026 Martin Dvorak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Dvorak
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Group.Defs


-- @@ L13-15 verbatim
/-!
# LeanPool.Duality.Common
-/


-- @@ L17-17 verbatim
@[expose] public section


-- @@ L19-19 verbatim
section finset_sums

-- @@ L20-20 verbatim
variable {α β : Type*}


-- @@ L22-29 verbatim
lemma Finset.subtype_univ_sum_eq_subtype_univ_sum {p q : α → Prop} (hpq : p = q)
    [Fintype { a : α // p a }] [Fintype { a : α // q a }] [AddCommMonoid β]
    {f : { a : α // p a } → β} {g : { a : α // q a } → β}
    (hfg : ∀ a : α, ∀ hpa : p a, ∀ hqa : q a, f ⟨a, hpa⟩ = g ⟨a, hqa⟩) :
    Finset.univ.sum f = Finset.univ.sum g := by
  subst hpq
  convert rfl
  simp_all


-- @@ L31-42 verbatim
lemma Finset.univ_sum_of_zero_when_not [Fintype α] [AddCommMonoid β]
    {f : α → β} (p : α → Prop) [DecidablePred p] (hpf : ∀ a : α, ¬(p a) → f a = 0) :
    Finset.univ.sum f = Finset.univ.sum (fun a : { a : α // p a } => f a.val) := by
  classical
  trans (Finset.univ.filter p).sum f
  · symm
    apply Finset.sum_subset_zero_on_sdiff
    · apply Finset.subset_univ
    · simpa
    · simp_all
  · apply Finset.sum_subtype
    simp


-- @@ L44-44 verbatim
end finset_sums



-- @@ L47-47 verbatim
section logic_with_neq

-- @@ L48-48 verbatim
variable {P Q : Prop}


-- @@ L50-50 verbatim
lemma or_of_neq (hpq : P ≠ Q) : P ∨ Q := by tauto


-- @@ L52-52 verbatim
lemma not_and_of_neq (hpq : P ≠ Q) : ¬(P ∧ Q) := by tauto


-- @@ L54-54 verbatim
lemma neq_of_iff_neg (hpq : P ↔ ¬Q) : P ≠ Q := by tauto


-- @@ L56-56 verbatim
lemma neg_iff_neg (hpq : P ↔ Q) : ¬P ↔ ¬Q := by tauto


-- @@ L58-58 verbatim
end logic_with_neq



-- @@ L61-61 verbatim
section notations


-- @@ L63-64 verbatim
/-- Writing `↓t` is slightly more general than writing `Function.const _ t`. -/
notation:max "↓"t:arg => (fun _ => t)


-- @@ L66-67 verbatim
/-- The left-to-right direction of `↔`. -/
postfix:max ".→" => Iff.mp


-- @@ L69-70 verbatim
/-- The right-to-left direction of `↔`. -/
postfix:max ".←" => Iff.mpr



-- @@ L73-73 verbatim
end notations



-- @@ L76-76 verbatim
section miscellaneous


-- @@ L78-79 verbatim
lemma le_of_nneg_add {α : Type*} [AddCommGroup α] [PartialOrder α] [IsOrderedAddMonoid α]
    {a b c : α} (habc : a + b = c) (ha : 0 ≤ a) : b ≤ c := by aesop


-- @@ L81-83 verbatim
/-- `change h to t` rewrites the hypothesis `h` to the definitionally equal type `t`. -/
@[tactic_alt Lean.Parser.Tactic.change]
macro "change " h:ident " to " t:term : tactic => `(tactic| change $t at $h:ident)


-- @@ L85-87 verbatim
/-- `aeply t` is shorthand for `intro <;> apply t <;> aesop`, useful for proving universally
    quantified goals where each instance is dispatched by `aesop` after applying `t`. -/
macro "aeply" t:term : tactic => `(tactic| intro <;> apply $t <;> aesop)


-- @@ L89-89 verbatim
end miscellaneous
