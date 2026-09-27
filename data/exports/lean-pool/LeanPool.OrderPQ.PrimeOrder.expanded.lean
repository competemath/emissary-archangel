/-
Copyright (c) 2026 Scott Harper, Peiran Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Harper, Peiran Wu
-/
module

public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.GroupTheory.Subgroup.Simple
public import Mathlib.SetTheory.Cardinal.Finite
import LeanPool.OrderPQ.IsCyclic
import LeanPool.OrderPQ.MonoidHom
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Positivity.Finset


-- @@ L17-19 verbatim
/-!
# LeanPool.OrderPQ.PrimeOrder
-/


-- @@ L21-21 verbatim
@[expose] public section


-- @@ L23-25 verbatim
lemma ne_iff_eq_of_or_and_ne {α : Type*} {a b c : α} (h1 : a = b ∨ a = c) (h2 : b ≠ c) :
    a ≠ b ↔ a = c :=
  ⟨h1.resolve_left, fun h3 => ne_of_eq_of_ne h3 h2.symm⟩


-- @@ L27-27 verbatim
namespace IsSimpleGroup


-- @@ L29-29 verbatim
variable {G : Type*} [Group G] [IsSimpleGroup G]


-- @@ L31-33 verbatim
@[to_additive]
lemma ne_bot_iff_eq_top_of_normal {H : Subgroup G} (h : H.Normal) : H ≠ ⊤ ↔ H = ⊥ := by
  exact ne_iff_eq_of_or_and_ne (eq_bot_or_eq_top_of_normal H h).symm bot_ne_top.symm


-- @@ L35-39 verbatim
@[to_additive]
lemma monoidHom_injective_or_eq_one {H : Type*} [Group H] (φ : G →* H) :
    Function.Injective φ ∨ φ = 1 := by
  rw [← MonoidHom.ker_eq_bot_iff φ, ← MonoidHom.ker_eq_top_iff (f := φ)]
  exact eq_bot_or_eq_top_of_normal φ.ker φ.normal_ker


-- @@ L41-45 verbatim
@[to_additive]
lemma monoidHom_ne_one_iff_injective {H : Type*} [Group H] (φ : G →* H) :
    φ ≠ 1 ↔ Function.Injective φ := by
  rw [← MonoidHom.ker_eq_bot_iff φ, ne_eq, ← MonoidHom.ker_eq_top_iff (f := φ)]
  exact ne_bot_iff_eq_top_of_normal φ.normal_ker


-- @@ L47-47 verbatim
end IsSimpleGroup


-- @@ L49-49 verbatim
section GroupsOfPrimeOrder


-- @@ L51-51 verbatim
variable {p : ℕ} [hp : Fact p.Prime]

-- @@ L52-52 verbatim
variable {G : Type*} [Group G] (h : Nat.card G = p) {H : Subgroup G}

-- @@ L53-53 verbatim
include h


-- @@ L55-60 verbatim
@[to_additive]
theorem Subgroup.eq_bot_or_eq_top_of_prime_card' :
    H = ⊥ ∨ H = ⊤ := by
  have := Finite.of_card_eq_neZero h
  rw [eq_bot_iff_card, ← card_eq_iff_eq_top, ← Nat.dvd_prime (h ▸ hp.elim)]
  exact card_subgroup_dvd_card H


-- @@ L62-66 verbatim
@[to_additive]
theorem IsSimpleGroup.of_prime_card :
    IsSimpleGroup G := by
  have := Nontrivial.of_card_eq_prime h
  exact ⟨fun H _ => H.eq_bot_or_eq_top_of_prime_card' h⟩


-- @@ L68-71 verbatim
@[to_additive]
lemma Subgroup.ne_top_iff_eq_bot_of_prime_card : H ≠ ⊤ ↔ H = ⊥ := by
  have := Nontrivial.of_card_eq_prime h
  refine ne_iff_eq_of_or_and_ne (eq_bot_or_eq_top_of_prime_card' h).symm bot_ne_top.symm


-- @@ L73-73 verbatim
variable {x : G} (hx : x ≠ 1)

-- @@ L74-74 verbatim
include hx


-- @@ L76-78 verbatim
@[to_additive]
lemma Subgroup.zpowers_eq_top_of_ne_one : Subgroup.zpowers x = ⊤ :=
  eq_bot_or_eq_top_of_prime_card' h |>.resolve_left <| hx ∘ zpowers_eq_bot.mp


-- @@ L80-82 verbatim
@[to_additive]
lemma MonoidHom.end_eq_of_apply_eq (f₁ f₂ : G →* G) (h2 : f₁ x = f₂ x) : f₁ = f₂ :=
  MonoidHom.eq_of_apply_eq (Subgroup.zpowers_eq_top_of_ne_one h hx ▸ Subgroup.mem_top) _ _ h2


-- @@ L84-86 verbatim
@[to_additive]
lemma MulAut.eq_of_apply_eq (f₁ f₂ : G ≃* G) (h2 : f₁ x = f₂ x) : f₁ = f₂ :=
  MulEquiv.eq_of_apply_eq (Subgroup.zpowers_eq_top_of_ne_one h hx ▸ Subgroup.mem_top) _ _ h2


-- @@ L88-88 verbatim
end GroupsOfPrimeOrder
