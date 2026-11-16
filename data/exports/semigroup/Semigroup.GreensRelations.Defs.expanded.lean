/-
Copyright (c) Re'em Melamed-Katz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Re'em Melamed-Katz
-/
import Mathlib.Algebra.Divisibility.Basic


-- @@ L8-36 verbatim
/-!
# Green's Relations Definitions


This file contains the fundamental definitions of Green's relations (L, R, H, D, and J)
on a general semigroup.

## Main definitions

* `RightDvd`: Right divisibility in a semigroup (from PR #40860's Divisibility changes).
* `IsGreenLeftDvd`: Left divisibility in a semigroup.
* `IsGreenRightDvd`: Right divisibility in a semigroup.
* `IsGreenJRel`: The basic step of being a two-sided multiple.
* `IsGreenL`: Green's L relation (generating the same left ideal).
* `IsGreenR`: Green's R relation (generating the same right ideal).
* `IsGreenH`: Green's H relation (the intersection of L and R).
* `IsGreenD`: Green's D relation (the composition of L and R).
* `IsGreenJ`: Green's J relation (generating the same two-sided ideal).

## Notation

The `GreensRelations` scoped namespace provides the textbook infix notation `a ≤𝓛 b`,
`a ≤𝓡 b`, `a ≤𝓙 b` for the divisibility preorders and `a 𝓛 b`, `a 𝓡 b`, `a 𝓗 b`,
`a 𝓓 b`, `a 𝓙 b` for the equivalence relations.

## References

* [T. Colcombet, *The Factorization Forest Theorem*][colcombet2008]
-/


-- @@ L38-38 verbatim
section RightDvd


-- @@ L40-40 verbatim
variable {α : Type*} [Semigroup α] {a b c : α}


-- @@ L42-44 verbatim
/-- Right divisibility relation. `RightDvd a b` means `a` right-divides `b`,
i.e., `∃ c, b = c * a`. -/
def RightDvd (a b : α) : Prop := ∃ c, b = c * a


-- @@ L46-49 verbatim
/-- Introduction rule for right divisibility: from `c * a = b` conclude that `a`
right-divides `b`. -/
theorem RightDvd.intro (c : α) (h : c * a = b) : RightDvd a b :=
  Exists.intro c h.symm


-- @@ L51-51 verbatim
alias rightDvd_of_mul_left_eq := RightDvd.intro


-- @@ L53-56 verbatim
/-- A right divisibility yields a witness: if `a` right-divides `b` then `b = c * a`
for some `c`. -/
theorem exists_eq_mul_left_of_rightDvd (h : RightDvd a b) : ∃ c, b = c * a :=
  h


-- @@ L58-61 verbatim
/-- Unfolding lemma for right divisibility: `RightDvd a b` iff `b = c * a` for
some `c`. -/
theorem rightDvd_def : RightDvd a b ↔ ∃ c, b = c * a :=
  Iff.rfl


-- @@ L63-63 verbatim
alias rightDvd_iff_exists_eq_mul_left := rightDvd_def


-- @@ L65-68 verbatim
/-- Elimination principle for right divisibility: to prove `P` from `RightDvd a b`,
prove it for every factorization `b = c * a`. -/
theorem RightDvd.elim {P : Prop} {a b : α} (H₁ : RightDvd a b) (H₂ : ∀ c, b = c * a → P) : P :=
  Exists.elim H₁ H₂


-- @@ L70-73 verbatim
/-- Right divisibility is transitive. -/
@[trans]
theorem rightDvd_trans : RightDvd a b → RightDvd b c → RightDvd a c
  | ⟨d, h₁⟩, ⟨e, h₂⟩ => ⟨e * d, h₁ ▸ h₂.trans <| (mul_assoc e d a).symm⟩


-- @@ L75-77 verbatim
/-- Transitivity of `RightDvd` for use in `calc` blocks. -/
instance : IsTrans α RightDvd :=
  ⟨fun _ _ _ => rightDvd_trans⟩


-- @@ L79-82 verbatim
/-- `a` right-divides any left multiple `b * a` of itself. -/
@[simp]
theorem rightDvd_mul_left (a b : α) : RightDvd a (b * a) :=
  RightDvd.intro b rfl


-- @@ L84-87 verbatim
/-- Right divisibility is preserved by further left multiplication: if `a`
right-divides `b`, then `a` right-divides `c * b`. -/
theorem rightDvd_mul_of_rightDvd_right (h : RightDvd a b) (c : α) : RightDvd a (c * b) :=
  rightDvd_trans h (rightDvd_mul_left b c)


-- @@ L89-89 verbatim
alias RightDvd.mul_left := rightDvd_mul_of_rightDvd_right


-- @@ L91-93 verbatim
/-- If a left multiple `b * a` right-divides `c`, then so does `a` itself. -/
theorem rightDvd_of_mul_left_rightDvd (h : RightDvd (b * a) c) : RightDvd a c :=
  rightDvd_trans (rightDvd_mul_left a b) h


-- @@ L95-100 verbatim
/-- Right divisibility is preserved by right multiplication on both sides: if `b`
right-divides `c`, then `b * a` right-divides `c * a`. -/
theorem mul_rightDvd_mul_right (a : α) (h : RightDvd b c) : RightDvd (b * a) (c * a) := by
  obtain ⟨d, rfl⟩ := h
  use d
  rw [mul_assoc]


-- @@ L102-102 verbatim
end RightDvd


-- @@ L104-104 verbatim
variable {S : Type*} [Semigroup S]


-- @@ L106-112 verbatim
/-!
Each relation is declared together with its scoped infix notation, following the
standard textbook notation: `a ≤𝓛 b`, `a ≤𝓡 b`, `a ≤𝓙 b` for the divisibility
preorders and `a 𝓛 b`, `a 𝓡 b`, `a 𝓗 b`, `a 𝓓 b`, `a 𝓙 b` for the equivalences.
The notation lives in the `GreensRelations` namespace and is used throughout the
definitions below.
-/


-- @@ L114-116 verbatim
/-- `IsGreenLeftDvd a b` means that `a` is a left multiple of `b`,
  i.e., `a = b` or `a = z * b`. -/
abbrev IsGreenLeftDvd (a b : S) : Prop := a = b ∨ RightDvd b a


-- @@ L118-118 verbatim
@[inherit_doc] scoped[GreensRelations] infix:50 " ≤𝓛 " => IsGreenLeftDvd


-- @@ L120-122 verbatim
/-- `IsGreenRightDvd a b` means that `a` is a right multiple of `b`,
  i.e., `a = b` or `a = b * z`. -/
abbrev IsGreenRightDvd (a b : S) : Prop := a = b ∨ b ∣ a


-- @@ L124-124 verbatim
@[inherit_doc] scoped[GreensRelations] infix:50 " ≤𝓡 " => IsGreenRightDvd


-- @@ L126-136 verbatim
/-- `IsGreenJRel a b` represents the basic step of being a two-sided multiple.
  `a` is related to `b` if `a = b`, `a = u * b`, `a = b * v`, or `a = u * b * v`. -/
inductive IsGreenJRel (a b : S) : Prop
  /-- `a` and `b` are equal. -/
  | of_eq (h : a = b)
  /-- `a` is a left multiple of `b`. -/
  | mul_left (u : S) (h : a = u * b)
  /-- `a` is a right multiple of `b`. -/
  | mul_right (v : S) (h : a = b * v)
  /-- `a` is a two-sided multiple of `b`. -/
  | mul_both (u v : S) (h : a = u * b * v)


-- @@ L138-138 verbatim
@[inherit_doc] scoped[GreensRelations] infix:50 " ≤𝓙 " => IsGreenJRel


-- @@ L140-140 verbatim
open scoped GreensRelations


-- @@ L142-143 expanded
/-- Green's L relation: `a` and `b` generate the same left ideal. -/
abbrev IsGreenL (a b : S) : Prop :=
  IsGreenLeftDvd a b ∧ IsGreenLeftDvd b a


-- @@ L145-145 verbatim
@[inherit_doc] scoped[GreensRelations] infix:50 " 𝓛 " => IsGreenL


-- @@ L147-148 expanded
/-- Green's R relation: `a` and `b` generate the same right ideal. -/
abbrev IsGreenR (a b : S) : Prop :=
  IsGreenRightDvd a b ∧ IsGreenRightDvd b a


-- @@ L150-150 verbatim
@[inherit_doc] scoped[GreensRelations] infix:50 " 𝓡 " => IsGreenR


-- @@ L152-153 expanded
/-- Green's H relation: the intersection of Green's L and Green's R relations. -/
abbrev IsGreenH (a b : S) : Prop :=
  IsGreenL a b ∧ IsGreenR a b


-- @@ L155-155 verbatim
@[inherit_doc] scoped[GreensRelations] infix:50 " 𝓗 " => IsGreenH


-- @@ L157-159 expanded
/-- Green's D relation: the composition of Green's L and Green's R relations.
Here defined explicitly as the existence of an intermediate element `z`. -/
abbrev IsGreenD (a b : S) : Prop :=
  ∃ z, IsGreenL a z ∧ IsGreenR z b


-- @@ L161-161 verbatim
@[inherit_doc] scoped[GreensRelations] infix:50 " 𝓓 " => IsGreenD


-- @@ L163-164 expanded
/-- Green's J relation: `a` and `b` generate the same two-sided ideal. -/
abbrev IsGreenJ (a b : S) : Prop :=
  IsGreenJRel a b ∧ IsGreenJRel b a


-- @@ L166-166 verbatim
@[inherit_doc] scoped[GreensRelations] infix:50 " 𝓙 " => IsGreenJ
