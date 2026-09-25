/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Card

-- @@ L10-14 verbatim
/-!

# Creation and annihilation parts of fields

-/


-- @@ L16-16 verbatim
@[expose] public section


-- @@ L18-24 verbatim
/-- The type `CreateAnnihilate` is the type containing two elements `create` and `annihilate`.
  This type is used to specify if an operator is a creation, or annihilation, operator
  or the sum thereof or integral thereof etc. -/
inductive CreateAnnihilate where
  | create : CreateAnnihilate
  | annihilate : CreateAnnihilate
deriving Inhabited, BEq, DecidableEq


-- @@ L26-26 verbatim
namespace CreateAnnihilate


-- @@ L28-35 verbatim
/-- The type `CreateAnnihilate` is finite. -/
instance : Fintype CreateAnnihilate where
  elems := {create, annihilate}
  complete := by
    intro c
    cases c
    · exact Finset.mem_insert_self create {annihilate}
    · exact Finset.insert_eq_self.mp rfl


-- @@ L37-38 verbatim
lemma eq_create_or_annihilate (φ : CreateAnnihilate) : φ = create ∨ φ = annihilate := by
  cases φ <;> simp


-- @@ L40-45 verbatim
/-- The normal ordering on creation and annihilation operators.
  Under this relation, `normalOrder a b` is false only if `a` is annihilate and `b` is create. -/
def normalOrder : CreateAnnihilate → CreateAnnihilate → Prop
  | create, _ => True
  | annihilate, annihilate => True
  | annihilate, create => False


-- @@ L47-52 verbatim
/-- The normal ordering on `CreateAnnihilate` is decidable. -/
instance : (φ φ' : CreateAnnihilate) → Decidable (normalOrder φ φ')
  | create, create => isTrue True.intro
  | annihilate, annihilate => isTrue True.intro
  | create, annihilate => isTrue True.intro
  | annihilate, create => isFalse False.elim


-- @@ L54-56 verbatim
/-- Normal ordering is total. -/
instance : Std.Total normalOrder where
  total := by decide


-- @@ L58-60 verbatim
/-- Normal ordering is transitive. -/
instance : IsTrans CreateAnnihilate normalOrder where
  trans := by decide


-- @@ L62-65 verbatim
@[simp]
lemma not_normalOrder_annihilate_iff_false (a : CreateAnnihilate) :
    (¬ normalOrder a annihilate) ↔ False := by
  cases a <;> simp [normalOrder]


-- @@ L67-70 verbatim
lemma sum_eq {M : Type} [AddCommMonoid M] (f : CreateAnnihilate → M) :
    ∑ i, f i = f create + f annihilate := by
  change ∑ i ∈ {create, annihilate}, f i = f create + f annihilate
  simp


-- @@ L72-73 verbatim
@[simp]
lemma CreateAnnihilate_card_eq_two : Fintype.card CreateAnnihilate = 2 := rfl


-- @@ L75-75 verbatim
end CreateAnnihilate
