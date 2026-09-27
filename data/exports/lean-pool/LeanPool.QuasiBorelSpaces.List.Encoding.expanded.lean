/-
Copyright (c) 2026 Anthony Vandikas, Kiarash Sotoudeh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthony Vandikas, Kiarash Sotoudeh
-/
module

public import Mathlib.Data.Nat.Notation
public import Aesop.BuiltinRules
import Mathlib.Tactic.Attr.Core
import Mathlib.Tactic.Push


-- @@ L13-17 verbatim
/-!
# LeanPool.QuasiBorelSpaces.List.Encoding

Imported Lean Pool material for `LeanPool.QuasiBorelSpaces.List.Encoding`.
-/


-- @@ L19-19 verbatim
@[expose] public section



-- @@ L22-22 verbatim
namespace List


-- @@ L24-24 verbatim
variable {A B C : Type*}


-- @@ L26-31 verbatim
/--
We derive the `QuasiBorelSpace` instance for `List A`s from their encoding as
`(n : ℕ) × (Fin n → A)`.
-/
abbrev Encoding (A : Type*) :=
  (n : ℕ) × (Fin n → A)


-- @@ L33-33 verbatim
namespace Encoding


-- @@ L35-36 verbatim
/-- The encoded version of `[]`. -/
def nil : Encoding A := ⟨0, Fin.elim0⟩


-- @@ L38-40 verbatim
/-- The encoded version of `· ∷ ·`. -/
def cons (x : A) (xs : Encoding A) : Encoding A :=
  ⟨xs.1 + 1, Fin.cases x xs.2⟩


-- @@ L42-45 verbatim
/-- The encoded version of `List.foldr`. -/
def foldr (cons : A → B → B) (nil : B) : Encoding A → B
  | ⟨0, _⟩ => nil
  | ⟨n + 1, k⟩ => cons (k 0) (foldr cons nil ⟨n, fun i ↦ k i.succ⟩)


-- @@ L47-49 verbatim
@[simp]
lemma foldr_nil {A B} (f : A → B → B) (z : B) : foldr f z nil = z := by
  simp only [nil, foldr]


-- @@ L51-55 verbatim
@[simp]
lemma foldr_cons {A B}
    (f : A → B → B) (z : B) (x : A) (xs : Encoding A)
    : foldr f z (cons x xs) = f x (foldr f z xs) := by
  simp only [cons, foldr, Fin.cases_zero, Fin.cases_succ]


-- @@ L57-61 verbatim
@[simp]
lemma nil_ne_cons (x : A) (xs : Encoding A) : nil ≠ cons x xs := by
  simp only [
    nil, cons, ne_eq, Sigma.mk.injEq, Nat.right_eq_add, Nat.add_eq_zero_iff,
    Nat.succ_ne_self, and_false, false_and, not_false_eq_true]


-- @@ L63-67 verbatim
@[simp]
lemma cons_ne_nil (x : A) (xs : Encoding A) : cons x xs ≠ nil := by
  simp only [
    nil, cons, ne_eq, Sigma.mk.injEq, Nat.add_eq_zero_iff,
    Nat.succ_ne_self, and_false, false_and, not_false_eq_true]


-- @@ L69-84 verbatim
@[simp]
lemma cons_inj_iff (x y : A) (xs ys : Encoding A) : cons x xs = cons y ys ↔ x = y ∧ xs = ys := by
  rcases xs
  rcases ys
  simp only [cons, Sigma.mk.injEq, Nat.add_right_cancel_iff]
  apply Iff.intro
  · simp only [and_imp]
    intro rfl h₁
    simp only [heq_eq_eq, funext_iff] at h₁
    have h₂ := h₁ 0
    have h₃ (n) := h₁ (Fin.succ n)
    simp only [Fin.cases_zero] at h₂
    simp only [Fin.cases_succ] at h₃
    simp only [h₂, heq_eq_eq, funext_iff, h₃, implies_true, and_self]
  · rintro ⟨rfl, rfl, rfl⟩
    simp only [heq_eq_eq, and_self]


-- @@ L86-88 verbatim
/-- Encodes a `List A` as an `Encoding A`. -/
def encode : List A → Encoding A :=
  List.foldr Encoding.cons Encoding.nil


-- @@ L90-92 verbatim
@[simp]
lemma encode_nil {A} : encode (A := A) [] = Encoding.nil := by
  rfl


-- @@ L94-96 verbatim
@[simp]
lemma encode_cons {A} (x : A) (xs : List A) : encode (x :: xs) = Encoding.cons x (encode xs) := by
  rfl


-- @@ L98-111 verbatim
@[simp]
lemma encode_injective : Function.Injective (encode (A := A)) := by
  intro xs ys h
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => simp only
    | cons y ys => simp only [encode_nil, encode_cons, Encoding.nil_ne_cons] at h
  | cons x xs ih =>
    cases ys with
    | nil => simp only [encode_cons, encode_nil, Encoding.cons_ne_nil] at h
    | cons y ys =>
      simp_all only [encode_cons, Encoding.cons_inj_iff, cons.injEq, true_and]
      grind


-- @@ L113-113 verbatim
end Encoding


-- @@ L115-115 verbatim
end List
