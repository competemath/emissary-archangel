/-
Copyright (c) 2026 Anthony Vandikas, Kiarash Sotoudeh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthony Vandikas, Kiarash Sotoudeh
-/
module

public import Mathlib.Logic.Equiv.List


-- @@ L10-14 verbatim
/-!
# LeanPool.QuasiBorelSpaces.RoseTree.Defs

Imported Lean Pool material for `LeanPool.QuasiBorelSpaces.RoseTree.Defs`.
-/


-- @@ L16-16 verbatim
@[expose] public section



-- @@ L19-19 verbatim
universe u

-- @@ L20-20 verbatim
variable {A B C : Type*}


-- @@ L22-27 verbatim
/-- The type of node-labelled, finitely branching trees. -/
structure Rose (A : Type u) : Type u where
  /-- The label of the root node. -/
  label : A
  /-- The list of child trees. -/
  children : List (Rose A)


-- @@ L29-29 verbatim
namespace Rose


-- @@ L31-34 verbatim
/-- The fold operation over trees. -/
@[simp]
def fold (f : A → List B → B) : Rose A → B
  | ⟨x, xs⟩ => f x (xs.map (fold f))


-- @@ L36-39 verbatim
/-- Grafts a tree to every sub-node in a `Rose` tree. -/
@[simp]
def bind (f : A → Rose B) : Rose A → Rose B := fun
  | ⟨x, xs⟩ => ⟨(f x).label, (f x).children ++ List.map (bind f) xs⟩


-- @@ L41-43 verbatim
/-- Applies a function to every label in a `Rose` tree. -/
def map (f : A → B) : Rose A → Rose B :=
  bind (fun x ↦ ⟨f x, []⟩)


-- @@ L45-47 verbatim
instance : Monad Rose where
  pure x := ⟨x, []⟩
  bind := flip bind


-- @@ L49-51 verbatim
/-- An injection into the natural numbers. -/
def encode [Encodable A] : Rose A → ℕ
  | ⟨x, xs⟩ => Nat.pair (Encodable.encode x) (Encodable.encode (List.map encode xs))


-- @@ L53-94 verbatim
/-- The inverse of `encode`. -/
def decode [Encodable A] (n : ℕ) : Option (Rose A) :=
  match Nat.unpair n, Nat.unpair_right_le n with
  | (i, j), h => do
    let x ← Encodable.decode₂ A i
    match h' : Encodable.decode j with
    | .none => .none
    | .some (is : List ℕ) => do
      let xs ← List.traverse id (List.ofFn fun i : Fin is.length ↦ decode is[i])
      return ⟨x, xs⟩
  decreasing_by
    apply Nat.lt_of_add_one_le
    simp only [Fin.getElem_fin] at ⊢ h
    apply le_trans ?_ h
    have : j = Encodable.encode is := by
      have := congr_arg (Option.map Encodable.encode) h'
      simp only [
        Denumerable.decode_eq_ofNat, Option.map_some,
        Denumerable.encode_ofNat, Option.some.injEq] at this
      exact this
    subst this
    induction is with
    | nil =>
      simp only [List.length_nil] at i
      apply i.elim0
    | cons head tail ih =>
      have := Nat.left_le_pair head (Encodable.encode tail)
      have := Nat.right_le_pair head (Encodable.encode tail)
      cases i using Fin.cases with
      | zero =>
        simp_all
      | succ i =>
        simp only [
          List.length_cons, Fin.val_succ, List.getElem_cons_succ,
          Encodable.encode_list_cons, Encodable.encode_nat,
          Nat.succ_eq_add_one, ge_iff_le]
        simp only [Encodable.encode_list_cons, Encodable.encode_nat, Nat.succ_eq_add_one] at h
        specialize ih i (by grind)
        simp only [
          Denumerable.decode_eq_ofNat, Denumerable.ofNat_encode,
          ge_iff_le, forall_const] at ih
        grind


-- @@ L96-97 verbatim
instance [LE A] : LE (Rose A) where
  le := fold fun x rec t ↦ x ≤ t.label ∧ List.Forall₂ id rec t.children


-- @@ L99-99 verbatim
end Rose
