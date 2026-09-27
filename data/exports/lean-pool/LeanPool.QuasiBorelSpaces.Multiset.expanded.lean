/-
Copyright (c) 2026 Anthony Vandikas, Kiarash Sotoudeh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthony Vandikas, Kiarash Sotoudeh
-/
module

public import LeanPool.QuasiBorelSpaces.List
public import LeanPool.QuasiBorelSpaces.Quotient
import LeanPool.QuasiBorelSpaces.Basic
import Mathlib.Tactic.Positivity.Finset


-- @@ L13-17 verbatim
/-!
# LeanPool.QuasiBorelSpaces.Multiset

Imported Lean Pool material for `LeanPool.QuasiBorelSpaces.Multiset`.
-/


-- @@ L19-19 verbatim
@[expose] public section


-- @@ L21-21 verbatim
namespace QuasiBorelSpace.Multiset


-- @@ L23-26 verbatim
variable
  {A : Type*} [QuasiBorelSpace A]
  {B : Type*} [QuasiBorelSpace B]
  {C : Type*} [QuasiBorelSpace C]


-- @@ L28-29 verbatim
instance : QuasiBorelSpace (Multiset A) :=
  lift (id : Quotient (List.isSetoid A) → Multiset A)


-- @@ L31-39 verbatim
@[fun_prop]
lemma isHom_fold
    {op : A → B → B → B} [∀ x, Std.Commutative (op x)] [∀ x, Std.Associative (op x)]
    (hop : IsHom (fun (x, y, z) ↦ op x y z))
    (z : A → B) (hz : IsHom z)
    (f : A → Multiset B) (hf : IsHom f)
    : IsHom (fun x ↦ Multiset.fold (op x) (z x) (f x)) := by
  unfold Multiset.fold Multiset.foldr
  fun_prop


-- @@ L41-43 verbatim
@[simp, fun_prop]
lemma isHom_ofList : IsHom (Multiset.ofList : List A → Multiset A) := by
  apply Quotient.isHom_mk


-- @@ L45-48 verbatim
@[simp, fun_prop]
lemma isHom_add : IsHom (fun x : Multiset A × Multiset A ↦ x.1 + x.2) := by
  simp only [HAdd.hAdd, Add.add, Multiset.add]
  fun_prop


-- @@ L50-55 verbatim
@[simp, fun_prop]
lemma isHom_sub
    [DecidableEq A] [IsHomDiagonal A]
    : IsHom (fun x : Multiset A × Multiset A ↦ x.1 - x.2) := by
  simp only [HSub.hSub, Sub.sub, Multiset.sub]
  fun_prop


-- @@ L57-62 verbatim
@[simp, fun_prop]
lemma isHom_union
    [DecidableEq A] [IsHomDiagonal A]
    : IsHom (fun x : Multiset A × Multiset A ↦ x.1 ∪ x.2) := by
  simp only [Union.union, Multiset.union]
  fun_prop


-- @@ L64-71 verbatim
@[simp, fun_prop]
lemma isHom_ndunion
    [DecidableEq B] [IsHomDiagonal B]
    {f : A → Multiset B} (hf : IsHom f)
    {g : A → Multiset B} (hg : IsHom g)
    : IsHom (fun x ↦ (f x).ndunion (g x)) := by
  simp only [Multiset.ndunion]
  fun_prop


-- @@ L73-76 verbatim
@[simp, fun_prop]
lemma isHom_cons : IsHom (fun x : A × Multiset A ↦ x.1 ::ₘ x.2) := by
  simp only [Multiset.cons]
  fun_prop


-- @@ L78-81 verbatim
@[simp, fun_prop]
lemma isHom_singleton : IsHom (fun x : A ↦ ({x} : Multiset A)) := by
  change IsHom fun a ↦ a ::ₘ 0
  fun_prop


-- @@ L83-89 verbatim
@[simp, fun_prop]
lemma isHom_map
    {f : A → B → C} (hf : IsHom fun (x, y) ↦ f x y)
    {g : A → Multiset B} (hg : IsHom g)
    : IsHom (fun x ↦ Multiset.map (f x) (g x)) := by
  unfold Multiset.map
  fun_prop


-- @@ L91-91 verbatim
end QuasiBorelSpace.Multiset
