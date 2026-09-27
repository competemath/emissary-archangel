/-
Copyright (c) 2026 Anthony Vandikas, Kiarash Sotoudeh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthony Vandikas, Kiarash Sotoudeh
-/
module

public import LeanPool.QuasiBorelSpaces.Multiset
public import LeanPool.QuasiBorelSpaces.Subtype
import LeanPool.QuasiBorelSpaces.Basic
import Mathlib.Tactic.Positivity.Finset


-- @@ L13-17 verbatim
/-!
# LeanPool.QuasiBorelSpaces.Finset

Imported Lean Pool material for `LeanPool.QuasiBorelSpaces.Finset`.
-/


-- @@ L19-19 verbatim
@[expose] public section


-- @@ L21-21 verbatim
namespace QuasiBorelSpace.Finset


-- @@ L23-26 verbatim
variable
  {A : Type*} [QuasiBorelSpace A]
  {B : Type*} [QuasiBorelSpace B]
  {C : Type*} [QuasiBorelSpace C]


-- @@ L28-30 verbatim
/-- View a finite set as its underlying nodup multiset. -/
irreducible_def toSubtype : Finset A → { xs : Multiset A // Multiset.Nodup xs }
  | ⟨x, h⟩ => ⟨x, h⟩


-- @@ L32-33 verbatim
private irreducible_def ofSubtype : { xs : Multiset A // Multiset.Nodup xs } → Finset A
  | ⟨x, h⟩ => ⟨x, h⟩


-- @@ L35-36 verbatim
instance : QuasiBorelSpace (Finset A) :=
  lift toSubtype


-- @@ L38-40 verbatim
@[local simp]
private lemma isHom_def (f : A → Finset B) : IsHom f ↔ IsHom (fun x ↦ toSubtype (f x)) := by
  rw [isHom_to_lift]


-- @@ L42-44 verbatim
@[local fun_prop]
private lemma isHom_toSubtype : IsHom (toSubtype (A := A)) :=
  isHom_of_lift toSubtype


-- @@ L46-48 verbatim
@[local fun_prop]
private lemma isHom_ofSubtype : IsHom (ofSubtype (A := A)) := by
  simp only [isHom_def, ofSubtype_def, toSubtype_def, Subtype.coe_eta, isHom_id']


-- @@ L50-62 verbatim
@[fun_prop]
lemma isHom_fold
    {op : A → C → C → C} [∀ x, Std.Commutative (op x)] [∀ x, Std.Associative (op x)]
    (hop : IsHom (fun (x, y, z) ↦ op x y z))
    (z : A → C) (hz : IsHom z)
    (f : A → B → C) (hf : IsHom fun (x, y) ↦ f x y)
    (g : A → Finset B) (hg : IsHom g)
    : IsHom (fun x ↦ Finset.fold (op x) (z x) (f x) (g x)) := by
  unfold Finset.fold
  have {x} : (g x).val = (toSubtype (g x)).val := by
    simp only [toSubtype_def]
  simp only [this]
  fun_prop


-- @@ L64-70 verbatim
@[simp, fun_prop]
lemma isHom_singleton : IsHom (fun x ↦ ({x} : Finset A)) := by
  have {x} : ({x} : Finset A) = ofSubtype ⟨_, Multiset.nodup_singleton x⟩ := by
    simp only [ofSubtype_def]
    rfl
  simp only [this]
  fun_prop


-- @@ L72-82 verbatim
@[simp, fun_prop]
lemma isHom_union
    [DecidableEq A] [IsHomDiagonal A]
    : IsHom (fun x : Finset A × Finset A ↦ x.1 ∪ x.2) := by
  have {x y : Finset A}
      : x ∪ y
      = ofSubtype ⟨_, .ndunion (toSubtype x) (toSubtype y).property⟩ := by
    simp only [toSubtype_def, ofSubtype_def]
    rfl
  simp only [this]
  fun_prop


-- @@ L84-84 verbatim
end QuasiBorelSpace.Finset
