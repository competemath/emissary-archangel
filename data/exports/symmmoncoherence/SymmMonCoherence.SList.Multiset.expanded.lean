/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

public import SymmMonCoherence.SList.Linear
public import Mathlib.CategoryTheory.Pi.Monoidal
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory


-- @@ L12-16 verbatim
/-! # The multiset of a symmetric list.

Given a symmetric list `L`, we define its underlying multiset.

-/


-- @@ L18-18 verbatim
universe u


-- @@ L20-20 verbatim
@[expose] public section


-- @@ L22-22 verbatim
namespace CategoryTheory.SList

-- @@ L23-23 verbatim
open MonoidalCategory


-- @@ L25-25 verbatim
variable {C : Type*}

-- @@ L26-26 verbatim
def multiset (L : SList C) : Multiset C := Multiset.ofList L.toList


-- @@ L28-29 expanded
@[grind =]
lemma multiset_nil : (nil : SList C).multiset = 0 := by simp [multiset]


-- @@ L31-33 expanded
@[grind =]
lemma multiset_cons (x : C) (L : SList C) : ((cons x).obj L).multiset = x ::ₘ L.multiset := by
  simp [multiset]


-- @@ L35-37 expanded
@[simp, grind =]
lemma multiset_singleton (x : C) : ((cons x).obj nil).multiset = { x } := by simp [multiset]


-- @@ L39-45 verbatim
lemma multiset_eq_of_hom {L L' : SList C} (f : L ⟶ L') : L.multiset = L'.multiset := by
  induction f using SList.hom_induction' with
  | comp f g _ _ => grind
  | id x => grind
  | cons head f _ => grind
  | swap x y l =>
    simpa [multiset] using .swap ..


-- @@ L47-49 verbatim
@[grind =]
lemma multiset_tensor (L L' : SList C) : (L ⊗ L').multiset = L.multiset + L'.multiset := by
  induction L using SList.cons_induction with simp [multiset, SList.tensorObj_toList]


-- @@ L51-57 verbatim
@[grind =]
lemma multiset_eq_iff_nonempty_iso (L L' : SList C) :
    L.multiset = L'.multiset ↔ Nonempty (L ≅ L') where
  mp h := by
    simp only [multiset, Multiset.coe_eq_coe] at h
    exact SList.toList_perm_iff_nonempty_iso.mp h
  mpr h := multiset_eq_of_hom h.some.hom


-- @@ L59-63 verbatim
@[grind →]
lemma nodup_of_linear (L : SList C) [Linear L] :
    L.multiset.Nodup := by
  simp only [multiset, Multiset.coe_nodup]
  exact Linear.nodup


-- @@ L65-67 verbatim
lemma linear_iff' (L : SList C) :
    L.Linear ↔ L.multiset.Nodup := by
  simp only [multiset, Multiset.coe_nodup, SList.linear_iff]


-- @@ L69-73 verbatim
/-- A choice of an isomorphism between two symmetric lists with same underlying multiset.
In general, this isomorphism is not unique, but it is if either list is linear. -/
@[no_expose] noncomputable def isoOfMultisetEq (L L' : SList C) (h : L.multiset = L'.multiset) :
    L ≅ L' :=
  (multiset_eq_iff_nonempty_iso ..|>.mp h).some


-- @@ L75-75 verbatim
end CategoryTheory.SList
