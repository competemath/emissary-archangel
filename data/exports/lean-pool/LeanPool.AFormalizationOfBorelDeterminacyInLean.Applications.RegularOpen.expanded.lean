/-
Copyright (c) 2026 Sven Manthe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sven Manthe
-/
module

public import Mathlib.Order.Heyting.Regular
public import Mathlib.Topology.Sets.Opens


-- @@ L11-15 verbatim
/-!
# LeanPool.AFormalizationOfBorelDeterminacyInLean.Applications.RegularOpen

Auxiliary declarations for the Borel determinacy formalization.
-/


-- @@ L17-17 verbatim
@[expose] public section



-- @@ L20-20 verbatim
variable {X : Type*} [tX : TopologicalSpace X] {A B : Set X} {U V : tX.Opens}


-- @@ L22-22 verbatim
namespace TopologicalSpace.Opens

-- @@ L23-23 verbatim
lemma le_def : U ≤ V ↔ (U : Set X) ⊆ V := by simp only [SetLike.coe_subset_coe]

-- @@ L24-30 verbatim
@[simp] lemma coe_himp' : U ⇨ V = interior (V ∪ (U : Set X)ᶜ) := by
  suffices U ⇨ V = Opens.interior (V ∪ (U : Set X)ᶜ) by
    simp_all
  apply eq_of_forall_le_iff; intro W
  simp_rw [le_himp_iff, ← SetLike.coe_subset_coe, coe_inf, coe_interior,
    W.isOpen.subset_interior_iff]
  constructor <;> (intro h; tauto_set)

-- @@ L31-31 verbatim
@[simp] lemma coe_compl' : Uᶜ = interior (U : Set X)ᶜ := by rw [← himp_bot, coe_himp']; simp

-- @@ L32-32 verbatim
lemma coe_compl_compl : ((Uᶜᶜ : tX.Opens) : Set X) = interior (closure U) := by simp

-- @@ L33-34 verbatim
lemma isRegular_iff : Heyting.IsRegular U ↔ interior (closure U) = (U : Set X) := by
  simp [Heyting.IsRegular, Opens.ext_iff]

-- @@ L35-35 verbatim
end TopologicalSpace.Opens

-- @@ L36-36 verbatim
open TopologicalSpace


-- @@ L38-41 verbatim
lemma interior_closure_interior_closure_eq_interior_closure :
  interior (closure (interior (closure A))) = interior (closure A) :=
  subset_antisymm (interior_mono (isClosed_closure.closure_interior_subset))
    isOpen_interior.subset_interior_closure

-- @@ L42-44 verbatim
lemma IsClosed.interior_isRegular (hA : IsClosed A) : Heyting.IsRegular (Opens.interior A) := by
  rw [Opens.isRegular_iff, ← hA.closure_eq, Opens.coe_interior,
    interior_closure_interior_closure_eq_interior_closure]
