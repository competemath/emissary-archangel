/-
Copyright (c) 2026 Jeremy Parker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy P Parker
-/
import Formalisation.HansenCograph.Invariant


-- @@ L8-16 verbatim
/-!
# Same-vertex deletion interface for cograph HDA

The coupled HDA tensor pairs a deletion in `G` with the deletion of the same
ambient vertex in `Gᶜ`.  This module fixes that common subtype before any
finite tensor is introduced.

No HDA inequality is proved here.
-/


-- @@ L18-18 verbatim
open scoped BigOperators Pointwise

-- @@ L19-19 verbatim
open Set

-- @@ L20-20 verbatim
open MeasureTheory

-- @@ L21-21 verbatim
open SimpleGraph


-- @@ L23-23 verbatim
universe u v


-- @@ L25-25 verbatim
namespace HansenCograph


-- @@ L27-27 verbatim
section DeleteVertex


-- @@ L29-29 verbatim
variable {V : Type u} [Fintype V] [DecidableEq V]


-- @@ L31-34 verbatim
/-- The graph induced by all vertices except `v`. -/
def deleteVertex (G : SimpleGraph V) (v : V) :
    SimpleGraph ↥(↑(Finset.univ.erase v) : Set V) :=
  inducedFinset G (Finset.univ.erase v)


-- @@ L36-42 verbatim
/-- Deleting one ambient vertex lowers the finite vertex cardinality by one. -/
theorem card_deleteVertex (v : V) :
    Fintype.card ↥(↑(Finset.univ.erase v) : Set V) = Fintype.card V - 1 := by
  change Fintype.card ↥(Finset.univ.erase v) = Fintype.card V - 1
  simpa using
    (Finset.card_erase_of_mem (s := (Finset.univ : Finset V))
      (Finset.mem_univ v))


-- @@ L44-49 verbatim
/-- Inducing a complement is the complement of the induced graph. -/
theorem inducedFinset_compl
    (G : SimpleGraph V) (s : Finset V) :
    inducedFinset Gᶜ s = (inducedFinset G s)ᶜ := by
  ext x y
  simp [inducedFinset, SimpleGraph.compl_adj]


-- @@ L51-59 verbatim
/--
Deleting the same ambient vertex commutes with graph complementation.  Both
sides are graphs on the identical subtype `V \ {v}`, as required by the
coupled complementary-deletion tensor.
-/
@[simp]
theorem deleteVertex_compl (G : SimpleGraph V) (v : V) :
    deleteVertex Gᶜ v = (deleteVertex G v)ᶜ := by
  simpa [deleteVertex] using inducedFinset_compl G (Finset.univ.erase v)


-- @@ L61-63 verbatim
/-- The normalized stable-set volume of a deletion is the corresponding induced volume. -/
theorem nu_deleteVertex_eq_nuInduced (G : SimpleGraph V) (v : V) :
    nu (deleteVertex G v) = nuInduced G (Finset.univ.erase v) := rfl


-- @@ L65-69 verbatim
/-- The complementary deletion has exactly the transported `N` invariant. -/
@[simp]
theorem N_deleteVertex_compl (G : SimpleGraph V) (v : V) :
    N (deleteVertex Gᶜ v) = N ((deleteVertex G v)ᶜ) := by
  rw [deleteVertex_compl]


-- @@ L71-75 verbatim
/-- The complementary deletion has exactly the transported section profile. -/
@[simp]
theorem q_deleteVertex_compl (G : SimpleGraph V) (v : V) (x : ℝ) :
    q (deleteVertex Gᶜ v) x = q ((deleteVertex G v)ᶜ) x := by
  rw [deleteVertex_compl]


-- @@ L77-77 verbatim
end DeleteVertex


-- @@ L79-79 verbatim
section DeleteVertexSumIso


-- @@ L81-81 verbatim
variable {V : Type u} {W : Type v}

-- @@ L82-82 verbatim
variable [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]


-- @@ L84-106 verbatim
/--
The carrier equivalence for deleting a left-summand vertex.  It is kept
separate from the graph proofs so the same map can transport both union and
join deletions.
-/
private def deleteSumInlEquiv (x : V) :
    ↥(↑((Finset.univ : Finset (V ⊕ W)).erase (Sum.inl x)) : Set (V ⊕ W)) ≃
      (↥(↑((Finset.univ : Finset V).erase x) : Set V) ⊕ W) :=
  { toFun := fun z => by
      rcases z with ⟨z, hz⟩
      cases z with
      | inl v => exact Sum.inl ⟨v, by simpa using hz⟩
      | inr w => exact Sum.inr w
    invFun := fun z =>
      match z with
      | Sum.inl v => ⟨Sum.inl v.1, by simpa using v.2⟩
      | Sum.inr w => ⟨Sum.inr w, by simp⟩
    left_inv := by
      rintro ⟨z, hz⟩
      cases z <;> rfl
    right_inv := by
      intro z
      cases z <;> rfl }


-- @@ L108-129 verbatim
/--
The carrier equivalence for deleting a right-summand vertex.  It is the
right-handed counterpart of `deleteSumInlEquiv`.
-/
private def deleteSumInrEquiv (y : W) :
    ↥(↑((Finset.univ : Finset (V ⊕ W)).erase (Sum.inr y)) : Set (V ⊕ W)) ≃
      (V ⊕ ↥(↑((Finset.univ : Finset W).erase y) : Set W)) :=
  { toFun := fun z => by
      rcases z with ⟨z, hz⟩
      cases z with
      | inl v => exact Sum.inl v
      | inr w => exact Sum.inr ⟨w, by simpa using hz⟩
    invFun := fun z =>
      match z with
      | Sum.inl v => ⟨Sum.inl v, by simp⟩
      | Sum.inr w => ⟨Sum.inr w.1, by simpa using w.2⟩
    left_inv := by
      rintro ⟨z, hz⟩
      cases z <;> rfl
    right_inv := by
      intro z
      cases z <;> rfl }


-- @@ L131-140 verbatim
/-- Deleting a left vertex commutes with disjoint union up to graph isomorphism. -/
def deleteVertex_sum_inl_iso
    (A : SimpleGraph V) (B : SimpleGraph W) (x : V) :
    deleteVertex (A ⊕g B) (Sum.inl x) ≃g deleteVertex A x ⊕g B :=
  { toEquiv := deleteSumInlEquiv (V := V) (W := W) x
    map_rel_iff' := by
      rintro ⟨z, hz⟩ ⟨w, hw⟩
      cases z <;> cases w <;>
        simp [deleteSumInlEquiv, deleteVertex, inducedFinset,
          SimpleGraph.sum_adj] }


-- @@ L142-151 verbatim
/-- Deleting a right vertex commutes with disjoint union up to graph isomorphism. -/
def deleteVertex_sum_inr_iso
    (A : SimpleGraph V) (B : SimpleGraph W) (y : W) :
    deleteVertex (A ⊕g B) (Sum.inr y) ≃g A ⊕g deleteVertex B y :=
  { toEquiv := deleteSumInrEquiv (V := V) (W := W) y
    map_rel_iff' := by
      rintro ⟨z, hz⟩ ⟨w, hw⟩
      cases z <;> cases w <;>
        simp [deleteSumInrEquiv, deleteVertex, inducedFinset,
          SimpleGraph.sum_adj] }


-- @@ L153-162 expanded
/-- Deleting a left vertex commutes with graph join up to graph isomorphism. -/
def deleteVertex_join_inl_iso (A : SimpleGraph V) (B : SimpleGraph W) (x : V) :
    deleteVertex (graphJoin A B) (Sum.inl x) ≃g graphJoin (deleteVertex A x) B :=
  { toEquiv := deleteSumInlEquiv (V := V) (W := W) x
    map_rel_iff' := by
      rintro ⟨z, hz⟩ ⟨w, hw⟩
      cases z <;> cases w <;>
        simp [deleteSumInlEquiv, deleteVertex, inducedFinset, graphJoin, SimpleGraph.sum_adj,
          -compl_sum_eq_join] }


-- @@ L164-173 expanded
/-- Deleting a right vertex commutes with graph join up to graph isomorphism. -/
def deleteVertex_join_inr_iso (A : SimpleGraph V) (B : SimpleGraph W) (y : W) :
    deleteVertex (graphJoin A B) (Sum.inr y) ≃g graphJoin A (deleteVertex B y) :=
  { toEquiv := deleteSumInrEquiv (V := V) (W := W) y
    map_rel_iff' := by
      rintro ⟨z, hz⟩ ⟨w, hw⟩
      cases z <;> cases w <;>
        simp [deleteSumInrEquiv, deleteVertex, inducedFinset, graphJoin, SimpleGraph.sum_adj,
          -compl_sum_eq_join] }


-- @@ L175-175 verbatim
end DeleteVertexSumIso


-- @@ L177-177 verbatim
end HansenCograph
