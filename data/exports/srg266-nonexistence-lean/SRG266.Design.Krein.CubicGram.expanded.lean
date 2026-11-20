/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Design.Krein.CommonTrace


-- @@ L8-8 verbatim
open scoped BigOperators Matrix


-- @@ L10-10 verbatim
namespace SRG266.QuasiSymmetric.TripleDesign57


-- @@ L12-13 verbatim
variable {P B : Type*} [Fintype P] [DecidableEq P] [Fintype B] [DecidableEq B]
    (D : TripleDesign57 P B)


-- @@ L15-15 verbatim
local notation "V" => KreinVertex (P := P) (B := B)


-- @@ L17-21 verbatim
theorem neighborCount_union (T U : Finset V) (hd : Disjoint T U) (x : V) :
    D.neighborCount (T ∪ U) x = D.neighborCount T x + D.neighborCount U x := by
  simp only [neighborCount, Finset.filter_union]
  exact Finset.card_union_of_disjoint
    (hd.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _))


-- @@ L23-26 verbatim
theorem bicliqueCubicLeft_card {S : Finset V} (hcard : S.card = 3)
    (hI : D.IndependentSet S) : (D.bicliqueCubicLeft S).card = 54 := by
  rw [bicliqueCubicLeft, Finset.card_union_of_disjoint (D.disjoint_biclique_class S 0),
    D.biclique_card hcard hI, (D.bicliqueClass_card hcard hI).1]


-- @@ L28-41 verbatim
theorem bicliqueCubicLeft_degrees {S : Finset V} (hcard : S.card = 3)
    (hI : D.IndependentSet S) {x : V} (hx : x ∈ D.bicliqueCubicLeft S) :
    D.neighborCount (D.bicliqueCubicLeft S) x = 3 ∧ D.neighborCount (D.bicliqueClass S 2) x = 18 := by
  have hu := D.neighborCount_union (S ∪ D.commonTo S) (D.bicliqueClass S 0)
    (D.disjoint_biclique_class S 0) x
  change D.neighborCount (D.bicliqueCubicLeft S) x = _ at hu
  rcases Finset.mem_union.mp hx with hxD | hx0
  · have hd := D.biclique_inside_degrees hcard hI hxD
    have ht := D.neighborCount_biclique_of_mem hcard hI hxD
    omega
  · obtain ⟨hxD,ht⟩ := (D.mem_bicliqueClass S 0 x).mp hx0
    have hd := D.biclique_local_degrees hcard hI hxD
    simp only [ht, if_true, zero_ne_one, if_false] at hd
    omega


-- @@ L43-52 verbatim
theorem bicliqueCubicRight_degrees {S : Finset V} (hcard : S.card = 3)
    (hI : D.IndependentSet S) {x : V} (hx : x ∈ D.bicliqueClass S 2) :
    D.neighborCount (D.bicliqueClass S 2) x = 3 ∧ D.neighborCount (D.bicliqueCubicLeft S) x = 18 := by
  have hu := D.neighborCount_union (S ∪ D.commonTo S) (D.bicliqueClass S 0)
    (D.disjoint_biclique_class S 0) x
  change D.neighborCount (D.bicliqueCubicLeft S) x = _ at hu
  obtain ⟨hxD,ht⟩ := (D.mem_bicliqueClass S 2 x).mp hx
  have hd := D.biclique_local_degrees hcard hI hxD
  norm_num [ht] at hd
  omega


-- @@ L54-54 verbatim
def setAdjMatrix (T : Finset V) : Matrix T T ℤ := fun x y => D.kreinMatrix x y


-- @@ L56-56 verbatim
def crossAdjMatrix (T U : Finset V) : Matrix T U ℤ := fun x y => D.kreinMatrix x y


-- @@ L58-63 verbatim
theorem setAdjMatrix_square (T : Finset V) (x y : T) :
    (D.setAdjMatrix T * D.setAdjMatrix T) x y = D.commonCount T x y := by
  simp only [Matrix.mul_apply, setAdjMatrix]
  simp_rw [D.kreinMatrix_comm _ (y : V)]
  rw [Finset.sum_coe_sort T (fun w : V => D.kreinMatrix x w * D.kreinMatrix y w)]
  exact (D.commonCount_cast T x y).symm


-- @@ L65-69 verbatim
theorem crossAdjMatrix_gram_left (T U : Finset V) (x y : T) :
    (D.crossAdjMatrix T U * (D.crossAdjMatrix T U).transpose) x y = D.commonCount U x y := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, crossAdjMatrix]
  rw [Finset.sum_coe_sort U (fun w : V => D.kreinMatrix x w * D.kreinMatrix y w)]
  exact (D.commonCount_cast U x y).symm


-- @@ L71-74 verbatim
theorem crossAdjMatrix_transpose (T U : Finset V) :
    (D.crossAdjMatrix T U).transpose = D.crossAdjMatrix U T := by
  ext x y
  exact D.kreinMatrix_comm y x


-- @@ L76-82 verbatim
theorem commonCount_of_adj (T : Finset V) {x y : V} (hxy : D.kreinGraph.Adj x y) :
    D.commonCount T x y = 0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_of_forall_notMem
  intro w hw
  obtain ⟨_, hxw, hyw⟩ := Finset.mem_filter.mp hw
  exact D.no_triangle hxy hxw hyw


-- @@ L84-108 verbatim
theorem crossAdjMatrix_gram_of_common (T U : Finset V)
    (hdeg : ∀ x ∈ T, D.neighborCount T x = 3 ∧ D.neighborCount U x = 18)
    (hcom : ∀ x ∈ T, ∀ y ∈ T, x ≠ y → ¬ D.kreinGraph.Adj x y →
      D.commonCount U x y = 6 + D.commonCount T x y) :
    D.crossAdjMatrix T U * (D.crossAdjMatrix T U).transpose =
      (D.setAdjMatrix T - (3 : ℤ) • 1)^2 + (6 : ℤ) • allOnesMatrix := by
  have hp : (D.setAdjMatrix T - (3 : ℤ) • 1)^2 + (6 : ℤ) • allOnesMatrix =
      D.setAdjMatrix T * D.setAdjMatrix T - (6 : ℤ) • D.setAdjMatrix T +
        (9 : ℤ) • 1 + (6 : ℤ) • allOnesMatrix := by noncomm_ring
  rw [hp]
  ext x y
  rw [D.crossAdjMatrix_gram_left]
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.one_apply, allOnesMatrix_apply, D.setAdjMatrix_square, setAdjMatrix]
  by_cases hxy : x = y
  · subst y
    rw [D.commonCount_self, D.commonCount_self, (hdeg x x.property).1,
      (hdeg x x.property).2]
    simp [← D.kreinGraph_adjMatrix, SimpleGraph.adjMatrix_apply]
  · have hval : (x : V) ≠ (y : V) := fun h => hxy (Subtype.ext h)
    by_cases ha : D.kreinGraph.Adj x y
    · rw [D.commonCount_of_adj U ha, D.commonCount_of_adj T ha]
      simp [hxy, ← D.kreinGraph_adjMatrix, SimpleGraph.adjMatrix_apply, ha]
    · rw [hcom x x.property y y.property hval ha]
      simp [hxy, ← D.kreinGraph_adjMatrix, SimpleGraph.adjMatrix_apply, ha, add_comm]


-- @@ L110-119 verbatim
theorem bicliqueCubic_gram_left {S : Finset V} (hcard : S.card = 3)
    (hI : D.IndependentSet S) :
    D.crossAdjMatrix (D.bicliqueCubicLeft S) (D.bicliqueClass S 2) *
      (D.crossAdjMatrix (D.bicliqueCubicLeft S) (D.bicliqueClass S 2)).transpose =
    (D.setAdjMatrix (D.bicliqueCubicLeft S) - (3 : ℤ) • 1)^2 + (6 : ℤ) • allOnesMatrix := by
  apply D.crossAdjMatrix_gram_of_common
  · intro x hx
    exact D.bicliqueCubicLeft_degrees hcard hI hx
  · intro x hx y hy hxy hn
    exact D.bicliqueCubicLeft_common hcard hI hx hy hxy hn


-- @@ L121-129 verbatim
theorem bicliqueCubic_gram_right {S : Finset V} (hcard : S.card = 3)
    (hI : D.IndependentSet S) :
    (D.crossAdjMatrix (D.bicliqueCubicLeft S) (D.bicliqueClass S 2)).transpose *
      D.crossAdjMatrix (D.bicliqueCubicLeft S) (D.bicliqueClass S 2) =
    (D.setAdjMatrix (D.bicliqueClass S 2) - (3 : ℤ) • 1)^2 + (6 : ℤ) • allOnesMatrix := by
  have h := D.crossAdjMatrix_gram_of_common (D.bicliqueClass S 2) (D.bicliqueCubicLeft S)
    (fun x hx => D.bicliqueCubicRight_degrees hcard hI hx)
    (fun x hx y hy hxy hn => D.bicliqueCubicRight_common hcard hI hx hy hxy hn)
  simpa only [D.crossAdjMatrix_transpose] using h


-- @@ L131-131 verbatim
end SRG266.QuasiSymmetric.TripleDesign57
