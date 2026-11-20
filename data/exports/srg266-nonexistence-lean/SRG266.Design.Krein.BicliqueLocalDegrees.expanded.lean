/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Design.Krein.BicliqueCensus


-- @@ L8-8 verbatim
open scoped BigOperators Matrix


-- @@ L10-10 verbatim
namespace SRG266.QuasiSymmetric.TripleDesign57


-- @@ L12-13 verbatim
variable {P B : Type*} [Fintype P] [DecidableEq P] [Fintype B] [DecidableEq B]
    (D : TripleDesign57 P B)


-- @@ L15-15 verbatim
local notation "V" => KreinVertex (P := P) (B := B)


-- @@ L17-23 verbatim
theorem neighborCount_weighted_sum (T : Finset V) (x : V) :
    (∑ y, D.kreinMatrix x y * (D.neighborCount T y : ℤ)) =
      45 * (if x ∈ T then 1 else 0) + 12 * T.card - 12 * D.neighborCount T x := by
  simp_rw [D.neighborCount_cast, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [← Matrix.mul_apply, D.kreinMatrix_square_apply]
  simp [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, mul_comm]


-- @@ L25-36 verbatim
theorem triangle_neighbor_moment_zero {x a b : V} (hxa : D.kreinGraph.Adj x a) :
    (∑ y, D.kreinMatrix x y * D.kreinMatrix y a * D.kreinMatrix y b) = 0 := by
  apply Finset.sum_eq_zero
  intro y _
  rw [← D.kreinGraph_adjMatrix]
  simp only [SimpleGraph.adjMatrix_apply]
  by_cases hxy : D.kreinGraph.Adj x y
  · have hay : ¬ D.kreinGraph.Adj y a := by
      intro hya
      exact D.no_triangle hxa hxy ((D.kreinGraph.adj_comm y a).mp hya)
    simp [hay]
  · simp [hxy]


-- @@ L38-56 verbatim
theorem independent_pair_neighbor_moment {x a b : V}
    (hxa : x ≠ a) (hxb : x ≠ b) (hab : a ≠ b) (hI : ¬ D.kreinGraph.Adj a b) :
    (∑ y, D.kreinMatrix x y * D.kreinMatrix y a * D.kreinMatrix y b) =
      if ¬ D.kreinGraph.Adj x a ∧ ¬ D.kreinGraph.Adj x b then 3 else 0 := by
  by_cases ha : D.kreinGraph.Adj x a
  · rw [D.triangle_neighbor_moment_zero ha]
    simp [ha]
  · by_cases hb : D.kreinGraph.Adj x b
    · have hz := D.triangle_neighbor_moment_zero (b := a) hb
      have heq : (∑ y, D.kreinMatrix x y * D.kreinMatrix y a * D.kreinMatrix y b) =
          ∑ y, D.kreinMatrix x y * D.kreinMatrix y b * D.kreinMatrix y a := by
        apply Finset.sum_congr rfl
        intro y _
        ring
      rw [heq, hz]
      simp [hb]
    · simpa only [ha, hb, not_false_eq_true, and_self, if_true,
        D.kreinMatrix_comm a, D.kreinMatrix_comm b] using
        D.independent_triple_neighbor_moment x a b hxa hxb hab ha hb hI


-- @@ L58-120 verbatim
theorem independentSet_weighted_square (T : Finset V) (hI : D.IndependentSet T)
    (x : V) (hx : x ∉ T) :
    (∑ y, D.kreinMatrix x y * (D.neighborCount T y : ℤ)^2) =
      12 * T.card - 12 * D.neighborCount T x +
      3 * (((T.filter fun a => ¬ D.kreinGraph.Adj x a).card : ℤ)^2 -
        (T.filter fun a => ¬ D.kreinGraph.Adj x a).card) := by
  have hentry (a) (ha : a ∈ T) (b) (hb : b ∈ T) :
      (∑ y, D.kreinMatrix x y * D.kreinMatrix y a * D.kreinMatrix y b) =
        (if a = b then 12 - 12 * D.kreinMatrix x a else 0) +
        3 * (if ¬ D.kreinGraph.Adj x a ∧ ¬ D.kreinGraph.Adj x b then 1 else 0) -
        3 * (if a = b ∧ ¬ D.kreinGraph.Adj x a then 1 else 0) := by
    have hxa : x ≠ a := fun h => hx (h ▸ ha)
    have hxb : x ≠ b := fun h => hx (h ▸ hb)
    by_cases hab : a = b
    · subst b
      have hi (y) : D.kreinMatrix x y * D.kreinMatrix y a * D.kreinMatrix y a =
          D.kreinMatrix x y * D.kreinMatrix y a := by
        rw [← D.kreinGraph_adjMatrix]
        simp only [SimpleGraph.adjMatrix_apply]
        split_ifs <;> norm_num
      rw [Finset.sum_congr rfl (fun y _ => hi y), ← Matrix.mul_apply,
        D.kreinMatrix_square_apply]
      simp [hxa]
    · rw [D.independent_pair_neighbor_moment hxa hxb hab (hI a ha b hb hab)]
      simp only [hab, if_false, false_and, zero_add]
      split_ifs <;> norm_num
  calc
    _ = ∑ a ∈ T, ∑ b ∈ T, ∑ y,
        D.kreinMatrix x y * D.kreinMatrix y a * D.kreinMatrix y b := by
      simp_rw [D.neighborCount_cast, pow_two, Finset.sum_mul, Finset.mul_sum]
      simp_rw [mul_assoc]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.sum_comm]
    _ = _ := by
      have heq := Finset.sum_congr rfl (fun a ha =>
        Finset.sum_congr rfl (fun b hb => hentry a ha b hb))
      rw [heq]
      simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
      have hdiag : (∑ a ∈ T, ∑ b ∈ T, if a = b then 12 - 12 * D.kreinMatrix x a else 0) =
          12 * T.card - 12 * D.neighborCount T x := by
        simp [Finset.sum_sub_distrib, ← Finset.mul_sum, D.neighborCount_cast, mul_comm]
      rw [hdiag]
      have hoff : (∑ a ∈ T, ∑ b ∈ T,
          if ¬ D.kreinGraph.Adj x a ∧ ¬ D.kreinGraph.Adj x b then (1 : ℤ) else 0) =
          ((T.filter fun a => ¬ D.kreinGraph.Adj x a).card : ℤ)^2 := by
        have hf (a b) : (if ¬ D.kreinGraph.Adj x a ∧ ¬ D.kreinGraph.Adj x b then (1 : ℤ) else 0) =
            (if ¬ D.kreinGraph.Adj x a then 1 else 0) * (if ¬ D.kreinGraph.Adj x b then 1 else 0) := by
          by_cases ha : D.kreinGraph.Adj x a <;>
            by_cases hb : D.kreinGraph.Adj x b <;> simp [ha, hb]
        simp_rw [hf, ← Finset.mul_sum, ← Finset.sum_mul, Finset.sum_boole, pow_two]
      have hdiag2 : (∑ a ∈ T, ∑ b ∈ T,
          if a = b ∧ ¬ D.kreinGraph.Adj x a then (1 : ℤ) else 0) =
          (T.filter fun a => ¬ D.kreinGraph.Adj x a).card := by
        have hi (a) (ha : a ∈ T) : (∑ b ∈ T,
            if a = b ∧ ¬ D.kreinGraph.Adj x a then (1 : ℤ) else 0) =
            if ¬ D.kreinGraph.Adj x a then 1 else 0 := by
          by_cases h : D.kreinGraph.Adj x a <;> simp [h, ha]
        rw [Finset.sum_congr rfl hi]
        simp only [Finset.sum_boole]
      rw [hoff, hdiag2]
      ring


-- @@ L122-133 verbatim
theorem independentTriple_weighted_square {S : Finset V} (hcard : S.card = 3)
    (hI : D.IndependentSet S) {x : V} (hx : x ∉ S) :
    (∑ y, D.kreinMatrix x y * (D.neighborCount S y : ℤ)^2) =
      54 - 27 * D.neighborCount S x + 3 * (D.neighborCount S x : ℤ)^2 := by
  have h := D.independentSet_weighted_square S hI x hx
  have hc : ((S.filter fun a => ¬ D.kreinGraph.Adj x a).card : ℤ) =
      3 - D.neighborCount S x := by
    have hpart := Finset.card_filter_add_card_filter_not (s := S) (p := fun a => D.kreinGraph.Adj x a)
    change D.neighborCount S x + (S.filter fun a => ¬ D.kreinGraph.Adj x a).card = S.card at hpart
    omega
  rw [h, hcard, hc]
  ring


-- @@ L135-139 verbatim
theorem biclique_neighborCount_split (S : Finset V) (x : V) :
    D.neighborCount (S ∪ D.commonTo S) x = D.neighborCount S x + D.neighborCount (D.commonTo S) x := by
  simp only [neighborCount, Finset.filter_union]
  exact Finset.card_union_of_disjoint
    ((D.disjoint_commonTo S).mono (Finset.filter_subset _ _) (Finset.filter_subset _ _))


-- @@ L141-152 verbatim
theorem biclique_neighborCount_product_zero (S : Finset V) (x : V) :
    (D.neighborCount S x : ℤ) * D.neighborCount (D.commonTo S) x = 0 := by
  by_cases hS : D.neighborCount S x = 0
  · simp [hS]
  · have hC : D.neighborCount (D.commonTo S) x = 0 := by
      by_contra hC
      obtain ⟨a,ha⟩ := Finset.card_pos.mp (by omega : 0 < D.neighborCount S x)
      obtain ⟨b,hb⟩ := Finset.card_pos.mp (by omega : 0 < D.neighborCount (D.commonTo S) x)
      obtain ⟨haS,hxa⟩ := Finset.mem_filter.mp ha
      obtain ⟨hbC,hxb⟩ := Finset.mem_filter.mp hb
      exact D.no_triangle hxa hxb ((D.mem_commonTo S b).mp hbC a haS)
    simp [hC]


-- @@ L154-173 verbatim
theorem biclique_weighted_square {S : Finset V} (hcard : S.card = 3)
    (hI : D.IndependentSet S) {x : V} (hx : x ∉ S ∪ D.commonTo S) :
    (∑ y, D.kreinMatrix x y * (D.neighborCount (S ∪ D.commonTo S) y : ℤ)^2) =
      108 - 27 * D.neighborCount (S ∪ D.commonTo S) x +
        3 * (D.neighborCount (S ∪ D.commonTo S) x : ℤ)^2 := by
  have hL := D.independentTriple_weighted_square hcard hI
    (fun h => hx (Finset.mem_union_left _ h))
  have hR := D.independentTriple_weighted_square (D.commonTo_card hcard hI)
    (D.commonTo_independent (Finset.card_pos.mp (by omega : 0 < S.card)))
    (fun h => hx (Finset.mem_union_right _ h))
  have heq (y) : D.kreinMatrix x y * (D.neighborCount (S ∪ D.commonTo S) y : ℤ)^2 =
      D.kreinMatrix x y * (D.neighborCount S y : ℤ)^2 +
        D.kreinMatrix x y * (D.neighborCount (D.commonTo S) y : ℤ)^2 := by
    rw [D.biclique_neighborCount_split, Nat.cast_add]
    have hz := D.biclique_neighborCount_product_zero S y
    linear_combination 2 * D.kreinMatrix x y * hz
  rw [Finset.sum_congr rfl (fun y _ => heq y), Finset.sum_add_distrib, hL, hR,
    D.biclique_neighborCount_split, Nat.cast_add]
  have hz := D.biclique_neighborCount_product_zero S x
  nlinarith


-- @@ L175-176 verbatim
def bicliqueOutsideNeighbors (S : Finset V) (x : V) : Finset V :=
  (D.bicliqueOutside S).filter fun y => D.kreinGraph.Adj x y


-- @@ L178-195 verbatim
theorem bicliqueOutside_neighbor_sum (S : Finset V) (x : V) (f : V → ℤ) (c : ℤ)
    (hc : ∀ y ∈ S ∪ D.commonTo S, f y = c) :
    (∑ y ∈ D.bicliqueOutsideNeighbors S x, f y) =
      (∑ y, D.kreinMatrix x y * f y) - c * D.neighborCount (S ∪ D.commonTo S) x := by
  let T := S ∪ D.commonTo S
  have hi : (∑ y ∈ T, D.kreinMatrix x y * f y) = c * D.neighborCount T x := by
    rw [D.neighborCount_cast, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y hy
    rw [hc y hy, mul_comm]
  have ho : (∑ y ∈ Finset.univ \ T, D.kreinMatrix x y * f y) =
      ∑ y ∈ D.bicliqueOutsideNeighbors S x, f y := by
    simp [bicliqueOutsideNeighbors, bicliqueOutside, T, ← D.kreinGraph_adjMatrix,
      SimpleGraph.adjMatrix_apply, Finset.sum_filter]
  have h := Finset.sum_sdiff (Finset.subset_univ T) (f := fun y => D.kreinMatrix x y * f y)
  rw [hi, ho] at h
  dsimp [T] at h
  linarith


-- @@ L197-218 verbatim
theorem bicliqueOutside_neighbor_moments {S : Finset V} (hcard : S.card = 3)
    (hI : D.IndependentSet S) {x : V} (hx : x ∉ S ∪ D.commonTo S) :
    ((D.bicliqueOutsideNeighbors S x).card : ℤ) =
      57 - D.neighborCount (S ∪ D.commonTo S) x ∧
    (∑ y ∈ D.bicliqueOutsideNeighbors S x, (D.neighborCount (S ∪ D.commonTo S) y : ℤ)) =
      72 - 15 * D.neighborCount (S ∪ D.commonTo S) x ∧
    (∑ y ∈ D.bicliqueOutsideNeighbors S x, (D.neighborCount (S ∪ D.commonTo S) y : ℤ)^2) =
      108 - 36 * D.neighborCount (S ∪ D.commonTo S) x +
        3 * (D.neighborCount (S ∪ D.commonTo S) x : ℤ)^2 := by
  have hin (y) (hy : y ∈ S ∪ D.commonTo S) :
      (D.neighborCount (S ∪ D.commonTo S) y : ℤ) = 3 := by
    rw [D.neighborCount_biclique_of_mem hcard hI hy]
    norm_num
  have h0 := D.bicliqueOutside_neighbor_sum S x (fun _ => 1) 1 (by simp)
  have h1 := D.bicliqueOutside_neighbor_sum S x (fun y => D.neighborCount (S ∪ D.commonTo S) y) 3 hin
  have h2 := D.bicliqueOutside_neighbor_sum S x (fun y => (D.neighborCount (S ∪ D.commonTo S) y : ℤ)^2) 9
    (by intro y hy; rw [hin y hy]; norm_num)
  simp only [mul_one, Finset.sum_const, nsmul_eq_mul, D.kreinMatrix_row_sum, one_mul] at h0
  rw [D.neighborCount_weighted_sum, if_neg hx, D.biclique_card hcard hI] at h1
  rw [D.biclique_weighted_square hcard hI hx] at h2
  norm_num at h1
  refine ⟨h0, ?_, ?_⟩ <;> linarith


-- @@ L220-227 verbatim
theorem bicliqueOutsideNeighbors_fiber_card (S : Finset V) (x : V) (i : ℕ) :
    ((D.bicliqueOutsideNeighbors S x).filter fun y => D.neighborCount (S ∪ D.commonTo S) y = i).card =
      D.neighborCount (D.bicliqueClass S i) x := by
  unfold bicliqueOutsideNeighbors neighborCount bicliqueClass
  congr 1
  ext y
  simp only [Finset.mem_filter]
  tauto


-- @@ L229-257 verbatim
theorem biclique_local_degrees {S : Finset V} (hcard : S.card = 3)
    (hI : D.IndependentSet S) {x : V} (hx : x ∉ S ∪ D.commonTo S) :
    D.neighborCount (D.bicliqueClass S 0) x =
      (if D.neighborCount (S ∪ D.commonTo S) x = 0 then 3 else
        if D.neighborCount (S ∪ D.commonTo S) x = 1 then 8 else 16) ∧
    D.neighborCount (D.bicliqueClass S 1) x =
      (if D.neighborCount (S ∪ D.commonTo S) x = 1 then 39 else 36) ∧
    D.neighborCount (D.bicliqueClass S 2) x =
      (if D.neighborCount (S ∪ D.commonTo S) x = 0 then 18 else
        if D.neighborCount (S ∪ D.commonTo S) x = 1 then 9 else 3) := by
  have hle : ∀ y ∈ D.bicliqueOutsideNeighbors S x, D.neighborCount (S ∪ D.commonTo S) y ≤ 2 := by
    intro y hy
    exact D.biclique_outside_degree_le_two hcard hI
      ((D.mem_bicliqueOutside S y).mp (Finset.mem_filter.mp hy).1)
  have h := boundedTwo_fiber_moments (D.bicliqueOutsideNeighbors S x)
    (D.neighborCount (S ∪ D.commonTo S)) hle
  simp only [D.bicliqueOutsideNeighbors_fiber_card] at h
  have hm := D.bicliqueOutside_neighbor_moments hcard hI hx
  have hbound := D.biclique_outside_degree_le_two hcard hI hx
  change D.neighborCount (S ∪ D.commonTo S) x ≤ 2 at hbound
  have hcases : D.neighborCount (S ∪ D.commonTo S) x = 0 ∨
      D.neighborCount (S ∪ D.commonTo S) x = 1 ∨ D.neighborCount (S ∪ D.commonTo S) x = 2 := by omega
  rcases hcases with h0 | h1 | h2
  · norm_num [h0] at hm ⊢
    omega
  · norm_num [h1] at hm ⊢
    omega
  · norm_num [h2] at hm ⊢
    omega


-- @@ L259-264 verbatim
theorem bicliqueClass_zero_degree_self {S : Finset V} (hcard : S.card = 3)
    (hI : D.IndependentSet S) {x : V} (hx : x ∈ D.bicliqueClass S 0) :
    D.neighborCount (D.bicliqueClass S 0) x = 3 := by
  obtain ⟨hxout,h0⟩ := Finset.mem_filter.mp hx
  have h := D.biclique_local_degrees hcard hI ((D.mem_bicliqueOutside S x).mp hxout)
  simpa only [h0, if_true] using h.1


-- @@ L266-271 verbatim
theorem bicliqueClass_two_degree_self {S : Finset V} (hcard : S.card = 3)
    (hI : D.IndependentSet S) {x : V} (hx : x ∈ D.bicliqueClass S 2) :
    D.neighborCount (D.bicliqueClass S 2) x = 3 := by
  obtain ⟨hxout,h2⟩ := Finset.mem_filter.mp hx
  have h := D.biclique_local_degrees hcard hI ((D.mem_bicliqueOutside S x).mp hxout)
  simpa [h2] using h.2.2


-- @@ L273-304 verbatim
theorem biclique_inside_degrees {S : Finset V} (hcard : S.card = 3)
    (hI : D.IndependentSet S) {x : V} (hx : x ∈ S ∪ D.commonTo S) :
    D.neighborCount (D.bicliqueClass S 0) x = 0 ∧
    D.neighborCount (D.bicliqueClass S 1) x = 36 ∧
    D.neighborCount (D.bicliqueClass S 2) x = 18 := by
  have hzero : D.neighborCount (D.bicliqueClass S 0) x = 0 := by
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_of_forall_notMem
    intro y hy
    obtain ⟨hy0,hxy⟩ := Finset.mem_filter.mp hy
    have h0 := (Finset.mem_filter.mp hy0).2
    have hpos : 0 < D.neighborCount (S ∪ D.commonTo S) y := Finset.card_pos.mpr
      ⟨x, Finset.mem_filter.mpr ⟨hx, (D.kreinGraph.adj_comm x y).mp hxy⟩⟩
    omega
  have hin (y) (hy : y ∈ S ∪ D.commonTo S) :
      (D.neighborCount (S ∪ D.commonTo S) y : ℤ) = 3 := by
    rw [D.neighborCount_biclique_of_mem hcard hI hy]
    norm_num
  have hm0 := D.bicliqueOutside_neighbor_sum S x (fun _ => 1) 1 (by simp)
  have hm1 := D.bicliqueOutside_neighbor_sum S x (fun y => D.neighborCount (S ∪ D.commonTo S) y) 3 hin
  rw [D.neighborCount_weighted_sum, if_pos hx, D.biclique_card hcard hI] at hm1
  simp only [mul_one, Finset.sum_const, nsmul_eq_mul, D.kreinMatrix_row_sum, one_mul] at hm0
  rw [D.neighborCount_biclique_of_mem hcard hI hx] at hm0 hm1
  norm_num at hm0 hm1
  have hle : ∀ y ∈ D.bicliqueOutsideNeighbors S x, D.neighborCount (S ∪ D.commonTo S) y ≤ 2 := by
    intro y hy
    exact D.biclique_outside_degree_le_two hcard hI
      ((D.mem_bicliqueOutside S y).mp (Finset.mem_filter.mp hy).1)
  have hf := boundedTwo_fiber_moments (D.bicliqueOutsideNeighbors S x)
    (D.neighborCount (S ∪ D.commonTo S)) hle
  simp only [D.bicliqueOutsideNeighbors_fiber_card] at hf
  omega


-- @@ L306-306 verbatim
end SRG266.QuasiSymmetric.TripleDesign57
