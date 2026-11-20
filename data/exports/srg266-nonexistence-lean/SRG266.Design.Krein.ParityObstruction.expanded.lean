/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Design.Krein.SquareExpansion


-- @@ L8-8 verbatim
open scoped BigOperators Matrix


-- @@ L10-10 verbatim
namespace SRG266.QuasiSymmetric.TripleDesign57


-- @@ L12-13 verbatim
variable {P B : Type*} [Fintype P] [DecidableEq P] [Fintype B] [DecidableEq B]
    (D : TripleDesign57 P B)


-- @@ L15-15 verbatim
local notation "V" => KreinVertex (P := P) (B := B)


-- @@ L17-19 verbatim
theorem neighborCount_mono {T U : Finset V} (hTU : T ⊆ U) (x : V) :
    D.neighborCount T x ≤ D.neighborCount U x :=
  Finset.card_le_card (Finset.filter_subset_filter _ hTU)


-- @@ L21-25 verbatim
theorem class_zero_side_counts {S : Finset V} {x : V} (hx : x ∈ D.bicliqueClass S 0) :
    D.neighborCount S x = 0 ∧ D.neighborCount (D.commonTo S) x = 0 := by
  have h := (D.mem_bicliqueClass S 0 x).mp hx |>.2
  rw [D.biclique_neighborCount_split] at h
  omega


-- @@ L27-41 verbatim
theorem outside_non_one_side_even {S : Finset V} (hcard : S.card = 3)
    (hI : D.IndependentSet S) {x : V} (hx : x ∉ S ∪ D.commonTo S)
    (hnot1 : x ∉ D.bicliqueClass S 1) : Even (D.neighborCount S x : ℤ) := by
  have hb := D.biclique_outside_degree_le_two hcard hI hx
  change D.neighborCount (S ∪ D.commonTo S) x ≤ 2 at hb
  have hn : D.neighborCount (S ∪ D.commonTo S) x ≠ 1 :=
    fun h => hnot1 ((D.mem_bicliqueClass S 1 x).mpr ⟨hx,h⟩)
  have hc : D.neighborCount (S ∪ D.commonTo S) x = 0 ∨
      D.neighborCount (S ∪ D.commonTo S) x = 2 := by omega
  rcases hc with h0 | h2
  · have hs := D.neighborCount_mono (Finset.subset_union_left : S ⊆ S ∪ D.commonTo S) x
    have hz : D.neighborCount S x = 0 := by omega
    simp [hz]
  · have hx2 := (D.mem_bicliqueClass S 2 x).mpr ⟨hx,h2⟩
    rcases D.bicliqueClass_two_sides hx2 with h | h <;> simp [h]


-- @@ L43-59 verbatim
theorem class_zero_common_one_eq {S : Finset V} (hcard : S.card = 3)
    (hI : D.IndependentSet S) {x y : V} (hx : x ∈ D.bicliqueClass S 0)
    (hy : y ∈ D.bicliqueClass S 0) (hxy : x ≠ y) (hn : ¬ D.kreinGraph.Adj x y) :
    D.commonCount (D.bicliqueClass S 1) x y +
      2 * D.commonCount (D.bicliqueClass S 0) x y = 6 := by
  have hc := D.commonCount_biclique_partition hcard hI x y
  rw [D.commonCount_univ hxy hn] at hc
  have hzero : D.commonCount (S ∪ D.commonTo S) x y = 0 := by
    have hle := D.commonCount_le_neighborCount (S ∪ D.commonTo S) x y
    have ht := (D.mem_bicliqueClass S 0 x).mp hx |>.2
    omega
  have hU := D.commonCount_union (S ∪ D.commonTo S) (D.bicliqueClass S 0)
    (D.disjoint_biclique_class S 0) x y
  have hgram := D.bicliqueCubicLeft_common hcard hI
    (Finset.mem_union_right _ hx) (Finset.mem_union_right _ hy) hxy hn
  change D.commonCount (D.bicliqueCubicLeft S) x y = _ at hU
  omega


-- @@ L61-105 verbatim
theorem class_zero_common_le_two {S : Finset V} (hcard : S.card = 3)
    (hI : D.IndependentSet S) {x y : V} (hx : x ∈ D.bicliqueClass S 0)
    (hy : y ∈ D.bicliqueClass S 0) (hxy : x ≠ y) :
    D.commonCount (D.bicliqueClass S 0) x y ≤ 2 := by
  by_cases hn : D.kreinGraph.Adj x y
  · rw [D.commonCount_of_adj _ hn]
    omega
  · by_contra hgt
    have hmass := D.class_zero_common_one_eq hcard hI hx hy hxy hn
    have hnone : D.commonCount (D.bicliqueClass S 1) x y = 0 := by omega
    have hxD := (D.mem_bicliqueClass S 0 x).mp hx |>.1
    have hyD := (D.mem_bicliqueClass S 0 y).mp hy |>.1
    have hxS : x ∉ S := fun h => hxD (Finset.mem_union_left _ h)
    have hyS : y ∉ S := fun h => hyD (Finset.mem_union_left _ h)
    have hxside := (D.class_zero_side_counts hx).1
    have hyside := (D.class_zero_side_counts hy).1
    have hcommonS : D.commonCount S x y = 0 := by
      have hle := D.commonCount_le_neighborCount S x y
      omega
    have ht := D.commonTrace_subset S hxy hn
    rw [hcard, hxside, hyside, hcommonS, if_neg hxS, if_neg hyS] at ht
    norm_num only [Nat.cast_ofNat, Nat.cast_zero, mul_zero, add_zero, sub_zero] at ht
    have heven (z : V) : Even (D.kreinMatrix x z * D.kreinMatrix y z *
        (D.neighborCount S z : ℤ)) := by
      by_cases hxz : D.kreinGraph.Adj x z
      · by_cases hyz : D.kreinGraph.Adj y z
        · have hzD : z ∉ S ∪ D.commonTo S := by
            intro hz
            have hpos : 0 < D.neighborCount (S ∪ D.commonTo S) x :=
              Finset.card_pos.mpr ⟨z, Finset.mem_filter.mpr ⟨hz,hxz⟩⟩
            have hzero := (D.mem_bicliqueClass S 0 x).mp hx |>.2
            omega
          have hz1 : z ∉ D.bicliqueClass S 1 := by
            intro hz
            have hpos : 0 < D.commonCount (D.bicliqueClass S 1) x y :=
              Finset.card_pos.mpr ⟨z, Finset.mem_filter.mpr ⟨hz,hxz,hyz⟩⟩
            omega
          exact (D.outside_non_one_side_even hcard hI hzD hz1).mul_left _
        · simp [← D.kreinGraph_adjMatrix, SimpleGraph.adjMatrix_apply, hyz]
      · simp [← D.kreinGraph_adjMatrix, SimpleGraph.adjMatrix_apply, hxz]
    have hsum : Even (∑ z, D.kreinMatrix x z * D.kreinMatrix y z *
        (D.neighborCount S z : ℤ)) := Finset.even_sum _ (fun z _ => heven z)
    rw [ht] at hsum
    obtain ⟨r,hr⟩ := hsum
    omega


-- @@ L107-124 verbatim
theorem no_biclique_in_class_zero {S R : Finset V} (hS : S.card = 3)
    (hSI : D.IndependentSet S) (hR : R.card = 3) (hRI : D.IndependentSet R) :
    ¬ R ∪ D.commonTo R ⊆ D.bicliqueClass S 0 := by
  intro hsub
  obtain ⟨a,b,c,hab,_,_,hReq⟩ := Finset.card_eq_three.mp hR
  have ha : a ∈ R := by rw [hReq]; simp
  have hb : b ∈ R := by rw [hReq]; simp
  have habound := D.class_zero_common_le_two hS hSI
    (hsub (Finset.mem_union_left _ ha)) (hsub (Finset.mem_union_left _ hb)) hab
  have hCsub : D.commonTo R ⊆ (D.bicliqueClass S 0).filter
      (fun z => D.kreinGraph.Adj a z ∧ D.kreinGraph.Adj b z) := by
    intro z hz
    exact Finset.mem_filter.mpr ⟨hsub (Finset.mem_union_right _ hz),
      (D.mem_commonTo R z).mp hz a ha, (D.mem_commonTo R z).mp hz b hb⟩
  have h := Finset.card_le_card hCsub
  change (D.commonTo R).card ≤ D.commonCount (D.bicliqueClass S 0) a b at h
  rw [D.commonTo_card hR hRI] at h
  omega


-- @@ L126-126 verbatim
end SRG266.QuasiSymmetric.TripleDesign57
