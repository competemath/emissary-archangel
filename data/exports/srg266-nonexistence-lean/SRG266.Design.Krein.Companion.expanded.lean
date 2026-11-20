/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Design.Krein.ParityObstruction


-- @@ L8-8 verbatim
open scoped BigOperators Matrix


-- @@ L10-10 verbatim
namespace SRG266.QuasiSymmetric.TripleDesign57


-- @@ L12-13 verbatim
variable {P B : Type*} [Fintype P] [DecidableEq P] [Fintype B] [DecidableEq B]
    (D : TripleDesign57 P B)


-- @@ L15-15 verbatim
local notation "V" => KreinVertex (P := P) (B := B)


-- @@ L17-18 verbatim
def IsBiclique (T : Finset V) : Prop :=
  ∃ R : Finset V, R.card = 3 ∧ D.IndependentSet R ∧ T = R ∪ D.commonTo R


-- @@ L20-22 verbatim
theorem biclique_set_card {T : Finset V} (hT : D.IsBiclique T) : T.card = 6 := by
  obtain ⟨R,hR,hRI,rfl⟩ := hT
  exact D.biclique_card hR hRI


-- @@ L24-38 verbatim
theorem biclique_in_class_two_closed {S T : Finset V} (hS : S.card = 3)
    (hSI : D.IndependentSet S) (hT : D.IsBiclique T) (hsub : T ⊆ D.bicliqueClass S 2)
    {x y : V} (hx : x ∈ T) (hy : y ∈ D.bicliqueClass S 2)
    (hxy : D.kreinGraph.Adj x y) : y ∈ T := by
  obtain ⟨R,hR,hRI,rfl⟩ := hT
  have hsmall := D.neighborCount_biclique_of_mem hR hRI hx
  have hlarge := D.bicliqueClass_two_degree_self hS hSI (hsub hx)
  have hs : (R ∪ D.commonTo R).filter (fun z => D.kreinGraph.Adj x z) ⊆
      (D.bicliqueClass S 2).filter (fun z => D.kreinGraph.Adj x z) :=
    Finset.filter_subset_filter _ hsub
  have heq := Finset.eq_of_subset_of_card_le hs (by
    change D.neighborCount (D.bicliqueClass S 2) x ≤ D.neighborCount (R ∪ D.commonTo R) x
    omega)
  have hmem := heq.symm ▸ Finset.mem_filter.mpr ⟨hy,hxy⟩
  exact (Finset.mem_filter.mp hmem).1


-- @@ L40-64 verbatim
theorem biclique_subset_of_closed {R A W : Finset V} (hR : R.card = 3)
    (hRI : D.IndependentSet R) (hsub : R ∪ D.commonTo R ⊆ W)
    (hclosed : ∀ x ∈ A, ∀ y ∈ W, D.kreinGraph.Adj x y → y ∈ A)
    {z : V} (hzA : z ∈ A) (hzR : z ∈ R ∪ D.commonTo R) : R ∪ D.commonTo R ⊆ A := by
  have hRpos : R.Nonempty := Finset.card_pos.mp (by omega)
  have hCpos : (D.commonTo R).Nonempty :=
    Finset.card_pos.mp (by rw [D.commonTo_card hR hRI]; omega)
  rcases Finset.mem_union.mp hzR with hzL | hzC
  · have hCA : D.commonTo R ⊆ A := by
      intro y hy
      exact hclosed z hzA y (hsub (Finset.mem_union_right _ hy)) ((D.mem_commonTo R y).mp hy z hzL)
    obtain ⟨b,hb⟩ := hCpos
    apply Finset.union_subset _ hCA
    intro y hy
    exact hclosed b (hCA hb) y (hsub (Finset.mem_union_left _ hy))
      ((D.kreinGraph.adj_comm y b).mp ((D.mem_commonTo R b).mp hb y hy))
  · have hRA : R ⊆ A := by
      intro y hy
      exact hclosed z hzA y (hsub (Finset.mem_union_left _ hy))
        ((D.kreinGraph.adj_comm y z).mp ((D.mem_commonTo R z).mp hzC y hy))
    obtain ⟨a,ha⟩ := hRpos
    apply Finset.union_subset hRA
    intro y hy
    exact hclosed a (hRA ha) y (hsub (Finset.mem_union_right _ hy))
      ((D.mem_commonTo R y).mp hy a ha)


-- @@ L66-97 verbatim
theorem bicliques_in_class_two_eq {S T U : Finset V} (hS : S.card = 3)
    (hSI : D.IndependentSet S) (hT : D.IsBiclique T) (hU : D.IsBiclique U)
    (hsubT : T ⊆ D.bicliqueClass S 2) (hsubU : U ⊆ D.bicliqueClass S 2) : T = U := by
  have hclosed : ∀ x ∈ T, ∀ y ∈ D.bicliqueClass S 2, D.kreinGraph.Adj x y → y ∈ T :=
    fun _ hx _ hy hxy => D.biclique_in_class_two_closed hS hSI hT hsubT hx hy hxy
  obtain ⟨R,hR,hRI,hTeq⟩ := hT
  obtain ⟨Q,hQ,hQI,hUeq⟩ := hU
  by_cases hdis : Disjoint T U
  · have hUX0 : U ⊆ D.bicliqueClass R 0 := by
      intro x hxU
      have hxT : x ∉ T := fun hxT => Finset.disjoint_left.mp hdis hxT hxU
      have hzero : D.neighborCount T x = 0 := by
        apply Finset.card_eq_zero.mpr
        apply Finset.eq_empty_of_forall_notMem
        intro y hy
        obtain ⟨hyT,hxy⟩ := Finset.mem_filter.mp hy
        exact hxT (hclosed y hyT x (hsubU hxU) ((D.kreinGraph.adj_comm x y).mp hxy))
      apply (D.mem_bicliqueClass R 0 x).mpr
      rw [← hTeq]
      exact ⟨hxT,hzero⟩
    have hno := D.no_biclique_in_class_zero hR hRI hQ hQI
    rw [← hUeq] at hno
    exact (hno hUX0).elim
  · simp only [Finset.disjoint_left] at hdis
    push Not at hdis
    obtain ⟨z,hzT,hzU⟩ := hdis
    have hUT : U ⊆ T := by
      rw [hUeq] at hsubU hzU ⊢
      exact D.biclique_subset_of_closed hQ hQI hsubU hclosed hzT hzU
    have hTcard : T.card = 6 := by rw [hTeq]; exact D.biclique_card hR hRI
    have hUcard : U.card = 6 := by rw [hUeq]; exact D.biclique_card hQ hQI
    exact (Finset.eq_of_subset_of_card_le hUT (by omega)).symm


-- @@ L99-106 verbatim
theorem exists_unique_biclique_companion {S : Finset V} (hS : S.card = 3)
    (hSI : D.IndependentSet S) :
    ∃! T : Finset V, D.IsBiclique T ∧ T ⊆ D.bicliqueClass S 2 := by
  obtain ⟨R,hR,hRI,hsub⟩ := D.exists_biclique_in_class_two hS hSI
  have hB : D.IsBiclique (R ∪ D.commonTo R) := ⟨R,hR,hRI,rfl⟩
  refine ⟨R ∪ D.commonTo R,⟨hB,hsub⟩,?_⟩
  intro T hT
  exact D.bicliques_in_class_two_eq hS hSI hT.1 hB hT.2 hsub


-- @@ L108-116 verbatim
theorem neighborCount_cross_sum (T U : Finset V) :
    (∑ x ∈ T, (D.neighborCount U x : ℤ)) = ∑ y ∈ U, (D.neighborCount T y : ℤ) := by
  simp_rw [D.neighborCount_cast]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro x _
  exact D.kreinMatrix_comm x y


-- @@ L118-148 verbatim
theorem biclique_companion_reciprocal {S R : Finset V} (hS : S.card = 3)
    (hSI : D.IndependentSet S) (hR : R.card = 3) (hRI : D.IndependentSet R)
    (hsub : R ∪ D.commonTo R ⊆ D.bicliqueClass S 2) :
    S ∪ D.commonTo S ⊆ D.bicliqueClass R 2 := by
  let T := S ∪ D.commonTo S
  let U := R ∪ D.commonTo R
  have hxout (x) (hx : x ∈ T) : x ∉ U := by
    intro hxU
    exact ((D.mem_bicliqueClass S 2 x).mp (hsub hxU)).1 hx
  have hle (x) (hx : x ∈ T) : D.neighborCount U x ≤ 2 :=
    D.biclique_outside_degree_le_two hR hRI (hxout x hx)
  have hUcard : U.card = 6 := D.biclique_card hR hRI
  have hTcard : T.card = 6 := D.biclique_card hS hSI
  have hsum : (∑ x ∈ T, (D.neighborCount U x : ℤ)) = 12 := by
    rw [D.neighborCount_cross_sum]
    have hy (y) (hyU : y ∈ U) : (D.neighborCount T y : ℤ) = 2 := by
      have h := (D.mem_bicliqueClass S 2 y).mp (hsub hyU) |>.2
      rw [h]
      norm_num
    rw [Finset.sum_congr rfl hy]
    simp [hUcard]
  intro x hx
  have htwo : D.neighborCount U x = 2 := by
    by_contra hn
    have hlt : (D.neighborCount U x : ℤ) < 2 := by have h := hle x hx; omega
    have hsumlt := Finset.sum_lt_sum (fun y hy => (by exact_mod_cast hle y hy :
      (D.neighborCount U y : ℤ) ≤ 2)) ⟨x,hx,hlt⟩
    have hc : (∑ _y ∈ T, (2 : ℤ)) = 12 := by simp [hTcard]
    rw [hsum, hc] at hsumlt
    omega
  exact (D.mem_bicliqueClass R 2 x).mpr ⟨hxout x hx,htwo⟩


-- @@ L150-150 verbatim
end SRG266.QuasiSymmetric.TripleDesign57
