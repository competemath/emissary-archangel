/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Design.Krein.Companion


-- @@ L8-8 verbatim
open scoped BigOperators Matrix


-- @@ L10-10 verbatim
namespace SRG266.QuasiSymmetric.TripleDesign57


-- @@ L12-13 verbatim
variable {P B : Type*} [Fintype P] [DecidableEq P] [Fintype B] [DecidableEq B]
    (D : TripleDesign57 P B)


-- @@ L15-15 verbatim
local notation "V" => KreinVertex (P := P) (B := B)


-- @@ L17-24 verbatim
structure CrownParts (L R : Finset V) : Prop where
  left_card : L.card = 6
  right_card : R.card = 6
  disjoint : Disjoint L R
  left_independent : D.IndependentSet L
  right_independent : D.IndependentSet R
  left_degree : ∀ x ∈ L, D.neighborCount R x = 5
  right_degree : ∀ x ∈ R, D.neighborCount L x = 5


-- @@ L26-26 verbatim
def IsCrown (W : Finset V) : Prop := ∃ L R : Finset V, D.CrownParts L R ∧ W = L ∪ R


-- @@ L28-29 verbatim
theorem independentSet_mono {T U : Finset V} (hTU : T ⊆ U) (hI : D.IndependentSet U) :
    D.IndependentSet T := fun x hx y hy hxy => hI x (hTU hx) y (hTU hy) hxy


-- @@ L31-37 verbatim
theorem independent_neighborCount_zero {T : Finset V} (hI : D.IndependentSet T)
    {x : V} (hx : x ∈ T) : D.neighborCount T x = 0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_of_forall_notMem
  intro y hy
  obtain ⟨hyT,hxy⟩ := Finset.mem_filter.mp hy
  exact hI x hx y hyT (D.kreinGraph.ne_of_adj hxy) hxy


-- @@ L39-43 verbatim
theorem not_adj_of_neighborCount_zero {T : Finset V} {x y : V}
    (hzero : D.neighborCount T x = 0) (hy : y ∈ T) : ¬ D.kreinGraph.Adj x y := by
  intro hxy
  have hp : 0 < D.neighborCount T x := Finset.card_pos.mpr ⟨y,Finset.mem_filter.mpr ⟨hy,hxy⟩⟩
  omega


-- @@ L45-53 verbatim
theorem independentSet_union {T U : Finset V} (hT : D.IndependentSet T)
    (hU : D.IndependentSet U) (hcross : ∀ x ∈ T, ∀ y ∈ U, ¬ D.kreinGraph.Adj x y) :
    D.IndependentSet (T ∪ U) := by
  intro x hx y hy hxy ha
  rcases Finset.mem_union.mp hx with hxT | hxU <;> rcases Finset.mem_union.mp hy with hyT | hyU
  · exact hT x hxT y hyT hxy ha
  · exact hcross x hxT y hyU ha
  · exact hcross y hyT x hxU ((D.kreinGraph.adj_comm x y).mp ha)
  · exact hU x hxU y hyU hxy ha


-- @@ L55-60 verbatim
theorem companions_disjoint {S R : Finset V}
    (hsub : R ∪ D.commonTo R ⊆ D.bicliqueClass S 2) :
    Disjoint (S ∪ D.commonTo S) (R ∪ D.commonTo R) := by
  apply Finset.disjoint_left.mpr
  intro x hxS hxR
  exact ((D.mem_bicliqueClass S 2 x).mp (hsub hxR)).1 hxS


-- @@ L62-87 verbatim
theorem companion_side_traces {S R : Finset V} (hS : S.card = 3)
    (hSI : D.IndependentSet S) (hR : R.card = 3) (hRI : D.IndependentSet R)
    (hsub : R ∪ D.commonTo R ⊆ D.bicliqueClass S 2) :
    ((∀ x ∈ R, D.neighborCount S x = 0) ∧ (∀ x ∈ D.commonTo R, D.neighborCount S x = 2)) ∨
    ((∀ x ∈ R, D.neighborCount S x = 2) ∧ (∀ x ∈ D.commonTo R, D.neighborCount S x = 0)) := by
  obtain ⟨a,ha⟩ := Finset.card_pos.mp (by omega : 0 < R.card)
  obtain ⟨b,hb⟩ := Finset.card_pos.mp (by rw [D.commonTo_card hR hRI]; omega : 0 < (D.commonTo R).card)
  have hab := D.bicliqueClass_two_adj_traces hS hSI
    (hsub (Finset.mem_union_left _ ha)) (hsub (Finset.mem_union_right _ hb))
    ((D.mem_commonTo R b).mp hb a ha)
  have hleft (x) (hx : x ∈ R) : D.neighborCount S x = D.neighborCount S a := by
    have h := D.bicliqueClass_two_adj_traces hS hSI
      (hsub (Finset.mem_union_left _ hx)) (hsub (Finset.mem_union_right _ hb))
      ((D.mem_commonTo R b).mp hb x hx)
    omega
  have hright (y) (hy : y ∈ D.commonTo R) : D.neighborCount S a + D.neighborCount S y = 2 :=
    D.bicliqueClass_two_adj_traces hS hSI
      (hsub (Finset.mem_union_left _ ha)) (hsub (Finset.mem_union_right _ hy))
      ((D.mem_commonTo R y).mp hy a ha)
  rcases D.bicliqueClass_two_sides (hsub (Finset.mem_union_left _ ha)) with h2 | h0
  · right
    exact ⟨fun x hx => by have h := hleft x hx; omega,
      fun y hy => by have h := hright y hy; omega⟩
  · left
    exact ⟨fun x hx => by have h := hleft x hx; omega,
      fun y hy => by have h := hright y hy; omega⟩


-- @@ L89-101 verbatim
theorem exists_oriented_companion {S : Finset V} (hS : S.card = 3)
    (hSI : D.IndependentSet S) : ∃ R : Finset V,
      R.card = 3 ∧ D.IndependentSet R ∧ R ∪ D.commonTo R ⊆ D.bicliqueClass S 2 ∧
      (∀ x ∈ R, D.neighborCount S x = 0) ∧ (∀ x ∈ D.commonTo R, D.neighborCount S x = 2) := by
  obtain ⟨R,hR,hRI,hsub⟩ := D.exists_biclique_in_class_two hS hSI
  rcases D.companion_side_traces hS hSI hR hRI hsub with hgood | hswap
  · exact ⟨R,hR,hRI,hsub,hgood⟩
  · refine ⟨D.commonTo R,D.commonTo_card hR hRI,
      D.commonTo_independent (Finset.card_pos.mp (by omega : 0 < R.card)),?_,hswap.2,?_⟩
    · rw [D.commonTo_involution hR hRI, Finset.union_comm]
      exact hsub
    · rw [D.commonTo_involution hR hRI]
      exact hswap.1


-- @@ L103-115 verbatim
theorem companion_union_degrees {S R : Finset V} (hS : S.card = 3)
    (hSI : D.IndependentSet S) (hR : R.card = 3) (hRI : D.IndependentSet R)
    (hsub : R ∪ D.commonTo R ⊆ D.bicliqueClass S 2) :
    ∀ x ∈ (S ∪ D.commonTo S) ∪ (R ∪ D.commonTo R),
      D.neighborCount ((S ∪ D.commonTo S) ∪ (R ∪ D.commonTo R)) x = 5 := by
  have hrec := D.biclique_companion_reciprocal hS hSI hR hRI hsub
  intro x hx
  rw [D.neighborCount_union _ _ (D.companions_disjoint hsub)]
  rcases Finset.mem_union.mp hx with hxS | hxR
  · rw [D.neighborCount_biclique_of_mem hS hSI hxS,
      ((D.mem_bicliqueClass R 2 x).mp (hrec hxS)).2]
  · rw [D.neighborCount_biclique_of_mem hR hRI hxR,
      ((D.mem_bicliqueClass S 2 x).mp (hsub hxR)).2]


-- @@ L117-160 verbatim
theorem crownParts_of_oriented_companion {S R : Finset V} (hS : S.card = 3)
    (hSI : D.IndependentSet S) (hR : R.card = 3) (hRI : D.IndependentSet R)
    (hsub : R ∪ D.commonTo R ⊆ D.bicliqueClass S 2)
    (hleft : ∀ x ∈ R, D.neighborCount S x = 0)
    (hright : ∀ x ∈ D.commonTo R, D.neighborCount S x = 2) :
    D.CrownParts (S ∪ R) (D.commonTo S ∪ D.commonTo R) := by
  have hdis := D.companions_disjoint hsub
  have hSR : Disjoint S R := hdis.mono Finset.subset_union_left Finset.subset_union_left
  have hCC : Disjoint (D.commonTo S) (D.commonTo R) :=
    hdis.mono Finset.subset_union_right Finset.subset_union_right
  have hbig : Disjoint (S ∪ R) (D.commonTo S ∪ D.commonTo R) := by
    apply Finset.disjoint_left.mpr
    intro x hxL hxBigR
    rcases Finset.mem_union.mp hxL with hxS | hxR <;> rcases Finset.mem_union.mp hxBigR with hxCS | hxCR
    · exact Finset.disjoint_left.mp (D.disjoint_commonTo S) hxS hxCS
    · exact Finset.disjoint_left.mp hdis (Finset.mem_union_left _ hxS) (Finset.mem_union_right _ hxCR)
    · exact Finset.disjoint_left.mp hdis (Finset.mem_union_right _ hxCS) (Finset.mem_union_left _ hxR)
    · exact Finset.disjoint_left.mp (D.disjoint_commonTo R) hxR hxCR
  have hIL : D.IndependentSet (S ∪ R) := D.independentSet_union hSI hRI (by
    intro x hx y hy hxy
    exact D.not_adj_of_neighborCount_zero (hleft y hy) hx ((D.kreinGraph.adj_comm x y).mp hxy))
  have hIR : D.IndependentSet (D.commonTo S ∪ D.commonTo R) := D.independentSet_union
    (D.commonTo_independent (Finset.card_pos.mp (by omega : 0 < S.card)))
    (D.commonTo_independent (Finset.card_pos.mp (by omega : 0 < R.card))) (by
      intro x hx y hy hxy
      have h2 := (D.mem_bicliqueClass S 2 y).mp (hsub (Finset.mem_union_right _ hy)) |>.2
      rw [D.biclique_neighborCount_split, hright y hy] at h2
      have hzero : D.neighborCount (D.commonTo S) y = 0 := by omega
      exact D.not_adj_of_neighborCount_zero hzero hx ((D.kreinGraph.adj_comm x y).mp hxy))
  have heq : (S ∪ D.commonTo S) ∪ (R ∪ D.commonTo R) =
      (S ∪ R) ∪ (D.commonTo S ∪ D.commonTo R) := by ac_rfl
  have hd := D.companion_union_degrees hS hSI hR hRI hsub
  rw [heq] at hd
  refine ⟨?_,?_,hbig,hIL,hIR,?_,?_⟩
  · rw [Finset.card_union_of_disjoint hSR, hS, hR]
  · rw [Finset.card_union_of_disjoint hCC, D.commonTo_card hS hSI, D.commonTo_card hR hRI]
  · intro x hx
    have h := hd x (Finset.mem_union_left _ hx)
    rw [D.neighborCount_union _ _ hbig, D.independent_neighborCount_zero hIL hx] at h
    omega
  · intro x hx
    have h := hd x (Finset.mem_union_right _ hx)
    rw [D.neighborCount_union _ _ hbig, D.independent_neighborCount_zero hIR hx] at h
    omega


-- @@ L162-168 verbatim
theorem exists_crown_of_independent_triple {S : Finset V} (hS : S.card = 3)
    (hSI : D.IndependentSet S) : ∃ W : Finset V, D.IsCrown W ∧ S ⊆ W := by
  obtain ⟨R,hR,hRI,hsub,hleft,hright⟩ := D.exists_oriented_companion hS hSI
  refine ⟨(S ∪ R) ∪ (D.commonTo S ∪ D.commonTo R),
    ⟨S ∪ R,D.commonTo S ∪ D.commonTo R,
      D.crownParts_of_oriented_companion hS hSI hR hRI hsub hleft hright,rfl⟩,?_⟩
  exact Finset.subset_union_left.trans Finset.subset_union_left


-- @@ L170-170 verbatim
end SRG266.QuasiSymmetric.TripleDesign57
