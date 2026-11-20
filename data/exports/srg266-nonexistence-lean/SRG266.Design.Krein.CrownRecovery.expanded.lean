/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Design.Krein.CrownMatching


-- @@ L8-8 verbatim
open scoped BigOperators Matrix


-- @@ L10-10 verbatim
namespace SRG266.QuasiSymmetric.TripleDesign57


-- @@ L12-13 verbatim
variable {P B : Type*} [Fintype P] [DecidableEq P] [Fintype B] [DecidableEq B]
    (D : TripleDesign57 P B)


-- @@ L15-15 verbatim
local notation "V" => KreinVertex (P := P) (B := B)


-- @@ L17-47 verbatim
theorem crown_independent_triple_one_part {L R T : Finset V} (h : D.CrownParts L R)
    (hT : T.card = 3) (hTI : D.IndependentSet T) (hsub : T ⊆ L ∪ R) : T ⊆ L ∨ T ⊆ R := by
  by_cases hTL : T ⊆ L
  · exact Or.inl hTL
  · by_cases hTR : T ⊆ R
    · exact Or.inr hTR
    · obtain ⟨x,hxT,hxR⟩ := Finset.not_subset.mp hTR
      obtain ⟨y,hyT,hyL⟩ := Finset.not_subset.mp hTL
      have hxL : x ∈ L := (Finset.mem_union.mp (hsub hxT)).resolve_right hxR
      have hyR : y ∈ R := (Finset.mem_union.mp (hsub hyT)).resolve_left hyL
      have hLsub : T ∩ L ⊆ L.filter (fun z => ¬ D.kreinGraph.Adj y z) := by
        intro z hz
        obtain ⟨hzT,hzL⟩ := Finset.mem_inter.mp hz
        exact Finset.mem_filter.mpr ⟨hzL,fun ha => hTI y hyT z hzT (D.kreinGraph.ne_of_adj ha) ha⟩
      have hRsub : T ∩ R ⊆ R.filter (fun z => ¬ D.kreinGraph.Adj x z) := by
        intro z hz
        obtain ⟨hzT,hzR⟩ := Finset.mem_inter.mp hz
        exact Finset.mem_filter.mpr ⟨hzR,fun ha => hTI x hxT z hzT (D.kreinGraph.ne_of_adj ha) ha⟩
      have hLc := Finset.card_le_card hLsub
      have hRc := Finset.card_le_card hRsub
      rw [D.crown_left_missing (D.crownParts_symm h) hyR] at hLc
      rw [D.crown_left_missing h hxL] at hRc
      have heq : T = (T ∩ L) ∪ (T ∩ R) := by
        ext z
        have hz := @hsub z
        simp only [Finset.mem_union, Finset.mem_inter] at hz ⊢
        tauto
      have hdis : Disjoint (T ∩ L) (T ∩ R) := h.disjoint.mono Finset.inter_subset_right Finset.inter_subset_right
      have hc := congrArg Finset.card heq
      rw [Finset.card_union_of_disjoint hdis] at hc
      omega


-- @@ L49-54 verbatim
theorem crown_degree {L R : Finset V} (h : D.CrownParts L R) {x : V} (hx : x ∈ L ∪ R) :
    D.neighborCount (L ∪ R) x = 5 := by
  rw [D.neighborCount_union _ _ h.disjoint]
  rcases Finset.mem_union.mp hx with hxL | hxR
  · rw [D.independent_neighborCount_zero h.left_independent hxL,h.left_degree x hxL]
  · rw [D.independent_neighborCount_zero h.right_independent hxR,h.right_degree x hxR]


-- @@ L56-101 verbatim
theorem crown_decomposition_left {L R T : Finset V} (h : D.CrownParts L R)
    (hT : T.card = 3) (hTL : T ⊆ L) : ∃ B : Finset V,
      D.IsBiclique B ∧ B ⊆ D.bicliqueClass T 2 ∧ L ∪ R = (T ∪ D.commonTo T) ∪ B := by
  let F := T.image (D.crownMate h)
  let U := L \ T
  have hFsub : F ⊆ R := D.crownMate_image_subset h hTL
  have hFcard : F.card = 3 := (D.crownMate_image_card h hTL).trans hT
  have hUcard : U.card = 3 := by rw [Finset.card_sdiff_of_subset hTL,h.left_card,hT]
  have hUI : D.IndependentSet U := D.independentSet_mono Finset.sdiff_subset h.left_independent
  have hCT : D.commonTo T = R \ F := D.crown_commonTo_triple h hT hTL
  have hFU : F ⊆ D.commonTo U := by
    intro y hy
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hy
    apply (D.mem_commonTo U (D.crownMate h a)).mpr
    intro x hx
    obtain ⟨hxL,hxT⟩ := Finset.mem_sdiff.mp hx
    apply (D.crown_adj_iff h hxL (D.crownMate_spec h (hTL ha)).1).mpr
    intro heq
    have hax := D.crownMate_injOn h (hTL ha) hxL heq
    exact hxT (hax ▸ ha)
  have hCU : D.commonTo U = F :=
    (Finset.eq_of_subset_of_card_le hFU (by rw [D.commonTo_card hUcard hUI,hFcard])).symm
  have hcover : (T ∪ D.commonTo T) ∪ (U ∪ D.commonTo U) = L ∪ R := by
    rw [hCT,hCU]
    ext z
    have ht : z ∈ T → z ∈ L := fun hz => hTL hz
    have hf : z ∈ F → z ∈ R := fun hz => hFsub hz
    simp only [U,Finset.mem_union,Finset.mem_sdiff]
    tauto
  have hdis : Disjoint (T ∪ D.commonTo T) (U ∪ D.commonTo U) := by
    rw [hCT,hCU]
    apply Finset.disjoint_left.mpr
    intro z hz0 hz1
    have ht : z ∈ T → z ∈ L := fun hz => hTL hz
    have hf : z ∈ F → z ∈ R := fun hz => hFsub hz
    have hn : ¬ (z ∈ L ∧ z ∈ R) := fun hz => Finset.disjoint_left.mp h.disjoint hz.1 hz.2
    simp only [U,Finset.mem_union,Finset.mem_sdiff] at hz0 hz1
    tauto
  have hsub : U ∪ D.commonTo U ⊆ D.bicliqueClass T 2 := by
    intro x hx
    have hxW : x ∈ L ∪ R := hcover ▸ Finset.mem_union_right _ hx
    have hd := D.crown_degree h hxW
    rw [← hcover,D.neighborCount_union _ _ hdis,D.neighborCount_biclique_of_mem hUcard hUI hx] at hd
    apply (D.mem_bicliqueClass T 2 x).mpr
    exact ⟨fun hxT => Finset.disjoint_left.mp hdis hxT hx,by omega⟩
  exact ⟨U ∪ D.commonTo U,⟨U,hUcard,hUI,rfl⟩,hsub,hcover.symm⟩


-- @@ L103-109 verbatim
theorem crown_decomposition {W T : Finset V} (hW : D.IsCrown W)
    (hT : T.card = 3) (hTI : D.IndependentSet T) (hsub : T ⊆ W) : ∃ B : Finset V,
      D.IsBiclique B ∧ B ⊆ D.bicliqueClass T 2 ∧ W = (T ∪ D.commonTo T) ∪ B := by
  obtain ⟨L,R,h,rfl⟩ := hW
  rcases D.crown_independent_triple_one_part h hT hTI hsub with hTL | hTR
  · exact D.crown_decomposition_left h hT hTL
  · simpa only [Finset.union_comm] using D.crown_decomposition_left (D.crownParts_symm h) hT hTR


-- @@ L111-117 verbatim
theorem crowns_eq_of_containing_triple {W Z T : Finset V} (hW : D.IsCrown W)
    (hZ : D.IsCrown Z) (hT : T.card = 3) (hTI : D.IndependentSet T)
    (hTW : T ⊆ W) (hTZ : T ⊆ Z) : W = Z := by
  obtain ⟨B,hB,hBX,hWeq⟩ := D.crown_decomposition hW hT hTI hTW
  obtain ⟨C,hC,hCX,hZeq⟩ := D.crown_decomposition hZ hT hTI hTZ
  have hBC := D.bicliques_in_class_two_eq hT hTI hB hC hBX hCX
  rw [hWeq,hZeq,hBC]


-- @@ L119-125 verbatim
theorem exists_unique_crown_of_independent_triple {T : Finset V}
    (hT : T.card = 3) (hTI : D.IndependentSet T) :
    ∃! W : Finset V, D.IsCrown W ∧ T ⊆ W := by
  obtain ⟨W,hW,hTW⟩ := D.exists_crown_of_independent_triple hT hTI
  refine ⟨W,⟨hW,hTW⟩,?_⟩
  intro Z hZ
  exact D.crowns_eq_of_containing_triple hZ.1 hW hT hTI hZ.2 hTW


-- @@ L127-127 verbatim
end SRG266.QuasiSymmetric.TripleDesign57
