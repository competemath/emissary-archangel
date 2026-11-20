/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Design.Krein.Crown


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
theorem crownParts_symm {L R : Finset V} (h : D.CrownParts L R) : D.CrownParts R L :=
  ⟨h.right_card,h.left_card,h.disjoint.symm,h.right_independent,h.left_independent,
    h.right_degree,h.left_degree⟩


-- @@ L21-26 verbatim
theorem crown_left_missing {L R : Finset V} (h : D.CrownParts L R)
    {x : V} (hx : x ∈ L) : (R.filter fun y => ¬ D.kreinGraph.Adj x y).card = 1 := by
  have hsum := Finset.card_filter_add_card_filter_not (s := R) (p := fun y => D.kreinGraph.Adj x y)
  change D.neighborCount R x + (R.filter fun y => ¬ D.kreinGraph.Adj x y).card = R.card at hsum
  rw [h.left_degree x hx, h.right_card] at hsum
  omega


-- @@ L28-32 verbatim
theorem crown_missing_exists {L R : Finset V} (h : D.CrownParts L R)
    {x : V} (hx : x ∈ L) : ∃ y, y ∈ R ∧ ¬ D.kreinGraph.Adj x y := by
  have hc := D.crown_left_missing h hx
  obtain ⟨y,hy⟩ := Finset.card_pos.mp (by omega : 0 < (R.filter fun y => ¬ D.kreinGraph.Adj x y).card)
  exact ⟨y,(Finset.mem_filter.mp hy).1,(Finset.mem_filter.mp hy).2⟩


-- @@ L34-35 verbatim
noncomputable def crownMate {L R : Finset V} (h : D.CrownParts L R) (x : V) : V :=
  if hx : x ∈ L then Classical.choose (D.crown_missing_exists h hx) else none


-- @@ L37-40 verbatim
theorem crownMate_spec {L R : Finset V} (h : D.CrownParts L R) {x : V} (hx : x ∈ L) :
    D.crownMate h x ∈ R ∧ ¬ D.kreinGraph.Adj x (D.crownMate h x) := by
  simp only [crownMate, dif_pos hx]
  exact Classical.choose_spec (D.crown_missing_exists h hx)


-- @@ L42-47 verbatim
theorem crownMate_unique {L R : Finset V} (h : D.CrownParts L R) {x y : V}
    (hx : x ∈ L) (hy : y ∈ R) (hn : ¬ D.kreinGraph.Adj x y) : y = D.crownMate h x := by
  have hc : (R.filter fun z => ¬ D.kreinGraph.Adj x z).card ≤ 1 := by
    rw [D.crown_left_missing h hx]
  exact Finset.card_le_one.mp hc y (Finset.mem_filter.mpr ⟨hy,hn⟩)
    (D.crownMate h x) (Finset.mem_filter.mpr (D.crownMate_spec h hx))


-- @@ L49-59 verbatim
theorem crownMate_injOn {L R : Finset V} (h : D.CrownParts L R) :
    Set.InjOn (D.crownMate h) L := by
  intro x hx y hy heq
  have hmx := D.crownMate_spec h hx
  have hmy := D.crownMate_spec h hy
  rw [← heq] at hmy
  have hc : (L.filter fun z => ¬ D.kreinGraph.Adj (D.crownMate h x) z).card ≤ 1 := by
    rw [D.crown_left_missing (D.crownParts_symm h) hmx.1]
  exact Finset.card_le_one.mp hc x
    (Finset.mem_filter.mpr ⟨hx,fun ha => hmx.2 ((D.kreinGraph.adj_comm _ _).mp ha)⟩) y
    (Finset.mem_filter.mpr ⟨hy,fun ha => hmy.2 ((D.kreinGraph.adj_comm _ _).mp ha)⟩)


-- @@ L61-65 verbatim
theorem crownMate_image_subset {L R T : Finset V} (h : D.CrownParts L R) (hTL : T ⊆ L) :
    T.image (D.crownMate h) ⊆ R := by
  intro y hy
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
  exact (D.crownMate_spec h (hTL hx)).1


-- @@ L67-69 verbatim
theorem crownMate_image_card {L R T : Finset V} (h : D.CrownParts L R) (hTL : T ⊆ L) :
    (T.image (D.crownMate h)).card = T.card :=
  Finset.card_image_of_injOn (fun _ hx _ hy heq => D.crownMate_injOn h (hTL hx) (hTL hy) heq)


-- @@ L71-74 verbatim
theorem crownMate_image_all {L R : Finset V} (h : D.CrownParts L R) :
    L.image (D.crownMate h) = R := by
  apply Finset.eq_of_subset_of_card_le (D.crownMate_image_subset h Finset.Subset.rfl)
  rw [D.crownMate_image_card h Finset.Subset.rfl, h.left_card, h.right_card]


-- @@ L76-83 verbatim
theorem crown_adj_iff {L R : Finset V} (h : D.CrownParts L R) {x y : V}
    (hx : x ∈ L) (hy : y ∈ R) : D.kreinGraph.Adj x y ↔ y ≠ D.crownMate h x := by
  constructor
  · intro ha heq
    exact (D.crownMate_spec h hx).2 (heq ▸ ha)
  · intro hne
    by_contra hn
    exact hne (D.crownMate_unique h hx hy hn)


-- @@ L85-100 verbatim
theorem crown_commonTo_triple {L R T : Finset V} (h : D.CrownParts L R)
    (hT : T.card = 3) (hTL : T ⊆ L) :
    D.commonTo T = R \ T.image (D.crownMate h) := by
  have hTI := D.independentSet_mono hTL h.left_independent
  have hc : (R \ T.image (D.crownMate h)).card = 3 := by
    rw [Finset.card_sdiff_of_subset (D.crownMate_image_subset h hTL),
      h.right_card, D.crownMate_image_card h hTL, hT]
  have hsub : R \ T.image (D.crownMate h) ⊆ D.commonTo T := by
    intro y hy
    obtain ⟨hyR,hyF⟩ := Finset.mem_sdiff.mp hy
    apply (D.mem_commonTo T y).mpr
    intro x hx
    apply (D.crown_adj_iff h (hTL hx) hyR).mpr
    intro heq
    exact hyF (Finset.mem_image.mpr ⟨x,hx,heq.symm⟩)
  exact (Finset.eq_of_subset_of_card_le hsub (by rw [D.commonTo_card hT hTI, hc])).symm


-- @@ L102-131 verbatim
theorem crown_commonCount_pair {L R : Finset V} (h : D.CrownParts L R)
    {x y : V} (hx : x ∈ L) (hy : y ∈ L) (hxy : x ≠ y) :
    D.commonCount (L ∪ R) x y = 4 := by
  have hmxy : D.crownMate h x ≠ D.crownMate h y := fun heq => hxy (D.crownMate_injOn h hx hy heq)
  have hsub : {D.crownMate h x,D.crownMate h y} ⊆ R := by
    intro z hz
    simp only [Finset.mem_insert,Finset.mem_singleton] at hz
    rcases hz with hz | hz
    · rw [hz]; exact (D.crownMate_spec h hx).1
    · rw [hz]; exact (D.crownMate_spec h hy).1
  have heq : (L ∪ R).filter (fun z => D.kreinGraph.Adj x z ∧ D.kreinGraph.Adj y z) =
      R \ {D.crownMate h x,D.crownMate h y} := by
    ext z
    constructor
    · intro hz
      obtain ⟨hzW,hxz,hyz⟩ := Finset.mem_filter.mp hz
      have hzR : z ∈ R := by
        rcases Finset.mem_union.mp hzW with hzL | hzR
        · exact (h.left_independent x hx z hzL (D.kreinGraph.ne_of_adj hxz) hxz).elim
        · exact hzR
      refine Finset.mem_sdiff.mpr ⟨hzR,?_⟩
      simp only [Finset.mem_insert,Finset.mem_singleton,not_or]
      exact ⟨(D.crown_adj_iff h hx hzR).mp hxz,(D.crown_adj_iff h hy hzR).mp hyz⟩
    · intro hz
      obtain ⟨hzR,hznot⟩ := Finset.mem_sdiff.mp hz
      simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hznot
      exact Finset.mem_filter.mpr ⟨Finset.mem_union_right _ hzR,
        (D.crown_adj_iff h hx hzR).mpr hznot.1,(D.crown_adj_iff h hy hzR).mpr hznot.2⟩
  rw [commonCount, heq, Finset.card_sdiff_of_subset hsub, h.right_card]
  simp [hmxy]


-- @@ L133-133 verbatim
end SRG266.QuasiSymmetric.TripleDesign57
