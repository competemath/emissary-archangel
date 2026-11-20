/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Design.Krein.FourthTrace


-- @@ L8-8 verbatim
open scoped BigOperators Matrix


-- @@ L10-10 verbatim
namespace SRG266.QuasiSymmetric.TripleDesign57


-- @@ L12-13 verbatim
variable {P B : Type*} [Fintype P] [DecidableEq P] [Fintype B] [DecidableEq B]
    (D : TripleDesign57 P B)


-- @@ L15-15 verbatim
local notation "V" => KreinVertex (P := P) (B := B)


-- @@ L17-22 verbatim
theorem commonCount_le_neighborCount (T : Finset V) (x y : V) :
    D.commonCount T x y ≤ D.neighborCount T x := by
  apply Finset.card_le_card
  intro z hz
  obtain ⟨hzT,hxz,_⟩ := Finset.mem_filter.mp hz
  exact Finset.mem_filter.mpr ⟨hzT,hxz⟩


-- @@ L24-26 verbatim
theorem commonCount_mono {T U : Finset V} (hTU : T ⊆ U) (x y : V) :
    D.commonCount T x y ≤ D.commonCount U x y :=
  Finset.card_le_card (Finset.filter_subset_filter _ hTU)


-- @@ L28-35 verbatim
theorem commonCount_eq_inter (T : Finset V) (x y : V) :
    D.commonCount T x y =
      ((T.filter fun z => D.kreinGraph.Adj x z) ∩ (T.filter fun z => D.kreinGraph.Adj y z)).card := by
  unfold commonCount
  congr 1
  ext z
  simp only [Finset.mem_filter, Finset.mem_inter]
  tauto


-- @@ L37-46 verbatim
theorem neighbor_pair_count_bound (T : Finset V) (x y : V) :
    D.neighborCount T x + D.neighborCount T y ≤ T.card + D.commonCount T x y := by
  have h := Finset.card_union_add_card_inter
    (T.filter fun z => D.kreinGraph.Adj x z) (T.filter fun z => D.kreinGraph.Adj y z)
  have hb : ((T.filter fun z => D.kreinGraph.Adj x z) ∪
      (T.filter fun z => D.kreinGraph.Adj y z)).card ≤ T.card :=
    Finset.card_le_card (Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _))
  rw [← D.commonCount_eq_inter] at h
  change _ + D.commonCount T x y = D.neighborCount T x + D.neighborCount T y at h
  omega


-- @@ L48-54 verbatim
theorem bicliqueClass_two_sides {S : Finset V} {x : V} (hx : x ∈ D.bicliqueClass S 2) :
    (D.neighborCount S x = 2 ∧ D.neighborCount (D.commonTo S) x = 0) ∨
    (D.neighborCount S x = 0 ∧ D.neighborCount (D.commonTo S) x = 2) := by
  have hs := (D.mem_bicliqueClass S 2 x).mp hx |>.2
  rw [D.biclique_neighborCount_split] at hs
  have hp := D.biclique_neighborCount_product_zero S x
  rcases mul_eq_zero.mp hp with hl | hr <;> omega


-- @@ L56-65 verbatim
theorem bicliqueClass_two_adj_traces {S : Finset V} (hcard : S.card = 3)
    (hI : D.IndependentSet S) {x y : V} (hx : x ∈ D.bicliqueClass S 2)
    (hy : y ∈ D.bicliqueClass S 2) (hxy : D.kreinGraph.Adj x y) :
    D.neighborCount S x + D.neighborCount S y = 2 := by
  have hL := D.neighbor_pair_count_bound S x y
  have hR := D.neighbor_pair_count_bound (D.commonTo S) x y
  rw [D.commonCount_of_adj S hxy, hcard] at hL
  rw [D.commonCount_of_adj (D.commonTo S) hxy, D.commonTo_card hcard hI] at hR
  rcases D.bicliqueClass_two_sides hx with hxl | hxr <;>
    rcases D.bicliqueClass_two_sides hy with hyl | hyr <;> omega


-- @@ L67-86 verbatim
theorem bicliqueClass_two_common_delta_pos {S : Finset V} (hcard : S.card = 3)
    (hI : D.IndependentSet S) {x y : V} (hx : x ∈ D.bicliqueClass S 2)
    (hy : y ∈ D.bicliqueClass S 2) (hp : 0 < D.commonCount (D.bicliqueClass S 2) x y) :
    0 < D.commonCount (S ∪ D.commonTo S) x y := by
  obtain ⟨f,hf⟩ := Finset.card_pos.mp hp
  obtain ⟨hf2,hxf,hyf⟩ := Finset.mem_filter.mp hf
  have heX := D.bicliqueClass_two_adj_traces hcard hI hx hf2 hxf
  have heY := D.bicliqueClass_two_adj_traces hcard hI hy hf2 hyf
  have hsY := (D.mem_bicliqueClass S 2 y).mp hy |>.2
  rw [D.biclique_neighborCount_split] at hsY
  rcases D.bicliqueClass_two_sides hx with hl | hr
  · have hb := D.neighbor_pair_count_bound S x y
    rw [hcard] at hb
    have hm := D.commonCount_mono (Finset.subset_union_left : S ⊆ S ∪ D.commonTo S) x y
    omega
  · have hb := D.neighbor_pair_count_bound (D.commonTo S) x y
    rw [D.commonTo_card hcard hI] at hb
    have hm := D.commonCount_mono
      (Finset.subset_union_right : D.commonTo S ⊆ S ∪ D.commonTo S) x y
    omega


-- @@ L88-90 verbatim
def zeroNeighborUnion (S : Finset V) (x y : V) : Finset V :=
  ((D.bicliqueClass S 0).filter fun z => D.kreinGraph.Adj x z) ∪
    ((D.bicliqueClass S 0).filter fun z => D.kreinGraph.Adj y z)


-- @@ L92-111 verbatim
theorem zeroNeighborUnion_count {S : Finset V} (hcard : S.card = 3)
    (hI : D.IndependentSet S) {x y : V} (hx : x ∈ D.bicliqueClass S 2)
    (hy : y ∈ D.bicliqueClass S 2) (hxy : x ≠ y) (hn : ¬ D.kreinGraph.Adj x y) :
    (D.zeroNeighborUnion S x y).card + (6 + D.commonCount (D.bicliqueClass S 2) x y) =
      32 + D.commonCount (S ∪ D.commonTo S) x y := by
  have hc := D.bicliqueCubicRight_common hcard hI hx hy hxy hn
  have hu := D.commonCount_union (S ∪ D.commonTo S) (D.bicliqueClass S 0)
    (D.disjoint_biclique_class S 0) x y
  change D.commonCount (D.bicliqueCubicLeft S) x y = _ at hu
  have hxD := D.biclique_local_degrees hcard hI ((D.mem_bicliqueClass S 2 x).mp hx).1
  have hyD := D.biclique_local_degrees hcard hI ((D.mem_bicliqueClass S 2 y).mp hy).1
  norm_num [(D.mem_bicliqueClass S 2 x).mp hx |>.2] at hxD
  norm_num [(D.mem_bicliqueClass S 2 y).mp hy |>.2] at hyD
  have hcount := Finset.card_union_add_card_inter
    ((D.bicliqueClass S 0).filter fun z => D.kreinGraph.Adj x z)
    ((D.bicliqueClass S 0).filter fun z => D.kreinGraph.Adj y z)
  rw [← D.commonCount_eq_inter] at hcount
  change (D.zeroNeighborUnion S x y).card + D.commonCount (D.bicliqueClass S 0) x y =
    D.neighborCount (D.bicliqueClass S 0) x + D.neighborCount (D.bicliqueClass S 0) y at hcount
  omega


-- @@ L113-130 verbatim
theorem two_common_of_square {S : Finset V} {x y f g : V}
    (hx : x ∈ D.bicliqueClass S 2) (hy : y ∈ D.bicliqueClass S 2) (hxy : x ≠ y)
    (hxf : D.kreinGraph.Adj x f) (hxg : D.kreinGraph.Adj x g)
    (hyf : D.kreinGraph.Adj y f) (hyg : D.kreinGraph.Adj y g) :
    2 ≤ D.commonCount (D.bicliqueClass S 2) f g := by
  have hsub : {x,y} ⊆ (D.bicliqueClass S 2).filter
      (fun z => D.kreinGraph.Adj f z ∧ D.kreinGraph.Adj g z) := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with hz | hz
    · subst z
      exact Finset.mem_filter.mpr ⟨hx, (D.kreinGraph.adj_comm x f).mp hxf,
        (D.kreinGraph.adj_comm x g).mp hxg⟩
    · subst z
      exact Finset.mem_filter.mpr ⟨hy, (D.kreinGraph.adj_comm y f).mp hyf,
        (D.kreinGraph.adj_comm y g).mp hyg⟩
  have h := Finset.card_le_card hsub
  simpa [hxy, commonCount] using h


-- @@ L132-170 verbatim
theorem bicliqueClass_two_common_three {S : Finset V} (hcard : S.card = 3)
    (hI : D.IndependentSet S) {x y : V} (hx : x ∈ D.bicliqueClass S 2)
    (hy : y ∈ D.bicliqueClass S 2) (hxy : x ≠ y)
    (hcommon : 2 ≤ D.commonCount (D.bicliqueClass S 2) x y) :
    D.commonCount (D.bicliqueClass S 2) x y = 3 := by
  have hupper := D.commonCount_le_neighborCount (D.bicliqueClass S 2) x y
  rw [D.bicliqueClass_two_degree_self hcard hI hx] at hupper
  by_contra hnot3
  have ht : D.commonCount (D.bicliqueClass S 2) x y = 2 := by omega
  have hcardF : 1 < ((D.bicliqueClass S 2).filter
      fun z => D.kreinGraph.Adj x z ∧ D.kreinGraph.Adj y z).card := by
    change 1 < D.commonCount (D.bicliqueClass S 2) x y
    omega
  obtain ⟨f,hf,g,hg,hfg⟩ := Finset.one_lt_card.mp hcardF
  obtain ⟨hf2,hxf,hyf⟩ := Finset.mem_filter.mp hf
  obtain ⟨hg2,hxg,hyg⟩ := Finset.mem_filter.mp hg
  have hfgcount := D.two_common_of_square hx hy hxy hxf hxg hyf hyg
  have hfgu := D.commonCount_le_neighborCount (D.bicliqueClass S 2) f g
  rw [D.bicliqueClass_two_degree_self hcard hI hf2] at hfgu
  have hdx := D.bicliqueClass_two_common_delta_pos hcard hI hx hy (by omega)
  have hdf := D.bicliqueClass_two_common_delta_pos hcard hI hf2 hg2 (by omega)
  have hnxy : ¬ D.kreinGraph.Adj x y := fun h => D.no_triangle h hxf hyf
  have hnfg : ¬ D.kreinGraph.Adj f g := fun h => D.no_triangle hxf hxg h
  have hux := D.zeroNeighborUnion_count hcard hI hx hy hxy hnxy
  have huf := D.zeroNeighborUnion_count hcard hI hf2 hg2 hfg hnfg
  have hdis : Disjoint (D.zeroNeighborUnion S x y) (D.zeroNeighborUnion S f g) := by
    apply Finset.disjoint_left.mpr
    intro z hzl hzr
    rcases Finset.mem_union.mp hzl with hzx | hzy <;>
      rcases Finset.mem_union.mp hzr with hzf | hzg
    · exact D.no_triangle hxf (Finset.mem_filter.mp hzx).2 (Finset.mem_filter.mp hzf).2
    · exact D.no_triangle hxg (Finset.mem_filter.mp hzx).2 (Finset.mem_filter.mp hzg).2
    · exact D.no_triangle hyf (Finset.mem_filter.mp hzy).2 (Finset.mem_filter.mp hzf).2
    · exact D.no_triangle hyg (Finset.mem_filter.mp hzy).2 (Finset.mem_filter.mp hzg).2
  have hsub (a b : V) : D.zeroNeighborUnion S a b ⊆ D.bicliqueClass S 0 :=
    Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have htotal := Finset.card_le_card (Finset.union_subset (hsub x y) (hsub f g))
  rw [Finset.card_union_of_disjoint hdis, (D.bicliqueClass_card hcard hI).1] at htotal
  omega


-- @@ L172-210 verbatim
theorem exists_biclique_in_class_two {S : Finset V} (hcard : S.card = 3)
    (hI : D.IndependentSet S) : ∃ R : Finset V,
      R.card = 3 ∧ D.IndependentSet R ∧ R ∪ D.commonTo R ⊆ D.bicliqueClass S 2 := by
  obtain ⟨x,hx,y,hy,hxy,hc⟩ := D.bicliqueCubic_right_square hcard hI
  let R := (D.bicliqueClass S 2).filter fun z => D.kreinGraph.Adj x z ∧ D.kreinGraph.Adj y z
  have hR : R.card = 3 := D.bicliqueClass_two_common_three hcard hI hx hy hxy hc
  have hRI : D.IndependentSet R := by
    intro f hf g hg _ hfg
    exact D.no_triangle (Finset.mem_filter.mp hf).2.1 (Finset.mem_filter.mp hg).2.1 hfg
  obtain ⟨f,hf⟩ := Finset.card_pos.mp (by omega : 0 < R.card)
  obtain ⟨hf2,hxf,hyf⟩ := Finset.mem_filter.mp hf
  let E := (D.bicliqueClass S 2).filter fun z => D.kreinGraph.Adj f z
  have hE : E.card = 3 := D.bicliqueClass_two_degree_self hcard hI hf2
  have hcross (g) (hg : g ∈ R) : ∀ e ∈ E, D.kreinGraph.Adj g e := by
    obtain ⟨hg2,hxg,hyg⟩ := Finset.mem_filter.mp hg
    by_cases hfg : f = g
    · subst g
      intro e he
      exact (Finset.mem_filter.mp he).2
    · have hfgcount := D.two_common_of_square hx hy hxy hxf hxg hyf hyg
      have hthree := D.bicliqueClass_two_common_three hcard hI hf2 hg2 hfg hfgcount
      have hsub : (D.bicliqueClass S 2).filter
          (fun z => D.kreinGraph.Adj f z ∧ D.kreinGraph.Adj g z) ⊆ E := by
        intro e he
        exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp he).1,(Finset.mem_filter.mp he).2.1⟩
      have heq : (D.bicliqueClass S 2).filter
          (fun z => D.kreinGraph.Adj f z ∧ D.kreinGraph.Adj g z) = E :=
        Finset.eq_of_subset_of_card_le hsub (by change E.card ≤ D.commonCount _ f g; omega)
      intro e he
      have he' := heq.symm ▸ he
      exact (Finset.mem_filter.mp he').2.2
  have hsub : E ⊆ D.commonTo R := by
    intro e he
    exact (D.mem_commonTo R e).mpr (fun g hg => hcross g hg e he)
  have heq : E = D.commonTo R :=
    Finset.eq_of_subset_of_card_le hsub (by rw [D.commonTo_card hR hRI, hE])
  refine ⟨R,hR,hRI,Finset.union_subset (Finset.filter_subset _ _) ?_⟩
  rw [← heq]
  exact Finset.filter_subset _ _


-- @@ L212-212 verbatim
end SRG266.QuasiSymmetric.TripleDesign57
