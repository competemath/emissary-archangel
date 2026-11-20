/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Design.Krein.TripleMoments


-- @@ L8-8 verbatim
namespace SRG266.QuasiSymmetric.TripleDesign57


-- @@ L10-11 verbatim
variable {P B : Type*} [Fintype P] [DecidableEq P] [Fintype B] [DecidableEq B]
    (D : TripleDesign57 P B)


-- @@ L13-13 verbatim
local notation "V" => KreinVertex (P := P) (B := B)


-- @@ L15-16 verbatim
def IndependentSet (S : Finset V) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, x ≠ y → ¬ D.kreinGraph.Adj x y


-- @@ L18-19 verbatim
def commonTo (S : Finset V) : Finset V :=
  Finset.univ.filter fun w => ∀ x ∈ S, D.kreinGraph.Adj x w


-- @@ L21-22 verbatim
@[simp] theorem mem_commonTo (S : Finset V) (w : V) :
    w ∈ D.commonTo S ↔ ∀ x ∈ S, D.kreinGraph.Adj x w := by simp [commonTo]


-- @@ L24-29 verbatim
theorem no_triangle {x y z : V} (hxy : D.kreinGraph.Adj x y)
    (hxz : D.kreinGraph.Adj x z) (hyz : D.kreinGraph.Adj y z) : False := by
  have hzero := D.kreinGraph_isSRGWith.of_adj x y hxy
  have hpos : 0 < Fintype.card (D.kreinGraph.commonNeighbors x y) :=
    Fintype.card_pos_iff.mpr ⟨⟨z, (D.kreinGraph.mem_commonNeighbors).mpr ⟨hxz,hyz⟩⟩⟩
  omega


-- @@ L31-43 verbatim
theorem commonTo_card {S : Finset V} (hcard : S.card = 3) (hI : D.IndependentSet S) :
    (D.commonTo S).card = 3 := by
  obtain ⟨a,b,c,hab,hac,hbc,rfl⟩ := Finset.card_eq_three.mp hcard
  have h := D.independent_triple_commonNeighbors a b c hab hac hbc
    (hI a (by simp) b (by simp) hab)
    (hI a (by simp) c (by simp) hac)
    (hI b (by simp) c (by simp) hbc)
  have heq : D.commonTo {a,b,c} = Finset.univ.filter fun w =>
      D.kreinGraph.Adj a w ∧ D.kreinGraph.Adj b w ∧ D.kreinGraph.Adj c w := by
    ext w
    simp [commonTo]
  rw [heq]
  exact h


-- @@ L45-50 verbatim
theorem commonTo_independent {S : Finset V} (hS : S.Nonempty) :
    D.IndependentSet (D.commonTo S) := by
  obtain ⟨a,ha⟩ := hS
  intro x hx y hy _ hxy
  exact D.no_triangle ((D.mem_commonTo S x).mp hx a ha)
    ((D.mem_commonTo S y).mp hy a ha) hxy


-- @@ L52-55 verbatim
theorem disjoint_commonTo (S : Finset V) : Disjoint S (D.commonTo S) := by
  apply Finset.disjoint_left.mpr
  intro x hx hxC
  exact D.kreinGraph.irrefl ((D.mem_commonTo S x).mp hxC x hx)


-- @@ L57-67 verbatim
theorem commonTo_involution {S : Finset V} (hcard : S.card = 3)
    (hI : D.IndependentSet S) : D.commonTo (D.commonTo S) = S := by
  have hSpos : S.Nonempty := Finset.card_pos.mp (by omega)
  have hCcard := D.commonTo_card hcard hI
  have hCCcard := D.commonTo_card hCcard (D.commonTo_independent hSpos)
  have hsub : S ⊆ D.commonTo (D.commonTo S) := by
    intro x hx
    apply (D.mem_commonTo _ x).mpr
    intro y hy
    exact (D.kreinGraph.adj_comm x y).mp ((D.mem_commonTo S y).mp hy x hx)
  exact (Finset.eq_of_subset_of_card_le hsub (by omega)).symm


-- @@ L69-71 verbatim
theorem biclique_card {S : Finset V} (hcard : S.card = 3) (hI : D.IndependentSet S) :
    (S ∪ D.commonTo S).card = 6 := by
  rw [Finset.card_union_of_disjoint (D.disjoint_commonTo S), hcard, D.commonTo_card hcard hI]


-- @@ L73-82 verbatim
theorem neighbor_trace_le_two {S : Finset V} (hcard : S.card = 3) {x : V}
    (hx : x ∉ D.commonTo S) : (S.filter fun y => D.kreinGraph.Adj x y).card ≤ 2 := by
  by_contra hgt
  have heq : S.filter (fun y => D.kreinGraph.Adj x y) = S :=
    Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by omega)
  apply hx
  apply (D.mem_commonTo S x).mpr
  intro y hy
  have hmem : y ∈ S.filter fun y => D.kreinGraph.Adj x y := heq.symm ▸ hy
  exact (D.kreinGraph.adj_comm x y).mp (Finset.mem_filter.mp hmem).2


-- @@ L84-111 verbatim
theorem biclique_outside_degree_le_two {S : Finset V}
    (hcard : S.card = 3) (hI : D.IndependentSet S) {x : V}
    (hx : x ∉ S ∪ D.commonTo S) :
    ((S ∪ D.commonTo S).filter fun y => D.kreinGraph.Adj x y).card ≤ 2 := by
  have hxS : x ∉ S := fun h => hx (Finset.mem_union_left _ h)
  have hxC : x ∉ D.commonTo S := fun h => hx (Finset.mem_union_right _ h)
  by_cases hleft : ∃ a ∈ S, D.kreinGraph.Adj x a
  · obtain ⟨a,ha,hxa⟩ := hleft
    have hsub : ((S ∪ D.commonTo S).filter fun y => D.kreinGraph.Adj x y) ⊆
        S.filter fun y => D.kreinGraph.Adj x y := by
      intro y hy
      obtain ⟨hyU,hxy⟩ := Finset.mem_filter.mp hy
      rcases Finset.mem_union.mp hyU with hyS | hyC
      · exact Finset.mem_filter.mpr ⟨hyS,hxy⟩
      · exact (D.no_triangle hxa hxy ((D.mem_commonTo S y).mp hyC a ha)).elim
    exact (Finset.card_le_card hsub).trans (D.neighbor_trace_le_two hcard hxC)
  · have hsub : ((S ∪ D.commonTo S).filter fun y => D.kreinGraph.Adj x y) ⊆
        (D.commonTo S).filter fun y => D.kreinGraph.Adj x y := by
      intro y hy
      obtain ⟨hyU,hxy⟩ := Finset.mem_filter.mp hy
      rcases Finset.mem_union.mp hyU with hyS | hyC
      · exact (hleft ⟨y,hyS,hxy⟩).elim
      · exact Finset.mem_filter.mpr ⟨hyC,hxy⟩
    have hxCC : x ∉ D.commonTo (D.commonTo S) := by
      rw [D.commonTo_involution hcard hI]
      exact hxS
    exact (Finset.card_le_card hsub).trans
      (D.neighbor_trace_le_two (D.commonTo_card hcard hI) hxCC)


-- @@ L113-123 verbatim
theorem exists_independent_three (p : V) : ∃ S : Finset V,
    S.card = 3 ∧ D.IndependentSet S := by
  have hle : 3 ≤ (D.kreinGraph.neighborFinset p).card := by
    change 3 ≤ D.kreinGraph.degree p
    rw [D.kreinGraph_degree]
    norm_num
  obtain ⟨S,hsub,hcard⟩ := Finset.exists_subset_card_eq hle
  refine ⟨S,hcard,?_⟩
  intro x hx y hy _ hxy
  exact D.no_triangle ((D.kreinGraph.mem_neighborFinset p x).mp (hsub hx))
    ((D.kreinGraph.mem_neighborFinset p y).mp (hsub hy)) hxy


-- @@ L125-125 verbatim
end SRG266.QuasiSymmetric.TripleDesign57
