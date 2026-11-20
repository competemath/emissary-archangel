/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Design.Krein.CrownRecovery
import SRG266.Design.Krein.QuadrupleObstruction


-- @@ L9-13 verbatim
/-! # A Steiner 3-(12,4,1) design forced by the Krein construction

Unique crown recovery supplies the Steiner blocks. Their replication
equation 3r = 55 excludes the constructed triple design on 57 points.
-/


-- @@ L15-15 verbatim
open scoped BigOperators Matrix


-- @@ L17-17 verbatim
namespace SRG266.QuasiSymmetric.TripleDesign57


-- @@ L19-20 verbatim
variable {P B : Type*} [Fintype P] [DecidableEq P] [Fintype B] [DecidableEq B]
    (D : TripleDesign57 P B)


-- @@ L22-22 verbatim
local notation "V" => KreinVertex (P := P) (B := B)


-- @@ L24-25 verbatim
def pairNeighborhood (a u : V) : Finset V :=
  Finset.univ.filter fun x => D.kreinGraph.Adj a x ∧ D.kreinGraph.Adj u x


-- @@ L27-28 verbatim
@[simp] theorem mem_pairNeighborhood (a u x : V) :
    x ∈ D.pairNeighborhood a u ↔ D.kreinGraph.Adj a x ∧ D.kreinGraph.Adj u x := by simp [pairNeighborhood]


-- @@ L30-31 verbatim
theorem pairNeighborhood_card {a u : V} (hne : a ≠ u) (hn : ¬ D.kreinGraph.Adj a u) :
    (D.pairNeighborhood a u).card = 12 := D.commonCount_univ hne hn


-- @@ L33-36 verbatim
theorem pairNeighborhood_independent (a u : V) : D.IndependentSet (D.pairNeighborhood a u) := by
  intro x hx y hy _ hxy
  exact D.no_triangle ((D.mem_pairNeighborhood a u x).mp hx).1
    ((D.mem_pairNeighborhood a u y).mp hy).1 hxy


-- @@ L38-39 verbatim
def crownSlice (W : Finset V) (a u : V) : Finset V :=
  W.filter fun x => D.kreinGraph.Adj a x ∧ D.kreinGraph.Adj u x


-- @@ L41-43 verbatim
@[simp] theorem mem_crownSlice (W : Finset V) (a u x : V) :
    x ∈ D.crownSlice W a u ↔ x ∈ W ∧ D.kreinGraph.Adj a x ∧ D.kreinGraph.Adj u x := by
  simp [crownSlice]


-- @@ L45-62 verbatim
theorem crownSlice_card_of_triple {W T : Finset V} {a u : V} (hW : D.IsCrown W)
    (hT : T.card = 3) (hTW : T ⊆ W) (hTX : T ⊆ D.pairNeighborhood a u) (hne : a ≠ u) :
    (D.crownSlice W a u).card = 4 := by
  have hTI := D.independentSet_mono hTX (D.pairNeighborhood_independent a u)
  have ha : a ∈ D.commonTo T := (D.mem_commonTo T a).mpr (by
    intro x hx
    exact (D.kreinGraph.adj_comm a x).mp ((D.mem_pairNeighborhood a u x).mp (hTX hx)).1)
  have hu : u ∈ D.commonTo T := (D.mem_commonTo T u).mpr (by
    intro x hx
    exact (D.kreinGraph.adj_comm u x).mp ((D.mem_pairNeighborhood a u x).mp (hTX hx)).2)
  obtain ⟨L,R,h,rfl⟩ := hW
  change D.commonCount (L ∪ R) a u = 4
  rcases D.crown_independent_triple_one_part h hT hTI hTW with hTL | hTR
  · rw [D.crown_commonTo_triple h hT hTL] at ha hu
    simpa only [Finset.union_comm] using D.crown_commonCount_pair (D.crownParts_symm h)
      (Finset.mem_sdiff.mp ha).1 (Finset.mem_sdiff.mp hu).1 hne
  · rw [D.crown_commonTo_triple (D.crownParts_symm h) hT hTR] at ha hu
    exact D.crown_commonCount_pair h (Finset.mem_sdiff.mp ha).1 (Finset.mem_sdiff.mp hu).1 hne


-- @@ L64-67 verbatim
noncomputable def steinerBlocks (a u : V) : Finset (Finset V) := by
  classical
  exact ((D.pairNeighborhood a u).powersetCard 4).filter fun Q =>
    ∃ W : Finset V, D.IsCrown W ∧ Q = D.crownSlice W a u


-- @@ L69-73 verbatim
theorem mem_steinerBlocks (a u : V) (Q : Finset V) :
    Q ∈ D.steinerBlocks a u ↔ (Q ⊆ D.pairNeighborhood a u ∧ Q.card = 4) ∧
      ∃ W : Finset V, D.IsCrown W ∧ Q = D.crownSlice W a u := by
  classical
  simp [steinerBlocks]


-- @@ L75-110 verbatim
theorem steinerBlocks_triple {a u : V} (hne : a ≠ u) (T : Finset V)
    (hTX : T ⊆ D.pairNeighborhood a u) (hT : T.card = 3) :
    ((D.steinerBlocks a u).filter fun Q => T ⊆ Q).card = 1 := by
  classical
  have hTI := D.independentSet_mono hTX (D.pairNeighborhood_independent a u)
  obtain ⟨W,hW,hTW⟩ := D.exists_crown_of_independent_triple hT hTI
  let Q := D.crownSlice W a u
  have hQcard : Q.card = 4 := D.crownSlice_card_of_triple hW hT hTW hTX hne
  have hQX : Q ⊆ D.pairNeighborhood a u := by
    intro x hx
    exact (D.mem_pairNeighborhood a u x).mpr ((D.mem_crownSlice W a u x).mp hx).2
  have hTQ : T ⊆ Q := by
    intro x hx
    exact (D.mem_crownSlice W a u x).mpr ⟨hTW hx,(D.mem_pairNeighborhood a u x).mp (hTX hx)⟩
  have hQmem : Q ∈ D.steinerBlocks a u := (D.mem_steinerBlocks a u Q).mpr
    ⟨⟨hQX,hQcard⟩,W,hW,rfl⟩
  have heq : (D.steinerBlocks a u).filter (fun B => T ⊆ B) = {Q} := by
    ext B
    constructor
    · intro hB
      obtain ⟨hBmem,hTB⟩ := Finset.mem_filter.mp hB
      obtain ⟨_,Z,hZ,hBeq⟩ := (D.mem_steinerBlocks a u B).mp hBmem
      have hTZ : T ⊆ Z := by
        intro x hx
        have hxb := hTB hx
        rw [hBeq] at hxb
        exact ((D.mem_crownSlice Z a u x).mp hxb).1
      have hZW := D.crowns_eq_of_containing_triple hZ hW hT hTI hTZ hTW
      have hBQ : B = Q := by rw [hBeq,hZW]
      simp [hBQ]
    · intro hB
      have hBQ := Finset.mem_singleton.mp hB
      subst B
      exact Finset.mem_filter.mpr ⟨hQmem,hTQ⟩
  rw [heq]
  simp


-- @@ L112-122 verbatim
theorem contradiction_of_nonadjacent_pair {a u : V} (hne : a ≠ u)
    (hn : ¬ D.kreinGraph.Adj a u) : False := by
  classical
  apply no_steinerQuadruple_on12 (D.pairNeighborhood a u) (D.pairNeighborhood_card hne hn)
    (D.steinerBlocks a u)
  · intro Q hQ
    exact ((D.mem_steinerBlocks a u Q).mp hQ).1.2
  · intro Q hQ
    exact ((D.mem_steinerBlocks a u Q).mp hQ).1.1
  · intro T hTX hT
    exact D.steinerBlocks_triple hne T hTX hT


-- @@ L124-129 verbatim
theorem no_tripleDesign57 (D : TripleDesign57 P B) : False := by
  obtain ⟨S,hS,hSI⟩ := D.exists_independent_three none
  obtain ⟨a,b,c,hab,_,_,hSeq⟩ := Finset.card_eq_three.mp hS
  have ha : a ∈ S := by rw [hSeq]; simp
  have hb : b ∈ S := by rw [hSeq]; simp
  exact D.contradiction_of_nonadjacent_pair hab (hSI a ha b hb hab)


-- @@ L131-131 verbatim
end SRG266.QuasiSymmetric.TripleDesign57


-- @@ L133-133 verbatim
namespace SRG266.QuasiSymmetric.ConcreteQSD56


-- @@ L135-135 verbatim
theorem no_concreteQSD56 (Q : ConcreteQSD56) : False := Q.toTripleDesign57.no_tripleDesign57


-- @@ L137-137 verbatim
end SRG266.QuasiSymmetric.ConcreteQSD56


-- @@ L139-139 verbatim
namespace SRG266.QuasiSymmetric


-- @@ L141-141 verbatim
universe u


-- @@ L143-144 verbatim
theorem no_quasi_symmetric_design : NoQuasiSymmetricDesign56.{u} :=
  noQuasiSymmetricDesign56_of_concrete ⟨ConcreteQSD56.no_concreteQSD56⟩


-- @@ L146-146 verbatim
end SRG266.QuasiSymmetric
