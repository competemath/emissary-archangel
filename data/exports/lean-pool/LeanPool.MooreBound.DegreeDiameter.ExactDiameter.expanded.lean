/-
Copyright (c) 2026 Wouter Cames van Batenburg, Samuel Korsky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Cames van Batenburg, Samuel Korsky
-/

module

public import LeanPool.MooreBound.DegreeDiameter.HalvedFlags
public import Mathlib.Data.Fin.Rev
public import Mathlib.Data.Nat.Dist
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.StdBasis


-- @@ L15-31 verbatim
/-!
# The rank-potential lower bound for the halved flag graph

This file follows the reverse inequality in the diameter paragraph of
Proposition 3.1.  Relative to a fixed nonzero vector `e`, `evenEntryBlock`
records the first retained even rank containing `e` (with `k + 1` as the
sentinel when no retained even rank contains it).  The paper's potential is
exactly `2 * (evenEntryBlock - 1)`.

Compatibility with one odd partial flag lets the entry block move by at most
one.  The standard and reverse basis flags have entry blocks `1` and `k + 1`;
hence every walk between them has at least `k` edges.  Combined with the
odd--even route upper bound, this proves exact extended diameter `k`.

Lean Pool port of wewantmoore commit d59bd80ea93fabb9faf769e790ab47692645e022.
The port adds a namespace and adapts proofs to the current Mathlib APIs and repository style.
-/


-- @@ L33-33 verbatim
@[expose] public section


-- @@ L35-35 verbatim
namespace MooreBound


-- @@ L37-37 verbatim
open Module


-- @@ L39-39 verbatim
namespace DegreeDiameter


-- @@ L41-41 verbatim
variable {K : Type*} [DivisionRing K]


-- @@ L43-45 verbatim
/-- The retained even rank `2*j` in dimension `2*k+1`. -/
def evenRank (k j : ℕ) (hj : j ≤ k) : Fin ((2 * k + 1) + 1) :=
  ⟨2 * j, by omega⟩


-- @@ L47-53 verbatim
/-- A candidate entry block: either a positive retained even rank containing
`e`, or the sentinel `k+1`. -/
def EvenEntryCandidate {V : Type*} [AddCommGroup V] [Module K V]
    (k : ℕ) (e : V)
    (P : EvenPartialFlag (K := K) (V := V) (n := 2 * k + 1))
    (j : ℕ) : Prop :=
  (1 ≤ j ∧ ∃ hj : j ≤ k, e ∈ P.1 (evenRank k j hj)) ∨ j = k + 1


-- @@ L55-59 verbatim
theorem exists_evenEntryCandidate {V : Type*} [AddCommGroup V] [Module K V]
    (k : ℕ) (e : V)
    (P : EvenPartialFlag (K := K) (V := V) (n := 2 * k + 1)) :
    ∃ j, EvenEntryCandidate k e P j :=
  ⟨k + 1, Or.inr rfl⟩


-- @@ L61-67 verbatim
/-- The first positive retained even rank containing `e`, numbered in blocks;
the value is `k+1` if no retained even rank contains `e`. -/
noncomputable def evenEntryBlock {V : Type*} [AddCommGroup V] [Module K V]
    (k : ℕ) (e : V)
    (P : EvenPartialFlag (K := K) (V := V) (n := 2 * k + 1)) : ℕ := by
  classical
  exact Nat.find (exists_evenEntryCandidate k e P)


-- @@ L69-75 verbatim
theorem evenEntryBlock_spec {V : Type*} [AddCommGroup V] [Module K V]
    (k : ℕ) (e : V)
    (P : EvenPartialFlag (K := K) (V := V) (n := 2 * k + 1)) :
    EvenEntryCandidate k e P (evenEntryBlock k e P) :=
  by
    classical
    exact Nat.find_spec (exists_evenEntryCandidate k e P)


-- @@ L77-83 verbatim
theorem one_le_evenEntryBlock {V : Type*} [AddCommGroup V] [Module K V]
    (k : ℕ) (e : V)
    (P : EvenPartialFlag (K := K) (V := V) (n := 2 * k + 1)) :
    1 ≤ evenEntryBlock k e P := by
  rcases evenEntryBlock_spec k e P with h | h
  · exact h.1
  · omega


-- @@ L85-90 verbatim
theorem evenEntryBlock_le_sentinel {V : Type*} [AddCommGroup V] [Module K V]
    (k : ℕ) (e : V)
    (P : EvenPartialFlag (K := K) (V := V) (n := 2 * k + 1)) :
    evenEntryBlock k e P ≤ k + 1 := by
  classical
  exact Nat.find_min' (exists_evenEntryCandidate k e P) (Or.inr rfl)


-- @@ L92-100 verbatim
theorem evenEntryBlock_le_of_mem {V : Type*} [AddCommGroup V] [Module K V]
    (k : ℕ) (e : V)
    (P : EvenPartialFlag (K := K) (V := V) (n := 2 * k + 1))
    (j : ℕ) (hj1 : 1 ≤ j) (hjk : j ≤ k)
    (hmem : e ∈ P.1 (evenRank k j hjk)) :
    evenEntryBlock k e P ≤ j := by
  classical
  exact Nat.find_min' (exists_evenEntryCandidate k e P)
    (Or.inl ⟨hj1, hjk, hmem⟩)


-- @@ L102-109 verbatim
theorem evenEntryBlock_mem {V : Type*} [AddCommGroup V] [Module K V]
    (k : ℕ) (e : V)
    (P : EvenPartialFlag (K := K) (V := V) (n := 2 * k + 1))
    (hblock : evenEntryBlock k e P ≤ k) :
    e ∈ P.1 (evenRank k (evenEntryBlock k e P) hblock) := by
  rcases evenEntryBlock_spec k e P with h | h
  · exact h.2.choose_spec
  · omega


-- @@ L111-118 verbatim
theorem evenEntryBlock_ofComplete_le_of_mem
    {V : Type*} [AddCommGroup V] [Module K V]
    (k : ℕ) (e : V) (F : CompleteFlag K V (2 * k + 1))
    (j : ℕ) (hj1 : 1 ≤ j) (hjk : j ≤ k)
    (hmem : e ∈ F (evenRank k j hjk)) :
    evenEntryBlock k e (PartialFlag.ofComplete 0 F) ≤ j := by
  apply evenEntryBlock_le_of_mem k e (PartialFlag.ofComplete 0 F) j hj1 hjk
  simpa [PartialFlag.ofComplete, flagPart, evenRank] using hmem


-- @@ L120-160 verbatim
/-- Compatibility with a common odd partial flag makes the first even entry
block move by at most one.  This is the paper's rank-potential estimate. -/
theorem evenEntryBlock_le_add_one_of_common_compatible
    {V : Type*} [AddCommGroup V] [Module K V]
    (k : ℕ) (e : V)
    {P P' : EvenPartialFlag (K := K) (V := V) (n := 2 * k + 1)}
    {Q : OddPartialFlag (K := K) (V := V) (n := 2 * k + 1)}
    (hPQ : Compatible P Q) (hP'Q : Compatible P' Q) :
    evenEntryBlock k e P' ≤ evenEntryBlock k e P + 1 := by
  let a := evenEntryBlock k e P
  by_cases hak : a < k
  · have ha_le : a ≤ k := by omega
    have ha1 : 1 ≤ a := one_le_evenEntryBlock k e P
    have hmemP : e ∈ P.1 (evenRank k a ha_le) := evenEntryBlock_mem k e P ha_le
    obtain ⟨F, hFP, hFQ⟩ := hPQ
    obtain ⟨G, hGP', hGQ⟩ := hP'Q
    let ie : Fin ((2 * k + 1) + 1) := evenRank k a ha_le
    let io : Fin ((2 * k + 1) + 1) := ⟨2 * a + 1, by omega⟩
    let ie' : Fin ((2 * k + 1) + 1) := evenRank k (a + 1) (by omega)
    have heF : e ∈ F ie := by
      have hm : e ∈ (PartialFlag.ofComplete 0 F).1 ie := by
        rw [hFP]
        exact hmemP
      simpa [PartialFlag.ofComplete, flagPart, ie, evenRank] using hm
    have heFo : e ∈ F io := F.strictMono_space.monotone (by simp [ie, io, evenRank]) heF
    have heQ : e ∈ Q.1 io := by
      rw [← hFQ]
      simpa [PartialFlag.ofComplete, flagPart, io] using heFo
    have heGo : e ∈ G io := by
      have hm : e ∈ (PartialFlag.ofComplete 1 G).1 io := by
        rw [hGQ]
        exact heQ
      simpa [PartialFlag.ofComplete, flagPart, io] using hm
    have heGe : e ∈ G ie' :=
      G.strictMono_space.monotone (by simp [io, ie', evenRank]) heGo
    have heP' : e ∈ P'.1 ie' := by
      rw [← hGP']
      simpa [PartialFlag.ofComplete, flagPart, ie', evenRank] using heGe
    exact evenEntryBlock_le_of_mem k e P' (a + 1) (by omega) (by omega) heP'
  · have hka : k ≤ a := by omega
    exact (evenEntryBlock_le_sentinel k e P').trans (by omega)


-- @@ L162-169 verbatim
theorem evenEntryBlock_adjacent
    {V : Type*} [AddCommGroup V] [Module K V]
    (k : ℕ) (e : V)
    {P P' : EvenPartialFlag (K := K) (V := V) (n := 2 * k + 1)}
    (h : (halvedFlagGraph (K := K) (V := V) (n := 2 * k + 1)).Adj P P') :
    evenEntryBlock k e P' ≤ evenEntryBlock k e P + 1 := by
  obtain ⟨_, Q, hPQ, hP'Q⟩ := (halvedFlagGraph_adj_iff.mp h)
  exact evenEntryBlock_le_add_one_of_common_compatible k e hPQ hP'Q


-- @@ L171-175 verbatim
/-- The rank potential `lambda` from the paper. -/
noncomputable def rankPotential {V : Type*} [AddCommGroup V] [Module K V]
    (k : ℕ) (e : V)
    (P : EvenPartialFlag (K := K) (V := V) (n := 2 * k + 1)) : ℕ :=
  2 * (evenEntryBlock k e P - 1)


-- @@ L177-189 verbatim
/-- Adjacent vertices have paper-potential values differing by at most two. -/
theorem rankPotential_dist_adjacent
    {V : Type*} [AddCommGroup V] [Module K V]
    (k : ℕ) (e : V)
    {P P' : EvenPartialFlag (K := K) (V := V) (n := 2 * k + 1)}
    (h : (halvedFlagGraph (K := K) (V := V) (n := 2 * k + 1)).Adj P P') :
    Nat.dist (rankPotential k e P) (rankPotential k e P') ≤ 2 := by
  have hforward := evenEntryBlock_adjacent k e h
  have hbackward := evenEntryBlock_adjacent k e h.symm
  have hP := one_le_evenEntryBlock k e P
  have hP' := one_le_evenEntryBlock k e P'
  simp only [rankPotential, Nat.dist]
  omega


-- @@ L191-208 verbatim
/-- Along a walk, the entry block changes by no more than its length. -/
theorem evenEntryBlock_walk_le
    {V : Type*} [AddCommGroup V] [Module K V]
    (k : ℕ) (e : V)
    {P P' : EvenPartialFlag (K := K) (V := V) (n := 2 * k + 1)}
    (p : (halvedFlagGraph (K := K) (V := V) (n := 2 * k + 1)).Walk P P') :
    evenEntryBlock k e P' ≤ evenEntryBlock k e P + p.length := by
  induction p with
  | nil => simp
  | @cons P Q P' h p ih =>
      have hstep := evenEntryBlock_adjacent k e h
      calc
        evenEntryBlock k e P' ≤ evenEntryBlock k e Q + p.length := ih
        _ ≤ (evenEntryBlock k e P + 1) + p.length :=
          Nat.add_le_add_right hstep p.length
        _ = evenEntryBlock k e P + (SimpleGraph.Walk.cons h p).length := by
          simp
          omega


-- @@ L210-221 verbatim
/-- The rank potential can increase by at most two per edge along a walk. -/
theorem rankPotential_walk_le
    {V : Type*} [AddCommGroup V] [Module K V]
    (k : ℕ) (e : V)
    {P P' : EvenPartialFlag (K := K) (V := V) (n := 2 * k + 1)}
    (p : (halvedFlagGraph (K := K) (V := V) (n := 2 * k + 1)).Walk P P') :
    rankPotential k e P' ≤ rankPotential k e P + 2 * p.length := by
  have hblock := evenEntryBlock_walk_le k e p
  have hP := one_le_evenEntryBlock k e P
  have hP' := one_le_evenEntryBlock k e P'
  simp only [rankPotential]
  omega


-- @@ L223-223 verbatim
section BasisEndpoints


-- @@ L225-225 verbatim
variable {V : Type*} [AddCommGroup V] [Module K V]


-- @@ L227-238 verbatim
theorem evenEntryBlock_standard_basis (k : ℕ) (hk : 1 ≤ k)
    (b : Basis (Fin (2 * k + 1)) K V) :
    evenEntryBlock k (b 0)
      (PartialFlag.ofComplete 0 (CompleteFlag.ofBasis b)) = 1 := by
  apply Nat.le_antisymm
  · apply evenEntryBlock_ofComplete_le_of_mem k (b 0)
      (CompleteFlag.ofBasis b) 1 (by omega) hk
    apply b.self_mem_flag
    change (0 : ℕ) < 2
    omega
  · exact one_le_evenEntryBlock k (b 0)
      (PartialFlag.ofComplete 0 (CompleteFlag.ofBasis b))


-- @@ L240-266 verbatim
theorem evenEntryBlock_opposite_basis (k : ℕ)
    (b : Basis (Fin (2 * k + 1)) K V) :
    evenEntryBlock k (b 0)
      (PartialFlag.ofComplete 0
        (CompleteFlag.ofBasis (b.reindex Fin.revPerm))) = k + 1 := by
  apply Nat.le_antisymm (evenEntryBlock_le_sentinel k (b 0) _)
  let a := evenEntryBlock k (b 0)
    (PartialFlag.ofComplete 0
      (CompleteFlag.ofBasis (b.reindex Fin.revPerm)))
  have hspec : EvenEntryCandidate k (b 0)
      (PartialFlag.ofComplete 0
        (CompleteFlag.ofBasis (b.reindex Fin.revPerm))) a :=
    evenEntryBlock_spec k (b 0) _
  rcases hspec with hentry | hsentinel
  · obtain ⟨ha1, ha, hmem⟩ := hentry
    have hmemFlag : b 0 ∈
        (b.reindex Fin.revPerm).flag (evenRank k a ha) := by
      change b 0 ∈ flagPart 0
        (CompleteFlag.ofBasis (b.reindex Fin.revPerm)) (evenRank k a ha) at hmem
      rw [flagPart, ite_eq_left (by simp [evenRank])] at hmem
      exact hmem
    have hb0 : b 0 = (b.reindex Fin.revPerm) (Fin.last (2 * k)) := by
      simp [Basis.reindex_apply]
    rw [hb0, (b.reindex Fin.revPerm).self_mem_flag_iff] at hmemFlag
    change 2 * k < 2 * a at hmemFlag
    omega
  · exact hsentinel.ge


-- @@ L268-272 verbatim
theorem rankPotential_standard_basis (k : ℕ) (hk : 1 ≤ k)
    (b : Basis (Fin (2 * k + 1)) K V) :
    rankPotential k (b 0)
      (PartialFlag.ofComplete 0 (CompleteFlag.ofBasis b)) = 0 := by
  simp [rankPotential, evenEntryBlock_standard_basis k hk b]


-- @@ L274-280 verbatim
theorem rankPotential_opposite_basis (k : ℕ)
    (b : Basis (Fin (2 * k + 1)) K V) :
    rankPotential k (b 0)
      (PartialFlag.ofComplete 0
        (CompleteFlag.ofBasis (b.reindex Fin.revPerm))) = 2 * k := by
  rw [rankPotential, evenEntryBlock_opposite_basis k b]
  omega


-- @@ L282-294 verbatim
/-- Every walk from the standard flag to the opposite flag has at least `k`
edges, exactly as in the potential argument in Proposition 3.1. -/
theorem standard_to_opposite_walk_length (k : ℕ) (hk : 1 ≤ k)
    (b : Basis (Fin (2 * k + 1)) K V)
    (p : (halvedFlagGraph (K := K) (V := V) (n := 2 * k + 1)).Walk
      (PartialFlag.ofComplete 0 (CompleteFlag.ofBasis b))
      (PartialFlag.ofComplete 0
        (CompleteFlag.ofBasis (b.reindex Fin.revPerm)))) :
    k ≤ p.length := by
  have h := rankPotential_walk_le k (b 0) p
  rw [rankPotential_standard_basis k hk b,
    rankPotential_opposite_basis k b] at h
  omega


-- @@ L296-320 verbatim
/-- The reverse inequality `k ≤ ediam`, witnessed by the standard and
opposite complete flags and proved with the paper's rank potential. -/
theorem halvedFlagGraph_ediam_ge_ofBasis (k : ℕ) (hk : 1 ≤ k)
    (b : Basis (Fin (2 * k + 1)) K V) :
    (k : ℕ∞) ≤
      (halvedFlagGraph (K := K) (V := V) (n := 2 * k + 1)).ediam := by
  let G := halvedFlagGraph (K := K) (V := V) (n := 2 * k + 1)
  let A := PartialFlag.ofComplete 0 (CompleteFlag.ofBasis b)
  let C := PartialFlag.ofComplete 0
    (CompleteFlag.ofBasis (b.reindex Fin.revPerm))
  have hupper : G.edist A C ≤ (k : ℕ∞) :=
    (SimpleGraph.edist_le_ediam (G := G)).trans
      (halvedFlagGraph_ediam_le (K := K) (V := V) k)
  have hfinite : G.edist A C ≠ ⊤ := by
    intro htop
    have : (⊤ : ℕ∞) ≤ (k : ℕ∞) := htop ▸ hupper
    simp at this
  obtain ⟨p, hp⟩ := SimpleGraph.exists_walk_of_edist_ne_top hfinite
  have hlength : k ≤ p.length := by
    exact standard_to_opposite_walk_length k hk b p
  have hdist : (k : ℕ∞) ≤ G.edist A C := by
    calc
      (k : ℕ∞) ≤ (p.length : ℕ∞) := by exact_mod_cast hlength
      _ = G.edist A C := hp
  exact hdist.trans SimpleGraph.edist_le_ediam


-- @@ L322-328 verbatim
/-- The exact diameter assertion `diam H_{k,q}=k` from Proposition 3.1,
in extended-diameter form. -/
theorem halvedFlagGraph_ediam_eq_ofBasis (k : ℕ) (hk : 1 ≤ k)
    (b : Basis (Fin (2 * k + 1)) K V) :
    (halvedFlagGraph (K := K) (V := V) (n := 2 * k + 1)).ediam = (k : ℕ∞) :=
  le_antisymm (halvedFlagGraph_ediam_le (K := K) (V := V) k)
    (halvedFlagGraph_ediam_ge_ofBasis k hk b)


-- @@ L330-330 verbatim
end BasisEndpoints


-- @@ L332-332 verbatim
section CoordinateFlags


-- @@ L334-335 verbatim
/-- The coordinate space used for the concrete graph `H_{k,q}`. -/
abbrev CoordinateFlagSpace (K : Type*) (k : ℕ) := Fin (2 * k + 1) → K


-- @@ L337-340 verbatim
/-- The standard coordinate basis `e₁,...,eₜ`. -/
noncomputable def coordinateBasis (k : ℕ) :
    Basis (Fin (2 * k + 1)) K (CoordinateFlagSpace K k) :=
  Pi.basisFun K (Fin (2 * k + 1))


-- @@ L342-344 verbatim
/-- The vector called `e₁` in the paper. -/
noncomputable def firstCoordinate (k : ℕ) : CoordinateFlagSpace K k :=
  coordinateBasis k 0


-- @@ L346-349 verbatim
/-- The even part of the standard complete flag `A`. -/
noncomputable def standardEvenFlag (k : ℕ) :
    EvenPartialFlag (K := K) (V := CoordinateFlagSpace K k) (n := 2 * k + 1) :=
  PartialFlag.ofComplete 0 (CompleteFlag.ofBasis (coordinateBasis k))


-- @@ L351-355 verbatim
/-- The even part of the reverse-coordinate complete flag `C`. -/
noncomputable def oppositeEvenFlag (k : ℕ) :
    EvenPartialFlag (K := K) (V := CoordinateFlagSpace K k) (n := 2 * k + 1) :=
  PartialFlag.ofComplete 0
    (CompleteFlag.ofBasis ((coordinateBasis k).reindex Fin.revPerm))


-- @@ L357-360 verbatim
theorem coordinate_halvedFlagGraph_ediam_eq (k : ℕ) (hk : 1 ≤ k) :
    (halvedFlagGraph (K := K) (V := CoordinateFlagSpace K k)
      (n := 2 * k + 1)).ediam = (k : ℕ∞) :=
  halvedFlagGraph_ediam_eq_ofBasis k hk (coordinateBasis k)


-- @@ L362-362 verbatim
end CoordinateFlags


-- @@ L364-364 verbatim
end DegreeDiameter


-- @@ L366-366 verbatim
end MooreBound
