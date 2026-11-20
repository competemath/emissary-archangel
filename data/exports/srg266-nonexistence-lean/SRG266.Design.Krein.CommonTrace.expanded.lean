/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Design.Krein.BicliqueLocalDegrees


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
def commonCount (T : Finset V) (x y : V) : ℕ :=
  (T.filter fun w => D.kreinGraph.Adj x w ∧ D.kreinGraph.Adj y w).card


-- @@ L20-23 verbatim
theorem commonCount_cast (T : Finset V) (x y : V) :
    (D.commonCount T x y : ℤ) = ∑ w ∈ T, D.kreinMatrix x w * D.kreinMatrix y w := by
  simp only [commonCount, ← D.kreinGraph_adjMatrix, SimpleGraph.adjMatrix_apply,
    ite_zero_mul_ite_zero, one_mul, Finset.sum_boole]


-- @@ L25-26 verbatim
theorem commonCount_self (T : Finset V) (x : V) :
    D.commonCount T x x = D.neighborCount T x := by simp [commonCount, neighborCount]


-- @@ L28-31 verbatim
theorem kreinMatrix_common_sum (x y : V) :
    (∑ w, D.kreinMatrix x w * D.kreinMatrix y w) =
      45 * (if x = y then 1 else 0) + 12 - 12 * D.kreinMatrix x y := by
  simpa only [Matrix.mul_apply, D.kreinMatrix_comm y] using D.kreinMatrix_square_apply x y


-- @@ L33-38 verbatim
theorem commonCount_univ {x y : V} (hxy : x ≠ y) (hn : ¬ D.kreinGraph.Adj x y) :
    D.commonCount Finset.univ x y = 12 := by
  have h : (D.commonCount Finset.univ x y : ℤ) = 12 := by
    rw [D.commonCount_cast, D.kreinMatrix_common_sum]
    simp [hxy, ← D.kreinGraph_adjMatrix, SimpleGraph.adjMatrix_apply, hn]
  exact_mod_cast h


-- @@ L40-80 verbatim
theorem commonTriple_moment {x y : V} (hxy : x ≠ y) (hn : ¬ D.kreinGraph.Adj x y) (z : V) :
    (∑ w, D.kreinMatrix x w * D.kreinMatrix y w * D.kreinMatrix z w) =
      3 * (1 - D.kreinMatrix x z - D.kreinMatrix y z +
        D.kreinMatrix x z * D.kreinMatrix y z) +
      9 * (if z = x then 1 else 0) + 9 * (if z = y then 1 else 0) := by
  have hdiag (a b : V) : (∑ w, D.kreinMatrix a w * D.kreinMatrix b w * D.kreinMatrix a w) =
      ∑ w, D.kreinMatrix a w * D.kreinMatrix b w := by
    apply Finset.sum_congr rfl
    intro w _
    rw [← D.kreinGraph_adjMatrix]
    simp only [SimpleGraph.adjMatrix_apply]
    split_ifs <;> norm_num
  by_cases hzx : z = x
  · subst z
    rw [hdiag, D.kreinMatrix_common_sum]
    simp [hxy, ← D.kreinGraph_adjMatrix, SimpleGraph.adjMatrix_apply,
      hn, D.kreinGraph.adj_comm y x]
  · by_cases hzy : z = y
    · subst z
      have heq : (∑ w, D.kreinMatrix x w * D.kreinMatrix y w * D.kreinMatrix y w) =
          ∑ w, D.kreinMatrix y w * D.kreinMatrix x w * D.kreinMatrix y w := by
        apply Finset.sum_congr rfl
        intro w _
        ring
      rw [heq, hdiag, D.kreinMatrix_common_sum]
      simp [Ne.symm hxy, ← D.kreinGraph_adjMatrix, SimpleGraph.adjMatrix_apply,
        hn, D.kreinGraph.adj_comm y x]
    · have h := D.independent_pair_neighbor_moment hzx hzy hxy hn
      have heq : (∑ w, D.kreinMatrix x w * D.kreinMatrix y w * D.kreinMatrix z w) =
          ∑ w, D.kreinMatrix z w * D.kreinMatrix w x * D.kreinMatrix w y := by
        apply Finset.sum_congr rfl
        intro w _
        rw [D.kreinMatrix_comm w x, D.kreinMatrix_comm w y]
        ring
      rw [heq, h]
      simp only [hzx, hzy, if_false, mul_zero, add_zero]
      rw [← D.kreinGraph_adjMatrix]
      simp only [SimpleGraph.adjMatrix_apply, D.kreinGraph.adj_comm z x,
        D.kreinGraph.adj_comm z y]
      by_cases hxz : D.kreinGraph.Adj x z <;>
        by_cases hyz : D.kreinGraph.Adj y z <;> simp [hxz, hyz]


-- @@ L82-93 verbatim
theorem commonTrace_subset (T : Finset V) {x y : V}
    (hxy : x ≠ y) (hn : ¬ D.kreinGraph.Adj x y) :
    (∑ w, D.kreinMatrix x w * D.kreinMatrix y w * (D.neighborCount T w : ℤ)) =
      3 * T.card - 3 * D.neighborCount T x - 3 * D.neighborCount T y +
      3 * D.commonCount T x y + 9 * (if x ∈ T then 1 else 0) +
        9 * (if y ∈ T then 1 else 0) := by
  simp_rw [D.neighborCount_cast, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [D.kreinMatrix_comm _ _, D.commonTriple_moment hxy hn]
  simp [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← D.neighborCount_cast, ← D.commonCount_cast, mul_comm]
  ring


-- @@ L95-99 verbatim
theorem commonCount_cast_indicator (T : Finset V) (x y : V) :
    (D.commonCount T x y : ℤ) =
      ∑ w, D.kreinMatrix x w * D.kreinMatrix y w * (if w ∈ T then 1 else 0) := by
  rw [D.commonCount_cast]
  simp [mul_ite]


-- @@ L101-104 verbatim
@[simp] theorem mem_bicliqueClass (S : Finset V) (i : ℕ) (x : V) :
    x ∈ D.bicliqueClass S i ↔ x ∉ S ∪ D.commonTo S ∧
      D.neighborCount (S ∪ D.commonTo S) x = i := by
  simp [bicliqueClass]


-- @@ L106-123 verbatim
theorem biclique_partition_indicators {S : Finset V} (hcard : S.card = 3)
    (hI : D.IndependentSet S) (x : V) :
    (1 : ℤ) = (if x ∈ S ∪ D.commonTo S then 1 else 0) +
      (if x ∈ D.bicliqueClass S 0 then 1 else 0) +
      (if x ∈ D.bicliqueClass S 1 then 1 else 0) +
      (if x ∈ D.bicliqueClass S 2 then 1 else 0) ∧
    (D.neighborCount (S ∪ D.commonTo S) x : ℤ) =
      3 * (if x ∈ S ∪ D.commonTo S then 1 else 0) +
      (if x ∈ D.bicliqueClass S 1 then 1 else 0) +
      2 * (if x ∈ D.bicliqueClass S 2 then 1 else 0) := by
  by_cases hx : x ∈ S ∪ D.commonTo S
  · have ht := D.neighborCount_biclique_of_mem hcard hI hx
    simp [hx, ht]
  · have hb := D.biclique_outside_degree_le_two hcard hI hx
    change D.neighborCount (S ∪ D.commonTo S) x ≤ 2 at hb
    have hc : D.neighborCount (S ∪ D.commonTo S) x = 0 ∨
        D.neighborCount (S ∪ D.commonTo S) x = 1 ∨ D.neighborCount (S ∪ D.commonTo S) x = 2 := by omega
    rcases hc with h | h | h <;> simp [hx, h]


-- @@ L125-134 verbatim
theorem commonCount_biclique_partition {S : Finset V} (hcard : S.card = 3)
    (hI : D.IndependentSet S) (x y : V) :
    (D.commonCount Finset.univ x y : ℤ) = D.commonCount (S ∪ D.commonTo S) x y +
      D.commonCount (D.bicliqueClass S 0) x y + D.commonCount (D.bicliqueClass S 1) x y +
      D.commonCount (D.bicliqueClass S 2) x y := by
  have h := Finset.sum_congr (s₁ := Finset.univ) rfl (fun w _ =>
    congrArg (fun z : ℤ => D.kreinMatrix x w * D.kreinMatrix y w * z)
      (D.biclique_partition_indicators hcard hI w).1)
  simpa only [mul_one, mul_add, Finset.sum_add_distrib, ← D.commonCount_cast,
    ← D.commonCount_cast_indicator] using h


-- @@ L136-151 verbatim
theorem commonTrace_biclique_partition {S : Finset V} (hcard : S.card = 3)
    (hI : D.IndependentSet S) (x y : V) :
    (∑ w, D.kreinMatrix x w * D.kreinMatrix y w * (D.neighborCount (S ∪ D.commonTo S) w : ℤ)) =
      3 * D.commonCount (S ∪ D.commonTo S) x y +
      D.commonCount (D.bicliqueClass S 1) x y + 2 * D.commonCount (D.bicliqueClass S 2) x y := by
  calc
    _ = ∑ w, (3 * (D.kreinMatrix x w * D.kreinMatrix y w *
          (if w ∈ S ∪ D.commonTo S then 1 else 0)) +
        D.kreinMatrix x w * D.kreinMatrix y w * (if w ∈ D.bicliqueClass S 1 then 1 else 0) +
        2 * (D.kreinMatrix x w * D.kreinMatrix y w * (if w ∈ D.bicliqueClass S 2 then 1 else 0))) := by
      apply Finset.sum_congr rfl
      intro w _
      rw [(D.biclique_partition_indicators hcard hI w).2]
      ring
    _ = _ := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← D.commonCount_cast_indicator]


-- @@ L153-154 verbatim
def bicliqueCubicLeft (S : Finset V) : Finset V :=
  (S ∪ D.commonTo S) ∪ D.bicliqueClass S 0


-- @@ L156-160 verbatim
theorem disjoint_biclique_class (S : Finset V) (i : ℕ) :
    Disjoint (S ∪ D.commonTo S) (D.bicliqueClass S i) := by
  apply Finset.disjoint_left.mpr
  intro x hx hi
  exact ((D.mem_bicliqueClass S i x).mp hi).1 hx


-- @@ L162-166 verbatim
theorem commonCount_union (T U : Finset V) (hd : Disjoint T U) (x y : V) :
    D.commonCount (T ∪ U) x y = D.commonCount T x y + D.commonCount U x y := by
  simp only [commonCount, Finset.filter_union]
  exact Finset.card_union_of_disjoint
    (hd.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _))


-- @@ L168-177 verbatim
theorem bicliqueCubicLeft_trace {S : Finset V} (hcard : S.card = 3)
    (hI : D.IndependentSet S) {x : V} (hx : x ∈ D.bicliqueCubicLeft S) :
    (3 : ℤ) * D.neighborCount (S ∪ D.commonTo S) x =
      9 * (if x ∈ S ∪ D.commonTo S then 1 else 0) := by
  rcases Finset.mem_union.mp hx with hxD | hx0
  · rw [D.neighborCount_biclique_of_mem hcard hI hxD, if_pos hxD]
    norm_num
  · obtain ⟨hxD,h0⟩ := (D.mem_bicliqueClass S 0 x).mp hx0
    rw [h0, if_neg hxD]
    norm_num


-- @@ L179-193 verbatim
theorem bicliqueCubicLeft_common {S : Finset V} (hcard : S.card = 3)
    (hI : D.IndependentSet S) {x y : V} (hx : x ∈ D.bicliqueCubicLeft S)
    (hy : y ∈ D.bicliqueCubicLeft S) (hxy : x ≠ y) (hn : ¬ D.kreinGraph.Adj x y) :
    D.commonCount (D.bicliqueClass S 2) x y = 6 + D.commonCount (D.bicliqueCubicLeft S) x y := by
  have ht := D.commonTrace_subset (S ∪ D.commonTo S) hxy hn
  have hp := D.commonTrace_biclique_partition hcard hI x y
  have hc := D.commonCount_biclique_partition hcard hI x y
  have hu := D.commonCount_union (S ∪ D.commonTo S) (D.bicliqueClass S 0)
    (D.disjoint_biclique_class S 0) x y
  have htx := D.bicliqueCubicLeft_trace hcard hI hx
  have hty := D.bicliqueCubicLeft_trace hcard hI hy
  rw [D.biclique_card hcard hI] at ht
  rw [D.commonCount_univ hxy hn] at hc
  change D.commonCount (D.bicliqueCubicLeft S) x y = _ at hu
  omega


-- @@ L195-209 verbatim
theorem bicliqueCubicRight_common {S : Finset V} (hcard : S.card = 3)
    (hI : D.IndependentSet S) {x y : V} (hx : x ∈ D.bicliqueClass S 2)
    (hy : y ∈ D.bicliqueClass S 2) (hxy : x ≠ y) (hn : ¬ D.kreinGraph.Adj x y) :
    D.commonCount (D.bicliqueCubicLeft S) x y = 6 + D.commonCount (D.bicliqueClass S 2) x y := by
  have ht := D.commonTrace_subset (S ∪ D.commonTo S) hxy hn
  have hp := D.commonTrace_biclique_partition hcard hI x y
  have hc := D.commonCount_biclique_partition hcard hI x y
  have hu := D.commonCount_union (S ∪ D.commonTo S) (D.bicliqueClass S 0)
    (D.disjoint_biclique_class S 0) x y
  obtain ⟨hxD,h2x⟩ := (D.mem_bicliqueClass S 2 x).mp hx
  obtain ⟨hyD,h2y⟩ := (D.mem_bicliqueClass S 2 y).mp hy
  rw [D.biclique_card hcard hI, h2x, h2y, if_neg hxD, if_neg hyD] at ht
  rw [D.commonCount_univ hxy hn] at hc
  change D.commonCount (D.bicliqueCubicLeft S) x y = _ at hu
  omega


-- @@ L211-211 verbatim
end SRG266.QuasiSymmetric.TripleDesign57
