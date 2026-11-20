/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Design.Krein.BicliqueGeometry


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
def neighborCount (T : Finset V) (x : V) : ℕ :=
  (T.filter fun y => D.kreinGraph.Adj x y).card


-- @@ L20-22 verbatim
theorem neighborCount_cast (T : Finset V) (x : V) :
    (D.neighborCount T x : ℤ) = ∑ y ∈ T, D.kreinMatrix x y := by
  simp [neighborCount, ← D.kreinGraph_adjMatrix, SimpleGraph.adjMatrix_apply]


-- @@ L24-26 verbatim
theorem kreinMatrix_comm (x y : V) : D.kreinMatrix x y = D.kreinMatrix y x := by
  simp only [← D.kreinGraph_adjMatrix, SimpleGraph.adjMatrix_apply,
    D.kreinGraph.adj_comm x y]


-- @@ L28-33 verbatim
theorem kreinMatrix_row_sum (x : V) : (∑ y, D.kreinMatrix x y) = 57 := by
  rw [← D.neighborCount_cast]
  have heq : D.neighborCount Finset.univ x = D.kreinGraph.degree x := by
    simp [neighborCount, SimpleGraph.degree, SimpleGraph.neighborFinset_eq_filter]
  rw [heq, D.kreinGraph_degree]
  norm_num


-- @@ L35-40 verbatim
theorem neighborCount_sum (T : Finset V) :
    (∑ x, (D.neighborCount T x : ℤ)) = 57 * T.card := by
  simp_rw [D.neighborCount_cast]
  rw [Finset.sum_comm]
  simp_rw [D.kreinMatrix_comm, D.kreinMatrix_row_sum]
  simp [mul_comm]


-- @@ L42-59 verbatim
theorem neighborCount_square_sum (T : Finset V) :
    (∑ x, (D.neighborCount T x : ℤ)^2) =
      45 * T.card + 12 * (T.card : ℤ)^2 - 12 * ∑ x ∈ T, (D.neighborCount T x : ℤ) := by
  have hpair (a b : V) : (∑ x, D.kreinMatrix x a * D.kreinMatrix x b) =
      45 * (if a = b then 1 else 0) + 12 - 12 * D.kreinMatrix a b := by
    simpa only [Matrix.mul_apply, D.kreinMatrix_comm a] using D.kreinMatrix_square_apply a b
  calc
    _ = ∑ a ∈ T, ∑ b ∈ T, ∑ x, D.kreinMatrix x a * D.kreinMatrix x b := by
      simp_rw [D.neighborCount_cast, pow_two, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.sum_comm]
    _ = _ := by
      simp_rw [hpair, Finset.sum_sub_distrib, Finset.sum_add_distrib,
        ← Finset.mul_sum, ← D.neighborCount_cast]
      simp
      ring


-- @@ L61-72 verbatim
theorem biclique_neighbors_of_mem_side {S : Finset V} (hI : D.IndependentSet S)
    {x : V} (hx : x ∈ S) :
    (S ∪ D.commonTo S).filter (fun y => D.kreinGraph.Adj x y) = D.commonTo S := by
  ext y
  constructor
  · intro hy
    obtain ⟨hyU,hxy⟩ := Finset.mem_filter.mp hy
    rcases Finset.mem_union.mp hyU with hyS | hyC
    · exact (hI x hx y hyS (D.kreinGraph.ne_of_adj hxy) hxy).elim
    · exact hyC
  · intro hy
    exact Finset.mem_filter.mpr ⟨Finset.mem_union_right _ hy, (D.mem_commonTo _ _).mp hy x hx⟩


-- @@ L74-82 verbatim
theorem neighborCount_biclique_of_mem {S : Finset V} (hcard : S.card = 3)
    (hI : D.IndependentSet S) {x : V} (hx : x ∈ S ∪ D.commonTo S) :
    D.neighborCount (S ∪ D.commonTo S) x = 3 := by
  rcases Finset.mem_union.mp hx with hxS | hxC
  · rw [neighborCount, D.biclique_neighbors_of_mem_side hI hxS, D.commonTo_card hcard hI]
  · have hC := D.biclique_neighbors_of_mem_side
      (D.commonTo_independent (Finset.card_pos.mp (by omega : 0 < S.card))) hxC
    rw [D.commonTo_involution hcard hI, Finset.union_comm] at hC
    rw [neighborCount, hC, hcard]


-- @@ L84-84 verbatim
def bicliqueOutside (S : Finset V) : Finset V := Finset.univ \ (S ∪ D.commonTo S)


-- @@ L86-87 verbatim
def bicliqueClass (S : Finset V) (i : ℕ) : Finset V :=
  (D.bicliqueOutside S).filter fun x => D.neighborCount (S ∪ D.commonTo S) x = i


-- @@ L89-90 verbatim
@[simp] theorem mem_bicliqueOutside (S : Finset V) (x : V) :
    x ∈ D.bicliqueOutside S ↔ x ∉ S ∪ D.commonTo S := by simp [bicliqueOutside]


-- @@ L92-95 verbatim
theorem bicliqueOutside_card {S : Finset V} (hcard : S.card = 3)
    (hI : D.IndependentSet S) : (D.bicliqueOutside S).card = 318 := by
  rw [bicliqueOutside, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
    D.kreinGraph_isSRGWith.card, D.biclique_card hcard hI]


-- @@ L97-121 verbatim
theorem bicliqueOutside_trace_moments {S : Finset V} (hcard : S.card = 3)
    (hI : D.IndependentSet S) :
    (∑ x ∈ D.bicliqueOutside S, (D.neighborCount (S ∪ D.commonTo S) x : ℤ)) = 324 ∧
    (∑ x ∈ D.bicliqueOutside S, (D.neighborCount (S ∪ D.commonTo S) x : ℤ)^2) = 432 := by
  let T := S ∪ D.commonTo S
  have hT : T.card = 6 := D.biclique_card hcard hI
  have hin : ∀ x ∈ T, (D.neighborCount T x : ℤ) = 3 := by
    intro x hx
    rw [D.neighborCount_biclique_of_mem hcard hI hx]
    norm_num
  have hs := D.neighborCount_sum T
  have hss := D.neighborCount_square_sum T
  have hins : (∑ x ∈ T, (D.neighborCount T x : ℤ)) = 18 := by
    rw [Finset.sum_congr rfl hin]
    simp [hT]
  have hinss : (∑ x ∈ T, (D.neighborCount T x : ℤ)^2) = 54 := by
    have h := Finset.sum_congr rfl (fun x hx => congrArg (fun z : ℤ => z^2) (hin x hx))
    rw [h]
    simp [hT]
  have htotal := Finset.sum_sdiff (Finset.subset_univ T) (f := fun x => (D.neighborCount T x : ℤ))
  have htotal2 := Finset.sum_sdiff (Finset.subset_univ T) (f := fun x => (D.neighborCount T x : ℤ)^2)
  simp only [hT, hins] at hs hss
  change (∑ x ∈ Finset.univ \ T, (D.neighborCount T x : ℤ)) = 324 ∧
    (∑ x ∈ Finset.univ \ T, (D.neighborCount T x : ℤ)^2) = 432
  constructor <;> omega


-- @@ L123-144 verbatim
theorem boundedTwo_fiber_moments {α : Type*} [DecidableEq α] (U : Finset α)
    (f : α → ℕ) (hle : ∀ x ∈ U, f x ≤ 2) :
    (U.card : ℤ) = (U.filter fun x => f x = 0).card +
      (U.filter fun x => f x = 1).card + (U.filter fun x => f x = 2).card ∧
    (∑ x ∈ U, (f x : ℤ)) = (U.filter fun x => f x = 1).card +
      2 * (U.filter fun x => f x = 2).card ∧
    (∑ x ∈ U, (f x : ℤ)^2) = (U.filter fun x => f x = 1).card +
      4 * (U.filter fun x => f x = 2).card := by
  have hp (x) (hx : x ∈ U) :
      (1 : ℤ) = (if f x = 0 then 1 else 0) + (if f x = 1 then 1 else 0) +
        (if f x = 2 then 1 else 0) ∧
      (f x : ℤ) = (if f x = 1 then 1 else 0) + 2 * (if f x = 2 then 1 else 0) ∧
      (f x : ℤ)^2 = (if f x = 1 then 1 else 0) + 4 * (if f x = 2 then 1 else 0) := by
    have h := hle x hx
    have hcases : f x = 0 ∨ f x = 1 ∨ f x = 2 := by omega
    rcases hcases with h0 | h1 | h2 <;> simp_all
  have h0 := Finset.sum_congr rfl (fun x hx => (hp x hx).1)
  have h1 := Finset.sum_congr rfl (fun x hx => (hp x hx).2.1)
  have h2 := Finset.sum_congr rfl (fun x hx => (hp x hx).2.2)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_boole,
    Finset.sum_const, nsmul_eq_mul, mul_one] at h0 h1 h2
  exact ⟨h0,h1,h2⟩


-- @@ L146-161 verbatim
theorem bicliqueClass_card {S : Finset V} (hcard : S.card = 3)
    (hI : D.IndependentSet S) :
    (D.bicliqueClass S 0).card = 48 ∧ (D.bicliqueClass S 1).card = 216 ∧
      (D.bicliqueClass S 2).card = 54 := by
  have hle : ∀ x ∈ D.bicliqueOutside S, D.neighborCount (S ∪ D.commonTo S) x ≤ 2 := by
    intro x hx
    exact D.biclique_outside_degree_le_two hcard hI ((D.mem_bicliqueOutside S x).mp hx)
  have h := boundedTwo_fiber_moments (D.bicliqueOutside S)
    (D.neighborCount (S ∪ D.commonTo S)) hle
  have hm := D.bicliqueOutside_trace_moments hcard hI
  have hc := D.bicliqueOutside_card hcard hI
  change (D.bicliqueOutside S).card = ((D.bicliqueClass S 0).card : ℤ) +
    (D.bicliqueClass S 1).card + (D.bicliqueClass S 2).card ∧
    _ = ((D.bicliqueClass S 1).card : ℤ) + 2 * (D.bicliqueClass S 2).card ∧
    _ = ((D.bicliqueClass S 1).card : ℤ) + 4 * (D.bicliqueClass S 2).card at h
  omega


-- @@ L163-163 verbatim
end SRG266.QuasiSymmetric.TripleDesign57
