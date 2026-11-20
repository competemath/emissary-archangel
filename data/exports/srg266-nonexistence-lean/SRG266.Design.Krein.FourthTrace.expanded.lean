/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Design.Krein.CubicGram
import Mathlib.LinearAlgebra.Matrix.Trace


-- @@ L9-9 verbatim
open scoped BigOperators Matrix


-- @@ L11-11 verbatim
namespace SRG266.QuasiSymmetric.TripleDesign57


-- @@ L13-14 verbatim
variable {P B : Type*} [Fintype P] [DecidableEq P] [Fintype B] [DecidableEq B]
    (D : TripleDesign57 P B)


-- @@ L16-16 verbatim
local notation "V" => KreinVertex (P := P) (B := B)


-- @@ L18-22 verbatim
theorem setAdjMatrix_row_sum (T : Finset V) (x : T) :
    (∑ y, D.setAdjMatrix T x y) = D.neighborCount T x := by
  unfold setAdjMatrix
  rw [Finset.sum_coe_sort T (fun y : V => D.kreinMatrix x y)]
  exact (D.neighborCount_cast T x).symm


-- @@ L24-25 verbatim
theorem setAdjMatrix_comm (T : Finset V) (x y : T) :
    D.setAdjMatrix T x y = D.setAdjMatrix T y x := D.kreinMatrix_comm x y


-- @@ L27-28 verbatim
theorem setAdjMatrix_trace (T : Finset V) : Matrix.trace (D.setAdjMatrix T) = 0 := by
  simp [Matrix.trace, setAdjMatrix, ← D.kreinGraph_adjMatrix, SimpleGraph.adjMatrix_apply]


-- @@ L30-36 verbatim
theorem setAdjMatrix_square_trace (T : Finset V)
    (hdeg : ∀ x ∈ T, D.neighborCount T x = 3) :
    Matrix.trace ((D.setAdjMatrix T)^2) = (3 : ℤ) * T.card := by
  simp only [Matrix.trace, Matrix.diag_apply, pow_two, D.setAdjMatrix_square, D.commonCount_self]
  have h (x : T) : (D.neighborCount T x : ℤ) = 3 := by rw [hdeg x x.property]; norm_num
  simp_rw [h]
  simp [mul_comm]


-- @@ L38-49 verbatim
theorem setAdjMatrix_cube_trace (T : Finset V) : Matrix.trace ((D.setAdjMatrix T)^3) = 0 := by
  apply Finset.sum_eq_zero
  intro x _
  change ((D.setAdjMatrix T)^3) x x = 0
  rw [pow_succ, pow_two, Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro y _
  by_cases hxy : D.kreinGraph.Adj x y
  · rw [D.setAdjMatrix_square, D.commonCount_of_adj T hxy]
    simp
  · simp [setAdjMatrix, ← D.kreinGraph_adjMatrix, SimpleGraph.adjMatrix_apply,
      D.kreinGraph.adj_comm (y : V) (x : V), hxy]


-- @@ L51-58 verbatim
theorem setAdjMatrix_mul_ones (T : Finset V)
    (hdeg : ∀ x ∈ T, D.neighborCount T x = 3) :
    D.setAdjMatrix T * allOnesMatrix = (3 : ℤ) • allOnesMatrix := by
  ext x y
  simp only [Matrix.mul_apply, allOnesMatrix_apply, mul_one, Matrix.smul_apply, smul_eq_mul,
    D.setAdjMatrix_row_sum]
  rw [hdeg x x.property]
  norm_num


-- @@ L60-67 verbatim
theorem ones_mul_setAdjMatrix (T : Finset V)
    (hdeg : ∀ x ∈ T, D.neighborCount T x = 3) :
    allOnesMatrix * D.setAdjMatrix T = (3 : ℤ) • allOnesMatrix := by
  ext x y
  simp only [Matrix.mul_apply, allOnesMatrix_apply, one_mul, Matrix.smul_apply, smul_eq_mul,
    D.setAdjMatrix_comm T _ y, D.setAdjMatrix_row_sum]
  rw [hdeg y y.property]
  norm_num


-- @@ L69-97 verbatim
theorem cubicGram_polynomial_trace (T : Finset V)
    (hdeg : ∀ x ∈ T, D.neighborCount T x = 3) :
    Matrix.trace (((D.setAdjMatrix T - (3 : ℤ) • 1)^2 + (6 : ℤ) • allOnesMatrix)^2) =
      Matrix.trace ((D.setAdjMatrix T)^4) + 243 * T.card + 36 * (T.card : ℤ)^2 := by
  let H := D.setAdjMatrix T
  let J : Matrix T T ℤ := allOnesMatrix
  have hHJ : H * J = (3 : ℤ) • J := D.setAdjMatrix_mul_ones T hdeg
  have hJH : J * H = (3 : ℤ) • J := D.ones_mul_setAdjMatrix T hdeg
  have hJJ : J * J = (T.card : ℤ) • J := by
    ext x y
    simp [J, Matrix.mul_apply, allOnesMatrix]
  have hJHH : J * (H * H) = (9 : ℤ) • J := by
    rw [← Matrix.mul_assoc, hJH, Matrix.smul_mul, hJH, smul_smul]
    norm_num
  have heq : ((H - (3 : ℤ) • 1)^2 + (6 : ℤ) • J)^2 =
      H^4 - (12 : ℤ) • H^3 + (54 : ℤ) • H^2 - (108 : ℤ) • H +
        (81 : ℤ) • 1 + (36 * T.card : ℤ) • J := by
    noncomm_ring [hHJ, hJH, hJJ, hJHH]
    module
  change Matrix.trace (((H - (3 : ℤ) • 1)^2 + (6 : ℤ) • J)^2) = _
  rw [heq]
  simp only [Matrix.trace_add, Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul]
  have ht : Matrix.trace H = 0 := D.setAdjMatrix_trace T
  have ht2 : Matrix.trace (H^2) = (3 : ℤ) * T.card := D.setAdjMatrix_square_trace T hdeg
  have ht3 : Matrix.trace (H^3) = 0 := D.setAdjMatrix_cube_trace T
  have htJ : Matrix.trace J = T.card := by simp [J, allOnesMatrix, Matrix.trace]
  rw [ht, ht2, ht3, htJ, Matrix.trace_one]
  simp only [Fintype.card_coe]
  ring


-- @@ L99-104 verbatim
theorem rectangular_gram_square_trace {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (M : Matrix α β ℤ) :
    Matrix.trace ((M * M.transpose)^2) = Matrix.trace ((M.transpose * M)^2) := by
  simpa only [pow_two, Matrix.mul_assoc] using
    (Matrix.trace_mul_comm M (M.transpose * M * M.transpose))


-- @@ L106-118 verbatim
theorem bicliqueCubic_fourth_trace {S : Finset V} (hcard : S.card = 3)
    (hI : D.IndependentSet S) :
    Matrix.trace ((D.setAdjMatrix (D.bicliqueCubicLeft S))^4) =
      Matrix.trace ((D.setAdjMatrix (D.bicliqueClass S 2))^4) := by
  have h := rectangular_gram_square_trace
    (D.crossAdjMatrix (D.bicliqueCubicLeft S) (D.bicliqueClass S 2))
  rw [D.bicliqueCubic_gram_left hcard hI, D.bicliqueCubic_gram_right hcard hI] at h
  rw [D.cubicGram_polynomial_trace (D.bicliqueCubicLeft S)
      (fun x hx => (D.bicliqueCubicLeft_degrees hcard hI hx).1),
    D.cubicGram_polynomial_trace (D.bicliqueClass S 2)
      (fun x hx => (D.bicliqueCubicRight_degrees hcard hI hx).1),
    D.bicliqueCubicLeft_card hcard hI, (D.bicliqueClass_card hcard hI).2.2] at h
  linarith


-- @@ L120-121 verbatim
theorem commonCount_comm (T : Finset V) (x y : V) :
    D.commonCount T x y = D.commonCount T y x := by simp [commonCount, and_comm]


-- @@ L123-136 verbatim
theorem setAdjMatrix_fourth_trace_sum (T : Finset V) :
    Matrix.trace ((D.setAdjMatrix T)^4) =
      ∑ x : T, ∑ y : T, (D.commonCount T x y : ℤ)^2 := by
  have hp : (D.setAdjMatrix T)^4 =
      (D.setAdjMatrix T * D.setAdjMatrix T) * (D.setAdjMatrix T * D.setAdjMatrix T) := by noncomm_ring
  rw [hp]
  simp only [Matrix.trace, Matrix.diag_apply]
  apply Finset.sum_congr rfl
  intro x _
  rw [Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro y _
  rw [D.setAdjMatrix_square, D.setAdjMatrix_square, D.commonCount_comm T (y : V) x]
  ring


-- @@ L138-150 verbatim
theorem setAdjMatrix_square_row_sum (T : Finset V)
    (hdeg : ∀ x ∈ T, D.neighborCount T x = 3) (x : T) :
    (∑ y : T, (D.commonCount T x y : ℤ)) = 9 := by
  have hr (y : T) : (D.neighborCount T y : ℤ) = 3 := by rw [hdeg y y.property]; norm_num
  calc
    _ = ∑ z : T, D.setAdjMatrix T x z * (∑ y : T, D.setAdjMatrix T z y) := by
      simp_rw [← D.setAdjMatrix_square, Matrix.mul_apply]
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ = _ := by
      simp_rw [D.setAdjMatrix_row_sum, hr]
      rw [← Finset.sum_mul, D.setAdjMatrix_row_sum, hr]
      norm_num


-- @@ L152-174 verbatim
theorem cubic_fourth_trace_surplus (T : Finset V)
    (hdeg : ∀ x ∈ T, D.neighborCount T x = 3) :
    Matrix.trace ((D.setAdjMatrix T)^4) = (15 : ℤ) * T.card +
      ∑ x : T, ∑ y : T, if x = y then 0 else
        (D.commonCount T x y : ℤ)^2 - D.commonCount T x y := by
  have htotal : (∑ x : T, ∑ y : T, (D.commonCount T x y : ℤ)) = 9 * T.card := by
    simp_rw [D.setAdjMatrix_square_row_sum T hdeg]
    simp [mul_comm]
  have hdelta : (∑ x : T, ∑ y : T, if x = y then (1 : ℤ) else 0) = T.card := by simp
  have he (x y : T) : (D.commonCount T x y : ℤ)^2 =
      (D.commonCount T x y : ℤ) + 6 * (if x = y then 1 else 0) +
        (if x = y then 0 else (D.commonCount T x y : ℤ)^2 - D.commonCount T x y) := by
    by_cases hxy : x = y
    · subst y
      rw [D.commonCount_self, hdeg x x.property]
      norm_num
    · simp only [hxy, if_false, mul_zero, add_zero]
      ring
  rw [D.setAdjMatrix_fourth_trace_sum]
  rw [Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => he x y))]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [htotal, hdelta]
  ring


-- @@ L176-180 verbatim
theorem natCast_square_sub_nonneg (n : ℕ) : 0 ≤ (n : ℤ)^2 - n := by
  by_cases h : n = 0
  · simp [h]
  · have h1 : (1 : ℤ) ≤ n := by omega
    nlinarith


-- @@ L182-198 verbatim
theorem cubic_fourth_trace_of_no_square (T : Finset V)
    (hdeg : ∀ x ∈ T, D.neighborCount T x = 3)
    (hno : ∀ x : T, ∀ y : T, x ≠ y → D.commonCount T x y ≤ 1) :
    Matrix.trace ((D.setAdjMatrix T)^4) = (15 : ℤ) * T.card := by
  rw [D.cubic_fourth_trace_surplus T hdeg]
  have hz : (∑ x : T, ∑ y : T, if x = y then (0 : ℤ) else
      (D.commonCount T x y : ℤ)^2 - D.commonCount T x y) = 0 := by
    apply Finset.sum_eq_zero
    intro x _
    apply Finset.sum_eq_zero
    intro y _
    by_cases hxy : x = y
    · simp [hxy]
    · have hc := hno x y hxy
      have hv : D.commonCount T x y = 0 ∨ D.commonCount T x y = 1 := by omega
      rcases hv with h | h <;> simp [hxy, h]
  rw [hz, add_zero]


-- @@ L200-220 verbatim
theorem cubic_fourth_trace_gt_of_square (T : Finset V)
    (hdeg : ∀ x ∈ T, D.neighborCount T x = 3) (x y : T)
    (hxy : x ≠ y) (hc : 2 ≤ D.commonCount T x y) :
    (15 : ℤ) * T.card < Matrix.trace ((D.setAdjMatrix T)^4) := by
  rw [D.cubic_fourth_trace_surplus T hdeg]
  have hn (a b : T) : (0 : ℤ) ≤ (if a = b then 0 else
      (D.commonCount T a b : ℤ)^2 - D.commonCount T a b) := by
    split_ifs
    · rfl
    · exact natCast_square_sub_nonneg _
  have hp : (0 : ℤ) < (if x = y then 0 else
      (D.commonCount T x y : ℤ)^2 - D.commonCount T x y) := by
    rw [if_neg hxy]
    have hc' : (2 : ℤ) ≤ D.commonCount T x y := by exact_mod_cast hc
    nlinarith
  have hs : (0 : ℤ) < ∑ a : T, ∑ b : T, if a = b then 0 else
      (D.commonCount T a b : ℤ)^2 - D.commonCount T a b := by
    apply Finset.sum_pos' (fun a _ => Finset.sum_nonneg (fun b _ => hn a b))
    refine ⟨x, Finset.mem_univ _, ?_⟩
    exact Finset.sum_pos' (fun b _ => hn x b) ⟨y, Finset.mem_univ _, hp⟩
  linarith


-- @@ L222-242 verbatim
theorem bicliqueCubic_left_square {S : Finset V} (hcard : S.card = 3)
    (hI : D.IndependentSet S) :
    ∃ x y : D.bicliqueCubicLeft S, x ≠ y ∧
      2 ≤ D.commonCount (D.bicliqueCubicLeft S) x y := by
  obtain ⟨a,b,c,hab,_,_,hS⟩ := Finset.card_eq_three.mp hcard
  have ha : a ∈ S := by rw [hS]; simp
  have hb : b ∈ S := by rw [hS]; simp
  let x : D.bicliqueCubicLeft S := ⟨a, Finset.mem_union_left _ (Finset.mem_union_left _ ha)⟩
  let y : D.bicliqueCubicLeft S := ⟨b, Finset.mem_union_left _ (Finset.mem_union_left _ hb)⟩
  refine ⟨x,y,fun h => hab (congrArg Subtype.val h),?_⟩
  have hsub : D.commonTo S ⊆ (D.bicliqueCubicLeft S).filter
      (fun z => D.kreinGraph.Adj a z ∧ D.kreinGraph.Adj b z) := by
    intro z hz
    refine Finset.mem_filter.mpr ⟨Finset.mem_union_left _ (Finset.mem_union_right _ hz),?_,?_⟩
    · exact (D.mem_commonTo S z).mp hz a ha
    · exact (D.mem_commonTo S z).mp hz b hb
  have h := Finset.card_le_card hsub
  rw [D.commonTo_card hcard hI] at h
  change 2 ≤ ((D.bicliqueCubicLeft S).filter
      fun z => D.kreinGraph.Adj a z ∧ D.kreinGraph.Adj b z).card
  omega


-- @@ L244-262 verbatim
theorem bicliqueCubic_right_square {S : Finset V} (hcard : S.card = 3)
    (hI : D.IndependentSet S) :
    ∃ x ∈ D.bicliqueClass S 2, ∃ y ∈ D.bicliqueClass S 2, x ≠ y ∧
      2 ≤ D.commonCount (D.bicliqueClass S 2) x y := by
  by_contra hnone
  have hno (x y : D.bicliqueClass S 2) (hxy : x ≠ y) :
      D.commonCount (D.bicliqueClass S 2) x y ≤ 1 := by
    by_contra hgt
    apply hnone
    refine ⟨x,x.property,y,y.property,?_,by omega⟩
    exact fun h => hxy (Subtype.ext h)
  have hr := D.cubic_fourth_trace_of_no_square (D.bicliqueClass S 2)
    (fun x hx => (D.bicliqueCubicRight_degrees hcard hI hx).1) hno
  obtain ⟨x,y,hxy,hc⟩ := D.bicliqueCubic_left_square hcard hI
  have hl := D.cubic_fourth_trace_gt_of_square (D.bicliqueCubicLeft S)
    (fun z hz => (D.bicliqueCubicLeft_degrees hcard hI hz).1) x y hxy hc
  rw [D.bicliqueCubic_fourth_trace hcard hI, hr, D.bicliqueCubicLeft_card hcard hI,
    (D.bicliqueClass_card hcard hI).2.2] at hl
  exact (lt_irrefl _ hl)


-- @@ L264-264 verbatim
end SRG266.QuasiSymmetric.TripleDesign57
