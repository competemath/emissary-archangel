import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Trace


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
open scoped BigOperators ComplexConjugate


-- @@ L8-8 verbatim
namespace LeanBlast.GotsmanLinial


-- @@ L10-10 verbatim
variable {ι κ : Type*} [Fintype ι] [Fintype κ]


-- @@ L12-15 verbatim
/-- The Hilbert--Schmidt norm squared for the counting inner product.
This explicit entry sum does not use any norm instance on matrices. -/
noncomputable def hsNormSq (A : Matrix ι κ ℂ) : ℝ :=
  ∑ i, ∑ j, ‖A i j‖ ^ 2


-- @@ L17-18 verbatim
theorem hsNormSq_nonneg (A : Matrix ι κ ℂ) : 0 ≤ hsNormSq A := by
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _


-- @@ L20-21 verbatim
@[simp] theorem hsNormSq_zero : hsNormSq (0 : Matrix ι κ ℂ) = 0 := by
  simp [hsNormSq]


-- @@ L23-25 verbatim
theorem hsNormSq_smul (c : ℂ) (A : Matrix ι κ ℂ) :
    hsNormSq (c • A) = ‖c‖ ^ 2 * hsNormSq A := by
  simp [hsNormSq, mul_pow, Finset.mul_sum]


-- @@ L27-30 verbatim
theorem hsNormSq_real_smul (c : ℝ) (A : Matrix ι κ ℂ) :
    hsNormSq ((c : ℂ) • A) = c ^ 2 * hsNormSq A := by
  rw [hsNormSq_smul]
  simp


-- @@ L32-35 verbatim
@[simp] theorem hsNormSq_conjTranspose (A : Matrix ι κ ℂ) :
    hsNormSq A.conjTranspose = hsNormSq A := by
  simp only [hsNormSq, Matrix.conjTranspose_apply, norm_star]
  exact Finset.sum_comm


-- @@ L37-38 verbatim
theorem ofReal_sq_norm (z : ℂ) : (↑(‖z‖ ^ 2) : ℂ) = star z * z := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self, Complex.star_def]


-- @@ L40-42 verbatim
private theorem ofReal_fintype_sum (f : ι → ℝ) :
    (↑(∑ i, f i) : ℂ) = ∑ i, (f i : ℂ) :=
  map_sum Complex.ofRealHom f Finset.univ


-- @@ L44-49 verbatim
omit [Fintype κ] in
theorem ofReal_sum_sq_norm_column (A : Matrix ι κ ℂ) (j : κ) :
    (↑(∑ i, ‖A i j‖ ^ 2) : ℂ) = (A.conjTranspose * A) j j := by
  rw [ofReal_fintype_sum]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
  exact Finset.sum_congr rfl fun i _ => ofReal_sq_norm _


-- @@ L51-56 verbatim
theorem ofReal_hsNormSq (A : Matrix ι κ ℂ) :
    (hsNormSq A : ℂ) = Matrix.trace (A.conjTranspose * A) := by
  rw [hsNormSq, Finset.sum_comm]
  rw [ofReal_fintype_sum]
  simp only [Matrix.trace, Matrix.diag_apply]
  exact Finset.sum_congr rfl fun j _ => ofReal_sum_sq_norm_column A j


-- @@ L58-60 verbatim
theorem hsNormSq_eq_re_trace (A : Matrix ι κ ℂ) :
    hsNormSq A = (Matrix.trace (A.conjTranspose * A)).re := by
  exact congrArg Complex.re (ofReal_hsNormSq A)


-- @@ L62-64 verbatim
theorem hsNormSq_eq_sum_columns (A : Matrix ι κ ℂ) :
    hsNormSq A = ∑ j, ∑ i, ‖A i j‖ ^ 2 := by
  exact Finset.sum_comm


-- @@ L66-69 verbatim
omit [Fintype κ] in
theorem sum_sq_norm_column_eq_re (A : Matrix ι κ ℂ) (j : κ) :
    ∑ i, ‖A i j‖ ^ 2 = ((A.conjTranspose * A) j j).re := by
  exact congrArg Complex.re (ofReal_sum_sq_norm_column A j)


-- @@ L71-80 verbatim
theorem hsNormSq_mul_left_of_unitary [DecidableEq ι]
    (U : Matrix ι ι ℂ) (A : Matrix ι κ ℂ) (hU : U.conjTranspose * U = 1) :
    hsNormSq (U * A) = hsNormSq A := by
  rw [hsNormSq_eq_re_trace, hsNormSq_eq_re_trace]
  congr 2
  calc
    (U * A).conjTranspose * (U * A) = A.conjTranspose *
        (U.conjTranspose * U) * A := by
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = A.conjTranspose * A := by rw [hU, Matrix.mul_one]


-- @@ L82-88 verbatim
theorem hsNormSq_mul_right_of_unitary [DecidableEq κ]
    (A : Matrix ι κ ℂ) (U : Matrix κ κ ℂ) (hU : U * U.conjTranspose = 1) :
    hsNormSq (A * U) = hsNormSq A := by
  rw [← hsNormSq_conjTranspose (A * U), Matrix.conjTranspose_mul]
  rw [hsNormSq_mul_left_of_unitary U.conjTranspose A.conjTranspose]
  · exact hsNormSq_conjTranspose A
  · simpa using hU


-- @@ L90-92 verbatim
@[simp] theorem hsNormSq_diagonal [DecidableEq ι] (d : ι → ℂ) :
    hsNormSq (Matrix.diagonal d) = ∑ i, ‖d i‖ ^ 2 := by
  simp [hsNormSq, Matrix.diagonal_apply, apply_ite]


-- @@ L94-97 verbatim
@[simp] theorem hsNormSq_one [DecidableEq ι] :
    hsNormSq (1 : Matrix ι ι ℂ) = Fintype.card ι := by
  rw [hsNormSq_eq_re_trace]
  simp


-- @@ L99-102 verbatim
theorem hsNormSq_of_unitary [DecidableEq ι] (U : Matrix ι ι ℂ)
    (hU : U.conjTranspose * U = 1) : hsNormSq U = Fintype.card ι := by
  rw [hsNormSq_eq_re_trace, hU]
  simp


-- @@ L104-107 verbatim
theorem hsNormSq_diagonal_of_norm_one [DecidableEq ι] (d : ι → ℂ)
    (hd : ∀ i, ‖d i‖ = 1) :
    hsNormSq (Matrix.diagonal d) = Fintype.card ι := by
  simp [hsNormSq_diagonal, hd]


-- @@ L109-112 verbatim
theorem hsNormSq_projection (P : Matrix ι ι ℂ)
    (hself : P.conjTranspose = P) (hidem : P * P = P) :
    hsNormSq P = (Matrix.trace P).re := by
  rw [hsNormSq_eq_re_trace, hself, hidem]


-- @@ L114-118 verbatim
theorem sum_sq_norm_column_of_unitary [DecidableEq ι]
    (U : Matrix ι ι ℂ) (hU : U.conjTranspose * U = 1) (j : ι) :
    ∑ i, ‖U i j‖ ^ 2 = 1 := by
  rw [sum_sq_norm_column_eq_re, hU]
  simp


-- @@ L120-124 verbatim
theorem sq_norm_entry_le_one_of_unitary [DecidableEq ι]
    (U : Matrix ι ι ℂ) (hU : U.conjTranspose * U = 1) (i j : ι) :
    ‖U i j‖ ^ 2 ≤ 1 := by
  rw [← sum_sq_norm_column_of_unitary U hU j]
  exact Finset.single_le_sum (fun k _ => sq_nonneg ‖U k j‖) (Finset.mem_univ i)


-- @@ L126-126 verbatim
end LeanBlast.GotsmanLinial


-- @@ L128-128 verbatim
end OAI
