import OAI.Analysis.NumericalRange.DomainBound


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
section

-- @@ L6-6 verbatim
noncomputable section

-- @@ L7-7 verbatim
open Set Filter Metric Complex MeasureTheory

-- @@ L8-8 verbatim
open scoped Matrix Topology ComplexConjugate ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker

-- @@ L9-9 verbatim
namespace CompleteCrouzeix

-- @@ L10-12 verbatim
lemma polynomialValue_smul {m d : ℕ} (B : Fin (d+1) → Matrix (Fin m) (Fin m) ℂ)
    (c z : ℂ) : polynomialValue (fun k => c • B k) z = c • polynomialValue B z := by
  simp only [polynomialValue,Finset.smul_sum,smul_comm (z^_) c]

-- @@ L13-16 verbatim
lemma polynomialAt_smul {n m d : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (B : Fin (d+1) → Matrix (Fin m) (Fin m) ℂ) (c : ℂ) :
    polynomialAt A (fun k => c • B k) = c • polynomialAt A B := by
  simp only [polynomialAt,Matrix.kronecker,Matrix.kronecker_smul,Finset.smul_sum]

-- @@ L17-22 verbatim
lemma rangeMaximum_nonneg {n m d : ℕ} (hn : 0 < n)
    (A : Matrix (Fin n) (Fin n) ℂ) (B : Fin (d+1) → Matrix (Fin m) (Fin m) ℂ) :
    0 ≤ rangeMaximum A B := by
  obtain ⟨z,hz,he⟩ := rangeMaximum_attained hn A B
  rw [he]
  exact norm_nonneg _

-- @@ L23-28 verbatim
lemma norm_polynomialValue_le_rangeMaximum {n m d : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (B : Fin (d+1) → Matrix (Fin m) (Fin m) ℂ)
    {z : ℂ} (hz : z ∈ numericalRange A) : ‖polynomialValue B z‖ ≤ rangeMaximum A B := by
  apply le_csSup
  · exact ((numericalRange_compact A).image (continuous_polynomialValue B).norm).bddAbove
  · exact ⟨z,hz,rfl⟩


-- @@ L30-59 verbatim
theorem complete_crouzeix_bound {n m d : ℕ} (hn : 0 < n) (_hm : 0 < m)
    (A : Matrix (Fin n) (Fin n) ℂ) (B : Fin (d+1) → Matrix (Fin m) (Fin m) ℂ) :
    ‖polynomialAt A B‖ ≤ 2 * rangeMaximum A B := by
  let : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  apply le_of_forall_pos_le_add
  intro ε hε
  let R := rangeMaximum A B + ε/2
  have hR : 0 < R := add_pos_of_nonneg_of_pos (rangeMaximum_nonneg hn A B) (half_pos hε)
  let U : Set ℂ := {z | ‖polynomialValue B z‖ < R}
  have hU : IsOpen U := isOpen_lt (continuous_polynomialValue B).norm continuous_const
  have hKU : numericalRange A ⊆ U := by
    intro z hz
    exact (norm_polynomialValue_le_rangeMaximum A B hz).trans_lt (by dsimp [R]; linarith)
  obtain ⟨D,hW,hout⟩ := exists_admissible_neighborhood (numericalRange_compact A)
    (numericalRange_nonempty hn A) (numericalRange_convex A) hU hKU
  let B' : Fin (d+1) → Matrix (Fin m) (Fin m) ℂ := fun k => ((R⁻¹:ℝ):ℂ) • B k
  have hn' : ∀ z ∈ closure D.domain, ‖polynomialValue B' z‖ ≤ 1 := by
    intro z hz
    have hzR : ‖polynomialValue B z‖ < R := hout hz
    rw [show B' = (fun k => ((R⁻¹:ℝ):ℂ) • B k) from rfl,polynomialValue_smul,norm_smul]
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hR)]
    exact (inv_mul_le_iff₀ hR).mpr (by simpa using hzR.le)
  have hb := D.polynomial_bound_unit Finset.univ A B' (fun k => k.val) hW
    (by simpa only [polynomialValue] using hn')
  change ‖polynomialAt A B'‖ ≤ 2 at hb
  rw [show B' = (fun k => ((R⁻¹:ℝ):ℂ) • B k) from rfl,polynomialAt_smul,norm_smul,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hR)] at hb
  have hh := (inv_mul_le_iff₀ hR).mp hb
  dsimp [R] at hh
  linarith


-- @@ L61-63 verbatim
theorem main : UniversalBound 2 ∧ ∀ C : ℝ, UniversalBound C → 2 ≤ C := by
  exact ⟨fun n m d hn hm A B => complete_crouzeix_bound hn hm A B,
    fun C hC => optimal_constant hC⟩

-- @@ L64-64 verbatim
end CompleteCrouzeix


-- @@ L66-66 verbatim
end


-- @@ L68-68 verbatim
end


-- @@ L70-70 verbatim
end OAI
