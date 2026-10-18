import LeanCert.Analysis.DBN.BadTime


-- @@ L3-9 verbatim
/-!
# The de Bruijn–Newman threshold

The actual real-zero time set is nonempty, closed, upward closed, and bounded
below. Its infimum is therefore an attained finite threshold, at most one half.
This is a qualitative classical certificate, not a sharper numerical bound.
-/

-- @@ L10-10 verbatim
namespace LeanCert.Analysis.DBN

-- @@ L11-11 verbatim
open Set


-- @@ L13-14 verbatim
/-- The real-valued de Bruijn–Newman constant for the normalization of `H`. -/
noncomputable def Lambda : ℝ := sInf realZeroTimes


-- @@ L16-17 verbatim
theorem Lambda_isLeast : IsLeast realZeroTimes Lambda :=
  realZeroTimes_isLeast_sInf realZeroTimes_bddBelow


-- @@ L19-20 verbatim
theorem Lambda_le_half : Lambda ≤ (1/2 : ℝ) :=
  realZeroTimes_sInf_le_half realZeroTimes_bddBelow


-- @@ L22-27 verbatim
/-- Exact threshold characterization for the actual heat integral. -/
theorem real_zeros_iff_Lambda_le (t : ℝ) :
    (∀ z : ℂ, H t z = 0 → z.im = 0) ↔ Lambda ≤ t := by
  change t ∈ realZeroTimes ↔ _
  rw [realZeroTimes_eq_Ici realZeroTimes_bddBelow realZeroTimes_forward]
  rfl


-- @@ L29-30 verbatim
theorem H_Lambda_real_zeros (z : ℂ) (hz : H Lambda z = 0) : z.im = 0 :=
  Lambda_isLeast.1 z hz


-- @@ L32-37 verbatim
theorem nonreal_zero_of_lt_Lambda {t : ℝ} (ht : t < Lambda) :
    ∃ z : ℂ, H t z = 0 ∧ z.im ≠ 0 := by
  have h : ¬ ∀ z : ℂ, H t z = 0 → z.im = 0 :=
    fun h => (not_le.mpr ht) ((real_zeros_iff_Lambda_le t).mp h)
  push Not at h
  exact h


-- @@ L39-44 verbatim
/-- The threshold is uniquely determined by its zero characterization. -/
theorem Lambda_unique {a : ℝ}
    (ha : ∀ t : ℝ, (∀ z : ℂ, H t z = 0 → z.im = 0) ↔ a ≤ t) : a = Lambda := by
  apply le_antisymm
  · exact (ha Lambda).mp Lambda_isLeast.1
  · exact (real_zeros_iff_Lambda_le a).mp ((ha a).mpr le_rfl)


-- @@ L46-51 verbatim
/-- Unconditional classical DBN certificate: a finite threshold, the exact
real-zero equivalence, and the one-half upper bound. -/
theorem dbn_certificate :
    ∃ a : ℝ, a ≤ (1/2 : ℝ) ∧
      ∀ t : ℝ, (∀ z : ℂ, H t z = 0 → z.im = 0) ↔ a ≤ t :=
  ⟨Lambda, Lambda_le_half, real_zeros_iff_Lambda_le⟩


-- @@ L53-53 verbatim
end LeanCert.Analysis.DBN
