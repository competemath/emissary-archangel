import OAI.NumberTheory.DirichletL.Detector.ScalarTable
import OAI.NumberTheory.DirichletL.Detector.PrimeConstants


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
noncomputable section

-- @@ L7-7 verbatim
open scoped Classical

-- @@ L8-8 verbatim
namespace SevenEighths.ProbePrimePower

-- @@ L9-9 verbatim
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge

-- @@ L10-10 verbatim
local notation "O" => ActualEisensteinCubic.O


-- @@ L12-13 verbatim
variable (p : O) (hp : Prime p) [(Ideal.span {p} : Ideal O).IsMaximal]
  (hg : goodLambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2)

-- @@ L14-14 verbatim
include hc


-- @@ L16-26 verbatim
theorem unramified_even_kzero (r m : ℕ) :
    positiveScalar p hp.ne_zero (actualSextic (Ideal.span {p}) hg) (6*r+5) 0 (6*m) =
      if r+1 ≤ m then
        (Ideal.absNorm (Ideal.span {p}):ℂ)^(6*r+5) * ((Ideal.absNorm (Ideal.span {p}):ℂ)-1)
      else 0 := by
  rw [positiveScalar_kzero, actualSextic_primePowerGauss_at_pow p hp hg hc,
    ite_eq_left (by omega : 6 ∣ 6*r+5+1)]
  by_cases hm : r+1 ≤ m
  · rw [ite_eq_left hm, ite_eq_left (by omega), ite_eq_left (by omega), pow_succ]
    ring
  · rw [ite_eq_right hm, ite_eq_right (by omega), ite_eq_right (by omega), sub_self]


-- @@ L28-36 verbatim
theorem unramified_squarefree_kzero (r m : ℕ) :
    positiveScalar p hp.ne_zero (actualSextic (Ideal.span {p}) hg) (6*r) 0 (6*m) =
      if m=r then (Ideal.absNorm (Ideal.span {p}):ℂ)^(6*r) *
        primeGauss p hp.ne_zero (actualSextic (Ideal.span {p}) hg) 1 else 0 := by
  rw [positiveScalar_kzero, actualSextic_primePowerGauss_at_pow p hp hg hc,
    ite_eq_right (by omega : ¬6 ∣ 6*r+1), actualSextic_pow_six_mul_add _ hg hc, pow_one]
  by_cases hm : m=r
  · rw [ite_eq_left hm, ite_eq_left (by omega)]
  · rw [ite_eq_right hm, ite_eq_right (by omega)]


-- @@ L38-56 verbatim
theorem unramified_squarefree_kone (r m : ℕ) :
    positiveScalar p hp.ne_zero (actualSextic (Ideal.span {p}) hg) (6*r) 1 (6*m) =
      if r<m then
        ((actualSextic (Ideal.span {p}) hg (-1))⁻¹ *
          primeGauss p hp.ne_zero (actualSextic (Ideal.span {p}) hg) 1) *
          ((Ideal.absNorm (Ideal.span {p}):ℂ)^(6*r) * ((Ideal.absNorm (Ideal.span {p}):ℂ)-1))
      else 0 := by
  rw [positiveScalar_actual_table p hp hg hc]
  rw [ite_eq_right (by decide : (1:ℕ) ≠ 0)]
  by_cases hm : r<m
  · rw [ite_eq_left ⟨rfl, by omega⟩, ite_eq_left hm, gaussValuationTable,
      ite_eq_left (by omega : 6 ∣ 6*r), ite_eq_left (by omega), ite_eq_left (by omega), pow_succ]
    ring
  · rw [ite_eq_right hm]
    by_cases hm0 : m=0
    · subst m
      rw [ite_eq_right (by omega)]
    · rw [ite_eq_left ⟨rfl, by omega⟩, gaussValuationTable,
        ite_eq_left (by omega : 6 ∣ 6*r), ite_eq_right (by omega), ite_eq_right (by omega), sub_self, mul_zero]


-- @@ L58-66 verbatim
theorem unramified_odd_zero (r m k : ℕ) (d : ℕ) (hd : d=2 ∨ d=3) :
    positiveScalar p hp.ne_zero (actualSextic (Ideal.span {p}) hg) (6*r+d) k (6*m) = 0 := by
  rw [positiveScalar_actual_table p hp hg hc]
  split_ifs with hk hk1
  · rw [gaussValuationTable, ite_eq_right (by rcases hd with rfl | rfl <;> omega),
      ite_eq_right (by rcases hd with rfl | rfl <;> omega)]
  · rw [gaussValuationTable, ite_eq_right (by rcases hd with rfl | rfl <;> omega),
      ite_eq_right (by rcases hd with rfl | rfl <;> omega), mul_zero]
  · rfl


-- @@ L68-99 verbatim
theorem unramified_even_kone (r m : ℕ) :
    positiveScalar p hp.ne_zero (actualSextic (Ideal.span {p}) hg) (6*r+5) 1 (6*m) =
      if m=r+1 then (Ideal.absNorm (Ideal.span {p}):ℂ)^(6*r+6) else 0 := by
  rw [positiveScalar_actual_table p hp hg hc, ite_eq_right (by decide : (1:ℕ) ≠ 0)]
  by_cases hm : m=r+1
  · subst m
    rw [ite_eq_left ⟨rfl, by omega⟩, ite_eq_left rfl, gaussValuationTable,
      ite_eq_right (by omega : ¬6 ∣ 6*r+5), ite_eq_left (by omega),
      actualSextic_pow_six_mul_add _ hg hc, actualSextic_fifth_inverse _ hg hc]
    have hχ : actualSextic (Ideal.span {p}) hg ≠ 1 := by
      intro h
      have hpow : actualSextic (Ideal.span {p}) hg ^ 1 = 1 := by simpa using h
      have hdiv := (actualSextic_pow_eq_one_iff _ hg hc 1).mp hpow
      norm_num at hdiv
    have hi := primeGauss_inverse_pair p hp.ne_zero (actualSextic (Ideal.span {p}) hg) hχ
    have hω : actualSextic (Ideal.span {p}) hg (-1) ≠ 0 :=
      (actualSextic (Ideal.span {p}) hg).apply_ne_zero_iff.mpr (isUnit_one.neg : IsUnit (-1 : O ⧸ Ideal.span {p}))
    calc
      _ = (Ideal.absNorm (Ideal.span {p}):ℂ)^(6*r+5) *
          ((actualSextic (Ideal.span {p}) hg (-1))⁻¹ *
            (primeGauss p hp.ne_zero (actualSextic (Ideal.span {p}) hg) 1 *
              primeGauss p hp.ne_zero (actualSextic (Ideal.span {p}) hg)⁻¹ 1)) := by ring
      _ = (Ideal.absNorm (Ideal.span {p}):ℂ)^(6*r+5) * (Ideal.absNorm (Ideal.span {p}):ℂ) := by
        rw [hi]
        field_simp
      _ = _ := (pow_succ _ (6*r+5)).symm
  · rw [ite_eq_right hm]
    by_cases hm0 : m=0
    · subst m
      rw [ite_eq_right (by omega)]
    · rw [ite_eq_left ⟨rfl, by omega⟩, gaussValuationTable,
        ite_eq_right (by omega : ¬6 ∣ 6*r+5), ite_eq_right (by omega), mul_zero]


-- @@ L101-101 verbatim
end SevenEighths.ProbePrimePower

-- @@ L102-102 verbatim
end


-- @@ L104-104 verbatim
end OAI
