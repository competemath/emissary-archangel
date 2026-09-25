module

public import APAP.Prereqs.FourierTransform.Discrete

import APAP.Mathlib.Algebra.Star.SelfAdjoint
import APAP.Mathlib.Basic.Complex.Basic
import APAP.Prereqs.Convolution.Discrete.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic


-- @@ L10-10 verbatim
@[expose] public noncomputable section


-- @@ L12-12 verbatim
open Finset Fintype Function MeasureTheory RCLike Real

-- @@ L13-13 verbatim
open scoped Nat Indicator


-- @@ L15-15 verbatim
variable {G : Type*} [AddCommGroup G] {s : Finset G}


-- @@ L17-18 verbatim
def energy (n : ℕ) (s : Finset G) (ν : G → ℂ) : ℝ :=
  ∑ γ ∈ piFinset fun _ : Fin n ↦ s, ∑ δ ∈ piFinset fun _ : Fin n ↦ s, ‖ν (∑ i, γ i - ∑ i, δ i)‖


-- @@ L20-22 verbatim
@[simp]
lemma energy_nonneg (n : ℕ) (s : Finset G) (ν : G → ℂ) : 0 ≤ energy n s ν := by
  unfold energy; positivity


-- @@ L24-27 verbatim
lemma energy_nsmul (m n : ℕ) (s : Finset G) (ν : G → ℂ) :
    energy n s (m • ν) = m • energy n s ν := by
  simp only [energy, nsmul_eq_mul, mul_sum, Pi.natCast_def, Pi.mul_apply, norm_mul,
    Complex.norm_natCast]


-- @@ L29-29 verbatim
@[simp] lemma energy_zero (s : Finset G) (ν : G → ℂ) : energy 0 s ν = ‖ν 0‖ := by simp [energy]


-- @@ L31-31 verbatim
variable [DecidableEq G]


-- @@ L33-33 verbatim
def boringEnergy (n : ℕ) (s : Finset G) : ℝ := energy n s trivChar


-- @@ L35-35 verbatim
@[simp] lemma boringEnergy_zero (s : Finset G) : boringEnergy 0 s = 1 := by simp [boringEnergy]


-- @@ L37-46 expanded
lemma boringEnergy_eq [Fintype G] (n : ℕ) (s : Finset G) :
    boringEnergy n s = ∑ x, (iterConv 𝟭_[(s : Set G)] n) x ^ 2 := by
  classical
  simp only [boringEnergy, energy, apply_ite norm, trivChar_apply, norm_one, norm_zero, sum_boole,
    sub_eq_zero]
  rw [← Finset.sum_fiberwise _ fun f : Fin n → G ↦ ∑ i, f i]
  congr with x
  rw [indicator_one_iterConv_apply, sq, ← nsmul_eq_mul, ← sum_const]
  congr! 4 with f hf
  simp_rw [(mem_filter.1 hf).2, eq_comm]


-- @@ L48-49 verbatim
@[simp] lemma boringEnergy_one [Finite G] (s : Finset G) : boringEnergy 1 s = #s := by
  cases nonempty_fintype G; simp [boringEnergy_eq, Set.indicator_apply]


-- @@ L51-51 verbatim
variable [Fintype G]


-- @@ L53-68 expanded
lemma cLpNorm_dft_indicator_one_pow [MeasurableSpace G] [DiscreteMeasurableSpace G] (n : ℕ)
    (s : Finset G) : cLpNorm (↑(2 * n)) (dft 𝟭_[(s : Set G)]) ^ (2 * n) = boringEnergy n s :=
  by
  obtain rfl | hn := n.eq_zero_or_pos
  · simp
  refine Complex.ofReal_injective ?_
  calc
    _ = ⟪dft (iterConv 𝟭_[(s : Set G)] n), dft (iterConv 𝟭_[s] n)⟫ₙ_[ℂ] := ?_
    _ = ⟪iterConv 𝟭_[(s : Set G), ℂ] n, iterConv 𝟭_[s] n⟫_[ℂ] := (wInner_cWeight_dft _ _)
    _ = _ := ?_
  · rw [cLpNorm_pow_eq_expect_norm (by positivity)]
    simp_rw [pow_mul', ← norm_pow _ n, Complex.ofReal_expect, Complex.ofReal_pow, ←
      Complex.conj_mul', wInner_cWeight_eq_expect, inner_apply', dft_iterConv_apply]
  ·
    simp only [wInner_one_eq_sum, RCLike.inner_apply, boringEnergy_eq, Complex.ofReal_mul,
      Complex.ofReal_sum, sq, Complex.ofReal_iterConv,
      (((isSelfAdjoint_indicator_one _).iterConv _).apply _).conj_eq,
      Complex.ofReal_comp_indicator_one]


-- @@ L70-75 expanded
omit [DecidableEq G] in
lemma cL2Norm_dft_indicator_one [MeasurableSpace G] [DiscreteMeasurableSpace G] (s : Finset G) :
    cLpNorm 2 (dft 𝟭_[(s : Set G)]) = sqrt #s := by
  classical
  rw [eq_comm, sqrt_eq_iff_eq_sq (by positivity) (by positivity), eq_comm]
  simpa using cLpNorm_dft_indicator_one_pow 1 s

