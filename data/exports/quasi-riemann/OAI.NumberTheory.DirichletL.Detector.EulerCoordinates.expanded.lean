import OAI.NumberTheory.DirichletL.Detector.CorrectionBounds
import OAI.NumberTheory.DirichletL.Detector.Row


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
noncomputable section

-- @@ L7-7 verbatim
namespace SevenEighths.ProbeEuler

-- @@ L8-8 verbatim
open ActualEisensteinCubic CompletedGauss

-- @@ L9-9 verbatim
local notation "O" => ActualEisensteinCubic.O


-- @@ L11-11 verbatim
def coordV (Q : ℝ) (z : ℂ) : ℂ := (Q : ℂ) ^ (-6*z)

-- @@ L12-12 verbatim
def coordR (Q : ℝ) (A x z : ℂ) : ℂ := A * (Q : ℂ) ^ (4-6*x-6*z)

-- @@ L13-13 verbatim
def coordW (Q : ℝ) (v w : ℂ) : ℂ := v * (Q : ℂ) ^ (-w)

-- @@ L14-14 verbatim
def coordD (Q : ℝ) (eta v x : ℂ) : ℂ := eta * star v * (Q : ℂ) ^ (-x)

-- @@ L15-15 verbatim
def coordK (Q : ℝ) (eta x w : ℂ) : ℂ := eta * (Q-1) * (Q : ℂ) ^ (-x-w)


-- @@ L17-23 verbatim
def unramifiedClosed (Q : ℝ) (A eta v x w z : ℂ) : ℂ :=
  let V := coordV Q z
  let R := coordR Q A x z
  let W := coordW Q v w
  let D := coordD Q eta v x
  let K := coordK Q eta x w
  ProbeLocal.continuedCorrection V W D (markedFactor R V (Q:ℂ)⁻¹ K (-D+W*R) 1)


-- @@ L25-26 verbatim
def actualAPhase (eta : HeckeFamily.Character) (p : O) : ℂ :=
  star (FiniteGaussPhase.angularFactor p) ^ 6 * HeckeFamily.elementCoeff eta p ^ 6


-- @@ L28-33 verbatim
def actualUnramifiedClosed (eta : HeckeFamily.Character) (p u : O)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (hg : ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p}) (x w z : ℂ) : ℂ :=
  unramifiedClosed (Ideal.absNorm (Ideal.span {p})) (actualAPhase eta p)
    (HeckeFamily.elementCoeff eta p)
    (actualSextic (Ideal.span {p}) hg (Ideal.Quotient.mk _ u)) x w z


-- @@ L35-40 verbatim
lemma actualAPhase_norm_le_one (eta : HeckeFamily.Character) (p : O) :
    ‖actualAPhase eta p‖ ≤ 1 := by
  simp only [actualAPhase, norm_mul, norm_pow, norm_star]
  exact (mul_le_of_le_one_left (by positivity)
    (pow_le_one₀ (norm_nonneg _) (CompletedGauss.angularFactor_norm_le_one p))).trans
    (pow_le_one₀ (norm_nonneg _) (ProbeRow.targetMonoid_norm_le_one eta p))


-- @@ L42-45 verbatim
lemma coordV_norm (Q : ℝ) (hQ : 0 < Q) (z : ℂ) :
    ‖coordV Q z‖ = Q ^ (-6*z.re) := by
  rw [coordV, Complex.norm_cpow_eq_rpow_re_of_pos hQ]
  simp


-- @@ L47-52 verbatim
lemma coordR_norm_le (Q : ℝ) (hQ : 0 < Q) (A x z : ℂ) (hA : ‖A‖ ≤ 1) :
    ‖coordR Q A x z‖ ≤ Q ^ (4-6*x.re-6*z.re) := by
  rw [coordR, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hQ]
  simp only [Complex.sub_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat,
    zero_mul, sub_zero]
  exact mul_le_of_le_one_left (Real.rpow_nonneg hQ.le _) hA


-- @@ L54-57 verbatim
lemma coordW_norm_le (Q : ℝ) (hQ : 0 < Q) (v w : ℂ) (hv : ‖v‖ ≤ 1) :
    ‖coordW Q v w‖ ≤ Q ^ (-w.re) := by
  rw [coordW, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hQ, Complex.neg_re]
  exact mul_le_of_le_one_left (Real.rpow_nonneg hQ.le _) hv


-- @@ L59-65 verbatim
lemma coordD_norm_le (Q : ℝ) (hQ : 0 < Q) (eta v x : ℂ)
    (he : ‖eta‖ ≤ 1) (hv : ‖v‖ ≤ 1) :
    ‖coordD Q eta v x‖ ≤ Q ^ (-x.re) := by
  rw [coordD, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hQ, Complex.neg_re]
  apply mul_le_of_le_one_left (Real.rpow_nonneg hQ.le _)
  rw [norm_mul, norm_star]
  exact (mul_le_of_le_one_left (norm_nonneg _) he).trans hv


-- @@ L67-79 verbatim
lemma coordK_norm_le (Q : ℝ) (hQ : 1 ≤ Q) (eta x w : ℂ) (he : ‖eta‖ ≤ 1) :
    ‖coordK Q eta x w‖ ≤ Q ^ (1-x.re-w.re) := by
  have hQ0 : 0 < Q := lt_of_lt_of_le zero_lt_one hQ
  have hsub : ‖(Q:ℂ)-1‖ = Q-1 := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr hQ)]
  rw [coordK, norm_mul, norm_mul, hsub, Complex.norm_cpow_eq_rpow_re_of_pos hQ0]
  have heq : (1-x.re-w.re) = 1 + (-x.re-w.re) := by ring
  rw [heq, Real.rpow_add hQ0, Real.rpow_one]
  simp only [Complex.sub_re, Complex.neg_re]
  gcongr
  calc ‖eta‖*(Q-1) ≤ 1*(Q-1) := mul_le_mul_of_nonneg_right he (sub_nonneg.mpr hQ)
       _ ≤ Q := by linarith


-- @@ L81-81 verbatim
end SevenEighths.ProbeEuler

-- @@ L82-82 verbatim
end


-- @@ L84-84 verbatim
end OAI
