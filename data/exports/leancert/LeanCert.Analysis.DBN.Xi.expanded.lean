import Mathlib.NumberTheory.LSeries.Dirichlet


-- @@ L3-14 verbatim
/-!
# Pole-safe xi and its initial zero strip

The entire definition uses Mathlib's pole-subtracted completed zeta, rather
than multiplying its totalized meromorphic values at 0 and 1. This agrees
definitionally with the downstream `Complex.riemannXi` definition, without
importing that project or its analytic placeholders.

`xiModel` has the DBN normalization and all its zeros lie in `|Im z| ≤ 1`.
This file does not depend on the heat-flow integral `H 0`.
The exact identification is proved separately in `XiIdentity.lean`.
-/


-- @@ L16-16 verbatim
namespace LeanCert.Analysis.DBN

-- @@ L17-17 verbatim
open Complex


-- @@ L19-21 verbatim
/-- The entire Riemann xi function, including its removable singularities. -/
noncomputable def riemannXi (s : ℂ) : ℂ :=
  (s * (s - 1) * completedRiemannZeta₀ s + 1) / 2


-- @@ L23-24 verbatim
@[simp] theorem riemannXi_zero : riemannXi 0 = 1 / 2 := by
  simp [riemannXi]


-- @@ L26-27 verbatim
@[simp] theorem riemannXi_one : riemannXi 1 = 1 / 2 := by
  simp [riemannXi]


-- @@ L29-31 verbatim
theorem riemannXi_entire : Differentiable ℂ riemannXi := by
  exact (((differentiable_id.mul (differentiable_id.sub (differentiable_const (1 : ℂ)))).mul
    differentiable_completedZeta₀).add (differentiable_const (1 : ℂ))).div_const 2


-- @@ L33-38 verbatim
theorem riemannXi_eq_mul_completed {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    riemannXi s = s * (s - 1) * completedRiemannZeta s / 2 := by
  rw [riemannXi, completedRiemannZeta_eq]
  have h : 1 - s ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  field_simp [h0, h]
  ring


-- @@ L40-42 verbatim
theorem riemannXi_one_sub (s : ℂ) : riemannXi (1 - s) = riemannXi s := by
  simp only [riemannXi, completedRiemannZeta₀_one_sub]
  ring


-- @@ L44-54 verbatim
theorem riemannXi_ne_zero_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    riemannXi s ≠ 0 := by
  have h0 : s ≠ 0 := by intro h; norm_num [h] at hs
  have h1 : s ≠ 1 := by intro h; simp [h] at hs
  have hζ := riemannZeta_ne_zero_of_one_lt_re hs
  rw [riemannZeta_def_of_ne_zero h0] at hζ
  have hc : completedRiemannZeta s ≠ 0 := by
    intro h
    exact hζ (by simp [h])
  rw [riemannXi_eq_mul_completed h0 h1]
  exact div_ne_zero (mul_ne_zero (mul_ne_zero h0 (sub_ne_zero.mpr h1)) hc) (by norm_num)


-- @@ L56-61 verbatim
theorem riemannXi_ne_zero_of_re_lt_zero {s : ℂ} (hs : s.re < 0) :
    riemannXi s ≠ 0 := by
  rw [← riemannXi_one_sub s]
  apply riemannXi_ne_zero_of_one_lt_re
  simp only [sub_re, one_re]
  linarith


-- @@ L63-70 verbatim
/-- No numerical RH verification is needed for the closed critical strip. -/
theorem riemannXi_zero_strip {s : ℂ} (hs : riemannXi s = 0) :
    0 ≤ s.re ∧ s.re ≤ 1 := by
  constructor
  · by_contra h
    exact riemannXi_ne_zero_of_re_lt_zero (lt_of_not_ge h) hs
  · by_contra h
    exact riemannXi_ne_zero_of_one_lt_re (lt_of_not_ge h) hs


-- @@ L72-74 verbatim
/-- The xi-side expression in the DBN identity; not a redefinition of `H`. -/
noncomputable def xiModel (z : ℂ) : ℂ :=
  riemannXi (1 / 2 + I * z / 2) / 8


-- @@ L76-79 verbatim
theorem xiModel_entire : Differentiable ℂ xiModel := by
  exact (riemannXi_entire.comp
    (differentiable_const _ |>.add
      ((differentiable_const _ |>.mul differentiable_id).div_const 2))).div_const 8


-- @@ L81-84 verbatim
theorem xiModel_even (z : ℂ) : xiModel (-z) = xiModel z := by
  unfold xiModel
  rw [show (1 / 2 + I * -z / 2 : ℂ) = 1 - (1 / 2 + I * z / 2) by ring,
    riemannXi_one_sub]


-- @@ L86-96 verbatim
/-- The normalized xi model has no zeros outside the initial DBN strip. -/
theorem xiModel_zero_strip {z : ℂ} (hz : xiModel z = 0) : |z.im| ≤ 1 := by
  have hx : riemannXi (1 / 2 + I * z / 2) = 0 := by
    simpa [xiModel, div_eq_zero_iff] using hz
  have hs := riemannXi_zero_strip hx
  have hre : (1 / 2 + I * z / 2 : ℂ).re = (1 - z.im) / 2 := by
    simp [Complex.div_ofNat_re, mul_re]
    ring
  rw [hre] at hs
  rw [abs_le]
  constructor <;> linarith [hs.1, hs.2]


-- @@ L98-99 verbatim
theorem xiModel_ne_zero_of_one_lt_abs_im {z : ℂ} (hz : 1 < |z.im|) :
    xiModel z ≠ 0 := fun h => (not_le_of_gt hz) (xiModel_zero_strip h)


-- @@ L101-101 verbatim
end LeanCert.Analysis.DBN
