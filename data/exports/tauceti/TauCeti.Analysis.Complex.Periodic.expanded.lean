/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.Analysis.Complex.Periodic
public import Mathlib.RingTheory.RootsOfUnity.Complex


-- @@ L12-38 verbatim
/-!
# The local parameter under translation, period rescaling, and differentiation

Identities for the local parameter `𝕢 h z = exp (2 π I z / h)` at a cusp: translating
the argument multiplies by an exponential, the `m`-th power of the local parameter at
period `m * h` is the local parameter at period `h`, the values at the integer offsets
`b < p` satisfy the roots-of-unity orthogonality relation, the parameter differentiates to
itself times `2πi/h`, and the logarithmic derivative of any periodic function of
nonzero width `h` factors through its cusp function along the parameter.

## Main declarations

* `TauCeti.Periodic.qParam_sub`: `𝕢 h (z - j) = 𝕢 h z * exp (-2 π I j / h)`.
* `TauCeti.Periodic.qParam_nat_mul_pow`: `𝕢 (m * h) z ^ m = 𝕢 h z` for `m ≠ 0`.
* `TauCeti.Periodic.sum_qParam_natCast_pow`: the roots-of-unity orthogonality relation
  `∑_{b < p} 𝕢 p b ^ m = if p ∣ m then p else 0`.
* `TauCeti.Periodic.hasDerivAt_qParam` (with `deriv_qParam`): the `q`-parameter
  differentiates to itself times `2πi/h`.
* `TauCeti.Periodic.logDeriv_eq_logDeriv_cuspFunction_mul_deriv_qParam`: the chain rule
  for the logarithmic derivative of a periodic function of nonzero width through its
  cusp function.

## References

* [Mathlib PR #39083](https://github.com/leanprover-community/mathlib4/pull/39083)
  (Chris Birkbeck) — the upstream draft this file ports onto the current Mathlib pin.
-/


-- @@ L40-40 verbatim
public section


-- @@ L42-42 verbatim
open Complex

-- @@ L43-43 verbatim
open scoped Real


-- @@ L45-45 verbatim
namespace TauCeti.Periodic


-- @@ L47-47 verbatim
open Function.Periodic


-- @@ L49-49 verbatim
local notation "𝕢" => Function.Periodic.qParam


-- @@ L51-51 verbatim
variable {h : ℝ}


-- @@ L53-57 verbatim
/-- Translation by `j` in the argument of `qParam` corresponds to multiplication by
`exp (-2 π I j / h)`. -/
theorem qParam_sub (z j : ℂ) : 𝕢 h (z - j) = 𝕢 h z * exp (-2 * π * I * j / h) := by
  simp only [qParam, ← Complex.exp_add]
  ring_nf


-- @@ L59-63 verbatim
/-- The `m`-th power of the local parameter at period `m * h` is the local parameter at
period `h`. -/
theorem qParam_nat_mul_pow {m : ℕ} (hm : m ≠ 0) (z : ℂ) : 𝕢 (m * h) z ^ m = 𝕢 h z := by
  simp only [qParam, ← Complex.exp_nat_mul, ofReal_mul, ofReal_natCast]
  rw [mul_div_assoc', mul_div_mul_left _ _ (Nat.cast_ne_zero.mpr hm)]


-- @@ L65-91 verbatim
/-- **Orthogonality of the `p`-th roots of unity**, in the local-parameter spelling: the
values `𝕢 p b = exp (2 π I b / p)` at the integer offsets `b < p` are the `p`-th roots of
unity, so summing their `m`-th powers gives `p` when `p ∣ m` and `0` otherwise.

This is the identity that makes a sum over the offsets `b < p` of a translated
`q`-expansion pick out the coefficients in the arithmetic progression `p ℕ`. -/
theorem sum_qParam_natCast_pow {p : ℕ} (m : ℕ) :
    ∑ b ∈ Finset.range p, 𝕢 (p : ℝ) (b : ℂ) ^ m = if p ∣ m then (p : ℂ) else 0 := by
  rcases eq_or_ne p 0 with rfl | hp
  · simp
  -- Every value `𝕢 p b` is a power of the primitive root `ζ = 𝕢 p 1`, so the sum is geometric
  -- in `ζ ^ m`.
  have hζ : IsPrimitiveRoot (𝕢 (p : ℝ) 1) p := by
    have hqe : 𝕢 (p : ℝ) 1 = Complex.exp (2 * π * I / p) := by
      rw [qParam, mul_one, Complex.ofReal_natCast]
    rw [hqe]
    exact Complex.isPrimitiveRoot_exp p hp
  have hterm : ∀ b ∈ Finset.range p, 𝕢 (p : ℝ) (b : ℂ) ^ m = (𝕢 (p : ℝ) 1 ^ m) ^ b := by
    intro b _
    simp only [qParam, ← Complex.exp_nat_mul]
    ring_nf
  rw [Finset.sum_congr rfl hterm]
  split_ifs with hd
  · rw [(hζ.pow_eq_one_iff_dvd m).mpr hd]
    simp
  · rw [geom_sum_eq (fun hone ↦ hd ((hζ.pow_eq_one_iff_dvd m).mp hone)),
      ← pow_mul, mul_comm m p, pow_mul, hζ.pow_eq_one, one_pow, sub_self, zero_div]


-- @@ L93-99 verbatim
/-- The `q`-parameter differentiates to itself times `2πi/h`. For `h = 0` the parameter
is the constant `1`, whose derivative is genuinely `0` — the value the division junk
`2πi/0 = 0` also produces — so the statement is unconditional. -/
theorem hasDerivAt_qParam (h : ℝ) (z : ℂ) :
    HasDerivAt (𝕢 h) (𝕢 h z * (2 * π * I / h)) z := by
  simpa only [Function.Periodic.qParam, id_eq, mul_one] using!
    (((hasDerivAt_id z).const_mul (2 * (π : ℂ) * I)).div_const h).cexp


-- @@ L101-104 verbatim
/-- The derivative of the `q`-parameter, in rewrite form. -/
@[simp]
theorem deriv_qParam (h : ℝ) (z : ℂ) : deriv (𝕢 h) z = 𝕢 h z * (2 * π * I / h) :=
  (hasDerivAt_qParam h z).deriv


-- @@ L106-126 verbatim
/-- The chain rule for the logarithmic derivative of a periodic function through its
cusp function: `logDeriv g` factors through `logDeriv (cuspFunction h g)` along the
`q`-parameter, for nonzero width `h`. The statement needs no differentiability: where
`g` is not
differentiable, neither is the cusp function at `𝕢 h z` — the composition
`cuspFunction h g ∘ 𝕢 h` is `g` — so both logarithmic derivatives take the junk
value `0`. -/
theorem logDeriv_eq_logDeriv_cuspFunction_mul_deriv_qParam {g : ℂ → ℂ} (hh : h ≠ 0)
    (hg : Function.Periodic g h) (z : ℂ) :
    logDeriv g z = logDeriv (cuspFunction h g) (𝕢 h z) * deriv (𝕢 h) z := by
  have hfun : g = fun w ↦ cuspFunction h g (𝕢 h w) :=
    funext fun w ↦ (eq_cuspFunction hh hg w).symm
  rcases em (DifferentiableAt ℂ g z) with hd | hd
  · conv_lhs => rw [hfun]
    exact logDeriv_comp (differentiableAt_cuspFunction hh hg hd)
      (hasDerivAt_qParam h z).differentiableAt
  · have hnc : ¬DifferentiableAt ℂ (cuspFunction h g) (𝕢 h z) := fun hc ↦ hd <| by
      rw [hfun]
      exact hc.comp z (hasDerivAt_qParam h z).differentiableAt
    rw [logDeriv_eq_zero_of_not_differentiableAt _ _ hd,
      logDeriv_eq_zero_of_not_differentiableAt _ _ hnc, zero_mul]


-- @@ L128-128 verbatim
end TauCeti.Periodic


-- @@ L130-130 verbatim
end
