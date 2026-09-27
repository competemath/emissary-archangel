/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import LeanPool.ZetaZeros.Hilbert.Defs
public import LeanPool.ZetaZeros.Zeta.Finite
public import LeanPool.ZetaZeros.Zeta.Defs
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt


-- @@ L15-28 verbatim
/-!
# The twisted functions live in `L²((-lam, lam))`

The twisted functions and their even and odd parts are square-integrable on the interval, so they
are genuine elements of the ambient Hilbert space and `Submodule.span` may be taken of them.

The bound is the only analytic content. `‖fz eta z u‖ = |eta u| · exp(2π u · im z)`, and on a
bounded interval the exponential is bounded by `exp(2π · lam · |im z|)`, so `fz` is dominated by a
constant multiple of `eta`, which is square-integrable by admissibility. Note the twist is *not*
bounded by `1` unless `z` is real — that is exactly why the interval has to be bounded.

Also here: the passage from the rescaled zeros as a `Set` to the `Finset` that
`IsConjInvariant` requires.
-/


-- @@ L30-30 verbatim
@[expose] public section


-- @@ L32-32 verbatim
namespace ZetaZeros


-- @@ L34-34 verbatim
open MeasureTheory


-- @@ L36-36 verbatim
variable {lam : ℝ} {eta : ℝ → ℝ}


-- @@ L38-43 verbatim
/-- The real part of the twist exponent is `2π u · im z`. -/
private lemma twist_exponent_re (z : ℂ) (u : ℝ) :
    (-(2 * (Real.pi : ℂ)) * Complex.I * (u : ℂ) * z).re = 2 * Real.pi * u * z.im := by
  simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.neg_re,
    Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, Complex.re_ofNat, Complex.im_ofNat]
  ring


-- @@ L45-50 verbatim
/-- The twist factor has norm `exp(2π u · im z)`; in particular it is not bounded by one unless
`z` is real. -/
private lemma norm_twist (z : ℂ) (u : ℝ) :
    ‖Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * (u : ℂ) * z)‖
      = Real.exp (2 * Real.pi * u * z.im) := by
  rw [Complex.norm_exp, twist_exponent_re]


-- @@ L52-55 verbatim
/-- The twist factor is continuous. -/
private lemma continuous_twist (z : ℂ) :
    Continuous fun u : ℝ => Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * (u : ℂ) * z) := by
  fun_prop


-- @@ L57-71 verbatim
/-- On the interval, `fz` is dominated by a constant multiple of `eta`. -/
private lemma norm_fz_le (z : ℂ) {u : ℝ} (hu : u ∈ Set.Ioo (-lam) lam) :
    ‖fz eta z u‖ ≤ Real.exp (2 * Real.pi * lam * |z.im|) * ‖eta u‖ := by
  have hu' : |u| ≤ lam := abs_le.mpr ⟨le_of_lt hu.1, le_of_lt hu.2⟩
  have hprod : u * z.im ≤ |u| * |z.im| :=
    le_trans (le_abs_self _) (le_of_eq (abs_mul u z.im))
  have hle : u * z.im ≤ lam * |z.im| :=
    le_trans hprod (mul_le_mul_of_nonneg_right hu' (abs_nonneg _))
  have hexp : 2 * Real.pi * u * z.im ≤ 2 * Real.pi * lam * |z.im| := by
    calc 2 * Real.pi * u * z.im = 2 * Real.pi * (u * z.im) := by ring
      _ ≤ 2 * Real.pi * (lam * |z.im|) :=
          mul_le_mul_of_nonneg_left hle (by positivity)
      _ = 2 * Real.pi * lam * |z.im| := by ring
  rw [fz, norm_mul, norm_twist, Complex.norm_real, mul_comm]
  exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hexp) (abs_nonneg _)


-- @@ L73-78 verbatim
/-- `fz` is measurable on the interval. -/
private lemma aestronglyMeasurable_fz (h : IsAdmissible lam eta) (z : ℂ) (s : Set ℝ) :
    AEStronglyMeasurable (fz eta z) (volume.restrict s) := by
  have he : AEStronglyMeasurable (fun u : ℝ => ((eta u : ℝ) : ℂ)) (volume.restrict s) :=
    Complex.continuous_ofReal.comp_aestronglyMeasurable (h.memLp.aestronglyMeasurable.restrict)
  exact he.mul (continuous_twist z).aestronglyMeasurable


-- @@ L80-86 verbatim
/-- **The twisted function is square-integrable on the interval.** -/
theorem memLp_fz (h : IsAdmissible lam eta) (z : ℂ) :
    MemLp (fz eta z) 2 (volume.restrict (Set.Ioo (-lam) lam)) := by
  refine MemLp.of_le_mul (c := Real.exp (2 * Real.pi * lam * |z.im|))
    ((h.memLp.restrict _)) (aestronglyMeasurable_fz h z _) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
  exact norm_fz_le z hu


-- @@ L88-94 verbatim
/-- The even part is square-integrable on the interval. -/
theorem memLp_gz (h : IsAdmissible lam eta) (z : ℂ) :
    MemLp (gz eta z) 2 (volume.restrict (Set.Ioo (-lam) lam)) := by
  have hg : gz eta z = (2 : ℂ)⁻¹ • (fz eta z + fz eta ((starRingEnd ℂ) z)) := by
    funext u; simp [gz, Pi.add_apply, smul_eq_mul]; ring
  rw [hg]
  exact ((memLp_fz h z).add (memLp_fz h ((starRingEnd ℂ) z))).const_smul _


-- @@ L96-104 verbatim
/-- The odd part is square-integrable on the interval. -/
theorem memLp_hz (h : IsAdmissible lam eta) (z : ℂ) :
    MemLp (hz eta z) 2 (volume.restrict (Set.Ioo (-lam) lam)) := by
  have hh : hz eta z = (2 * Complex.I)⁻¹ • (fz eta z - fz eta ((starRingEnd ℂ) z)) := by
    funext u
    simp only [hz, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [div_eq_inv_mul]
  rw [hh]
  exact ((memLp_fz h z).sub (memLp_fz h ((starRingEnd ℂ) z))).const_smul _


-- @@ L106-106 verbatim
/-! ## From the rescaled zeros as a set to the finite set the propositions need -/


-- @@ L108-112 verbatim
/-- The rescaled zeros as a `Finset`, which is what `IsConjInvariant` and the key
proposition take. The rescaled zeros are defined as a `Set`; finiteness of the zero set is what
bridges the two. -/
noncomputable def rescaledZerosFinset (T : ℝ) : Finset ℂ :=
  (nontrivialZeros_finite T).toFinset.image (rescale T)


-- @@ L114-117 verbatim
@[simp]
theorem coe_rescaledZerosFinset (T : ℝ) :
    ((rescaledZerosFinset T : Finset ℂ) : Set ℂ) = rescaledZeros T := by
  simp [rescaledZerosFinset, rescaledZeros, Set.Finite.coe_toFinset]


-- @@ L119-119 verbatim
end ZetaZeros
