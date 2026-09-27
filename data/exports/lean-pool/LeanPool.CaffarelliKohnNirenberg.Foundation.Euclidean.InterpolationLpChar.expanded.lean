/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Euclidean.InterpolationBasic


-- @@ L10-32 verbatim
/-!
# `L^p` membership as finiteness of a Lebesgue integral

The interpolation argument of `InterpolationBasic.lean` works throughout with
Lebesgue integrals of the `ℝ≥0∞`-valued modulus `absE f x = ENNReal.ofReal |f x|`
of a real function.  To feed its conclusions back into Mathlib's Bochner theory
one has to translate between that modulus and the `L^p` predicates `MemLp`,
`Integrable` and the integral `∫⁻ x, ‖f x‖ₑ`.

This file records the four translations needed for that purpose.  They rely on
the identity `‖r‖ₑ = ENNReal.ofReal |r|` for real `r`, which makes `absE f`
agree pointwise with `‖f ·‖ₑ`.  The results are:

* membership in `L^p` for real `p > 0` implies finiteness of
  `∫⁻ x, absE f x ^ p` (`lintegral_absE_rpow_lt_top`);
* conversely finiteness of that integral, together with a.e. strong
  measurability, gives membership in `L^p`
  (`memLp_ofReal_of_lintegral_absE_rpow_lt_top`);
* the case `p = 2`, stated separately because the exponent `2` there is a
  natural-number power (`memLp_two_of_lintegral_absE_sq_lt_top`);
* finiteness of `∫⁻ x, absE f x` is exactly Bochner integrability of `f`
  (`integrable_of_lintegral_absE_lt_top`).
-/


-- @@ L34-34 verbatim
@[expose] public section


-- @@ L36-36 verbatim
open scoped ENNReal NNReal Topology


-- @@ L38-38 verbatim
open MeasureTheory MeasureTheory.Measure Set Filter



-- @@ L41-41 verbatim
noncomputable section


-- @@ L43-43 verbatim
namespace CKN.Foundation.Euclidean


-- @@ L45-45 verbatim
open CKN.Foundation.Parabolic


-- @@ L47-53 verbatim
lemma lintegral_absE_rpow_lt_top {f : Vec3 → ℝ} {p : ℝ} (hp : 0 < p)
    (hf : MemLp f (ENNReal.ofReal p) volume) :
    ∫⁻ x, absE f x ^ p < ∞ := by
  have h := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
    (p := ENNReal.ofReal p) (f := f) (μ := volume)
    (ENNReal.ofReal_pos.mpr hp).ne' ENNReal.ofReal_ne_top hf
  simpa only [absE, Real.enorm_eq_ofReal_abs, ENNReal.toReal_ofReal hp.le] using h


-- @@ L55-62 verbatim
lemma memLp_ofReal_of_lintegral_absE_rpow_lt_top {f : Vec3 → ℝ} {p : ℝ} (hp : 0 < p)
    (hf : AEStronglyMeasurable f volume) (h : ∫⁻ x, absE f x ^ p < ∞) :
    MemLp f (ENNReal.ofReal p) volume := by
  rw [memLp_iff]
  refine (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
    (p := ENNReal.ofReal p) (f := f) (μ := volume)
    (ENNReal.ofReal_pos.mpr hp).ne' ENNReal.ofReal_ne_top hf).mpr ?_
  simpa only [absE, Real.enorm_eq_ofReal_abs, ENNReal.toReal_ofReal hp.le] using h


-- @@ L64-71 verbatim
lemma memLp_two_of_lintegral_absE_sq_lt_top {f : Vec3 → ℝ}
    (hf : AEStronglyMeasurable f volume) (h : ∫⁻ x, absE f x ^ 2 < ∞) :
    MemLp f 2 volume := by
  have h' : ∫⁻ x, absE f x ^ ((2 : ℕ) : ℝ) < ∞ := by
    simpa only [ENNReal.rpow_natCast] using h
  have h2 := memLp_ofReal_of_lintegral_absE_rpow_lt_top (f := f)
    (p := ((2 : ℕ) : ℝ)) (by norm_num) hf h'
  simpa using h2


-- @@ L73-78 verbatim
lemma integrable_of_lintegral_absE_lt_top {f : Vec3 → ℝ}
    (hf : AEStronglyMeasurable f volume) (h : ∫⁻ x, absE f x < ∞) :
    Integrable f volume := by
  refine ⟨hf, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  simpa only [absE, Real.enorm_eq_ofReal_abs] using h


-- @@ L80-80 verbatim
end CKN.Foundation.Euclidean
