/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.CompletedZeta.FunctionalEquation
public import LeanPool.Odlyzko.DedekindZeta.PrimePowerExpansion
import LeanPool.Odlyzko.CompletedZeta.RightHalfPlane
import Mathlib.Tactic.ArithMult.Init


-- @@ L13-13 verbatim
/-! TODO: Add doc-string. -/


-- @@ L15-15 verbatim
@[expose] public section


-- @@ L17-17 verbatim
noncomputable section


-- @@ L19-19 verbatim
section


-- @@ L21-21 verbatim
open Complex Ideal IsDedekindDomain NumberField.InfinitePlace


-- @@ L23-23 verbatim
namespace NumberField.Odlyzko


-- @@ L25-25 verbatim
variable (K : Type*) [Field K] [NumberField K]


-- @@ L27-29 verbatim
/-- A completed dedekind xi used in the Odlyzko-bound argument. -/
noncomputable def completedDedekindXi (s : ℂ) : ℂ :=
  s * (s - 1) * CompletedZeta.completed K s


-- @@ L31-45 verbatim
lemma completedDedekindXi_ne_zero_of_one_lt_re {s : ℂ}
    (hs : 1 < s.re) :
    completedDedekindXi K s ≠ 0 := by
  exact mul_ne_zero
    (mul_ne_zero
      (by
        intro h
        have : s.re = 0 := congrArg Complex.re h
        linarith)
      (by
        intro h
        have : s.re - 1 = 0 := by
          simpa using congrArg Complex.re h
        linarith))
    (completedDedekindZeta_ne_zero_of_one_lt_re K hs)


-- @@ L47-47 verbatim
variable [IsTotallyComplex K]


-- @@ L49-91 verbatim
theorem logDeriv_completedDedekindXi_rightHalfPlane {s : ℂ}
    (hs : 1 < s.re) :
    logDeriv (completedDedekindXi K) s =
      1 / s + 1 / (s - 1) +
        Complex.log ((|(discr K : ℝ)| : ℝ) : ℂ) / 2 +
        nrComplexPlaces K *
          (Complex.digamma s - Complex.log (2 * (Real.pi : ℂ))) -
        ∑' pe : HeightOneSpectrum (𝓞 K) × ℕ,
          primePowerLogTerm K pe.1 pe.2 s := by
  have hs0 : s ≠ 0 := by
    intro h
    subst s
    norm_num at hs
  have hs1 : s - 1 ≠ 0 := by
    intro h
    have : s.re - 1 = 0 := by
      simpa using congrArg Complex.re h
    linarith
  have hdiffS : DifferentiableAt ℂ (fun z : ℂ ↦ z) s := differentiableAt_id
  have hdiffS1 : DifferentiableAt ℂ (fun z : ℂ ↦ z - 1) s := by simp
  have hprod0 : s * (s - 1) ≠ 0 := mul_ne_zero hs0 hs1
  have hdiffCompleted :
      DifferentiableAt ℂ (CompletedZeta.completed K) s := by
    change DifferentiableAt ℂ
      (fun z ↦ CompletedZeta.discriminantFactor K z *
        CompletedZeta.archimedeanFactor K z * dedekindZeta K z) s
    exact ((differentiable_dedekindDiscriminantFactor K s).mul
      (differentiableAt_dedekindArchimedeanFactor_of_isTotallyComplex K
        (by linarith))).mul
      (differentiableAt_dedekindZeta K hs)
  change logDeriv
    (fun z : ℂ ↦ z * (z - 1) * CompletedZeta.completed K z) s = _
  rw [logDeriv_fun_mul (f := fun z : ℂ ↦ z * (z - 1))
      (g := CompletedZeta.completed K) s hprod0
      (completedDedekindZeta_ne_zero_of_one_lt_re K hs)
      (hdiffS.mul hdiffS1)
      hdiffCompleted,
    logDeriv_fun_mul (f := fun z : ℂ ↦ z) (g := fun z : ℂ ↦ z - 1)
      s hs0 hs1 hdiffS hdiffS1,
    logDeriv_apply, logDeriv_apply]
  simp only [deriv_id'', deriv_sub_const, one_div]
  rw [logDeriv_completedDedekindZeta_rightHalfPlane_eq_primePower K hs]
  ring


-- @@ L93-93 verbatim
end NumberField.Odlyzko


-- @@ L95-95 verbatim
end


-- @@ L97-97 verbatim
section


-- @@ L99-99 verbatim
open Complex Filter Ideal IsDedekindDomain NumberField NumberField.InfinitePlace

-- @@ L100-100 verbatim
open scoped Topology


-- @@ L102-102 verbatim
namespace NumberField.Odlyzko


-- @@ L104-104 verbatim
variable (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]


-- @@ L106-112 verbatim
theorem poleClearedCompletedDedekindZetaContinuation_eq_neg_finrank_mul_xi
    {s : ℂ} (hs : 1 < s.re) :
    poleClearedCompletedDedekindZetaContinuation K s =
      -(Module.finrank ℚ K : ℂ) * completedDedekindXi K s := by
  rw [poleClearedCompletedDedekindZetaContinuation_eq_completedDedekindZeta K hs,
    completedDedekindXi]
  ring


-- @@ L114-121 verbatim
theorem poleClearedCompletedDedekindZetaContinuation_ne_zero_of_one_lt_re
    {s : ℂ} (hs : 1 < s.re) :
    poleClearedCompletedDedekindZetaContinuation K s ≠ 0 := by
  rw [poleClearedCompletedDedekindZetaContinuation_eq_neg_finrank_mul_xi K hs]
  exact mul_ne_zero
    (neg_ne_zero.mpr (by
      exact_mod_cast (ne_of_gt (Module.finrank_pos (R := ℚ) (M := K)))))
    (completedDedekindXi_ne_zero_of_one_lt_re K hs)


-- @@ L123-141 verbatim
theorem logDeriv_poleClearedCompletedDedekindZetaContinuation_rightHalfPlane
    {s : ℂ} (hs : 1 < s.re) :
    logDeriv (poleClearedCompletedDedekindZetaContinuation K) s =
      logDeriv (completedDedekindXi K) s := by
  have heq :
      poleClearedCompletedDedekindZetaContinuation K =ᶠ[𝓝 s]
        fun z ↦ -(Module.finrank ℚ K : ℂ) * completedDedekindXi K z := by
    have hright :
        {z : ℂ | 1 < z.re} ∈ 𝓝 s :=
      (continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds hs
    filter_upwards [hright] with z hz
    exact
      poleClearedCompletedDedekindZetaContinuation_eq_neg_finrank_mul_xi K hz
  have hn : -(Module.finrank ℚ K : ℂ) ≠ 0 := by
    exact neg_ne_zero.mpr (by
      exact_mod_cast (ne_of_gt (Module.finrank_pos (R := ℚ) (M := K))))
  rw [logDeriv_apply, heq.deriv_eq, heq.eq_of_nhds,
    ← logDeriv_apply]
  exact logDeriv_const_mul s _ hn


-- @@ L143-153 verbatim
theorem logDeriv_poleClearedCompletedDedekindZetaContinuation_eq_primePower
    {s : ℂ} (hs : 1 < s.re) :
    logDeriv (poleClearedCompletedDedekindZetaContinuation K) s =
      1 / s + 1 / (s - 1) +
        Complex.log ((|(discr K : ℝ)| : ℝ) : ℂ) / 2 +
        nrComplexPlaces K *
          (Complex.digamma s - Complex.log (2 * (Real.pi : ℂ))) -
        ∑' pe : HeightOneSpectrum (𝓞 K) × ℕ,
          primePowerLogTerm K pe.1 pe.2 s := by
  rw [logDeriv_poleClearedCompletedDedekindZetaContinuation_rightHalfPlane K hs,
    logDeriv_completedDedekindXi_rightHalfPlane K hs]


-- @@ L155-173 verbatim
theorem deriv_poleClearedCompletedDedekindZetaContinuation_one_sub
    (s : ℂ) :
    deriv (poleClearedCompletedDedekindZetaContinuation K) (1 - s) =
      -deriv (poleClearedCompletedDedekindZetaContinuation K) s := by
  let Ξ := poleClearedCompletedDedekindZetaContinuation K
  have hΞ : Differentiable ℂ Ξ :=
    differentiable_poleClearedCompletedDedekindZetaContinuation K
  have hfun : Ξ = fun z ↦ Ξ (1 - z) := by
    funext z
    exact poleClearedCompletedDedekindZetaContinuation_functionalEquation K z
  have hcomp :
      HasDerivAt (fun z ↦ Ξ (1 - z)) (-deriv Ξ (1 - s)) s := by
    simpa only [Function.comp_def, Pi.sub_apply, id_eq, zero_sub, mul_neg,
      mul_one] using
      (hΞ.differentiableAt.hasDerivAt.comp s
        ((hasDerivAt_const s (1 : ℂ)).sub (hasDerivAt_id s)))
  have heq : deriv Ξ s = -deriv Ξ (1 - s) := by
    exact (congrArg (fun f : ℂ → ℂ ↦ deriv f s) hfun).trans hcomp.deriv
  grind


-- @@ L175-183 verbatim
theorem logDeriv_poleClearedCompletedDedekindZetaContinuation_one_sub
    {s : ℂ}
    (_hs : poleClearedCompletedDedekindZetaContinuation K s ≠ 0) :
    logDeriv (poleClearedCompletedDedekindZetaContinuation K) (1 - s) =
      -logDeriv (poleClearedCompletedDedekindZetaContinuation K) s := by
  rw [logDeriv_apply, logDeriv_apply,
    deriv_poleClearedCompletedDedekindZetaContinuation_one_sub K s]
  rw [poleClearedCompletedDedekindZetaContinuation_functionalEquation K s]
  grind


-- @@ L185-197 verbatim
theorem logDeriv_poleClearedCompletedDedekindZetaContinuation_one_sub_all
    (s : ℂ) :
    logDeriv (poleClearedCompletedDedekindZetaContinuation K) (1 - s) =
      -logDeriv (poleClearedCompletedDedekindZetaContinuation K) s := by
  by_cases hs :
      poleClearedCompletedDedekindZetaContinuation K s = 0
  · have hs' :
        poleClearedCompletedDedekindZetaContinuation K (1 - s) = 0 := by
      rw [← poleClearedCompletedDedekindZetaContinuation_functionalEquation K s]
      simp_all
    simp [logDeriv_apply, hs, hs']
  · exact
      logDeriv_poleClearedCompletedDedekindZetaContinuation_one_sub K hs


-- @@ L199-199 verbatim
end NumberField.Odlyzko


-- @@ L201-201 verbatim
end
