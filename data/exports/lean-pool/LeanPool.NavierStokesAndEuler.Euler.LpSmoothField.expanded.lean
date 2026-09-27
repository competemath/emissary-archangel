/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import LeanPool.NavierStokesAndEuler.Euler.LpDerivativeBundling
public import LeanPool.NavierStokesAndEuler.Euler.LpTranslation
import LeanPool.NavierStokesAndEuler.Euler.LpSmoothApproximation
import LeanPool.NavierStokesAndEuler.ForMathlib.SmoothnessOrder
import Mathlib.Analysis.Calculus.ContDiff.Bounds


-- @@ L16-16 verbatim
/-! Actual all-order translation regularity from ordinary square-integrable spatial derivatives. -/


-- @@ L18-18 verbatim
@[expose] public section



-- @@ L21-21 verbatim
noncomputable section



-- @@ L24-24 verbatim
namespace EulerLpTranslation


-- @@ L26-26 verbatim
open MeasureTheory EulerSmoothLimit EulerLpDerivative Filter

-- @@ L27-27 verbatim
open scoped ContDiff Topology


-- @@ L29-29 verbatim
universe u


-- @@ L31-31 verbatim
variable {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]


-- @@ L33-44 verbatim
theorem derivativeMap_translation (D : L2Space (Space →L[ℝ] V)) (a : Space) :
    derivativeMap volume (translation a D) =
      (translation a).toContinuousLinearMap.comp (derivativeMap volume D) := by
  apply ContinuousLinearMap.ext
  intro v
  apply Lp.ext
  filter_upwards [derivativeMap_ae volume (translation a D) v, translation_ae a D,
    translation_ae a (derivativeMap volume D v),
    (measurePreserving_add_right (volume : Measure Space) a).quasiMeasurePreserving.ae
      (derivativeMap_ae volume D v)] with x hm ht hv hd
  change derivativeMap volume (translation a D) v x = translation a (derivativeMap volume D v) x
  rw [hm, ht, hv, hd]


-- @@ L46-52 verbatim
/-- The hypotheses are ordinary derivatives of a concrete smooth function, not translation-orbit
regularity. -/
structure SmoothL2Field (V : Type u) [NormedAddCommGroup V] [NormedSpace ℝ V] where
  /-- Underlying field of `SmoothL2Field`, of type `Space → V`. -/
  field : Space → V
  smooth : ContDiff ℝ ∞ field
  integrable : ∀ n : ℕ, MemLp (iteratedFDeriv ℝ n field) 2 volume


-- @@ L54-54 verbatim
namespace SmoothL2Field


-- @@ L56-58 verbatim
theorem memLp (A : SmoothL2Field V) : MemLp A.field 2 volume :=
  (A.integrable 0).congr_norm A.smooth.continuous.aestronglyMeasurable
    (Eventually.of_forall (fun _ => norm_iteratedFDeriv_zero))


-- @@ L60-61 verbatim
/-- To Lᵖ, given by `A.memLp.toLp A.field`. -/
def toLp (A : SmoothL2Field V) : L2Space V := A.memLp.toLp A.field


-- @@ L63-63 verbatim
theorem toLp_ae (A : SmoothL2Field V) : A.toLp =ᵐ[volume] A.field := A.memLp.coeFn_toLp


-- @@ L65-67 verbatim
/-- Jet Lᵖ, given by `(A.integrable n).toLp (iteratedFDeriv ℝ n A.field)`. -/
def jetLp (A : SmoothL2Field V) (n : ℕ) : L2Space (Space [×n]→L[ℝ] V) :=
  (A.integrable n).toLp (iteratedFDeriv ℝ n A.field)


-- @@ L69-76 verbatim
/-- Derivative, bundling `field`, `smooth`, `integrable`. -/
def derivative (A : SmoothL2Field V) : SmoothL2Field (Space →L[ℝ] V) where
  field := fderiv ℝ A.field
  smooth := A.smooth.fderiv_right (m := ∞) (by simp)
  integrable n := (A.integrable (n+1)).congr_norm
    ((A.smooth.fderiv_right (m := ∞) (by
        simp)).continuous_iteratedFDeriv (by simp)).aestronglyMeasurable
    (Eventually.of_forall (fun x => norm_iteratedFDeriv_fderiv.symm))


-- @@ L78-83 verbatim
theorem translation_hasFDerivAt (A : SmoothL2Field V) (a : Space) :
    HasFDerivAt (fun b : Space => translation b A.toLp)
      (derivativeMap volume (translation a A.derivative.toLp)) a := by
  rw [derivativeMap_translation]
  exact translation_hasFDerivAt_all A.toLp (derivativeMap volume A.derivative.toLp)
    (smooth_hasFDerivAt A.field A.smooth A.memLp A.derivative.memLp) a


-- @@ L85-88 verbatim
theorem translation_fderiv (A : SmoothL2Field V) :
    fderiv ℝ (fun a : Space => translation a A.toLp) =
      fun a => derivativeBundling volume (translation a A.derivative.toLp) :=
  funext (fun a => (A.translation_hasFDerivAt a).fderiv)


-- @@ L90-104 verbatim
private theorem translation_contDiff_nat_aux (n : ℕ) :
    ∀ (V : Type u) [NormedAddCommGroup V] [NormedSpace ℝ V] (A : SmoothL2Field V),
      ContDiff ℝ n (fun a : Space => translation a A.toLp) := by
  induction n with
  | zero =>
    intro V _ _ A
    exact contDiff_zero.mpr (translation_continuous A.toLp)
  | succ n ih =>
    intro V _ _ A
    rw [Nat.cast_add, Nat.cast_one, contDiff_succ_iff_fderiv]
    refine ⟨fun a => (A.translation_hasFDerivAt a).differentiableAt, by simp, ?_⟩
    rw [A.translation_fderiv]
    exact (ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := (n : WithTop ℕ∞))
      (E := L2Space (Space →L[ℝ] V)) (F := Space →L[ℝ] L2Space V)
      (derivativeBundling volume)).comp (ih (Space →L[ℝ] V) A.derivative)


-- @@ L106-110 verbatim
/-- Genuine all-order smoothness of the translation orbit follows from the ordinary spatial L² jets.
-/
theorem translation_contDiff (A : SmoothL2Field V) :
    ContDiff ℝ ∞ (fun a : Space => translation a A.toLp) :=
  contDiff_infty.mpr (fun n => translation_contDiff_nat_aux n V A)


-- @@ L112-116 verbatim
theorem norm_jetLp_zero (A : SmoothL2Field V) : ‖A.jetLp 0‖ = ‖A.toLp‖ := by
  simp only [jetLp, toLp, Lp.norm_toLp]
  congr 1
  exact eLpNorm_congr_norm_ae (A.integrable 0).aestronglyMeasurable
    A.memLp.aestronglyMeasurable (Eventually.of_forall (fun x => norm_iteratedFDeriv_zero))


-- @@ L118-124 verbatim
theorem norm_derivative_jetLp (A : SmoothL2Field V) (n : ℕ) :
    ‖A.derivative.jetLp n‖ = ‖A.jetLp (n+1)‖ := by
  simp only [jetLp, Lp.norm_toLp]
  congr 1
  exact eLpNorm_congr_norm_ae (A.derivative.integrable n).aestronglyMeasurable
    (A.integrable (n + 1)).aestronglyMeasurable
    (Eventually.of_forall (fun x => norm_iteratedFDeriv_fderiv))


-- @@ L126-142 verbatim
private theorem norm_iteratedFDeriv_translation_aux (n : ℕ) :
    ∀ (V : Type u) [NormedAddCommGroup V] [NormedSpace ℝ V] (A : SmoothL2Field V) (a : Space),
      ‖iteratedFDeriv ℝ n (fun b : Space => translation b A.toLp) a‖ ≤ ‖A.jetLp n‖ := by
  induction n with
  | zero =>
    intro V _ _ A a
    rw [norm_iteratedFDeriv_zero, (translation a).norm_map, A.norm_jetLp_zero]
  | succ n ih =>
    intro V _ _ A a
    rw [← norm_iteratedFDeriv_fderiv, A.translation_fderiv]
    have h := ContinuousLinearMap.norm_iteratedFDeriv_comp_left (𝕜 := ℝ) (E := Space)
      (F := L2Space (Space →L[ℝ] V)) (G := Space →L[ℝ] L2Space V)
      (derivativeBundling volume)
      (A.derivative.translation_contDiff.contDiffAt (x := a)) (n := n) (by simp)
    exact h.trans ((mul_le_mul_of_nonneg_right
      (derivativeBundling_norm_le_one (P := Space) (V := V) volume) (norm_nonneg _)).trans
      (by simpa only [one_mul, A.norm_derivative_jetLp n] using ih (Space →L[ℝ] V) A.derivative a))


-- @@ L144-147 verbatim
/-- Translation jets are controlled with constant one by the actual ordinary spatial L² jets. -/
theorem norm_iteratedFDeriv_translation_le (A : SmoothL2Field V) (n : ℕ) (a : Space) :
    ‖iteratedFDeriv ℝ n (fun b : Space => translation b A.toLp) a‖ ≤ ‖A.jetLp n‖ :=
  norm_iteratedFDeriv_translation_aux n V A a


-- @@ L149-149 verbatim
end SmoothL2Field


-- @@ L151-151 verbatim
end EulerLpTranslation
