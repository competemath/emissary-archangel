/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.Foundations.PressureSpatialRegularity
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.MeasureTheory.Measure.Haar.Unique


-- @@ L14-14 verbatim
/-! The actual joint spatial and angular reflection on cylinder L² fields. -/


-- @@ L16-16 verbatim
@[expose] public section



-- @@ L19-19 verbatim
noncomputable section


-- @@ L21-21 verbatim
namespace EulerCylinderReflection


-- @@ L23-23 verbatim
open MeasureTheory EulerLiftedGradientSpace EulerPressureSpatialRegularity

-- @@ L24-24 verbatim
open scoped Topology ContDiff


-- @@ L26-26 verbatim
variable (period : ℝ) [Fact (0 < period)]


-- @@ L28-33 verbatim
/-- Joint negation of the spatial and periodic coordinates preserves cylinder measure. -/
theorem measurePreserving_reflection :
    MeasurePreserving (fun x : LiftDomain period => -x) (liftMeasure period) (liftMeasure period)
        := by
  exact (Measure.measurePreserving_neg (volume : Measure Vector3)).prod
    (Measure.measurePreserving_neg (volume : Measure (AddCircle period)))


-- @@ L35-38 verbatim
/-- Pullback by joint spatial and angular reflection, as an actual L² isometry. -/
def reflection : LiftL2 period →ₗᵢ[ℝ] LiftL2 period :=
  Lp.compMeasurePreservingₗᵢ ℝ (fun x : LiftDomain period => -x) (measurePreserving_reflection
      period)


-- @@ L40-43 verbatim
/-- The L² reflection is represented by literal composition with negation. -/
theorem reflection_ae (f : LiftL2 period) :
    reflection period f =ᵐ[liftMeasure period] fun x => f (-x) :=
  Lp.coeFn_compMeasurePreserving f (measurePreserving_reflection period)


-- @@ L45-52 verbatim
/-- Reflecting twice is the identity on the actual L² field. -/
@[simp] theorem reflection_involutive (f : LiftL2 period) :
    reflection period (reflection period f) = f := by
  apply Lp.ext
  filter_upwards [reflection_ae period (reflection period f),
    (measurePreserving_reflection period).quasiMeasurePreserving.ae (reflection_ae period f)] with
        x hx hy
  rw [hx, hy, neg_neg]


-- @@ L54-56 verbatim
/-- Reflection preserves the actual L² norm. -/
theorem reflection_norm (f : LiftL2 period) : ‖reflection period f‖ = ‖f‖ :=
  (reflection period).norm_map f


-- @@ L58-69 verbatim
/-- Reflection reverses translations in every spatial or angular direction. -/
theorem reflection_translation (a : LiftDomain period) (f : LiftL2 period) :
    reflection period (translation period a f) = translation period (-a) (reflection period f) := by
  apply Lp.ext
  filter_upwards [reflection_ae period (translation period a f),
    (measurePreserving_reflection period).quasiMeasurePreserving.ae (translation_ae period a f),
    translation_ae period (-a) (reflection period f),
    (measurePreserving_translation period (-a)).quasiMeasurePreserving.ae (reflection_ae period f)]
    with x h1 h2 h3 h4
  rw [h1, h2, h3, h4]
  congr 1
  abel


-- @@ L71-75 verbatim
omit [Fact (0 < period)] in
/-- Negating a translation parameter negates its point on the cylinder. -/
@[simp] theorem translationPath_neg (a : LiftTangent) (t : ℝ) :
    translationPath period a (-t) = -translationPath period a t := by
  simp [translationPath, coveringMap, neg_smul]


-- @@ L77-92 verbatim
/-- Strong translation derivatives reverse sign under actual reflection. -/
theorem reflection_hasDerivAt (a : LiftTangent) {f g : LiftL2 period}
    (h : HasDerivAt (fun t => translation period (translationPath period a t) f) g 0) :
    HasDerivAt (fun t => translation period (translationPath period a t) (reflection period f))
      (-reflection period g) 0 := by
  have h0 : HasDerivAt (fun t => translation period (translationPath period a t) f) g ((-id) (0 :
      ℝ)) := by
    simpa using h
  have hn := h0.scomp 0 ((hasDerivAt_id (0 : ℝ)).neg)
  have hr := (reflection period).toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt 0 hn
  convert! hr using 1
  · funext t
    change translation period (translationPath period a t) (reflection period f) =
      reflection period (translation period (translationPath period a (-t)) f)
    rw [reflection_translation, translationPath_neg, neg_neg]
  · simp


-- @@ L94-95 verbatim
/-- A scalar test pulled back by joint negation. -/
def reflectedTest (φ : LiftDomain period → ℝ) : LiftDomain period → ℝ := fun x => φ (-x)


-- @@ L97-102 verbatim
omit [Fact (0 < period)] in
/-- In covering coordinates reflection is exactly negation of the increment. -/
theorem localLift_reflected (φ : LiftDomain period → ℝ) (x : LiftDomain period) :
    localLift period (reflectedTest period φ) x = fun h => localLift period φ (-x) (-h) := by
  funext h
  simp [localLift, reflectedTest, neg_add_rev, add_comm]


-- @@ L104-112 verbatim
omit [Fact (0 < period)] in
/-- Reflection preserves the class of smooth compact scalar tests. -/
theorem smoothCompactTest_reflected (φ : LiftDomain period → ℝ)
    (hφ : HasCompactSupport φ ∧ ∀ x, ContDiff ℝ ∞ (localLift period φ x)) :
    HasCompactSupport (reflectedTest period φ) ∧
      ∀ x, ContDiff ℝ ∞ (localLift period (reflectedTest period φ) x) := by
  refine ⟨hφ.1.comp_homeomorph (Homeomorph.neg _), fun x => ?_⟩
  rw [localLift_reflected]
  exact (hφ.2 (-x)).comp contDiff_id.neg


-- @@ L114-129 verbatim
omit [Fact (0 < period)] in
/-- The actual lifted gradient reverses parity under joint reflection. -/
theorem liftedGradient_reflected (κ : ℝ) (m : Vector3) (φ : LiftDomain period → ℝ)
    (hφ : ∀ x, ContDiff ℝ ∞ (localLift period φ x)) (x : LiftDomain period) :
    liftedGradient period κ m (reflectedTest period φ) x = -liftedGradient period κ m φ (-x) := by
  have hd := ((hφ (-x)).differentiable (by simp) (0 : LiftTangent)).hasFDerivAt
  have hn := (hasFDerivAt_id (𝕜 := ℝ) (0 : LiftTangent)).neg
  have hd0 : HasFDerivAt (localLift period φ (-x)) (fderiv ℝ (localLift period φ (-x)) 0)
      ((-id) (0 : LiftTangent)) := by simpa using hd
  have hh := hd0.comp (0 : LiftTangent) hn
  have hder : fderiv ℝ (localLift period (reflectedTest period φ) x) 0 =
      -fderiv ℝ (localLift period φ (-x)) 0 := by
    rw [localLift_reflected]
    simpa [Function.comp_def] using hh.fderiv
  ext i
  simp [liftedGradient, hder, add_comm]


-- @@ L131-131 verbatim
end EulerCylinderReflection
