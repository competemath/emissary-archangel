/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.MeanCoefficientSpatial


-- @@ L11-11 verbatim
/-! All-order parameter regularity of actual bounded smooth coefficient translations. -/


-- @@ L13-13 verbatim
@[expose] public section



-- @@ L16-16 verbatim
noncomputable section


-- @@ L18-18 verbatim
namespace EulerMeanCoefficients


-- @@ L20-20 verbatim
open EulerSmoothLimit MeasureTheory InnerProductSpace

-- @@ L21-21 verbatim
open scoped ContDiff BoundedContinuousFunction


-- @@ L23-23 verbatim
universe u


-- @@ L25-25 verbatim
variable {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]


-- @@ L27-29 verbatim
theorem fieldDerivativeMap_norm_le (DA : Space →ᵇ (Space →L[ℝ] V)) :
    ‖fieldDerivativeMap DA‖ ≤ ‖DA‖ :=
  (fieldDerivativeMap DA).opNorm_le_bound (norm_nonneg DA) (fieldDirection_norm_le DA)


-- @@ L31-46 verbatim
/-- Derivative bundling linear, bundling `toFun`, `map_add`, `map_smul`. -/
def derivativeBundlingLinear : (Space →ᵇ (Space →L[ℝ] V)) →ₗ[ℝ]
    (Space →L[ℝ] (Space →ᵇ V)) where
  toFun := fieldDerivativeMap
  map_add' A B := by
    apply ContinuousLinearMap.ext
    intro v
    apply BoundedContinuousFunction.ext
    intro x
    rfl
  map_smul' c A := by
    apply ContinuousLinearMap.ext
    intro v
    apply BoundedContinuousFunction.ext
    intro x
    rfl


-- @@ L48-54 verbatim
/-- Currying a bounded field of linear maps is itself a bounded linear operation. -/
def derivativeBundling : (Space →ᵇ (Space →L[ℝ] V)) →L[ℝ]
    (Space →L[ℝ] (Space →ᵇ V)) where
  toLinearMap := derivativeBundlingLinear
  cont := AddMonoidHomClass.continuous_of_bound derivativeBundlingLinear 1 (fun A => by
    change ‖fieldDerivativeMap A‖ ≤ 1 * ‖A‖
    simpa only [one_mul] using fieldDerivativeMap_norm_le A)


-- @@ L56-57 verbatim
@[simp] theorem derivativeBundling_apply (A : Space →ᵇ (Space →L[ℝ] V)) :
    derivativeBundling A = fieldDerivativeMap A := rfl


-- @@ L59-64 verbatim
/-- A concrete smooth coefficient with globally bounded actual derivatives of every order. -/
structure BoundedSmoothField (V : Type u) [NormedAddCommGroup V] [NormedSpace ℝ V] where
  /-- Underlying field of `BoundedSmoothField`, of type `Space →ᵇ V`. -/
  field : Space →ᵇ V
  smooth : ContDiff ℝ ∞ (field : Space → V)
  bounded : ∀ n : ℕ, ∃ C : ℝ, ∀ x, ‖iteratedFDeriv ℝ n (field : Space → V) x‖ ≤ C


-- @@ L66-66 verbatim
namespace BoundedSmoothField


-- @@ L68-76 verbatim
/-- Derivative, bundling `field`, `smooth`, `bounded`. -/
def derivative (A : BoundedSmoothField V) : BoundedSmoothField (Space →L[ℝ] V) where
  field := boundedDerivative A.field A.smooth (Classical.choose (A.bounded 1)) (fun x => by
    rw [← norm_iteratedFDeriv_one]
    exact Classical.choose_spec (A.bounded 1) x)
  smooth := A.smooth.fderiv_right (m := ∞) (by simp)
  bounded n := by
    change ∃ C : ℝ, ∀ x, ‖iteratedFDeriv ℝ n (fderiv ℝ (A.field : Space → V)) x‖ ≤ C
    simpa only [norm_iteratedFDeriv_fderiv] using A.bounded (n+1)


-- @@ L78-79 verbatim
@[simp] theorem derivative_field_apply (A : BoundedSmoothField V) (x : Space) :
    A.derivative.field x = fderiv ℝ (A.field : Space → V) x := rfl


-- @@ L81-88 verbatim
theorem translation_hasFDerivAt (A : BoundedSmoothField V) (a : Space) :
    HasFDerivAt (translated A.field) (fieldDerivativeMap (translated A.derivative.field a)) a := by
  obtain ⟨M, hM⟩ := A.bounded 2
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  apply translated_hasFDerivAt A.field A.derivative.field A.smooth (fun _ => rfl) M hM0
  intro x
  rw [← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv]
  exact hM x


-- @@ L90-92 verbatim
theorem translation_fderiv (A : BoundedSmoothField V) :
    fderiv ℝ (translated A.field) = fun a => derivativeBundling (translated A.derivative.field a) :=
  funext (fun a => (A.translation_hasFDerivAt a).fderiv)


-- @@ L94-107 verbatim
private theorem translation_contDiff_nat_aux (n : ℕ) :
    ∀ (V : Type u) [NormedAddCommGroup V] [NormedSpace ℝ V] (A : BoundedSmoothField V),
      ContDiff ℝ n (translated A.field) := by
  induction n with
  | zero =>
    intro V _ _ A
    apply contDiff_zero.mpr
    exact continuous_iff_continuousAt.mpr (fun a => (A.translation_hasFDerivAt a).continuousAt)
  | succ n ih =>
    intro V _ _ A
    rw [Nat.cast_add, Nat.cast_one, contDiff_succ_iff_fderiv]
    refine ⟨fun a => (A.translation_hasFDerivAt a).differentiableAt, by simp, ?_⟩
    rw [A.translation_fderiv]
    exact (derivativeBundling (V := V)).contDiff.comp (ih (Space →L[ℝ] V) A.derivative)


-- @@ L109-112 verbatim
/-- Every spatial translation of an actual globally bounded smooth coefficient depends smoothly on
its parameter. -/
theorem translation_contDiff (A : BoundedSmoothField V) : ContDiff ℝ ∞ (translated A.field) :=
  contDiff_infty.mpr (fun n => translation_contDiff_nat_aux n V A)


-- @@ L114-114 verbatim
end BoundedSmoothField


-- @@ L116-116 verbatim
end EulerMeanCoefficients
