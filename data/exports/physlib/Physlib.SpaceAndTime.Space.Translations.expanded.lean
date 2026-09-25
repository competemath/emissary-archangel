/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.SpaceAndTime.Space.Derivatives.Div

-- @@ L9-16 verbatim
/-!

# Translations on space

We define translations on space, and how translations act on distributions.
Translations for part of the Poincaré group.

-/


-- @@ L18-18 verbatim
@[expose] public section


-- @@ L20-20 verbatim
open Physlib

-- @@ L21-21 verbatim
section


-- @@ L23-28 verbatim
variable
  {𝕜} [NontriviallyNormedField 𝕜]
  {X} [NormedAddCommGroup X] [NormedSpace ℝ X]
  {Y} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
  {ι : Type*} [Fintype ι] {Y' : ι → Type*} [∀ i, NormedAddCommGroup (Y' i)]
  [∀ i, NormedSpace 𝕜 (Y' i)] {Φ : X → ∀ i, Y' i} {x : X}


-- @@ L30-30 verbatim
namespace Space


-- @@ L32-36 verbatim
/-!

## Translations of distributions

-/


-- @@ L38-38 verbatim
open Distribution

-- @@ L39-39 verbatim
open SchwartzMap


-- @@ L41-83 verbatim
/-- The continuous linear map translating Schwartz maps. -/
noncomputable def translateSchwartz {d : ℕ} (a : EuclideanSpace ℝ (Fin d)) :
    𝓢(Space d, X) →L[ℝ] 𝓢(Space d, X) :=
  SchwartzMap.compCLM (𝕜 := ℝ)
      (g := fun x => x - basis.repr.symm a)
      (by
        apply Function.HasTemperateGrowth.of_fderiv (k := 1) (C := 1 + ‖a‖)
        · have hx : (fderiv ℝ (fun (x : Space d) => (x - basis.repr.symm a: Space d))) =
              fun _ => ContinuousLinearMap.id ℝ (Space d) := by
            funext x
            erw [fderiv_sub]
            simp only [fderiv_fun_id, fderiv_fun_const, Pi.zero_apply, sub_zero]
            fun_prop
            fun_prop
          rw [hx]
          exact Function.HasTemperateGrowth.const
              (ContinuousLinearMap.id ℝ (Space d))
        · fun_prop
        · intro x
          simp only [pow_one]
          change ‖x - basis.repr.symm a‖ ≤ _
          trans ‖x‖ + ‖a‖
          · apply (norm_sub_le x (basis.repr.symm a)).trans
            simp
          simp [mul_add, add_mul]
          trans 1 + (‖x‖ + ‖a‖)
          · simp
          trans (1 + (‖x‖ + ‖a‖)) + ‖x‖ * ‖a‖
          · simp
            positivity
          ring_nf
          rfl) (by
          use 1, (1 + ‖a‖)
          intro x
          simp only [pow_one]
          apply (norm_le_norm_add_norm_sub' x (basis.repr.symm a)).trans
          trans 1 + (‖a‖ + ‖x - basis.repr.symm a‖)
          · simp
          trans (1 + (‖a‖ + ‖x - basis.repr.symm a‖)) + ‖a‖ * ‖x - basis.repr.symm a‖
          · simp
            positivity
          ring_nf
          rfl)


-- @@ L85-88 verbatim
@[simp]
lemma translateSchwartz_apply {d : ℕ} (a : EuclideanSpace ℝ (Fin d))
    (η : 𝓢(Space d, X)) (x : Space d) :
    translateSchwartz a η x = η (x - basis.repr.symm a) := rfl


-- @@ L90-94 verbatim
lemma translateSchwartz_coe_eq {d : ℕ} (a : EuclideanSpace ℝ (Fin d))
    (η : 𝓢(Space d, X)) :
    (translateSchwartz a η : Space d → X) = fun x => η (x - basis.repr.symm a) := by
  ext
  simp


-- @@ L96-104 expanded
/-- The continuous linear map translating distributions. -/
noncomputable def distTranslate {d : ℕ} (a : EuclideanSpace ℝ (Fin d)) :
    (Distribution ℝ (Space d) X) →ₗ[ℝ] (Distribution ℝ (Space d) X)
    where
  toFun T := T.comp (translateSchwartz (-a))
  map_add' T1
    T2 := by
    ext η
    simp
  map_smul' c T := by simp


-- @@ L106-108 expanded
lemma distTranslate_apply {d : ℕ} (a : EuclideanSpace ℝ (Fin d)) (T : Distribution ℝ (Space d) X)
    (η : 𝓢(Space d, ℝ)) : distTranslate a T η = T (translateSchwartz (-a) η) :=
  rfl


-- @@ L110-110 verbatim
open InnerProductSpace


-- @@ L112-127 expanded
@[simp]
lemma distTranslate_distGrad {d : ℕ} (a : EuclideanSpace ℝ (Fin d))
    (T : Distribution ℝ (Space d) ℝ) :
    distGrad (distTranslate a T) = distTranslate a (distGrad T) :=
  by
  apply distGrad_eq_of_inner
  intro η y
  rw [distTranslate_apply, distGrad_inner_eq]
  rw [fderivD_apply, fderivD_apply, distTranslate_apply]
  congr 2
  ext x
  simp only [translateSchwartz_apply, map_neg, sub_neg_eq_add, LinearIsometryEquiv.symm_apply_apply]
  change fderiv ℝ η (x + basis.repr.symm a) y = fderiv ℝ _ x y
  rw [translateSchwartz_coe_eq]
  simp only [map_neg, sub_neg_eq_add]
  rw [fderiv_comp_add_right]


-- @@ L129-129 verbatim
open MeasureTheory

-- @@ L130-146 verbatim
set_option backward.isDefEq.respectTransparency false in
lemma distTranslate_ofFunction {d : ℕ} (a : EuclideanSpace ℝ (Fin d))
    (f : Space d → X) (hf : IsDistBounded f) :
    distTranslate a (distOfFunction f hf) =
    distOfFunction (fun x => f (x - basis.repr.symm a))
    (IsDistBounded.comp_add_right hf (- basis.repr.symm a)) := by
  ext η
  rw [distTranslate_apply, distOfFunction_apply, distOfFunction_apply]
  trans ∫ (x : Space d), η ((x - basis.repr.symm a) + basis.repr.symm a) •
    f (x - basis.repr.symm a); swap
  · simp
  let f' := fun x : Space d => η (x + basis.repr.symm a) • f (x)
  change _ = ∫ (x : Space d), f' (x - basis.repr.symm a)
  rw [MeasureTheory.integral_sub_right_eq_self]
  congr
  funext x
  simp [f']


-- @@ L148-170 expanded
@[simp]
lemma distDiv_distTranslate {d : ℕ} (a : EuclideanSpace ℝ (Fin d))
    (T : Distribution ℝ (Space d) (EuclideanSpace ℝ (Fin d))) :
    distDiv (distTranslate a T) = distTranslate a (distDiv T) :=
  by
  ext η
  rw [distDiv_apply_eq_sum_fderivD]
  rw [distTranslate_apply, distDiv_apply_eq_sum_fderivD]
  congr
  funext i
  rw [fderivD_apply, fderivD_apply, distTranslate_apply]
  simp only [PiLp.neg_apply, neg_inj]
  have h1 :
    ((translateSchwartz (-a))
        ((SchwartzMap.evalCLM ℝ (Space d) ℝ (basis i)) ((fderivCLM ℝ (Space d) ℝ) η))) =
      ((SchwartzMap.evalCLM ℝ (Space d) ℝ (basis i))
        ((fderivCLM ℝ (Space d) ℝ) ((translateSchwartz (-a)) η))) :=
    by
    ext x
    rw [translateSchwartz_apply]
    simp only [map_neg, sub_neg_eq_add]
    change fderiv ℝ η (x + basis.repr.symm a) (basis i) = fderiv ℝ _ x (basis i)
    rw [translateSchwartz_coe_eq]
    simp only [map_neg, sub_neg_eq_add]
    rw [fderiv_comp_add_right]
  rw [h1]


-- @@ L172-172 verbatim
end Space
