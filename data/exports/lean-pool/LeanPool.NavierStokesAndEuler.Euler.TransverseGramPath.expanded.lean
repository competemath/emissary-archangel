/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TransverseGramInverse
import LeanPool.NavierStokesAndEuler.Euler.Foundations.InverseRegularity
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul


-- @@ L14-20 verbatim
/-!
# Time-dependent inverse of a coercive transverse Gram matrix

The coefficient inverse and its derivative are constructed from the frame and
its quantitative lower bound. These are coefficient theorems, independent of
any chosen variational solution.
-/


-- @@ L22-22 verbatim
@[expose] public section



-- @@ L25-25 verbatim
noncomputable section


-- @@ L27-27 verbatim
namespace EulerTransverseGramPath


-- @@ L29-30 verbatim
open Set ContinuousLinearMap EulerCoerciveProjection EulerInverseRegularity
  EulerTransverseGramInverse  EulerVolterraConvolution


-- @@ L32-34 verbatim
variable {U E : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]


-- @@ L36-40 verbatim
/-- The within-set derivative of an actual adjoint. -/
theorem hasDerivWithinAt_adjoint (Q : ℝ → U →L[ℝ] E) (Q₁ : U →L[ℝ] E)
    (s : Set ℝ) (t : ℝ) (hQ : HasDerivWithinAt Q Q₁ s t) :
    HasDerivWithinAt (fun r => (Q r).adjoint) Q₁.adjoint s t :=
  ((realAdjoint (U := U) (E := E)).hasFDerivAt).comp_hasDerivWithinAt t hQ


-- @@ L42-47 verbatim
/-- The within-set derivative of an actual Gram matrix. -/
theorem hasDerivWithinAt_gram (Q : ℝ → U →L[ℝ] E) (Q₁ : U →L[ℝ] E)
    (s : Set ℝ) (t : ℝ) (hQ : HasDerivWithinAt Q Q₁ s t) :
    HasDerivWithinAt (fun r => gram (Q r))
      (Q₁.adjoint.comp (Q t) + (Q t).adjoint.comp Q₁) s t :=
  (hasDerivWithinAt_adjoint Q Q₁ s t hQ).clm_comp hQ


-- @@ L49-74 verbatim
/-- Actual inverse differentiation is valid within the time interval, including endpoints. -/
theorem hasDerivWithinAt_gramInverse (Q : ℝ → U →L[ℝ] E) (c : ℝ) (hc : 0 < c)
    (hQ : ∀ r x, c * ‖x‖ ^ 2 ≤ ‖Q r x‖ ^ 2)
    (Q₁ : U →L[ℝ] E) (s : Set ℝ) (t : ℝ)
    (hd : HasDerivWithinAt Q Q₁ s t) :
    HasDerivWithinAt (fun r => gramInverse (Q r) c hc (hQ r))
      (-(gramInverse (Q t) c hc (hQ t)).comp
        ((Q₁.adjoint.comp (Q t) + (Q t).adjoint.comp Q₁).comp
          (gramInverse (Q t) c hc (hQ t)))) s t := by
  let B := gram (Q t)
  let hB := gram_coercive (Q t) c (hQ t)
  let u : (U →L[ℝ] U)ˣ := (coerciveEquiv B c hc hB).toUnit
  have hu : (u : U →L[ℝ] U) = B := by
    ext x
    exact coerciveEquiv_apply B c hc hB x
  have hui : (↑u⁻¹ : U →L[ℝ] U) = gramInverse (Q t) c hc (hQ t) := rfl
  have hi := hasFDerivAt_ringInverse (𝕜 := ℝ) u
  rw [hu] at hi
  have hcomp := hi.comp_hasDerivWithinAt t (hasDerivWithinAt_gram Q Q₁ s t hd)
  have hfun : (fun r => gramInverse (Q r) c hc (hQ r)) =
      Ring.inverse ∘ (fun r => gram (Q r)) := by
    funext r
    exact coerciveInverse_eq_ringInverse (gram (Q r)) c hc (gram_coercive (Q r) c (hQ r))
  rw [hfun]
  simpa only [neg_apply, ContinuousLinearMap.mulLeftRight_apply, hui,
    ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_assoc] using hcomp


-- @@ L76-79 verbatim
variable (T : ℝ)
  (Q Q₁ : C(Icc (0 : ℝ) T, U →L[ℝ] E))
  (c : ℝ) (hc : 0 < c)
  (hQ : ∀ t x, c * ‖x‖ ^ 2 ≤ ‖Q t x‖ ^ 2)


-- @@ L81-84 verbatim
/-- Continuous Gram coefficient, constructed by the actual adjoint and composition. -/
def gramPath : C(Icc (0 : ℝ) T, U →L[ℝ] U) :=
  ⟨fun t => gram (Q t),
    ((realAdjoint (U := U) (E := E)).continuous.comp Q.continuous).clm_comp Q.continuous⟩


-- @@ L86-92 verbatim
/-- Continuous derivative coefficient of the Gram matrix. -/
def gramDerivativePath : C(Icc (0 : ℝ) T, U →L[ℝ] U) :=
  ⟨fun t => (Q₁ t).adjoint.comp (Q t) + (Q t).adjoint.comp (Q₁ t),
    (((realAdjoint (U := U) (E := E)).continuous.comp Q₁.continuous).clm_comp
      Q.continuous).add
      (((realAdjoint (U := U) (E := E)).continuous.comp Q.continuous).clm_comp
        Q₁.continuous)⟩


-- @@ L94-110 verbatim
/-- The genuinely constructed Gram inverse varies continuously on the interval. -/
def gramInversePath : C(Icc (0 : ℝ) T, U →L[ℝ] U) where
  toFun t := gramInverse (Q t) c hc (hQ t)
  continuous_toFun := by
    have heq : (fun t => gramInverse (Q t) c hc (hQ t)) =
        fun t => Ring.inverse (gram (Q t)) := by
      funext t
      exact coerciveInverse_eq_ringInverse (gram (Q t)) c hc (gram_coercive (Q t) c (hQ t))
    rw [heq, continuous_iff_continuousAt]
    intro t
    let e := coerciveEquiv (gram (Q t)) c hc (gram_coercive (Q t) c (hQ t))
    have he : (e.toUnit : U →L[ℝ] U) = gram (Q t) := by
      ext x
      exact coerciveEquiv_apply (gram (Q t)) c hc (gram_coercive (Q t) c (hQ t)) x
    have hcont := (hasFDerivAt_ringInverse (𝕜 := ℝ) e.toUnit).continuousAt
    rw [he] at hcont
    exact hcont.comp (x := t) (gramPath T Q).continuous.continuousAt


-- @@ L112-118 verbatim
/-- Explicit continuous coefficient of the inverse derivative `-K⁻¹ K' K⁻¹`. -/
def gramInverseDerivativePath : C(Icc (0 : ℝ) T, U →L[ℝ] U) :=
  ⟨fun t => -(gramInversePath T Q c hc hQ t).comp
      ((gramDerivativePath T Q Q₁ t).comp (gramInversePath T Q c hc hQ t)),
    ((gramInversePath T Q c hc hQ).continuous.clm_comp
      ((gramDerivativePath T Q Q₁).continuous.clm_comp
        (gramInversePath T Q c hc hQ).continuous)).neg⟩


-- @@ L120-124 verbatim
/-- The canonical left-inverse coefficient is continuous. -/
def frameLeftInversePath : C(Icc (0 : ℝ) T, E →L[ℝ] U) :=
  ⟨fun t => (gramInversePath T Q c hc hQ t).comp (Q t).adjoint,
    (gramInversePath T Q c hc hQ).continuous.clm_comp
      ((realAdjoint (U := U) (E := E)).continuous.comp Q.continuous)⟩


-- @@ L126-133 verbatim
/-- The continuous coefficient of the derivative of the frame left inverse. -/
def frameLeftInverseDerivativePath : C(Icc (0 : ℝ) T, E →L[ℝ] U) :=
  ⟨fun t => (gramInverseDerivativePath T Q Q₁ c hc hQ t).comp (Q t).adjoint +
      (gramInversePath T Q c hc hQ t).comp (Q₁ t).adjoint,
    ((gramInverseDerivativePath T Q Q₁ c hc hQ).continuous.clm_comp
      ((realAdjoint (U := U) (E := E)).continuous.comp Q.continuous)).add
      ((gramInversePath T Q c hc hQ).continuous.clm_comp
        ((realAdjoint (U := U) (E := E)).continuous.comp Q₁.continuous))⟩


-- @@ L135-137 verbatim
variable (hT : 0 ≤ T)
    (hd : ∀ t : Icc (0 : ℝ) T,
      HasDerivWithinAt (extendPath T hT Q) (Q₁ t) (Icc (0 : ℝ) T) t)


-- @@ L139-149 verbatim
include hd in
/-- The constructed inverse coefficient has its claimed within-interval derivative. -/
theorem gramInversePath_hasDerivWithinAt (t : Icc (0 : ℝ) T) :
    HasDerivWithinAt (extendPath T hT (gramInversePath T Q c hc hQ))
      (gramInverseDerivativePath T Q Q₁ c hc hQ t) (Icc (0 : ℝ) T) t := by
  have hi := hasDerivWithinAt_gramInverse (extendPath T hT Q) c hc
    (fun r => hQ (projIcc 0 T hT r)) (Q₁ t) (Icc (0 : ℝ) T) t (hd t)
  convert hi using 1
  · rfl
  · simp only [extendPath, projIcc_of_mem hT t.property]
    rfl


-- @@ L151-161 verbatim
include hd in
/-- The constructed frame left inverse has its claimed within-interval derivative. -/
theorem frameLeftInversePath_hasDerivWithinAt (t : Icc (0 : ℝ) T) :
    HasDerivWithinAt (extendPath T hT (frameLeftInversePath T Q c hc hQ))
      (frameLeftInverseDerivativePath T Q Q₁ c hc hQ t) (Icc (0 : ℝ) T) t := by
  have hi := (gramInversePath_hasDerivWithinAt T Q Q₁ c hc hQ hT hd t).clm_comp
    (hasDerivWithinAt_adjoint (extendPath T hT Q) (Q₁ t) (Icc (0 : ℝ) T) t (hd t))
  convert hi using 1
  · rfl
  · simp only [extendPath, projIcc_of_mem hT t.property]
    rfl


-- @@ L163-163 verbatim
end EulerTransverseGramPath
