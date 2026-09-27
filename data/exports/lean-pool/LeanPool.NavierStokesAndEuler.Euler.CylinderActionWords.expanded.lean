/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.LpCylinderTranslation
public import LeanPool.NavierStokesAndEuler.Euler.ParameterSobolevBlocks
public import LeanPool.NavierStokesAndEuler.Euler.TimeLpBoundedMap
import LeanPool.NavierStokesAndEuler.Euler.CylinderTranslationAdjoint
import LeanPool.NavierStokesAndEuler.Euler.LpCylinderOrbit
import LeanPool.NavierStokesAndEuler.Euler.MeanPathLpBlocks
import LeanPool.NavierStokesAndEuler.Euler.ParameterSobolevLinear
import LeanPool.NavierStokesAndEuler.Euler.IsometricActionCalculus
import LeanPool.NavierStokesAndEuler.Euler.ParameterWordHigher
import Mathlib.Analysis.Calculus.ContDiff.Comp


-- @@ L19-19 verbatim
/-! Exact mixed-word invariance on cylinder L² and its time-function spaces. -/


-- @@ L21-21 verbatim
section


-- @@ L23-30 verbatim
/-!
# Exact word-norm invariance along a genuine isometric orbit

Every actual derivative word of a smooth linear-isometric orbit is the orbit
of its derivative at zero. Consequently its fixed-Sobolev word block is
independent of the translation parameter, with constant one and no radius
change. This applies equally to spatial L² and its time-function spaces.
-/


-- @@ L32-32 verbatim
@[expose] public section


-- @@ L34-34 verbatim
noncomputable section


-- @@ L36-36 verbatim
namespace EulerIsometricAction


-- @@ L38-38 verbatim
open ContinuousLinearMap Finset EulerParameterWordGevrey

-- @@ L39-39 verbatim
open scoped ContDiff


-- @@ L41-44 verbatim
variable {X E ι : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  (τ : X → E →ₗᵢ[ℝ] E) (hadd : ∀ a b u, τ a (τ b u) = τ (a + b) u)
  (hzero : ∀ u, τ 0 u = u)


-- @@ L46-47 verbatim
/-- Derivative at zero, given by `fderiv ℝ (fun a => τ a u) 0 v`. -/
def derivativeAtZero (u : E) (v : X) : E := fderiv ℝ (fun a => τ a u) 0 v


-- @@ L49-54 verbatim
include hadd in
theorem derivativeAtZero_translation (u : E) (hu : ContDiff ℝ ∞ (fun a => τ a u)) (v a : X) :
    τ a (derivativeAtZero τ u v) = fderiv ℝ (fun b => τ b u) a v := by
  have h := hasFDerivAt_all τ hadd u (fderiv ℝ (fun b => τ b u) 0)
    ((hu.differentiable (by simp) (0 : X)).hasFDerivAt) a
  exact (congrArg (fun D : X →L[ℝ] E => D v) h.fderiv).symm


-- @@ L56-63 verbatim
include hadd in
theorem derivativeAtZero_smooth (u : E) (hu : ContDiff ℝ ∞ (fun a => τ a u)) (v : X) :
    ContDiff ℝ ∞ (fun a => τ a (derivativeAtZero τ u v)) := by
  have he : (fun a => τ a (derivativeAtZero τ u v)) =
      fun a => fderiv ℝ (fun b => τ b u) a v :=
    funext (fun a => derivativeAtZero_translation τ hadd u hu v a)
  rw [he]
  exact (hu.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const


-- @@ L65-67 verbatim
/-- Word at zero, given by `wordDerivative directions (fun a => τ a u) w 0`. -/
def wordAtZero (directions : ι → X) (u : E) {n : ℕ} (w : Fin n → ι) : E :=
  wordDerivative directions (fun a => τ a u) w 0


-- @@ L69-72 verbatim
include hzero in
theorem wordAtZero_zero (directions : ι → X) (u : E) (w : Fin 0 → ι) :
    wordAtZero τ directions u w = u := by
  simp only [wordAtZero,wordDerivative_zero,hzero]


-- @@ L74-83 verbatim
include hadd in
theorem wordAtZero_snoc (directions : ι → X) (u : E) (hu : ContDiff ℝ ∞ (fun a => τ a u))
    {n : ℕ} (w : Fin n → ι) (i : ι) :
    wordAtZero τ directions u (Fin.snoc w i) =
      wordAtZero τ directions (derivativeAtZero τ u (directions i)) w := by
  have he : directional directions (fun a => τ a u) i =
      fun a => τ a (derivativeAtZero τ u (directions i)) :=
    funext (fun a => (derivativeAtZero_translation τ hadd u hu (directions i) a).symm)
  unfold wordAtZero
  rw [wordDerivative_snoc directions _ hu w i 0,he]


-- @@ L85-102 verbatim
include hadd hzero in
theorem wordAtZero_translation (directions : ι → X) (u : E) (hu : ContDiff ℝ ∞ (fun a => τ a u))
    {n : ℕ} (w : Fin n → ι) (a : X) :
    τ a (wordAtZero τ directions u w) = wordDerivative directions (fun b => τ b u) w a := by
  induction n generalizing u with
  | zero => simp only [wordAtZero_zero τ hzero,wordDerivative_zero]
  | succ n ih =>
    have hw : wordAtZero τ directions u w =
        wordAtZero τ directions (derivativeAtZero τ u (directions (w (Fin.last n)))) (Fin.init w)
            := by
      simpa only [Fin.snoc_init_self] using wordAtZero_snoc τ hadd directions u hu (Fin.init w) (w
          (Fin.last n))
    rw [hw,ih _ (derivativeAtZero_smooth τ hadd u hu _) (Fin.init w)]
    have he : directional directions (fun b => τ b u) (w (Fin.last n)) =
        fun b => τ b (derivativeAtZero τ u (directions (w (Fin.last n)))) :=
      funext (fun b => (derivativeAtZero_translation τ hadd u hu _ b).symm)
    simpa only [Fin.snoc_init_self,he] using
      (wordDerivative_snoc directions (fun b => τ b u) hu (Fin.init w) (w (Fin.last n)) a).symm


-- @@ L104-111 verbatim
include hadd hzero in
theorem wordAtZero_smooth (directions : ι → X) (u : E) (hu : ContDiff ℝ ∞ (fun a => τ a u))
    {n : ℕ} (w : Fin n → ι) : ContDiff ℝ ∞ (fun a => τ a (wordAtZero τ directions u w)) := by
  have he : (fun a => τ a (wordAtZero τ directions u w)) =
      wordDerivative directions (fun b => τ b u) w :=
    funext (wordAtZero_translation τ hadd hzero directions u hu w)
  rw [he]
  exact wordDerivative_contDiff directions _ hu w


-- @@ L113-113 verbatim
variable [Fintype ι]


-- @@ L115-123 verbatim
include hadd hzero in
theorem wordSum_orbit_constant (directions : ι → X) (u : E) (hu : ContDiff ℝ ∞ (fun a => τ a u))
    (n : ℕ) (a : X) : wordSum directions (fun b => τ b u) n a =
      wordSum directions (fun b => τ b u) n 0 := by
  unfold wordSum
  apply sum_congr rfl
  intro w _
  rw [← wordAtZero_translation τ hadd hzero directions u hu w a]
  exact (τ a).norm_map (wordAtZero τ directions u w)


-- @@ L125-132 verbatim
include hadd hzero in
theorem baseSize_orbit_constant (directions : ι → X) (q : ℕ) (u : E)
    (hu : ContDiff ℝ ∞ (fun a => τ a u)) (a : X) :
    baseSize directions q (fun b => τ b u) a = baseSize directions q (fun b => τ b u) 0 := by
  unfold baseSize
  apply sum_congr rfl
  intro k _
  exact wordSum_orbit_constant τ hadd hzero directions u hu k a


-- @@ L134-146 verbatim
include hadd hzero in
theorem block_orbit_constant (directions : ι → X) (q : ℕ) (u : E)
    (hu : ContDiff ℝ ∞ (fun a => τ a u)) (n : ℕ) (a : X) :
    block directions q (fun b => τ b u) n a = block directions q (fun b => τ b u) n 0 := by
  unfold block
  apply sum_congr rfl
  intro w _
  have he : wordDerivative directions (fun b => τ b u) w =
      fun b => τ b (wordAtZero τ directions u w) :=
    (funext (wordAtZero_translation τ hadd hzero directions u hu w)).symm
  rw [he]
  exact baseSize_orbit_constant τ hadd hzero directions q _
    (wordAtZero_smooth τ hadd hzero directions u hu w) a


-- @@ L148-148 verbatim
end EulerIsometricAction


-- @@ L150-150 verbatim
end

-- @@ L151-151 verbatim
end


-- @@ L153-153 verbatim
end


-- @@ L155-155 verbatim
@[expose] public section


-- @@ L157-157 verbatim
noncomputable section


-- @@ L159-159 verbatim
namespace EulerLpCylinderTranslation


-- @@ L161-162 verbatim
open Set MeasureTheory ContinuousLinearMap EulerLiftedGradientSpace
  EulerTimeLp EulerTimeLpBoundedMap EulerParameterWordGevrey

-- @@ L163-163 verbatim
open scoped ContDiff


-- @@ L165-165 verbatim
variable (P : ℝ) [Fact (0 < P)] {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]


-- @@ L167-167 verbatim
section Path


-- @@ L169-169 verbatim
variable {K : Type*} [TopologicalSpace K] [CompactSpace K]


-- @@ L171-182 verbatim
theorem pathTranslate_norm_map (a : LiftTangent) (f : C(K, CylinderL2 P V)) :
    ‖pathTranslate P a f‖ = ‖f‖ := by
  apply le_antisymm
  · apply (ContinuousMap.norm_le _ (norm_nonneg f)).2
    intro t
    change ‖translate P a (f t)‖ ≤ ‖f‖
    rw [LinearIsometry.norm_map]
    exact f.norm_coe_le_norm t
  · apply (ContinuousMap.norm_le _ (norm_nonneg (pathTranslate P a f))).2
    intro t
    rw [← (translate P a).norm_map (f t)]
    exact (pathTranslate P a f).norm_coe_le_norm t


-- @@ L184-187 verbatim
/-- Path translate isometry, bundling `toLinearMap`, `norm_map`. -/
def pathTranslateIsometry (a : LiftTangent) : C(K,CylinderL2 P V) →ₗᵢ[ℝ] C(K,CylinderL2 P V) where
  toLinearMap := (pathTranslate P a).toLinearMap
  norm_map' := pathTranslate_norm_map P a


-- @@ L189-196 verbatim
theorem path_block_constant {ι : Type*} [Fintype ι] (directions : ι → LiftTangent) (q : ℕ)
    (f : C(K, CylinderL2 P V)) (hf : ContDiff ℝ ∞ (fun a => pathTranslate P a f)) (n : ℕ) (a :
        LiftTangent) :
    block directions q (fun b => pathTranslate P b f) n a =
      block directions q (fun b => pathTranslate P b f) n 0 :=
  EulerIsometricAction.block_orbit_constant (X := LiftTangent)
    (E := C(K,CylinderL2 P V)) (ι := ι) (pathTranslateIsometry (K := K) (V := V) P)
    (fun a b u => pathTranslate_add P a b u) (fun u => pathTranslate_zero P u) directions q f hf n a


-- @@ L198-198 verbatim
end Path


-- @@ L200-203 verbatim
/-- Time translate isometry, given by `timeLiftIsometry T (translate P a)`. -/
def timeTranslateIsometry (T : ℝ) (a : LiftTangent) :
    TimeLp T (CylinderL2 P V) →ₗᵢ[ℝ] TimeLp T (CylinderL2 P V) :=
  timeLiftIsometry T (translate P a)


-- @@ L205-217 verbatim
theorem timeTranslateIsometry_add (T : ℝ) (a b : LiftTangent) (f : TimeLp T (CylinderL2 P V)) :
    timeTranslateIsometry P T a (timeTranslateIsometry P T b f) = timeTranslateIsometry P T (a+b) f
        := by
  apply Lp.ext
  filter_upwards [timeLift_ae T (translate P a).toContinuousLinearMap (timeTranslateIsometry P T b
      f),
    timeLift_ae T (translate P b).toContinuousLinearMap f,
    timeLift_ae T (translate P (a+b)).toContinuousLinearMap f] with t ha hb hab
  change timeTranslateIsometry P T a (timeTranslateIsometry P T b f) t = _ at ha
  change timeTranslateIsometry P T b f t = _ at hb
  change timeTranslateIsometry P T (a+b) f t = _ at hab
  rw [ha,hb,hab]
  exact translate_add P a b (f t)


-- @@ L219-225 verbatim
theorem timeTranslateIsometry_zero (T : ℝ) (f : TimeLp T (CylinderL2 P V)) :
    timeTranslateIsometry P T 0 f = f := by
  apply Lp.ext
  filter_upwards [timeLift_ae T (translate P 0).toContinuousLinearMap f] with t ht
  change timeTranslateIsometry P T 0 f t = _ at ht
  rw [ht]
  exact translate_zero P (f t)


-- @@ L227-236 verbatim
theorem time_block_constant {ι : Type*} [Fintype ι] (directions : ι → LiftTangent) (q : ℕ)
    (T : ℝ) (f : TimeLp T (CylinderL2 P V))
    (hf : ContDiff ℝ ∞ (fun a => timeLift T (translate P a).toContinuousLinearMap f))
    (n : ℕ) (a : LiftTangent) :
    block directions q (fun b => timeLift T (translate P b).toContinuousLinearMap f) n a =
      block directions q (fun b => timeLift T (translate P b).toContinuousLinearMap f) n 0 :=
  EulerIsometricAction.block_orbit_constant (X := LiftTangent)
    (E := TimeLp T (CylinderL2 P V)) (ι := ι) (timeTranslateIsometry (V := V) P T)
    (fun a b u => timeTranslateIsometry_add P T a b u)
    (fun u => timeTranslateIsometry_zero P T u) directions q f hf n a


-- @@ L238-247 verbatim
theorem pathLp_orbit_contDiff (T : ℝ) (hT : 0 ≤ T) (f : C(Icc (0 : ℝ) T, CylinderL2 P V))
    (hf : ContDiff ℝ ∞ (fun a => pathTranslate P a f)) :
    ContDiff ℝ ∞ (fun a => timeLift T (translate P a).toContinuousLinearMap (pathLp T hT f)) := by
  have he : (fun a => timeLift T (translate P a).toContinuousLinearMap (pathLp T hT f)) =
      (pathLpOperator T hT) ∘ (fun a => pathTranslate P a f) := by
    funext a
    convert (pathLp_timeLift T hT (translate P a).toContinuousLinearMap f).symm using 1
    rfl
  rw [he]
  exact (pathLpOperator (E := CylinderL2 P V) T hT).contDiff.comp hf


-- @@ L249-266 verbatim
/-- The actual Ctime-to-time-L² inclusion preserves all mixed word blocks
with exactly the square-root time length factor. -/
theorem pathLp_block_le {ι : Type*} [Fintype ι] (directions : ι → LiftTangent) (q : ℕ)
    (T : ℝ) (hT : 0 ≤ T) (f : C(Icc (0 : ℝ) T, CylinderL2 P V))
    (hf : ContDiff ℝ ∞ (fun a => pathTranslate P a f)) (n : ℕ) (a : LiftTangent) :
    block directions q (fun b => timeLift T (translate P b).toContinuousLinearMap (pathLp T hT f))
        n a ≤
      Real.sqrt T*block directions q (fun b => pathTranslate P b f) n a := by
  have he : (fun b => timeLift T (translate P b).toContinuousLinearMap (pathLp T hT f)) =
      (pathLpOperator T hT) ∘ (fun b => pathTranslate P b f) := by
    funext b
    convert (pathLp_timeLift T hT (translate P b).toContinuousLinearMap f).symm using 1
    rfl
  rw [he]
  exact (block_comp_clm_le directions q (pathLpOperator (E := CylinderL2 P V) T hT) _ hf n a).trans
    (mul_le_mul_of_nonneg_right
      (EulerMeanTimeContinuousTranslation.pathLpOperator_norm_sqrt T hT)
      (block_nonneg directions q _ n a))


-- @@ L268-268 verbatim
end EulerLpCylinderTranslation
