/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.LpMultilinearBundling
public import LeanPool.NavierStokesAndEuler.Euler.LpSmoothField
import LeanPool.NavierStokesAndEuler.Euler.LpSmoothFieldJets
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.SmoothLimit
public import Mathlib.Topology.ContinuousMap.Compact
import LeanPool.NavierStokesAndEuler.Euler.MeanCutoffTaylor
import LeanPool.NavierStokesAndEuler.ForMathlib.SmoothnessOrder
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Bounds


-- @@ L18-24 verbatim
/-!
# Actual forcing derivatives in the uniform time norm

Continuous paths of the literal ordinary spatial L² jets give genuine
smoothness of the forcing translation orbit in C(time,L²). The derivative
norm is bounded by the original uniform-time spatial jet norm, with no loss.
-/


-- @@ L26-26 verbatim
section


-- @@ L28-35 verbatim
/-!
# Actual spatial derivatives in the uniform norm on continuous paths

A family of continuous paths whose pointwise spatial derivatives are actual
continuous paths, with uniform bounds, is smooth in the uniform path norm.
The proof uses a quadratic Taylor remainder and loses no derivative-bound
constant. No uniform-path differentiability is assumed.
-/


-- @@ L37-37 verbatim
@[expose] public section


-- @@ L39-39 verbatim
noncomputable section


-- @@ L41-41 verbatim
namespace EulerContinuousSpatialFamily


-- @@ L43-43 verbatim
open ContinuousLinearMap EulerSmoothLimit Filter

-- @@ L44-44 verbatim
open scoped ContDiff Topology


-- @@ L46-46 verbatim
universe u v


-- @@ L48-48 verbatim
section Bundling


-- @@ L50-51 verbatim
variable {K : Type u} [TopologicalSpace K] [CompactSpace K]
  {V : Type v} [NormedAddCommGroup V] [NormedSpace ℝ V]


-- @@ L53-55 verbatim
/-- Cache the standard `NormedAddCommGroup (Space →L[ℝ] V)` instance to shorten typeclass
synthesis. -/
local instance instContinuousSpatialFamily1 : NormedAddCommGroup (Space →L[ℝ] V) := inferInstance

-- @@ L56-57 verbatim
/-- Cache the standard `NormedSpace ℝ (Space →L[ℝ] V)` instance to shorten typeclass synthesis. -/
local instance instContinuousSpatialFamily2 : NormedSpace ℝ (Space →L[ℝ] V) := inferInstance

-- @@ L58-59 verbatim
/-- Cache the standard `NormedAddCommGroup C(K,V)` instance to shorten typeclass synthesis. -/
local instance instContinuousSpatialFamily3 : NormedAddCommGroup C(K,V) := inferInstance

-- @@ L60-61 verbatim
/-- Cache the standard `NormedSpace ℝ C(K,V)` instance to shorten typeclass synthesis. -/
local instance instContinuousSpatialFamily4 : NormedSpace ℝ C(K,V) := inferInstance

-- @@ L62-64 verbatim
/-- Cache the standard `NormedAddCommGroup C(K,Space →L[ℝ] V)` instance to shorten typeclass
synthesis. -/
local instance instContinuousSpatialFamily5 : NormedAddCommGroup C(K,Space →L[ℝ] V) := inferInstance

-- @@ L65-67 verbatim
/-- Cache the standard `NormedSpace ℝ C(K,Space →L[ℝ] V)` instance to shorten typeclass
synthesis. -/
local instance instContinuousSpatialFamily6 : NormedSpace ℝ C(K,Space →L[ℝ] V) := inferInstance

-- @@ L68-71 verbatim
/-- Cache the standard `NormedAddCommGroup (Space →L[ℝ] C(K,V))` instance to shorten typeclass
synthesis. -/
local instance instContinuousSpatialFamily7 : NormedAddCommGroup (Space →L[ℝ] C(K,V)) :=
    inferInstance

-- @@ L72-74 verbatim
/-- Cache the standard `NormedSpace ℝ (Space →L[ℝ] C(K,V))` instance to shorten typeclass
synthesis. -/
local instance instContinuousSpatialFamily8 : NormedSpace ℝ (Space →L[ℝ] C(K,V)) := inferInstance


-- @@ L76-78 verbatim
/-- Direction, given by `⟨fun t => D t a, D.continuous.clm_apply continuous_const⟩`. -/
def direction (D : C(K, Space →L[ℝ] V)) (a : Space) : C(K,V) :=
  ⟨fun t => D t a, D.continuous.clm_apply continuous_const⟩


-- @@ L80-85 verbatim
theorem direction_norm_le (D : C(K, Space →L[ℝ] V)) (a : Space) :
    ‖direction D a‖ ≤ ‖D‖*‖a‖ := by
  apply (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg D) (norm_nonneg a))).2
  intro t
  exact ((D t).le_opNorm a).trans
    (mul_le_mul_of_nonneg_right (D.norm_coe_le_norm t) (norm_nonneg a))


-- @@ L87-91 verbatim
/-- Derivative linear, bundling `toFun`, `map_add`, `map_smul`. -/
def derivativeLinear (D : C(K, Space →L[ℝ] V)) : Space →ₗ[ℝ] C(K,V) where
  toFun := direction D
  map_add' a b := by ext t; exact (D t).map_add a b
  map_smul' c a := by ext t; exact (D t).map_smul c a


-- @@ L93-97 verbatim
/-- Derivative map, bundling `toLinearMap`, `cont`. -/
def derivativeMap (D : C(K, Space →L[ℝ] V)) : Space →L[ℝ] C(K,V) where
  toLinearMap := derivativeLinear D
  cont := AddMonoidHomClass.continuous_of_bound (derivativeLinear D) ‖D‖
    (direction_norm_le D)


-- @@ L99-100 verbatim
@[simp] theorem derivativeMap_apply (D : C(K, Space →L[ℝ] V)) (a : Space) (t : K) :
    derivativeMap D a t = D t a := rfl


-- @@ L102-103 verbatim
theorem derivativeMap_norm_le (D : C(K, Space →L[ℝ] V)) : ‖derivativeMap D‖ ≤ ‖D‖ :=
  (derivativeMap D).opNorm_le_bound (norm_nonneg D) (direction_norm_le D)


-- @@ L105-109 verbatim
/-- Derivative bundling linear, bundling `toFun`, `map_add`, `map_smul`. -/
def derivativeBundlingLinear : C(K,Space →L[ℝ] V) →ₗ[ℝ] (Space →L[ℝ] C(K,V)) where
  toFun := derivativeMap
  map_add' D E := by ext a t; rfl
  map_smul' c D := by ext a t; rfl


-- @@ L111-117 verbatim
/-- Derivative bundling, bundling `toLinearMap`, `cont`. -/
def derivativeBundling : C(K,Space →L[ℝ] V) →L[ℝ] (Space →L[ℝ] C(K,V)) where
  toLinearMap := derivativeBundlingLinear
  cont := AddMonoidHomClass.continuous_of_bound (derivativeBundlingLinear (K := K) (V := V)) 1
    (fun D => by
      change ‖derivativeMap D‖ ≤ 1*‖D‖
      simpa only [one_mul] using derivativeMap_norm_le D)


-- @@ L119-123 verbatim
theorem derivativeBundling_norm_le_one : ‖derivativeBundling (K := K) (V := V)‖ ≤ 1 := by
  apply opNorm_le_bound _ zero_le_one
  intro D
  change ‖derivativeMap D‖ ≤ 1*‖D‖
  simpa only [one_mul] using derivativeMap_norm_le D


-- @@ L125-125 verbatim
end Bundling


-- @@ L127-140 verbatim
/-- Actual continuous spatial derivative paths and finite uniform bounds.
The `jet_eq` field identifies every supplied jet with the ordinary derivative. -/
structure SpatialFamily (K : Type u) [TopologicalSpace K] [CompactSpace K]
    (V : Type v) [NormedAddCommGroup V] [NormedSpace ℝ V] where
  /-- Underlying field of `SpatialFamily`, of type `Space → C(K,V)`. -/
  field : Space → C(K,V)
  smooth : ∀ t, ContDiff ℝ ∞ (fun a => field a t)
  /-- Jet of `SpatialFamily`, of type `(n : ℕ) → Space → C(K,Space [×n]→L[ℝ] V)`. -/
  jet : (n : ℕ) → Space → C(K,Space [×n]→L[ℝ] V)
  jet_eq : ∀ n a t, jet n a t = iteratedFDeriv ℝ n (fun b => field b t) a
  /-- Bound of `SpatialFamily`, of type `ℕ → ℝ`. -/
  bound : ℕ → ℝ
  bound_nonneg : ∀ n, 0 ≤ bound n
  bounded : ∀ n a t, ‖iteratedFDeriv ℝ n (fun b => field b t) a‖ ≤ bound n


-- @@ L142-142 verbatim
namespace SpatialFamily


-- @@ L144-145 verbatim
variable {K : Type u} [TopologicalSpace K] [CompactSpace K]
  {V : Type v} [NormedAddCommGroup V] [NormedSpace ℝ V]


-- @@ L147-149 verbatim
/-- Cache the standard `NormedAddCommGroup (Space →L[ℝ] V)` instance to shorten typeclass
synthesis. -/
local instance instContinuousSpatialFamily9 : NormedAddCommGroup (Space →L[ℝ] V) := inferInstance

-- @@ L150-151 verbatim
/-- Cache the standard `NormedSpace ℝ (Space →L[ℝ] V)` instance to shorten typeclass synthesis. -/
local instance instContinuousSpatialFamily10 : NormedSpace ℝ (Space →L[ℝ] V) := inferInstance

-- @@ L152-153 verbatim
/-- Cache the standard `NormedAddCommGroup C(K,V)` instance to shorten typeclass synthesis. -/
local instance instContinuousSpatialFamily11 : NormedAddCommGroup C(K,V) := inferInstance

-- @@ L154-155 verbatim
/-- Cache the standard `NormedSpace ℝ C(K,V)` instance to shorten typeclass synthesis. -/
local instance instContinuousSpatialFamily12 : NormedSpace ℝ C(K,V) := inferInstance

-- @@ L156-159 verbatim
/-- Cache the standard `NormedAddCommGroup C(K,Space →L[ℝ] V)` instance to shorten typeclass
synthesis. -/
local instance instContinuousSpatialFamily13 : NormedAddCommGroup C(K,Space →L[ℝ] V) :=
    inferInstance

-- @@ L160-162 verbatim
/-- Cache the standard `NormedSpace ℝ C(K,Space →L[ℝ] V)` instance to shorten typeclass
synthesis. -/
local instance instContinuousSpatialFamily14 : NormedSpace ℝ C(K,Space →L[ℝ] V) := inferInstance

-- @@ L163-166 verbatim
/-- Cache the standard `NormedAddCommGroup (Space →L[ℝ] C(K,V))` instance to shorten typeclass
synthesis. -/
local instance instContinuousSpatialFamily15 : NormedAddCommGroup (Space →L[ℝ] C(K,V)) :=
    inferInstance

-- @@ L167-169 verbatim
/-- Cache the standard `NormedSpace ℝ (Space →L[ℝ] C(K,V))` instance to shorten typeclass
synthesis. -/
local instance instContinuousSpatialFamily16 : NormedSpace ℝ (Space →L[ℝ] C(K,V)) := inferInstance


-- @@ L171-176 verbatim
/-- Derivative field, given by `(continuousMultilinearCurryFin1 ℝ Space
V).toContinuousLinearEquiv.toContinuousLinearMap.compLeftContinuous ℝ K (A.jet 1 a)`. -/
def derivativeField (A : SpatialFamily K V) (a : Space) : C(K,Space →L[ℝ] V) :=
  (continuousMultilinearCurryFin1 ℝ Space
      V).toContinuousLinearEquiv.toContinuousLinearMap.compLeftContinuous ℝ K
    (A.jet 1 a)


-- @@ L178-185 verbatim
theorem derivativeField_eq (A : SpatialFamily K V) (a : Space) (t : K) :
    A.derivativeField a t = fderiv ℝ (fun b => A.field b t) a := by
  change continuousMultilinearCurryFin1 ℝ Space V (A.jet 1 a t) = _
  rw [A.jet_eq]
  apply ContinuousLinearMap.ext
  intro v
  rw [continuousMultilinearCurryFin1_apply, iteratedFDeriv_one_apply]
  simp


-- @@ L187-192 verbatim
/-- Derivative jet as an element of `C(K,Space [×n]→L[ℝ] (Space →L[ℝ] V))`. -/
def derivativeJet (A : SpatialFamily K V) (n : ℕ) (a : Space) :
    C(K,Space [×n]→L[ℝ] (Space →L[ℝ] V)) :=
  (continuousMultilinearCurryRightEquiv' ℝ n Space
      V).toContinuousLinearEquiv.toContinuousLinearMap.compLeftContinuous ℝ K
    (A.jet (n+1) a)


-- @@ L194-198 verbatim
theorem derivativeJet_eq (A : SpatialFamily K V) (n : ℕ) (a : Space) (t : K) :
    A.derivativeJet n a t = iteratedFDeriv ℝ n (fderiv ℝ (fun b => A.field b t)) a := by
  change continuousMultilinearCurryRightEquiv' ℝ n Space V (A.jet (n+1) a t) = _
  rw [A.jet_eq, iteratedFDeriv_succ_eq_comp_right]
  exact (continuousMultilinearCurryRightEquiv' ℝ n Space V).apply_symm_apply _


-- @@ L200-221 verbatim
/-- Derivative, bundling `field`, `smooth`, `have`, `funext` and the required compatibility
proofs. -/
def derivative (A : SpatialFamily K V) : SpatialFamily K (Space →L[ℝ] V) where
  field := A.derivativeField
  smooth t := by
    have he : (fun a => A.derivativeField a t) = fderiv ℝ (fun a => A.field a t) :=
      funext (fun a => A.derivativeField_eq a t)
    rw [he]
    exact (A.smooth t).fderiv_right (m := ∞) (by simp)
  jet := A.derivativeJet
  jet_eq n a t := by
    have he : (fun b => A.derivativeField b t) = fderiv ℝ (fun b => A.field b t) :=
      funext (fun b => A.derivativeField_eq b t)
    rw [he]
    exact A.derivativeJet_eq n a t
  bound n := A.bound (n+1)
  bound_nonneg n := A.bound_nonneg (n+1)
  bounded n a t := by
    have he : (fun b => A.derivativeField b t) = fderiv ℝ (fun b => A.field b t) :=
      funext (fun b => A.derivativeField_eq b t)
    rw [he, norm_iteratedFDeriv_fderiv]
    exact A.bounded (n+1) a t


-- @@ L223-224 verbatim
@[simp] theorem derivative_bound (A : SpatialFamily K V) (n : ℕ) :
    A.derivative.bound n = A.bound (n+1) := rfl


-- @@ L226-237 verbatim
theorem taylor_bound (A : SpatialFamily K V) (a b : Space) :
    ‖A.field b-A.field a-derivativeMap (A.derivative.field a) (b-a)‖ ≤
      A.bound 2*‖b-a‖^2 := by
  apply (ContinuousMap.norm_le _ (mul_nonneg (A.bound_nonneg 2) (sq_nonneg _))).2
  intro t
  change ‖A.field b t-A.field a t-A.derivativeField a t (b-a)‖ ≤ _
  rw [A.derivativeField_eq]
  have hD (x : Space) : ‖fderiv ℝ (fderiv ℝ (fun y => A.field y t)) x‖ ≤ A.bound 2 := by
    simpa only [← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv] using A.bounded 2 x t
  have h := EulerMeanBoundary.norm_linearization_remainder_le
    (fun x => A.field x t) (A.smooth t) (A.bound 2) (A.bound_nonneg 2) hD a (b-a)
  simpa only [add_sub_cancel] using h


-- @@ L239-254 verbatim
/-- Genuine differentiability in the uniform path norm, from the pointwise Taylor estimate. -/
theorem hasFDerivAt_field (A : SpatialFamily K V) (a : Space) :
    HasFDerivAt A.field (derivativeMap (A.derivative.field a)) a := by
  apply hasFDerivAt_iff_tendsto.mpr
  apply squeeze_zero (fun b => mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (norm_nonneg _))
    (g := fun b : Space => A.bound 2*‖b-a‖)
  · intro b
    calc
      _ ≤ ‖b-a‖⁻¹*(A.bound 2*‖b-a‖^2) := mul_le_mul_of_nonneg_left
        (A.taylor_bound a b) (inv_nonneg.mpr (norm_nonneg _))
      _ = A.bound 2*‖b-a‖ := by
        by_cases h : ‖b-a‖ = 0
        · simp only [h, inv_zero, zero_mul, mul_zero]
        · field_simp
  · have hc : Continuous (fun b : Space => A.bound 2*‖b-a‖) := by fun_prop
    simpa only [sub_self, norm_zero, mul_zero] using hc.tendsto a


-- @@ L256-258 verbatim
theorem fderiv_field (A : SpatialFamily K V) :
    fderiv ℝ A.field = fun a => derivativeBundling (A.derivative.field a) :=
  funext (fun a => (A.hasFDerivAt_field a).fderiv)


-- @@ L260-275 verbatim
private theorem contDiff_field_aux (n : ℕ) :
    ∀ (V : Type v) [NormedAddCommGroup V] [NormedSpace ℝ V] (A : SpatialFamily K V),
      ContDiff ℝ n A.field := by
  induction n with
  | zero =>
    intro V _ _ A
    exact contDiff_zero.mpr (continuous_iff_continuousAt.mpr
      (fun a => (A.hasFDerivAt_field a).continuousAt))
  | succ n ih =>
    intro V _ _ A
    rw [Nat.cast_add, Nat.cast_one, contDiff_succ_iff_fderiv]
    refine ⟨fun a => (A.hasFDerivAt_field a).differentiableAt, by simp, ?_⟩
    rw [A.fderiv_field]
    exact (ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := (n : ℕ∞ω))
      (E := C(K,Space →L[ℝ] V)) (F := Space →L[ℝ] C(K,V))
      (derivativeBundling (K := K) (V := V))).comp (ih (Space →L[ℝ] V) A.derivative)


-- @@ L277-279 verbatim
/-- All ordinary pointwise derivatives produce genuine uniform-path smoothness. -/
theorem contDiff_field (A : SpatialFamily K V) : ContDiff ℝ ∞ A.field :=
  contDiff_infty.mpr (fun n => contDiff_field_aux n V A)


-- @@ L281-300 verbatim
private theorem norm_iteratedFDeriv_field_aux (n : ℕ) :
    ∀ (V : Type v) [NormedAddCommGroup V] [NormedSpace ℝ V] (A : SpatialFamily K V) (a : Space),
      ‖iteratedFDeriv ℝ n A.field a‖ ≤ A.bound n := by
  induction n with
  | zero =>
    intro V _ _ A a
    rw [norm_iteratedFDeriv_zero]
    apply (ContinuousMap.norm_le _ (A.bound_nonneg 0)).2
    intro t
    simpa only [norm_iteratedFDeriv_zero] using A.bounded 0 a t
  | succ n ih =>
    intro V _ _ A a
    rw [← norm_iteratedFDeriv_fderiv, A.fderiv_field]
    have h := ContinuousLinearMap.norm_iteratedFDeriv_comp_left (𝕜 := ℝ) (E := Space)
      (F := C(K,Space →L[ℝ] V)) (G := Space →L[ℝ] C(K,V))
      (derivativeBundling (K := K) (V := V))
      (A.derivative.contDiff_field.contDiffAt (x := a)) (n := n) (by simp)
    exact h.trans ((mul_le_mul_of_nonneg_right
      (derivativeBundling_norm_le_one (K := K) (V := V)) (norm_nonneg _)).trans
      (by simpa only [one_mul, derivative_bound] using ih (Space →L[ℝ] V) A.derivative a))


-- @@ L302-305 verbatim
/-- The original pointwise uniform derivative bound holds without any additional factor. -/
theorem norm_iteratedFDeriv_field_le (A : SpatialFamily K V) (n : ℕ) (a : Space) :
    ‖iteratedFDeriv ℝ n A.field a‖ ≤ A.bound n :=
  norm_iteratedFDeriv_field_aux n V A a


-- @@ L307-307 verbatim
end SpatialFamily


-- @@ L309-309 verbatim
end EulerContinuousSpatialFamily


-- @@ L311-311 verbatim
end

-- @@ L312-312 verbatim
end


-- @@ L314-314 verbatim
end


-- @@ L316-316 verbatim
@[expose] public section


-- @@ L318-318 verbatim
noncomputable section


-- @@ L320-320 verbatim
namespace EulerContinuousForcing


-- @@ L322-323 verbatim
open MeasureTheory ContinuousLinearMap EulerSmoothLimit EulerLpTranslation
  EulerLpDerivative EulerContinuousSpatialFamily

-- @@ L324-324 verbatim
open scoped ContDiff


-- @@ L326-327 verbatim
variable {K V : Type*} [TopologicalSpace K] [CompactSpace K]
  [NormedAddCommGroup V] [NormedSpace ℝ V]


-- @@ L329-331 verbatim
/-- Ordinary translation applied to every value of an actual continuous L² path. -/
def translate (a : Space) (f : C(K, L2Space V)) : C(K,L2Space V) :=
  (EulerLpTranslation.translation a).toContinuousLinearMap.compLeftContinuous ℝ K f


-- @@ L333-335 verbatim
omit [CompactSpace K] in
@[simp] theorem translate_apply (a : Space) (f : C(K, L2Space V)) (t : K) :
    translate a f t = EulerLpTranslation.translation a (f t) := rfl


-- @@ L337-339 verbatim
variable (A : K → SmoothL2Field V)
  (hA : ∀ n, Continuous (fun t => (A t).jetLp n))
  (f : C(K, L2Space V)) (hf : ∀ t, f t = (A t).toLp)


-- @@ L341-343 verbatim
/-- The original ordinary spatial jet, as a genuine continuous L² path. -/
def spatialJetPath (n : ℕ) : C(K,L2Space (Space [×n]→L[ℝ] V)) :=
  ⟨fun t => (A t).jetLp n, hA n⟩


-- @@ L345-349 verbatim
/-- The actual translation jets form a continuous path because they are
bounded linear images of the original ordinary L² spatial jets. -/
def orbitJetPath (n : ℕ) (a : Space) : C(K,Space [×n]→L[ℝ] L2Space V) :=
  (multilinearBundling (P := Space) (V := V) volume n).compLeftContinuous ℝ K
    (translate a (spatialJetPath A hA n))


-- @@ L351-359 verbatim
include hf in
omit [CompactSpace K] in
theorem orbitJetPath_eq (n : ℕ) (a : Space) (t : K) :
    orbitJetPath A hA n a t = iteratedFDeriv ℝ n (fun b : Space => translate b f t) a := by
  change multilinearBundling (P := Space) (V := V) volume n
      (EulerLpTranslation.translation a ((A t).jetLp n)) =
    iteratedFDeriv ℝ n (fun b : Space => EulerLpTranslation.translation b (f t)) a
  rw [hf t]
  exact ((A t).iteratedFDeriv_translation_eq n a).symm


-- @@ L361-377 verbatim
/-- This package contains only actual pointwise spatial derivatives and their
original uniform-time L² bounds. -/
def forcingFamily : SpatialFamily K (L2Space V) where
  field a := translate a f
  smooth t := by
    change ContDiff ℝ ∞ (fun a : Space => EulerLpTranslation.translation a (f t))
    rw [hf t]
    exact (A t).translation_contDiff
  jet := orbitJetPath A hA
  jet_eq := orbitJetPath_eq A hA f hf
  bound n := ‖spatialJetPath A hA n‖
  bound_nonneg n := norm_nonneg _
  bounded n a t := by
    change ‖iteratedFDeriv ℝ n (fun b : Space => EulerLpTranslation.translation b (f t)) a‖ ≤ _
    rw [hf t]
    exact ((A t).norm_iteratedFDeriv_translation_le n a).trans
      ((spatialJetPath A hA n).norm_coe_le_norm t)


-- @@ L379-379 verbatim
include hA hf


-- @@ L381-384 verbatim
/-- Literal smooth forcing slices with continuous spatial L² jets have a
genuinely smooth translation orbit in the uniform time norm. -/
theorem forcing_translation_contDiff : ContDiff ℝ ∞ (fun a : Space => translate a f) :=
  (forcingFamily A hA f hf).contDiff_field


-- @@ L386-390 verbatim
/-- Every actual orbit derivative is controlled by the original uniform-time
ordinary L² spatial derivative with constant one. -/
theorem forcing_translation_jet_bound (n : ℕ) (a : Space) :
    ‖iteratedFDeriv ℝ n (fun b : Space => translate b f) a‖ ≤ ‖spatialJetPath A hA n‖ :=
  (forcingFamily A hA f hf).norm_iteratedFDeriv_field_le n a


-- @@ L392-392 verbatim
end EulerContinuousForcing
