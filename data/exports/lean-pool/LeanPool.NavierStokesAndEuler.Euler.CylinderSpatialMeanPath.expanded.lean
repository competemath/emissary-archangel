/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CylinderSpatialMean
import LeanPool.NavierStokesAndEuler.Euler.ParameterSobolevLinear


-- @@ L12-12 verbatim
/-! Continuous-time and same-radius word estimates for the actual spatial mean. -/


-- @@ L14-14 verbatim
@[expose] public section



-- @@ L17-17 verbatim
noncomputable section


-- @@ L19-19 verbatim
namespace EulerCylinderSpatialMean


-- @@ L21-22 verbatim
open Set MeasureTheory ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace
  EulerLpCylinderTranslation EulerCylinderSpatialEmbedding EulerParameterWordGevrey EulerGevrey

-- @@ L23-23 verbatim
open scoped ContDiff


-- @@ L25-27 verbatim
variable (P : ℝ) [Fact (0 < P)]
  {V K : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [TopologicalSpace K] [CompactSpace K]


-- @@ L29-32 verbatim
/-- Cache the standard `NormedAddCommGroup C(K,CylinderL2 P V)` instance to shorten typeclass
synthesis. -/
local instance instCylinderSpatialMeanPath1 : NormedAddCommGroup C(K,CylinderL2 P V) :=
    inferInstance

-- @@ L33-35 verbatim
/-- Cache the standard `NormedSpace ℝ C(K,CylinderL2 P V)` instance to shorten typeclass
synthesis. -/
local instance instCylinderSpatialMeanPath2 : NormedSpace ℝ C(K,CylinderL2 P V) := inferInstance

-- @@ L36-38 verbatim
/-- Cache the standard `NormedAddCommGroup C(K,SpatialL2 V)` instance to shorten typeclass
synthesis. -/
local instance instCylinderSpatialMeanPath3 : NormedAddCommGroup C(K,SpatialL2 V) := inferInstance

-- @@ L39-40 verbatim
/-- Cache the standard `NormedSpace ℝ C(K,SpatialL2 V)` instance to shorten typeclass synthesis. -/
local instance instCylinderSpatialMeanPath4 : NormedSpace ℝ C(K,SpatialL2 V) := inferInstance

-- @@ L41-45 verbatim
/-- Cache the standard `NormedAddCommGroup (C(K,CylinderL2 P V) →L[ℝ] C(K,SpatialL2 V))`
instance to shorten typeclass synthesis. -/
local instance instCylinderSpatialMeanPath5 : NormedAddCommGroup (C(K,CylinderL2 P V) →L[ℝ]
    C(K,SpatialL2 V)) :=
    inferInstance

-- @@ L46-49 verbatim
/-- Cache the standard `NormedSpace ℝ (C(K,CylinderL2 P V) →L[ℝ] C(K,SpatialL2 V))` instance to
shorten typeclass synthesis. -/
local instance instCylinderSpatialMeanPath6 : NormedSpace ℝ (C(K,CylinderL2 P V) →L[ℝ]
    C(K,SpatialL2 V)) := inferInstance


-- @@ L51-53 verbatim
/-- Path mean, given by `(mean P).compLeftContinuous ℝ K`. -/
def pathMean : C(K,CylinderL2 P V) →L[ℝ] C(K,SpatialL2 V) :=
  (mean P).compLeftContinuous ℝ K


-- @@ L55-57 verbatim
omit [CompactSpace K] in
@[simp] theorem pathMean_apply (p : C(K, CylinderL2 P V)) (t : K) :
    pathMean P p t = mean P (p t) := rfl


-- @@ L59-62 verbatim
/-- Spatial path translation, given by `(EulerLpTranslation.translation
a).toContinuousLinearMap.compLeftContinuous ℝ K`. -/
def spatialPathTranslation (a : Space) : C(K,SpatialL2 V) →L[ℝ] C(K,SpatialL2 V) :=
  (EulerLpTranslation.translation a).toContinuousLinearMap.compLeftContinuous ℝ K


-- @@ L64-69 verbatim
omit [CompactSpace K] in
theorem pathMean_translation (p : C(K, CylinderL2 P V)) (a : LiftTangent) :
    pathMean P (pathTranslate P a p) = spatialPathTranslation a.1 (pathMean P p) := by
  apply ContinuousMap.ext
  intro t
  exact mean_translate P a (p t)


-- @@ L71-79 verbatim
theorem pathMean_norm : ‖pathMean (K := K) (V := V) P‖ ≤ P⁻¹*Real.sqrt P := by
  have hc : 0 ≤ P⁻¹*Real.sqrt P :=
    mul_nonneg (inv_nonneg.mpr (le_of_lt (Fact.out : 0 < P))) (Real.sqrt_nonneg P)
  apply opNorm_le_bound _ hc
  intro p
  apply (ContinuousMap.norm_le _ (mul_nonneg hc (norm_nonneg p))).mpr
  intro t
  exact ((mean (V := V) P).le_of_opNorm_le (mean_norm P) (p t)).trans
    (mul_le_mul_of_nonneg_left (p.norm_coe_le_norm t) hc)


-- @@ L81-87 verbatim
/-- All ordinary spatial derivatives of the mean are inherited from the actual mixed orbit. -/
theorem pathMean_orbit_contDiff (p : C(K, CylinderL2 P V))
    (hp : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a p)) :
    ContDiff ℝ ∞ (fun a : Space => spatialPathTranslation a (pathMean P p)) := by
  have h := (pathMean (K := K) (V := V) P).contDiff.comp
    (hp.comp (contDiff_id.prodMk (contDiff_const : ContDiff ℝ ∞ (fun _ : Space => (0 : ℝ)))))
  simpa only [Function.comp_def, pathMean_translation, id_eq] using h


-- @@ L89-89 verbatim
variable {X ι : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [Fintype ι]


-- @@ L91-97 verbatim
theorem pathMean_block_bound (directions : ι → X) (q : ℕ)
    (f : X → C(K, CylinderL2 P V)) (hf : ContDiff ℝ ∞ f) (n : ℕ) (x : X) :
    block directions q (fun y => pathMean P (f y)) n x ≤
      (P⁻¹*Real.sqrt P)*block directions q f n x := by
  have h := block_comp_clm_le (E := C(K,CylinderL2 P V)) (F := C(K,SpatialL2 V))
    directions q (pathMean (K := K) (V := V) P) f hf n x
  exact h.trans (mul_le_mul_of_nonneg_right (pathMean_norm P) (block_nonneg directions q f n x))


-- @@ L99-107 verbatim
theorem pathMean_block_majorant (directions : ι → X) (q : ℕ)
    (f : X → C(K, CylinderL2 P V)) (hf : ContDiff ℝ ∞ f) (R C : ℝ) (d : ℕ)
    (hb : ∀ n x, block directions q f n x ≤ C * majorant R d n) (n : ℕ) (x : X) :
    block directions q (fun y => pathMean P (f y)) n x ≤
      ((P⁻¹*Real.sqrt P)*C)*majorant R d n :=
  (pathMean_block_bound P directions q f hf n x).trans
    ((mul_le_mul_of_nonneg_left (hb n x)
      (mul_nonneg (inv_nonneg.mpr (le_of_lt (Fact.out : 0 < P))) (Real.sqrt_nonneg P))).trans_eq
      (mul_assoc (P⁻¹*Real.sqrt P) C _).symm)


-- @@ L109-109 verbatim
end EulerCylinderSpatialMean
