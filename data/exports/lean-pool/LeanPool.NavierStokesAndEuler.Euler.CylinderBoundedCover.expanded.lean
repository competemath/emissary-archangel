/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CylinderSobolevOrbit
public import LeanPool.NavierStokesAndEuler.Euler.CylinderTimeRegularity


-- @@ L12-14 verbatim
/-! The real periodic lift of a genuine cylinder H3 field is bounded and
continuous. This construction uses the cylinder norm, never an L² norm on
the full real covering space. -/


-- @@ L16-16 verbatim
@[expose] public section



-- @@ L19-19 verbatim
noncomputable section



-- @@ L22-22 verbatim
namespace EulerCylinderBoundedCover


-- @@ L24-25 verbatim
open Set MeasureTheory ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace
  EulerCylinderSobolevSpace EulerCylinderSmoothOrbit EulerLpCylinderTranslation

-- @@ L26-26 verbatim
open scoped ContDiff BoundedContinuousFunction


-- @@ L28-28 verbatim
variable (P : ℝ) [Fact (0 < P)]


-- @@ L30-32 verbatim
/-- Cache the standard `NormedAddCommGroup (SobolevSpace P 3)` instance to shorten typeclass
synthesis. -/
local instance instCylinderBoundedCover1 : NormedAddCommGroup (SobolevSpace P 3) := inferInstance

-- @@ L33-35 verbatim
/-- Cache the standard `NormedSpace ℝ (SobolevSpace P 3)` instance to shorten typeclass
synthesis. -/
local instance instCylinderBoundedCover2 : NormedSpace ℝ (SobolevSpace P 3) := inferInstance

-- @@ L36-39 verbatim
/-- Cache the standard `NormedAddCommGroup (LiftTangent →ᵇ Space)` instance to shorten typeclass
synthesis. -/
local instance instCylinderBoundedCover3 : NormedAddCommGroup (LiftTangent →ᵇ Space) :=
    inferInstance

-- @@ L40-42 verbatim
/-- Cache the standard `NormedSpace ℝ (LiftTangent →ᵇ Space)` instance to shorten typeclass
synthesis. -/
local instance instCylinderBoundedCover4 : NormedSpace ℝ (LiftTangent →ᵇ Space) := inferInstance


-- @@ L44-51 verbatim
/-- Cover, constructed using `BoundedContinuousFunction.ofNormedAddCommGroup`. -/
def cover (u : SobolevSpace P 3) : LiftTangent →ᵇ Space :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x => EulerSobolevPointEvaluation.pointEvaluation P (coveringMap P x) u)
    ((EulerSobolevPointEvaluation.representative_continuous P u).comp
      (coveringMap_isOpenQuotient P).continuous)
    (sobolevEmbeddingConstant P 3 * ‖u‖)
    (fun x => EulerSobolevPointEvaluation.representative_bound P u (coveringMap P x))


-- @@ L53-54 verbatim
@[simp] theorem cover_apply (u : SobolevSpace P 3) (x : LiftTangent) :
    cover P u x = EulerSobolevPointEvaluation.pointEvaluation P (coveringMap P x) u := rfl


-- @@ L56-61 verbatim
theorem cover_norm_le (u : SobolevSpace P 3) :
    ‖cover P u‖ ≤ sobolevEmbeddingConstant P 3 * ‖u‖ := by
  apply (BoundedContinuousFunction.norm_le
    (mul_nonneg (sobolevEmbeddingConstant_nonneg P 3) (norm_nonneg u))).2
  intro x
  exact EulerSobolevPointEvaluation.representative_bound P u (coveringMap P x)


-- @@ L63-73 verbatim
/-- Cover linear, bundling `toFun`, `map_add`, `map_smul`. -/
def coverLinear : SobolevSpace P 3 →ₗ[ℝ] (LiftTangent →ᵇ Space) where
  toFun := cover P
  map_add' u v := by
    apply BoundedContinuousFunction.ext
    intro x
    exact (EulerSobolevPointEvaluation.pointEvaluation P (coveringMap P x)).map_add u v
  map_smul' c u := by
    apply BoundedContinuousFunction.ext
    intro x
    exact (EulerSobolevPointEvaluation.pointEvaluation P (coveringMap P x)).map_smul c u


-- @@ L75-79 verbatim
/-- Cover map, bundling `toLinearMap`, `cont`. -/
def coverMap : SobolevSpace P 3 →L[ℝ] (LiftTangent →ᵇ Space) where
  toLinearMap := coverLinear P
  cont := AddMonoidHomClass.continuous_of_bound (coverLinear P)
    (sobolevEmbeddingConstant P 3) (cover_norm_le P)


-- @@ L81-83 verbatim
theorem coverMap_norm_le : ‖coverMap P‖ ≤ sobolevEmbeddingConstant P 3 := by
  apply opNorm_le_bound _ (sobolevEmbeddingConstant_nonneg P 3)
  exact cover_norm_le P


-- @@ L85-85 verbatim
variable {K : Type*} [TopologicalSpace K] [CompactSpace K]


-- @@ L87-90 verbatim
/-- Cache the standard `NormedAddCommGroup C(K, SobolevSpace P 3)` instance to shorten typeclass
synthesis. -/
local instance instCylinderBoundedCover5 : NormedAddCommGroup C(K, SobolevSpace P 3) :=
    inferInstance

-- @@ L91-93 verbatim
/-- Cache the standard `NormedSpace ℝ C(K, SobolevSpace P 3)` instance to shorten typeclass
synthesis. -/
local instance instCylinderBoundedCover6 : NormedSpace ℝ C(K, SobolevSpace P 3) := inferInstance

-- @@ L94-97 verbatim
/-- Cache the standard `NormedAddCommGroup C(K, LiftTangent →ᵇ Space)` instance to shorten
typeclass synthesis. -/
local instance instCylinderBoundedCover7 : NormedAddCommGroup C(K, LiftTangent →ᵇ Space) :=
    inferInstance

-- @@ L98-100 verbatim
/-- Cache the standard `NormedSpace ℝ C(K, LiftTangent →ᵇ Space)` instance to shorten typeclass
synthesis. -/
local instance instCylinderBoundedCover8 : NormedSpace ℝ C(K, LiftTangent →ᵇ Space) := inferInstance


-- @@ L102-104 verbatim
/-- Cover path map, given by `(coverMap P).compLeftContinuous ℝ K`. -/
def coverPathMap : C(K, SobolevSpace P 3) →L[ℝ] C(K, LiftTangent →ᵇ Space) :=
  (coverMap P).compLeftContinuous ℝ K


-- @@ L106-114 verbatim
theorem coverPathMap_norm_le :
    ‖coverPathMap (K := K) P‖ ≤ sobolevEmbeddingConstant P 3 := by
  apply opNorm_le_bound _ (sobolevEmbeddingConstant_nonneg P 3)
  intro p
  apply (ContinuousMap.norm_le _
    (mul_nonneg (sobolevEmbeddingConstant_nonneg P 3) (norm_nonneg p))).2
  intro t
  exact (cover_norm_le P (p t)).trans
    (mul_le_mul_of_nonneg_left (p.norm_coe_le_norm t) (sobolevEmbeddingConstant_nonneg P 3))


-- @@ L116-119 verbatim
/-- Cover path, given by `coverPathMap P (sobolevPath P 3 p hp)`. -/
def coverPath (p : C(K, LiftL2 P))
    (hp : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a p)) :
    C(K, LiftTangent →ᵇ Space) := coverPathMap P (sobolevPath P 3 p hp)


-- @@ L121-124 verbatim
@[simp] theorem coverPath_apply (p : C(K, LiftL2 P))
    (hp : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a p))
    (t : K) (x : LiftTangent) :
    coverPath P p hp t x = pointField P p hp t (coveringMap P x) := rfl


-- @@ L126-130 verbatim
/-- Cover orbit, given by `coverPathMap P (sobolevOrbit P 3 p hp a)`. -/
def coverOrbit (p : C(K, LiftL2 P))
    (hp : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a p))
    (a : LiftTangent) : C(K, LiftTangent →ᵇ Space) :=
  coverPathMap P (sobolevOrbit P 3 p hp a)


-- @@ L132-137 verbatim
theorem coverOrbit_contDiff (p : C(K, LiftL2 P))
    (hp : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a p)) :
    ContDiff ℝ ∞ (coverOrbit P p hp) :=
  (ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := ∞)
    (E := C(K, SobolevSpace P 3)) (F := C(K, LiftTangent →ᵇ Space))
    (coverPathMap (K := K) P)).comp (sobolevOrbit_contDiff P 3 p hp)


-- @@ L139-157 verbatim
theorem coverOrbit_apply (p : C(K, LiftL2 P))
    (hp : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a p))
    (a : LiftTangent) (t : K) (x : LiftTangent) :
    coverOrbit P p hp a t x = coverPath P p hp t (x+a) := by
  have hc : Continuous (pointField P p hp t) :=
    EulerSobolevPointEvaluation.representative_continuous P (sobolevPath P 3 p hp t)
  have he := EulerSobolevPointEvaluation.pointEvaluation_eq P (coveringMap P x)
    (sobolevOrbit P 3 p hp a t)
    (fun y => pointField P p hp t (y + coveringMap P a))
    (hc.comp (continuous_id.add continuous_const))
    (by
      rw [sobolevOrbit_value]
      exact (translate_ae P a (p t)).trans
        ((measurePreserving_translation P (coveringMap P a)).quasiMeasurePreserving.ae
          (pointField_ae P p hp t)))
  change EulerSobolevPointEvaluation.pointEvaluation P (coveringMap P x)
    (sobolevOrbit P 3 p hp a t) = pointField P p hp t (coveringMap P (x+a))
  rw [coveringMap_add]
  exact he


-- @@ L159-166 verbatim
@[simp] theorem coverOrbit_zero (p : C(K, LiftL2 P))
    (hp : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a p)) :
    coverOrbit P p hp 0 = coverPath P p hp := by
  apply ContinuousMap.ext
  intro t
  apply BoundedContinuousFunction.ext
  intro x
  simpa only [add_zero] using coverOrbit_apply P p hp 0 t x


-- @@ L168-168 verbatim
end EulerCylinderBoundedCover
