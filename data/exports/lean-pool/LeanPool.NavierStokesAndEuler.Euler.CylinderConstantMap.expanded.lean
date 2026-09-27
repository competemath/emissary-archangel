/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.LpCylinderTranslation


-- @@ L11-11 verbatim
/-! Fixed bounded maps on actual cylinder L² classes and continuous paths. -/


-- @@ L13-13 verbatim
@[expose] public section



-- @@ L16-16 verbatim
noncomputable section


-- @@ L18-18 verbatim
namespace EulerCylinderConstantMap


-- @@ L20-21 verbatim
open Set MeasureTheory ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace
  EulerLpCylinderTranslation

-- @@ L22-22 verbatim
open scoped ContDiff


-- @@ L24-26 verbatim
variable (period : ℝ) [Fact (0 < period)]
  {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]


-- @@ L28-30 verbatim
/-- Map, given by `L.compLpL 2 (liftMeasure period)`. -/
def map (L : E →L[ℝ] F) : CylinderL2 period E →L[ℝ] CylinderL2 period F :=
  L.compLpL 2 (liftMeasure period)


-- @@ L32-33 verbatim
theorem map_ae (L : E →L[ℝ] F) (u : CylinderL2 period E) :
    map period L u =ᵐ[liftMeasure period] fun x => L (u x) := L.coeFn_compLpL u


-- @@ L35-35 verbatim
theorem map_norm (L : E →L[ℝ] F) : ‖map period L‖ ≤ ‖L‖ := L.norm_compLpL_le


-- @@ L37-44 verbatim
theorem map_comp (L : F →L[ℝ] G) (M : E →L[ℝ] F) :
    map period (L.comp M) = (map period L).comp (map period M) := by
  apply ContinuousLinearMap.ext
  intro u
  apply Lp.ext
  filter_upwards [map_ae period (L.comp M) u,map_ae period L (map period M u),map_ae period M u]
    with x hl hr hm
  exact hl.trans ((congrArg L hm).symm.trans hr.symm)


-- @@ L46-50 verbatim
@[simp] theorem map_id : map period (ContinuousLinearMap.id ℝ E) =
    ContinuousLinearMap.id ℝ (CylinderL2 period E) := by
  apply ContinuousLinearMap.ext
  intro u
  exact Lp.ext (map_ae period (ContinuousLinearMap.id ℝ E) u)


-- @@ L52-59 verbatim
theorem map_translation (L : E →L[ℝ] F) (a : LiftTangent) (u : CylinderL2 period E) :
    map period L (translate period a u) = translate period a (map period L u) := by
  apply Lp.ext
  filter_upwards [map_ae period L (translate period a u),translate_ae period a u,
    translate_ae period a (map period L u),
    (measurePreserving_translation period (coveringMap period a)).quasiMeasurePreserving.ae
      (map_ae period L u)] with x hl hu hr hm
  exact hl.trans ((congrArg L hu).trans (hm.symm.trans hr.symm))


-- @@ L61-61 verbatim
variable {K : Type*} [TopologicalSpace K] [CompactSpace K]


-- @@ L63-65 verbatim
/-- Path map, given by `(map period L).compLeftContinuous ℝ K`. -/
def pathMap (L : E →L[ℝ] F) : C(K,CylinderL2 period E) →L[ℝ] C(K,CylinderL2 period F) :=
  (map period L).compLeftContinuous ℝ K


-- @@ L67-69 verbatim
omit [CompactSpace K] in
@[simp] theorem pathMap_apply (L : E →L[ℝ] F) (u : C(K, CylinderL2 period E)) (t : K) :
    pathMap period L u t = map period L (u t) := rfl


-- @@ L71-78 verbatim
theorem pathMap_norm (L : E →L[ℝ] F) : ‖pathMap (K := K) period L‖ ≤ ‖L‖ := by
  apply opNorm_le_bound _ (norm_nonneg L)
  intro u
  apply (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg L) (norm_nonneg u))).2
  intro t
  exact ((map period L).le_opNorm (u t)).trans
    ((mul_le_mul_of_nonneg_right (map_norm period L) (norm_nonneg (u t))).trans
      (mul_le_mul_of_nonneg_left (u.norm_coe_le_norm t) (norm_nonneg L)))


-- @@ L80-85 verbatim
omit [CompactSpace K] in
theorem pathMap_translation (L : E →L[ℝ] F) (a : LiftTangent) (u : C(K, CylinderL2 period E)) :
    pathMap period L (pathTranslate period a u) = pathTranslate period a (pathMap period L u) := by
  apply ContinuousMap.ext
  intro t
  exact map_translation period L a (u t)


-- @@ L87-94 verbatim
theorem pathMap_orbit_contDiff (L : E →L[ℝ] F) (u : C(K, CylinderL2 period E))
    (hu : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate period a u)) :
    ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate period a (pathMap period L u)) := by
  have he : (fun a : LiftTangent => pathTranslate period a (pathMap period L u)) =
      (fun a => pathMap period L (pathTranslate period a u)) :=
    funext (fun a => (pathMap_translation period L a u).symm)
  rw [he]
  exact (pathMap period L).contDiff.comp hu


-- @@ L96-96 verbatim
end EulerCylinderConstantMap
