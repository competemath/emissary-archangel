/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.LpCylinderTranslation
public import LeanPool.NavierStokesAndEuler.Euler.TimeLpBoundedMap


-- @@ L12-12 verbatim
/-! The adjoint of the genuine mixed cylinder translation is its inverse. -/


-- @@ L14-14 verbatim
@[expose] public section



-- @@ L17-17 verbatim
noncomputable section


-- @@ L19-19 verbatim
namespace EulerLpCylinderTranslation


-- @@ L21-21 verbatim
open ContinuousLinearMap InnerProductSpace EulerLiftedGradientSpace


-- @@ L23-24 verbatim
variable (P : ℝ) [Fact (0 < P)] {V : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]


-- @@ L26-36 verbatim
theorem translate_adjoint (a : LiftTangent) :
    ((translate (V := V) P a).toContinuousLinearMap).adjoint =
      (translate P (-a)).toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro u
  apply ext_inner_right ℝ
  intro v
  rw [adjoint_inner_left]
  change ⟪u,translate P a v⟫_ℝ = ⟪translate P (-a) u,v⟫_ℝ
  simpa only [translate_add,add_neg_cancel,translate_zero] using
    (translate (V := V) P a).inner_map_map (translate P (-a) u) v


-- @@ L38-38 verbatim
end EulerLpCylinderTranslation


-- @@ L40-40 verbatim
namespace EulerTimeLpBoundedMap


-- @@ L42-42 verbatim
open Set MeasureTheory ContinuousLinearMap EulerTimeLp EulerVolterraConvolution


-- @@ L44-45 verbatim
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]


-- @@ L47-56 verbatim
/-- The actual continuous-time embedding commutes with bounded spatial maps. -/
theorem pathLp_timeLift (T : ℝ) (hT : 0 ≤ T) (A : E →L[ℝ] F)
    (f : C(Icc (0 : ℝ) T, E)) :
    pathLp T hT ((A.compLeftContinuous ℝ (Icc (0 : ℝ) T)) f) =
      timeLift T A (pathLp T hT f) := by
  apply Lp.ext
  filter_upwards [pathLp_ae T hT ((A.compLeftContinuous ℝ (Icc (0 : ℝ) T)) f),
    timeLift_ae T A (pathLp T hT f),pathLp_ae T hT f] with t hl hr hf
  rw [hl,hr,hf]
  rfl


-- @@ L58-58 verbatim
end EulerTimeLpBoundedMap
