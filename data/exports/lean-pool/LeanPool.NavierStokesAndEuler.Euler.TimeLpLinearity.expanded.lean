/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TimeLp


-- @@ L11-11 verbatim
/-! The actual continuous-path embedding as a bounded linear time-space map. -/


-- @@ L13-13 verbatim
@[expose] public section



-- @@ L16-16 verbatim
noncomputable section


-- @@ L18-18 verbatim
namespace EulerTimeLp


-- @@ L20-20 verbatim
open MeasureTheory Set EulerVolterraConvolution

-- @@ L21-21 verbatim
open scoped Topology


-- @@ L23-23 verbatim
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]


-- @@ L25-34 verbatim
omit [NormedSpace ℝ E] in
/-- The actual continuous-path inclusion preserves addition. -/
theorem pathLp_add (T : ℝ) (hT : 0 ≤ T) (f g : C(Icc (0 : ℝ) T, E)) :
    pathLp T hT (f+g) = pathLp T hT f+pathLp T hT g := by
  apply Lp.ext
  filter_upwards [pathLp_ae T hT (f+g), pathLp_ae T hT f, pathLp_ae T hT g,
    Lp.coeFn_add (pathLp T hT f) (pathLp T hT g)] with t h1 h2 h3 h4
  simp only [Pi.add_apply] at h4
  rw [h1, h4, h2, h3]
  rfl


-- @@ L36-44 verbatim
/-- The actual continuous-path inclusion preserves real scalar multiplication. -/
theorem pathLp_smul (T : ℝ) (hT : 0 ≤ T) (r : ℝ) (f : C(Icc (0 : ℝ) T, E)) :
    pathLp T hT (r • f) = r • pathLp T hT f := by
  apply Lp.ext
  filter_upwards [pathLp_ae T hT (r • f), pathLp_ae T hT f,
    Lp.coeFn_smul r (pathLp T hT f)] with t h1 h2 h3
  simp only [Pi.smul_apply] at h3
  rw [h1, h3, h2]
  rfl


-- @@ L46-52 verbatim
/-- The genuine continuous-path to Bochner L² embedding is a bounded linear map. -/
def pathLpOperator (T : ℝ) (hT : 0 ≤ T) : C(Icc (0 : ℝ) T, E) →L[ℝ] TimeLp T E :=
  ({ toFun := pathLp T hT
     map_add' := pathLp_add T hT
     map_smul' := fun r f => by simpa only [RingHom.id_apply] using pathLp_smul T hT r f } :
      C(Icc (0 : ℝ) T, E) →ₗ[ℝ] TimeLp T E).mkContinuous
    ((measureUnivNNReal (timeMeasure T) : ℝ) ^ (1/2 : ℝ)) (pathLp_bound T hT)


-- @@ L54-56 verbatim
/-- The bounded embedding is exactly the actual L² equivalence class of the path. -/
theorem pathLpOperator_apply (T : ℝ) (hT : 0 ≤ T) (f : C(Icc (0 : ℝ) T, E)) :
    pathLpOperator T hT f = pathLp T hT f := rfl


-- @@ L58-58 verbatim
end EulerTimeLp
