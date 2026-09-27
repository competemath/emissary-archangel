/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.AngleMeanZeroPrimitive


-- @@ L11-11 verbatim
/-! Bounded linear maps commute with the literal normalized angular integral. -/


-- @@ L13-13 verbatim
@[expose] public section



-- @@ L16-16 verbatim
noncomputable section


-- @@ L18-18 verbatim
namespace EulerAngleMeanZeroPrimitive


-- @@ L20-20 verbatim
open MeasureTheory ContinuousLinearMap


-- @@ L22-23 verbatim
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]


-- @@ L25-27 verbatim
theorem rawPrimitive_map (L : E →L[ℝ] F) (f : ℝ → E) (hf : Continuous f) (θ : ℝ) :
    L (rawPrimitive f θ) = rawPrimitive (fun s => L (f s)) θ :=
  (L.intervalIntegral_comp_comm (hf.intervalIntegrable 0 θ)).symm


-- @@ L29-34 verbatim
theorem primitive_map (L : E →L[ℝ] F) (P : ℝ) (f : ℝ → E) (hf : Continuous f) (θ : ℝ) :
    L (primitive P f θ) = primitive P (fun s => L (f s)) θ := by
  unfold primitive
  rw [map_sub,map_smul,← L.intervalIntegral_comp_comm
    ((rawPrimitive_continuous f hf).intervalIntegrable 0 P),rawPrimitive_map L f hf θ]
  simp only [rawPrimitive_map L f hf]


-- @@ L36-36 verbatim
end EulerAngleMeanZeroPrimitive
