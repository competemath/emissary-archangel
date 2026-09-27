/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CylinderScalarClassical
import LeanPool.NavierStokesAndEuler.Euler.AnglePrimitiveParity


-- @@ L12-12 verbatim
/-! The normalized scalar angular primitive converts joint odd parity to even parity. -/


-- @@ L14-14 verbatim
@[expose] public section



-- @@ L17-17 verbatim
noncomputable section


-- @@ L19-19 verbatim
namespace EulerCylinderScalarPrimitive


-- @@ L21-21 verbatim
open Set MeasureTheory EulerSmoothLimit EulerLiftedGradientSpace EulerAngleMeanZeroPrimitive


-- @@ L23-24 verbatim
variable (P : ℝ) [Fact (0 < P)] (f : LiftDomain P → ℝ) (hf : Continuous f)
  (hmean : ∀ y, (∫ s in (0 : ℝ)..P, f (y, (s : AddCircle P))) = 0)


-- @@ L26-39 verbatim
theorem classicalPrimitive_joint_even
    (hodd : ∀ y θ, f (-y, ((-θ : ℝ) : AddCircle P)) = -f (y, (θ : AddCircle P)))
    (y : Space) (θ : ℝ) :
    classicalPrimitive P f hf hmean (-y,((-θ : ℝ) : AddCircle P)) =
      classicalPrimitive P f hf hmean (y,(θ : AddCircle P)) := by
  rw [classicalPrimitive_cover,classicalPrimitive_cover]
  have he : (fun s : ℝ => f (-y,(s : AddCircle P))) = fun s => -f (y,((-s : ℝ) : AddCircle P)) := by
    funext s
    simpa only [neg_neg] using hodd y (-s)
  rw [he,primitive_reflection P (Fact.out : 0 < P).ne'
    (fun s : ℝ => f (y,(s : AddCircle P)))
    (hf.comp (continuous_const.prodMk (AddCircle.continuous_mk' P)))
    (scalarAngle_periodic P f y) (hmean y)]
  simp only [neg_neg]


-- @@ L41-41 verbatim
end EulerCylinderScalarPrimitive
