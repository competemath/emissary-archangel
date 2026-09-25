/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Joseph Tooby-Smith
-/
module

public import Physlib.SpaceAndTime.SpaceTime.Basic
public import Physlib.Relativity.Tensors.RealTensor.Vector.Causality.LightLike
public import Physlib.Relativity.Tensors.RealTensor.Vector.Causality.TimeLike

-- @@ L11-16 verbatim
/-!
# Proper Time

This file introduces 4d Minkowski spacetime.

-/


-- @@ L18-18 verbatim
@[expose] public section


-- @@ L20-20 verbatim
noncomputable section


-- @@ L22-22 verbatim
namespace SpaceTime


-- @@ L24-24 verbatim
open Manifold

-- @@ L25-25 verbatim
open Matrix

-- @@ L26-26 verbatim
open Real

-- @@ L27-27 verbatim
open ComplexConjugate

-- @@ L28-28 verbatim
open Lorentz

-- @@ L29-29 verbatim
open Vector


-- @@ L31-34 verbatim
/-- The proper time from `q` to `p`. Defaults to zero if `p` and `q`
  have a space-like separation. -/
def properTime {d : ℕ} (q p : SpaceTime d) : ℝ :=
  √⟪p - q, p - q⟫ₘ


-- @@ L36-41 verbatim
lemma properTime_pos_ofTimeLike {d : ℕ} (q p : SpaceTime d)
    (h : causalCharacter (p - q) = .timeLike) :
    0 < properTime q p := by
  rw [properTime]
  refine sqrt_pos_of_pos ?_
  exact (timeLike_iff_norm_sq_pos (p - q)).mp h


-- @@ L43-48 verbatim
lemma properTime_zero_ofLightLike {d : ℕ} (q p : SpaceTime d)
    (h : causalCharacter (p - q) = .lightLike) :
    properTime q p = 0 := by
  rw [properTime]
  rw [lightLike_iff_norm_sq_zero] at h
  simp only [h, sqrt_zero]


-- @@ L50-55 verbatim
lemma properTime_zero_ofSpaceLike {d : ℕ} (q p : SpaceTime d)
    (h : causalCharacter (p - q) = .spaceLike) :
    properTime q p = 0 := by
  rw [properTime]
  rw [spaceLike_iff_norm_sq_neg] at h
  exact sqrt_eq_zero'.mpr (le_of_lt h)


-- @@ L57-57 verbatim
end SpaceTime


-- @@ L59-59 verbatim
end
