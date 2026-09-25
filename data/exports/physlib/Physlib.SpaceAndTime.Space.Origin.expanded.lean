/-
Copyright (c) 2026 Shaopeng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shaopeng Zhu, Joseph Tooby-Smith
-/
module

public import Physlib.SpaceAndTime.Space.Basic


-- @@ L10-21 verbatim
/-!
# The origin of `Space` and the Euclidean chart

The choice of origin for `Space d` is its vector-space zero `(0 : Space d)`. This file provides
that `Zero` instance and the standard chart, isolated so they can be shared by the full module
structure (`Space/Module.lean`) and the Euclidean action (`Space/EuclideanGroup/Action.lean`)
without those depending on each other.

* `(0 : Space d)` — the coordinate origin, the point all of whose coordinates vanish.
* `Space.chartEuclidean` — the standard affine isometry `Space d ≃ᵃⁱ[ℝ] EuclideanSpace ℝ (Fin d)`,
  `p ↦ p -ᵥ 0`, identifying a point with its coordinate vector relative to the origin.
-/


-- @@ L23-23 verbatim
@[expose] public section


-- @@ L25-25 verbatim
namespace Space


-- @@ L27-28 verbatim
instance {d} : Zero (Space d) where
  zero := ⟨fun _ => 0⟩


-- @@ L30-31 verbatim
@[simp]
lemma zero_val {d : ℕ} : (0 : Space d).val = fun _ => 0 := rfl


-- @@ L33-36 verbatim
@[simp]
lemma zero_apply {d : ℕ} (i : Fin d) :
    (0 : Space d) i = 0 := by
  simp [zero_val]


-- @@ L38-40 verbatim
/-- A Euclidean vector, based at the chosen origin, viewed as a point of `Space d`. -/
noncomputable def vectorToSpace {d : ℕ} (v : EuclideanSpace ℝ (Fin d)) : Space d :=
  v +ᵥ (0 : Space d)


-- @@ L42-45 verbatim
@[simp]
lemma vectorToSpace_apply {d : ℕ} (v : EuclideanSpace ℝ (Fin d)) (i : Fin d) :
    vectorToSpace v i = v i := by
  simp [vectorToSpace]


-- @@ L47-51 verbatim
@[simp]
lemma vectorToSpace_vsub_zero {d : ℕ} (v : EuclideanSpace ℝ (Fin d)) :
    vectorToSpace v -ᵥ (0 : Space d) = v := by
  ext i
  simp [vectorToSpace]


-- @@ L53-57 verbatim
/-- The standard chart `Space d ≃ᵃⁱ[ℝ] EuclideanSpace ℝ (Fin d)`, `p ↦ p -ᵥ 0`, identifying a point
with its coordinate vector relative to the origin (the vector-space zero `(0 : Space d)`). -/
noncomputable def chartEuclidean (d : ℕ) :
    Space d ≃ᵃⁱ[ℝ] EuclideanSpace ℝ (Fin d) :=
  (AffineIsometryEquiv.vaddConst ℝ (0 : Space d)).symm


-- @@ L59-60 verbatim
@[simp] lemma chartEuclidean_apply (d : ℕ) (p : Space d) :
    chartEuclidean d p = p -ᵥ (0 : Space d) := rfl


-- @@ L62-62 verbatim
end Space
