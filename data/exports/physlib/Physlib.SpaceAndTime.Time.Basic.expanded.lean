/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Mathlib.Data.Real.Basic
public import Mathlib.LinearAlgebra.AffineSpace.Defs

-- @@ L10-21 verbatim
/-!
# Time

`Time` represents instants with a fixed but arbitrary unit and orientation. It is an
affine space over `ℝ`: two instants determine a real-valued elapsed time, and adding
such a duration to an instant produces another instant. There is no distinguished zero.

The field `Time.val` is an implementation coordinate, not a frame-relative time
coordinate. A reference frame chooses its own time origin. Import
`Physlib.SpaceAndTime.Time.InnerProductSpace` to use the inner product space structure with the
implicit origin `Time.mk 0`, including addition of instants, norms, and derivatives.
-/


-- @@ L23-23 verbatim
@[expose] public section


-- @@ L25-27 verbatim
/-!
# A. The `Time` type
-/


-- @@ L29-33 verbatim
/-- An instant in time with a given unit and orientation, but no distinguished origin. -/
@[ext]
structure Time where
  /-- The implementation coordinate associated with an instant. -/
  val : ℝ


-- @@ L35-35 verbatim
namespace Time


-- @@ L37-37 verbatim
lemma val_injective : Function.Injective val := fun _ _ h => Time.ext h


-- @@ L39-39 verbatim
instance : Nonempty Time := ⟨⟨0⟩⟩


-- @@ L41-43 verbatim
/-!
# B. The affine structure
-/


-- @@ L45-46 verbatim
instance : VAdd ℝ Time where
  vadd dt t := ⟨dt + t.val⟩


-- @@ L48-49 verbatim
@[simp]
lemma vadd_val (dt : ℝ) (t : Time) : (dt +ᵥ t).val = dt + t.val := rfl


-- @@ L51-52 verbatim
instance : VSub ℝ Time where
  vsub t₁ t₂ := t₁.val - t₂.val


-- @@ L54-55 verbatim
@[simp]
lemma vsub_eq_val (t₁ t₂ : Time) : t₁ -ᵥ t₂ = t₁.val - t₂.val := rfl


-- @@ L57-61 verbatim
instance : AddTorsor ℝ Time where
  zero_vadd t := by ext; simp
  add_vadd dt₁ dt₂ t := by ext; simp [add_assoc]
  vsub_vadd' t₁ t₂ := by ext; simp
  vadd_vsub' dt t := by simp


-- @@ L63-63 verbatim
end Time
