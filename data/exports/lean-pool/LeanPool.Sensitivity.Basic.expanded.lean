/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import LeanPool.Sensitivity.Defs


-- @@ L10-24 verbatim
/-!
# Elementary Properties of Sensitivity

Basic bounds and symmetries for the sensitivity of Boolean functions.

## Main results

* `LeanPoolSensitivity.BoolFun.localSensitivity_not` — taking the negation of
  a Boolean function preserves local sensitivity.
* `LeanPoolSensitivity.BoolFun.sensitivity_not` — and likewise sensitivity.
* `LeanPoolSensitivity.BoolFun.localSensitivity_le` — local sensitivity at
  any input is at most `n`.
* `LeanPoolSensitivity.BoolFun.sensitiveAt_flipBit` — the sensitivity
  predicate is invariant under flipping the same coordinate at the input.
-/


-- @@ L26-26 verbatim
@[expose] public section


-- @@ L28-28 verbatim
namespace LeanPoolSensitivity


-- @@ L30-30 verbatim
variable {n : ℕ}


-- @@ L32-32 verbatim
namespace BoolFun


-- @@ L34-50 verbatim
/-- The local sensitivity of the negation of `f` equals the local sensitivity
of `f`. -/
theorem localSensitivity_not (f : BoolFun n) (x : Fin n → Bool) :
    BoolFun.localSensitivity (fun y => !f y) x = f.localSensitivity x := by
  have not_ne_not_iff (a b : Bool) : ((!a) ≠ (!b)) ↔ a ≠ b := by
    constructor
    · intro h hab
      exact h (congrArg (fun z : Bool => !z) hab)
    · intro h hab
      apply h
      have := congrArg (fun z : Bool => !z) hab
      simpa using this
  unfold localSensitivity sensitiveAt
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro i _
  exact not_ne_not_iff (f (flipBit x i)) (f x)


-- @@ L52-55 verbatim
/-- The sensitivity of the negation of `f` equals the sensitivity of `f`. -/
theorem sensitivity_not (f : BoolFun n) :
    BoolFun.sensitivity (fun y => !f y) = f.sensitivity := by
  simp [sensitivity, f.localSensitivity_not]


-- @@ L57-61 verbatim
/-- The local sensitivity of `f` at any input `x` is at most `n`. -/
theorem localSensitivity_le (f : BoolFun n) (x : Fin n → Bool) :
    f.localSensitivity x ≤ n := by
  unfold localSensitivity
  exact (Finset.card_filter_le _ _).trans (by simp)


-- @@ L63-67 verbatim
/-- Unfolding lemma: `f` is sensitive at `x` in coordinate `i` iff flipping
that coordinate changes the value of `f`. -/
theorem sensitiveAt_iff (f : BoolFun n) (x : Fin n → Bool) (i : Fin n) :
    f.sensitiveAt x i ↔ f (flipBit x i) ≠ f x :=
  Iff.rfl


-- @@ L69-74 verbatim
/-- Sensitivity at `x` is symmetric in the following sense: `f` is sensitive
at `x` in direction `i` iff `f` is sensitive at `flipBit x i` in direction
`i`. -/
theorem sensitiveAt_flipBit (f : BoolFun n) (x : Fin n → Bool) (i : Fin n) :
    f.sensitiveAt (flipBit x i) i ↔ f.sensitiveAt x i := by
  simp [sensitiveAt, flipBit_flipBit_same, eq_comm]


-- @@ L76-76 verbatim
end BoolFun


-- @@ L78-78 verbatim
end LeanPoolSensitivity
