/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Finset.Lattice.Fold


-- @@ L11-29 verbatim
/-!
# Boolean Function Definitions

Core definitions for Boolean functions on the hypercube `Fin n → Bool`,
including bit flips, sensitivity, and local sensitivity.

## Main definitions

* `LeanPoolSensitivity.BoolFun` — a Boolean function on `n` variables.
* `LeanPoolSensitivity.flipBit` — flip the `i`-th coordinate of an input.
* `LeanPoolSensitivity.BoolFun.sensitiveAt` — predicate: `f` changes value when
  flipping coordinate `i` at input `x`.
* `LeanPoolSensitivity.BoolFun.localSensitivity` — the number of sensitive
  coordinates of `f` at a given input.
* `LeanPoolSensitivity.BoolFun.sensitivity` — the maximum local sensitivity
  over all inputs.
* `LeanPoolSensitivity.flipCoords` — flip all bits inside a finite set of
  coordinates simultaneously.
-/


-- @@ L31-31 verbatim
@[expose] public section


-- @@ L33-33 verbatim
namespace LeanPoolSensitivity


-- @@ L35-37 verbatim
/-- A Boolean function on `n` variables, viewed as a map
`(Fin n → Bool) → Bool`. -/
abbrev BoolFun (n : ℕ) := (Fin n → Bool) → Bool


-- @@ L39-39 verbatim
variable {n : ℕ}


-- @@ L41-44 verbatim
/-- Flip the `i`-th bit of an input `x : Fin n → Bool`, leaving all other
coordinates fixed. -/
def flipBit (x : Fin n → Bool) (i : Fin n) : Fin n → Bool :=
  Function.update x i (!x i)


-- @@ L46-49 verbatim
@[simp]
theorem flipBit_apply_same (x : Fin n → Bool) (i : Fin n) :
    flipBit x i i = !x i := by
  simp [flipBit]


-- @@ L51-54 verbatim
@[simp]
theorem flipBit_apply_ne (x : Fin n → Bool) (i : Fin n) {j : Fin n} (h : j ≠ i) :
    flipBit x i j = x j := by
  simp [flipBit, Function.update_of_ne h]


-- @@ L56-60 verbatim
@[simp]
theorem flipBit_flipBit_same (x : Fin n → Bool) (i : Fin n) :
    flipBit (flipBit x i) i = x := by
  ext j
  by_cases h : j = i <;> simp [flipBit, Function.update_of_ne, h, Bool.not_not]


-- @@ L62-66 verbatim
/-- `flipBit x i` is never equal to `x` itself: the `i`-th coordinate
differs. -/
theorem flipBit_ne_self (x : Fin n → Bool) (i : Fin n) :
    flipBit x i ≠ x := by
  intro h; simp [flipBit] at h


-- @@ L68-74 verbatim
/-- Different coordinates produce different bit flips of `x`. -/
theorem flipBit_injective (x : Fin n → Bool) : Function.Injective (flipBit x) := by
  intro i j hij
  by_contra h
  have h1 := flipBit_apply_same x i
  rw [congr_fun hij i, flipBit_apply_ne x j h] at h1
  simp at h1


-- @@ L76-76 verbatim
namespace BoolFun


-- @@ L78-81 verbatim
/-- `f` is sensitive at input `x` in coordinate `i` when flipping bit `i`
changes the value of `f`. -/
def sensitiveAt (f : BoolFun n) (x : Fin n → Bool) (i : Fin n) : Prop :=
  f (flipBit x i) ≠ f x


-- @@ L83-85 verbatim
instance (f : BoolFun n) (x : Fin n → Bool) (i : Fin n) :
    Decidable (f.sensitiveAt x i) :=
  inferInstanceAs (Decidable (f (flipBit x i) ≠ f x))


-- @@ L87-90 verbatim
/-- The local sensitivity of `f` at input `x`: number of coordinates `i` at
which `f` is sensitive. -/
def localSensitivity (f : BoolFun n) (x : Fin n → Bool) : ℕ :=
  (Finset.univ.filter fun i => f.sensitiveAt x i).card


-- @@ L92-95 verbatim
/-- The sensitivity of `f`: the maximum of `f.localSensitivity x` over all
inputs `x`. -/
noncomputable def sensitivity (f : BoolFun n) : ℕ :=
  Finset.univ.sup (fun x => f.localSensitivity x)


-- @@ L97-102 verbatim
/-- The sensitivity of any Boolean function on `n` variables is at most `n`. -/
theorem sensitivity_le (f : BoolFun n) : f.sensitivity ≤ n := by
  apply Finset.sup_le
  intro x _
  unfold localSensitivity
  exact (Finset.card_filter_le _ _).trans (by simp)


-- @@ L104-108 verbatim
/-- The local sensitivity at any specific input is bounded above by the
sensitivity of `f`. -/
theorem localSensitivity_le_sensitivity (f : BoolFun n) (x : Fin n → Bool) :
    f.localSensitivity x ≤ f.sensitivity := by
  exact Finset.le_sup (f := fun x => f.localSensitivity x) (Finset.mem_univ x)


-- @@ L110-110 verbatim
end BoolFun


-- @@ L112-115 verbatim
/-- Flip all bits whose index lies in the finite set `S`, leaving the
remaining coordinates fixed. -/
def flipCoords (x : Fin n → Bool) (S : Finset (Fin n)) : Fin n → Bool :=
  fun j => if j ∈ S then !x j else x j


-- @@ L117-117 verbatim
end LeanPoolSensitivity
