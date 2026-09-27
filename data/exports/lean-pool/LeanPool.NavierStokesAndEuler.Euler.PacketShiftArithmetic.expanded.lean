/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import Aesop.BuiltinRules
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.ToAdditive
public import Mathlib.Tactic.ToDual


-- @@ L14-14 verbatim
/-! Uniform shift room for the recursive packet estimates in the manuscript. -/


-- @@ L16-16 verbatim
@[expose] public section




-- @@ L20-20 verbatim
namespace EulerPacketShiftArithmetic


-- @@ L22-23 verbatim
/-- High shift, given by `100*p-80`. -/
def highShift (p : ℕ) : ℕ := 100*p-80

-- @@ L24-25 verbatim
/-- Mean shift, given by `100*p-140`. -/
def meanShift (p : ℕ) : ℕ := 100*p-140

-- @@ L26-27 verbatim
/-- High force shift, given by `highShift p-10`. -/
def highForceShift (p : ℕ) : ℕ := highShift p-10

-- @@ L28-29 verbatim
/-- Mean force shift, given by `meanShift p-10`. -/
def meanForceShift (p : ℕ) : ℕ := meanShift p-10


-- @@ L31-31 verbatim
theorem primary_shift : highShift 1=20 := rfl


-- @@ L33-36 verbatim
theorem slow_high_high_room (i j p : ℕ) (hi : 1 ≤ i) (hj : 1 ≤ j) (hp : i + j = p) :
    highShift i+highShift j+2+8 ≤ meanForceShift p := by
  dsimp only [highShift, meanShift, meanForceShift]
  omega


-- @@ L38-41 verbatim
theorem slow_mean_high_room (i j p : ℕ) (hi : 2 ≤ i) (hj : 1 ≤ j) (hp : i + j = p) :
    meanShift i+highShift j+2+8 ≤ meanForceShift p := by
  dsimp only [highShift, meanShift, meanForceShift]
  omega


-- @@ L43-46 verbatim
theorem slow_mean_mean_room (i j p : ℕ) (hi : 2 ≤ i) (hj : 2 ≤ j) (hp : i + j = p) :
    meanShift i+meanShift j+2+8 ≤ meanForceShift p := by
  dsimp only [meanShift, meanForceShift]
  omega


-- @@ L48-51 verbatim
theorem fast_mean_high_room (i j p : ℕ) (hi : 2 ≤ i) (hj : 1 ≤ j) (hp : i + j = p + 1) :
    meanShift i+highShift j+2+8 ≤ highForceShift p := by
  dsimp only [highShift, meanShift, highForceShift]
  omega


-- @@ L53-56 verbatim
theorem fast_corrector_high_room (i j p : ℕ) (hi : 2 ≤ i) (hj : 1 ≤ j) (hp : i + j = p + 1) :
    highShift (i-1)+highShift j+2+8 ≤ meanForceShift p := by
  dsimp only [highShift, meanShift, meanForceShift]
  omega


-- @@ L58-62 verbatim
theorem fast_corrector_corrector_room (i j p : ℕ) (hi : 2 ≤ i) (hj : 2 ≤ j)
    (hp : i + j = p + 1) :
    highShift (i-1)+highShift (j-1)+2+8 ≤ meanForceShift p := by
  dsimp only [highShift, meanShift, meanForceShift]
  omega


-- @@ L64-67 verbatim
theorem previous_linear_room (p : ℕ) (hp : 2 ≤ p) :
    highShift (p-1)+2+8 ≤ meanForceShift p := by
  dsimp only [highShift, meanShift, meanForceShift]
  omega


-- @@ L69-71 verbatim
theorem mean_force_le_high_force (p : ℕ) : meanForceShift p ≤ highForceShift p := by
  dsimp only [highShift, meanShift, meanForceShift, highForceShift]
  omega


-- @@ L73-76 verbatim
theorem force_shift_dominates_grade (p : ℕ) (hp : 2 ≤ p) :
    25*p ≤ meanForceShift p ∧ 25*p ≤ highForceShift p := by
  dsimp only [highShift, meanShift, meanForceShift, highForceShift]
  omega


-- @@ L78-78 verbatim
end EulerPacketShiftArithmetic
