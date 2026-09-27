/-
Copyright (c) 2026 Seewoo Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seewoo Lee
-/
module



-- @@ L9-13 verbatim
/-!
# LeanPool.LeanPolyABC.Lib.Max3

Imported Lean Pool material for `LeanPool.LeanPolyABC.Lib.Max3`.
-/


-- @@ L15-15 verbatim
@[expose] public section


-- @@ L17-17 verbatim
namespace Nat


-- @@ L19-21 verbatim
/-- The maximum of three natural numbers, `max (max a b) c`. -/
def max₃ (a b c : Nat) : Nat :=
  max (max a b) c


-- @@ L23-24 verbatim
theorem max₃_mul_distrib_left (a b c d : Nat) : a * max₃ b c d = max₃ (a * b) (a * c) (a * d) := by
  rw [max₃, max₃, Nat.mul_max_mul_left, Nat.mul_max_mul_left]


-- @@ L26-27 verbatim
theorem max₃_add_distrib_left (a b c d : Nat) : d + max₃ a b c = max₃ (d + a) (d + b) (d + c) := by
  rw [max₃, max₃, Nat.add_max_add_left, Nat.add_max_add_left]


-- @@ L29-30 verbatim
theorem max₃_add_distrib_right (a b c d : Nat) : max₃ a b c + d = max₃ (a + d) (b + d) (c + d) := by
  rw [max₃, max₃, Nat.add_max_add_right, Nat.add_max_add_right]


-- @@ L32-33 verbatim
theorem le_max₃_left (a b c : Nat) : a ≤ max₃ a b c :=
  Nat.le_trans (Nat.le_max_left a b) (Nat.le_max_left _ _)


-- @@ L35-36 verbatim
theorem le_max₃_middle (a b c : Nat) : b ≤ max₃ a b c :=
  Nat.le_trans (Nat.le_max_right a b) (Nat.le_max_left _ _)


-- @@ L38-39 verbatim
theorem le_max₃_right (a b c : Nat) : c ≤ max₃ a b c :=
  Nat.le_max_right _ c


-- @@ L41-42 verbatim
theorem max₃_lt {a b c d : Nat} : max₃ a b c < d ↔ a < d ∧ b < d ∧ c < d := by
  rw [max₃, Nat.max_lt, Nat.max_lt, and_assoc]


-- @@ L44-45 verbatim
theorem max₃_le {a b c d : Nat} : max₃ a b c ≤ d ↔ a ≤ d ∧ b ≤ d ∧ c ≤ d := by
  rw [max₃, Nat.max_le, Nat.max_le, and_assoc]


-- @@ L47-47 verbatim
end Nat
