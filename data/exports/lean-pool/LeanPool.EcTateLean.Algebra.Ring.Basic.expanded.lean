/-
Copyright (c) 2023 Alex J. Best and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best
-/
module

public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Ring.Defs
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow


-- @@ L13-17 verbatim
/-!
# LeanPool.EcTateLean.Algebra.Ring.Basic

Imported Lean Pool material for `LeanPool.EcTateLean.Algebra.Ring.Basic`.
-/


-- @@ L19-19 verbatim
@[expose] public section




-- @@ L23-23 verbatim
variable {R : Type _}


-- @@ L25-25 verbatim
theorem add_self_eq_mul_two [Semiring R] (a : R) : a + a = 2 * a := (two_mul a).symm


-- @@ L27-27 verbatim
section CommRing

-- @@ L28-28 verbatim
variable [CommRing R]



-- @@ L31-32 verbatim
theorem evenpow_neg {n m : ℕ} (a : R) (h : n = 2 * m) : (-a) ^ n = a ^ n := by
  rw [h, pow_mul, pow_mul, neg_sq]


-- @@ L34-35 verbatim
theorem oddpow_neg {n m : ℕ} (a : R) (h : n = 2 * m + 1) : (-a) ^ n = -(a ^ n) := by
  rw [h, pow_succ, evenpow_neg a (show 2 * m = 2 * m by rfl), pow_succ, mul_neg]


-- @@ L37-37 verbatim
end CommRing



-- @@ L40-40 verbatim
section IntegralDomain

-- @@ L41-43 verbatim
variable [CommRing R] [IsDomain R]

-- TODO maybe delete

-- @@ L44-45 verbatim
theorem nzero_mul_left_cancel (a b c : R) : a ≠ 0 → a * b = a * c → b = c :=
  fun h => mul_left_cancel₀ h



-- @@ L48-48 verbatim
end IntegralDomain
