/-
Copyright (c) 2024 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Varun Thakore
-/

module

public import CompPoly.Fields.Basic
public import CompPoly.Fields.PrattCertificate


-- @@ L12-16 verbatim
/-!
  # Mersenne prime field `2^{31} - 1`

  This is the field used in Circle STARKs.
-/


-- @@ L18-18 verbatim
@[expose] public section


-- @@ L20-20 verbatim
namespace Mersenne31


-- @@ L22-24 verbatim
/-- The Mersenne31 prime modulus `2^31 - 1`. -/
@[reducible]
def fieldSize : Nat := 2 ^ 31 - 1


-- @@ L26-28 verbatim
/-- The canonical mathematical Mersenne31 field, implemented as integers modulo
`fieldSize`. -/
abbrev Field := ZMod fieldSize


-- @@ L30-33 verbatim
/-- The Mersenne31 modulus is prime, verified by a Pratt certificate. -/
theorem is_prime : Nat.Prime fieldSize := by
  unfold fieldSize
  pratt


-- @@ L35-36 verbatim
/-- Register primality of `fieldSize` for Mathlib instances such as `ZMod.instField`. -/
instance : Fact (Nat.Prime fieldSize) := ⟨is_prime⟩


-- @@ L38-39 verbatim
/-- The canonical Mersenne31 carrier is a field because its modulus is prime. -/
instance : _root_.Field Field := ZMod.instField fieldSize


-- @@ L41-46 verbatim
/-- Mersenne31 has characteristic different from two. -/
instance : NonBinaryField Field where
  char_neq_2 := by
    -- `decide` can discharge this concrete ZMod equality.
    simpa [Field, fieldSize] using
      (by decide : (2 : ZMod (2 ^ 31 - 1)) ≠ 0)


-- @@ L48-48 verbatim
end Mersenne31
