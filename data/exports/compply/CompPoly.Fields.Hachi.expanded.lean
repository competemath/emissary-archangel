/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public import CompPoly.Fields.Basic
public import CompPoly.Fields.PrattCertificate


-- @@ L11-33 verbatim
/-!
# Hachi prime field `2^32 - 99`

A 32-bit prime field. The name is provisional.

`p - 1 = 2^2 · 3 · 13 · 67 · 163 · 2521`, so:

* `p ≡ 1 mod 4`, which is what makes `X^4 - W` irreducible for any non-square `W`
  (see `CompPoly/Fields/Hachi/Ext4.lean`);
* the two-adicity is only **2**, so unlike BabyBear and KoalaBear this field admits no large
  smooth multiplicative subgroup and therefore **no radix-2 NTT domain**. That is irrelevant for
  degree-4 extension arithmetic, which is schoolbook, but it does rule out the
  `CompPoly/Univariate/NTT*` fast-multiplication paths for polynomials over this field.

## Implementation notes

There is deliberately no `FastField` (Montgomery) implementation for this modulus.
`Montgomery/Native32Field.lean` requires `modulus < 2 ^ 31`, because radix-`2^32` Montgomery
reduction needs `x + m * p < 2 ^ 64`; at `p ≈ 2 ^ 32` that overflows `UInt64`. A 64-bit-radix
(or two-limb) Montgomery layer would be needed, and is orthogonal to the extension framework —
`CompPoly/Fields/Extension/` is generic over the base-field carrier and would pick it up
unchanged.
-/


-- @@ L35-35 verbatim
@[expose] public section


-- @@ L37-37 verbatim
namespace Hachi


-- @@ L39-41 verbatim
/-- The Hachi field modulus, `2^32 - 99`. -/
@[reducible]
def fieldSize : Nat := 2 ^ 32 - 99


-- @@ L43-44 verbatim
/-- The Hachi prime field as a `ZMod`. -/
abbrev Field := ZMod fieldSize


-- @@ L46-48 verbatim
/-- The Hachi modulus is prime. -/
theorem is_prime : Nat.Prime fieldSize := by
  pratt


-- @@ L50-50 verbatim
instance : Fact (Nat.Prime fieldSize) := ⟨is_prime⟩


-- @@ L52-52 verbatim
instance : _root_.Field Field := ZMod.instField fieldSize


-- @@ L54-55 verbatim
instance : NonBinaryField Field where
  char_neq_2 := by decide


-- @@ L57-59 verbatim
/-- Bit width of the Hachi modulus. -/
@[reducible]
def pBits : Nat := 32


-- @@ L61-64 verbatim
/-- The two-adicity of `fieldSize - 1`, i.e. `2` — deliberately small; see the module
docstring. -/
@[reducible]
def twoAdicity : Nat := 2


-- @@ L66-67 verbatim
theorem fieldSize_sub_one_factorization : fieldSize - 1 = 2 ^ twoAdicity * 1073741799 := by
  decide


-- @@ L69-69 verbatim
end Hachi
