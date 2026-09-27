/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Basic
public import TauCeti.Algebra.Module.Rat
public import TauCeti.RingTheory.DividedPowers.Commutation


-- @@ L12-46 verbatim
/-!
# Cartan and root-vector commutation in a universal enveloping algebra

Let `h` and `x` be elements of a Lie algebra over `ℚ` satisfying

```text
[h, x] = z x,     z : ℤ.
```

Inside the universal enveloping algebra this becomes `h x = x (h + z)`.  The generic
binomial/divided-power reordering identities therefore give

```text
(h choose m) x⁽ⁿ⁾ = x⁽ⁿ⁾ (h + n z choose m),
x⁽ⁿ⁾ (h choose m) = (h - n z choose m) x⁽ⁿ⁾.
```

Here an integer such as `n z` denotes that integer times the unit of the enveloping algebra.
For the Chevalley generators, `z` is the integral Cartan integer pairing a simple coroot with a
root.  These formulas are the Cartan/root-vector part of normal ordering the generators of the
Kostant integral form; the root/root part requires the separate root-string formulas.

## Main results

* `TauCeti.UniversalEnvelopingAlgebra.ι_mul_ι_eq_ι_mul_ι_add_zsmul_one`: the associative-ring
  form of an integral weight relation.
* `TauCeti.UniversalEnvelopingAlgebra.ringChoose_ι_mul_dividedPower_ι`: move a Cartan binomial
  coefficient to the right of a root-vector divided power.
* `TauCeti.UniversalEnvelopingAlgebra.dividedPower_ι_mul_ringChoose_ι`: the reverse reordering.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §26.2.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.
-/


-- @@ L48-48 verbatim
public section


-- @@ L50-50 verbatim
namespace TauCeti.UniversalEnvelopingAlgebra


-- @@ L52-52 verbatim
universe u v


-- @@ L54-54 verbatim
variable {L : Type u} [LieRing L]


-- @@ L56-56 verbatim
attribute [local instance 100] LieRing.ofAssociativeRing


-- @@ L58-69 verbatim
/-- The associative-ring form of an integral weight relation in a Lie algebra. -/
theorem ι_mul_ι_eq_ι_mul_ι_add_zsmul_one {R : Type*} [CommRing R] [LieAlgebra R L]
    {h x : L} {z : ℤ} (hz : ⁅h, x⁆ = z • x) :
    _root_.UniversalEnvelopingAlgebra.ι R h *
        _root_.UniversalEnvelopingAlgebra.ι R x =
      _root_.UniversalEnvelopingAlgebra.ι R x *
        (_root_.UniversalEnvelopingAlgebra.ι R h +
          z • (1 : _root_.UniversalEnvelopingAlgebra R L)) := by
  have hmap := LieHom.map_lie (_root_.UniversalEnvelopingAlgebra.ι R) h x
  rw [hz, map_zsmul, LieRing.of_associative_ring_bracket] at hmap
  rw [mul_add, zsmul_one, ← zsmul_eq_mul', add_comm]
  exact eq_add_of_sub_eq hmap.symm


-- @@ L71-71 verbatim
local notation "U" => _root_.UniversalEnvelopingAlgebra ℚ L


-- @@ L73-73 verbatim
attribute [local instance] TauCeti.moduleNNRat


-- @@ L75-75 verbatim
variable [LieAlgebra ℚ L]


-- @@ L77-88 verbatim
/-- A Cartan binomial coefficient moves to the right of a root-vector divided power by adding
`n` copies of the integral weight to its argument. -/
theorem ringChoose_ι_mul_dividedPower_ι {h x : L} {z : ℤ} (hz : ⁅h, x⁆ = z • x)
    (m n : ℕ) :
    Ring.choose (_root_.UniversalEnvelopingAlgebra.ι ℚ h) m *
        Associative.dividedPower n (_root_.UniversalEnvelopingAlgebra.ι ℚ x) =
      Associative.dividedPower n (_root_.UniversalEnvelopingAlgebra.ι ℚ x) *
        Ring.choose
          (_root_.UniversalEnvelopingAlgebra.ι ℚ h + ((n * z : ℤ) : U)) m := by
  simpa only [nsmul_eq_mul, zsmul_eq_mul, mul_one, Int.cast_natCast, Int.cast_mul] using
    Associative.ringChoose_mul_dividedPower m
      (ι_mul_ι_eq_ι_mul_ι_add_zsmul_one hz) ((Commute.one_left _).smul_left z) n


-- @@ L90-101 verbatim
/-- A Cartan binomial coefficient moves to the left of a root-vector divided power by subtracting
`n` copies of the integral weight from its argument. -/
theorem dividedPower_ι_mul_ringChoose_ι {h x : L} {z : ℤ} (hz : ⁅h, x⁆ = z • x)
    (m n : ℕ) :
    Associative.dividedPower n (_root_.UniversalEnvelopingAlgebra.ι ℚ x) *
        Ring.choose (_root_.UniversalEnvelopingAlgebra.ι ℚ h) m =
      Ring.choose
          (_root_.UniversalEnvelopingAlgebra.ι ℚ h - ((n * z : ℤ) : U)) m *
        Associative.dividedPower n (_root_.UniversalEnvelopingAlgebra.ι ℚ x) := by
  simpa only [nsmul_eq_mul, zsmul_eq_mul, mul_one, Int.cast_natCast, Int.cast_mul] using
    Associative.dividedPower_mul_ringChoose m
      (ι_mul_ι_eq_ι_mul_ι_add_zsmul_one hz) ((Commute.one_left _).smul_left z) n


-- @@ L103-103 verbatim
end TauCeti.UniversalEnvelopingAlgebra
