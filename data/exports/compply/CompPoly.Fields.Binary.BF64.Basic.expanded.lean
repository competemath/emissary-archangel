/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Schleicher
-/
module

public import CompPoly.Fields.Binary.BF64.BaseCertificate
public import CompPoly.Data.Polynomial.Rabin
public import CompPoly.Data.RingTheory.CanonicalEuclideanDomain
public import Mathlib.Data.ZMod.Basic
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.Tactic.ComputeDegree


-- @@ L15-64 verbatim
/-!
# `GF(2^64)` in a polynomial basis

The field

```text
GF(2)[x] / (x^64 + x^4 + x^3 + x + 1)
```

as a *flat* quotient by a single irreducible degree-64 polynomial, with an element
represented by the 64-bit word whose bit `i` is the coefficient of `x^i`. The modulus is
the standard low-weight pentanomial for this width, and its tail `x^4 + x^3 + x + 1`
(the constant `0x1B`) is what makes the reduction in `BF64/Reduce.lean` cheap.

This is a different presentation from the binary tower in
`CompPoly/Fields/Binary/Tower/`, which builds `GF(2^64)` as an iterated quadratic
extension. The two fields are abstractly isomorphic but use different bases, so their
bit-level encodings disagree: on the same bit patterns `2 * 3` is `6` here and `1` in the
tower's rung. Neither is a substitute for the other where the encoding is observable.

## Main definitions

* `basePoly` — the modulus, as a `Polynomial (ZMod 2)`. Specification only.
* `BF64Quot` — the field, as `AdjoinRoot basePoly`.
* `baseTail` — the modulus below its leading term, `x^4 + x^3 + x + 1`.

## Main statements

* `basePoly_irreducible` — irreducibility, by Rabin's test against the kernel-checked
  chains in `BF64.BaseCert`.
* `mul_pow_reduce` — the reduction identity `x^64 ≡ x^4 + x^3 + x + 1`.
* `card_bf64Quot` — `Fintype.card BF64Quot = 2 ^ 64`.

## Implementation notes

`basePoly` is `noncomputable` because Mathlib's `Polynomial` is a `Finsupp`, which has no
executable representation. It exists to state irreducibility and is never evaluated.
`CompPoly.Extension.ExtensionParams.poly` makes the same choice.

`BF64Quot` is the *quotient* presentation, used for cardinality and as the target of the
bridge. The computable presentation that arithmetic runs on is `BF64` in
`CompPoly/Fields/Binary/BF64/Impl.lean`, a `BitVec 64`; the two are related by
`BF64.toQuot`, which `BF64.toQuot_injective` and `BF64.toQuot_surjective` show is a
bijection.

## References

* [Rabin80] Michael O. Rabin. Probabilistic Algorithms in Finite Fields.
  SIAM Journal on Computing, 9(2):273-280, 1980. https://doi.org/10.1137/0209024
-/


-- @@ L66-66 verbatim
@[expose] public section


-- @@ L68-68 verbatim
namespace BF64


-- @@ L70-70 verbatim
open Polynomial CompPoly.RabinCert BF64.BaseCert


-- @@ L72-72 verbatim
set_option maxHeartbeats 400000

-- @@ L73-73 verbatim
set_option maxRecDepth 4000


-- @@ L75-77 verbatim
/-- Little-endian coefficients of `x^64 + x^4 + x^3 + x + 1`: the terms of degree
`0, 1, 3, 4` and `64`. -/
def baseCoeffs : List ℕ := [1, 1, 0, 1, 1] ++ List.replicate 59 0 ++ [1]


-- @@ L79-81 verbatim
/-- The modulus `x^64 + x^4 + x^3 + x + 1` over `GF(2)`. Part of the specification only;
it is never evaluated. -/
noncomputable def basePoly : Polynomial (ZMod 2) := X ^ 64 + X ^ 4 + X ^ 3 + X + 1


-- @@ L83-91 verbatim
/-- A run of zero coefficients shifts the rest of the list up by that many degrees. -/
theorem toPoly_replicate_zero {p : ℕ} (n : ℕ) (rest : List ℕ) :
    toPoly p (List.replicate n 0 ++ rest) = X ^ n * toPoly p rest := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [List.replicate_succ, List.cons_append, toPoly_cons, ih]
    simp [pow_succ]
    ring


-- @@ L93-98 verbatim
/-- The certificate's coefficient encoding denotes `basePoly`. -/
theorem toPoly_baseCoeffs : toPoly 2 baseCoeffs = basePoly := by
  show toPoly 2 ([1, 1, 0, 1, 1] ++ (List.replicate 59 0 ++ [1])) = basePoly
  simp only [List.cons_append, List.nil_append, toPoly_cons, toPoly_replicate_zero, toPoly_nil,
    Nat.cast_zero, Nat.cast_one, map_zero, map_one, basePoly]
  ring


-- @@ L100-102 verbatim
/-- The modulus has degree `64`: the leading `X ^ 64` dominates the tail. -/
theorem basePoly_natDegree : basePoly.natDegree = 64 := by
  rw [basePoly]; compute_degree!


-- @@ L104-106 verbatim
/-- `basePoly_natDegree` in `degree` form, as the division lemmas expect. -/
theorem basePoly_degree : basePoly.degree = (64 : ℕ) := by
  rw [basePoly]; compute_degree!


-- @@ L108-113 verbatim
/-- The modulus is nonzero, so it can be divided by. -/
theorem basePoly_ne_zero : basePoly ≠ 0 := by
  intro h
  have hd := basePoly_natDegree
  rw [h, natDegree_zero] at hd
  exact absurd hd (by norm_num)


-- @@ L115-119 verbatim
/-- The prime factors of `64`. `decide` cannot do this: `Nat.primeFactorsList` is
well-founded recursive and does not reduce in the kernel. -/
private theorem primeFactors_sixtyFour : (64 : ℕ).primeFactors = {2} := by
  rw [show (64 : ℕ) = 2 ^ 6 from by norm_num,
    Nat.primeFactors_prime_pow (by norm_num) Nat.prime_two]


-- @@ L121-143 verbatim
/--
`x^64 + x^4 + x^3 + x + 1` is irreducible over `GF(2)`, by Rabin's test against the
kernel-checked chains in `BF64.BaseCert`.

Degree `64` has the single prime factor `2`, so the trace condition is joined by one
coprimality check, at exponent `2^32`. Note that the collapsed
`irreducible_of_rabin_prime_degree` is *unsound* at this degree — it would accept a
product of equal-degree factors — so the general `Polynomial.irreducible_of_rabin` is
used, with `primeFactors_sixtyFour` supplying the prime factors of `64`.
-/
theorem basePoly_irreducible : Irreducible basePoly := by
  refine Polynomial.irreducible_of_rabin (d := 64) ?_ (by norm_num) ?_ ?_
  · exact basePoly_natDegree
  · rw [ZMod.card]
    exact dvd_X_pow_sub_X_of_runChain (steps := traceSteps) toPoly_baseCoeffs basePoly_ne_zero
      (by rfl) (by rfl)
  · intro ℓ hℓ
    rw [primeFactors_sixtyFour, Finset.mem_singleton] at hℓ
    subst hℓ
    rw [ZMod.card]
    exact isCoprime_X_pow_sub_X_of_runChain (steps := cop32Steps) (rp := cop32Rp)
      (w := cop32W) (u := cop32U) (v := cop32V) toPoly_baseCoeffs basePoly_ne_zero
      (by rfl) (by rfl) (by rfl) (by rfl)


-- @@ L145-145 verbatim
instance : Fact (Irreducible basePoly) := ⟨basePoly_irreducible⟩


-- @@ L147-147 verbatim
/-! ## The reduction identity -/


-- @@ L149-151 verbatim
/-- The modulus below its leading term: `x^4 + x^3 + x + 1`, denoted by the reduction
constant `0x1B`. -/
noncomputable def baseTail : Polynomial (ZMod 2) := X ^ 4 + X ^ 3 + X + 1


-- @@ L153-154 verbatim
/-- The defining equation of `baseTail`, for rewriting. -/
theorem baseTail_eq : baseTail = X ^ 4 + X ^ 3 + X + 1 := rfl


-- @@ L156-157 verbatim
/-- The defining equation of `basePoly`, for rewriting. -/
theorem basePoly_eq : basePoly = X ^ 64 + X ^ 4 + X ^ 3 + X + 1 := rfl


-- @@ L159-161 verbatim
/-- The modulus split into its leading term and its tail. -/
theorem basePoly_eq_add_tail : basePoly = X ^ 64 + baseTail := by
  unfold basePoly baseTail; ring


-- @@ L163-170 verbatim
/-- `x^64 ≡ x^4 + x^3 + x + 1` modulo the modulus: multiplying by `X ^ 64` may be
replaced by multiplying by `baseTail`. -/
theorem mul_pow_reduce (A : Polynomial (ZMod 2)) :
    (A * X ^ 64) % basePoly = (A * baseTail) % basePoly := by
  have hadd : (X : (ZMod 2)[X]) ^ 64 = basePoly + baseTail := by
    rw [basePoly_eq_add_tail, add_assoc, CharTwo.add_self_eq_zero, add_zero]
  rw [hadd, mul_add, show A * basePoly + A * baseTail = A * baseTail + basePoly * A from by ring,
    CanonicalEuclideanDomain.add_mul_mod_right _ _ _ basePoly_ne_zero]


-- @@ L172-172 verbatim
/-! ## The base field -/


-- @@ L174-178 verbatim
/-- `GF(2^64)` as the quotient `GF(2)[x] / (x^64 + x^4 + x^3 + x + 1)`.

This is the specification-side presentation. Arithmetic runs on the computable `BF64` in
`CompPoly/Fields/Binary/BF64/Impl.lean`. -/
noncomputable abbrev BF64Quot : Type := AdjoinRoot basePoly


-- @@ L180-180 verbatim
noncomputable instance : Field BF64Quot := AdjoinRoot.instField


-- @@ L182-188 verbatim
noncomputable instance : Fintype BF64Quot := by
  let pb := AdjoinRoot.powerBasis basePoly_ne_zero
  letI : Module.Finite (ZMod 2) BF64Quot := PowerBasis.finite pb
  haveI : Finite BF64Quot := by
    have : Module.finrank (ZMod 2) BF64Quot = pb.dim := PowerBasis.finrank pb
    exact Finite.of_equiv (Fin pb.dim →₀ ZMod 2) (pb.basis.repr.toEquiv.symm)
  exact Fintype.ofFinite BF64Quot


-- @@ L190-197 verbatim
/-- `BF64Quot` has `2^64` elements. -/
theorem card_bf64Quot : Fintype.card BF64Quot = 2 ^ 64 := by
  rw [Module.card_eq_pow_finrank (K := ZMod 2) (V := BF64Quot)]
  let pb := AdjoinRoot.powerBasis basePoly_ne_zero
  rw [PowerBasis.finrank pb]
  have hdim : pb.dim = basePoly.natDegree := rfl
  rw [hdim, basePoly_natDegree]
  norm_num


-- @@ L199-199 verbatim
end BF64
