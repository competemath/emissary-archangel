module

public import BernoulliRegular.Reflection.ResidueSymbol.Basic
public import Mathlib.NumberTheory.MulChar.Basic
public import Mathlib.GroupTheory.OrderOfElement


-- @@ L7-44 verbatim
/-!
# Residue character at a prime as a `MulChar` (REF-18c2a)

This file packages the `p`-th-power residue character at a maximal ideal
`q ∤ p` of a Dedekind domain `R` (typically `R = 𝓞_K` for a cyclotomic
field `K = ℚ(ζ_p)`) as a `MulChar (R ⧸ q) R'` for a target ring `R'`
containing a primitive `p`-th root of unity.

REF-16 (`BernoulliRegular.Reflection.ResidueSymbol.PowerResidue`) provides
the additive form `finiteFieldExponent : kˣ → ZMod p` and `primeExponent`
at the maximal-ideal level. This file lifts that exponent into a target
ring `R'` containing `μ_p`, packaging the result as a multiplicative
character that the Gauss-sum machinery (`Mathlib.NumberTheory.GaussSum`)
can directly consume.

## Approach

Given a primitive `p`-th root of unity `ζ_R` in the target `R'`, we send
`x ∈ kˣ` to `ζ_R ^ (finiteFieldExponent ... x).val ∈ R'ˣ`. The
multiplicativity of the underlying map follows from
`finiteFieldExponent_mul` together with the fact that `ζ_R` has order `p`,
so `ζ_R ^ ((a.val + b.val) % p) = ζ_R ^ (a.val + b.val)`. The lift to a
`MulChar k R'` (with non-units mapping to `0`) is then immediate via
`MulChar.ofUnitHom`.

## Main definitions

* `BernoulliRegular.Furtwaengler.residueUnitHom`: the unit-group
  homomorphism `kˣ →* R'ˣ` sending `x` to `ζ_R ^ (finiteFieldExponent ... x).val`.
* `BernoulliRegular.Furtwaengler.residueMulChar`: the corresponding
  `MulChar k R'`, obtained via `MulChar.ofUnitHom`.
* `residueMulChar_apply_unit`: the agreement
  `residueMulChar (x : kˣ) = ζ_R ^ (finiteFieldExponent ... x).val`.

The Galois-equivariance API (needed by REF-18c2c) is intentionally deferred
to a later commit; this ticket only delivers the bare `MulChar` packaging
plus the link back to REF-16.
-/


-- @@ L46-46 verbatim
@[expose] public section


-- @@ L48-48 verbatim
noncomputable section


-- @@ L50-50 verbatim
namespace BernoulliRegular


-- @@ L52-52 verbatim
namespace Furtwaengler


-- @@ L54-54 verbatim
open Reflection.ResidueSymbol.PowerResidue


-- @@ L56-56 verbatim
variable {k : Type*} [Field k] [Fintype k]

-- @@ L57-57 verbatim
variable {R' : Type*} [CommMonoidWithZero R']

-- @@ L58-58 verbatim
variable {p : ℕ}


-- @@ L60-71 verbatim
/-- `finiteFieldExponent` vanishes on the identity. -/
theorem finiteFieldExponent_one [NeZero p]
    (zeta_q : kˣ) (hzeta_q : IsPrimitiveRoot zeta_q p)
    (hdiv : p ∣ Fintype.card k - 1) :
    finiteFieldExponent zeta_q hzeta_q hdiv 1 = 0 := by
  have h := finiteFieldExponent_mul zeta_q hzeta_q hdiv 1 1
  rw [mul_one] at h
  have h' : 0 + finiteFieldExponent zeta_q hzeta_q hdiv 1 =
      finiteFieldExponent zeta_q hzeta_q hdiv 1 +
        finiteFieldExponent zeta_q hzeta_q hdiv 1 := by
    rw [zero_add]; exact h
  exact (add_right_cancel h').symm


-- @@ L73-92 verbatim
/-- The unit-group residue homomorphism, lifting REF-16's
`finiteFieldExponent : kˣ → ZMod p` to a multiplicative map `kˣ →* R'ˣ`
via a chosen primitive `p`-th root of unity in `R'`. -/
def residueUnitHom [NeZero p]
    (zeta_q : kˣ) (hzeta_q : IsPrimitiveRoot zeta_q p)
    (hdiv : p ∣ Fintype.card k - 1)
    (zeta_R : R'ˣ) (hzeta_R : IsPrimitiveRoot zeta_R p) :
    kˣ →* R'ˣ where
  toFun x := zeta_R ^ (finiteFieldExponent zeta_q hzeta_q hdiv x).val
  map_one' := by
    rw [finiteFieldExponent_one zeta_q hzeta_q hdiv, ZMod.val_zero, pow_zero]
  map_mul' x y := by
    rw [finiteFieldExponent_mul zeta_q hzeta_q hdiv, ← pow_add, ZMod.val_add]
    -- Goal: zeta_R ^ ((a.val + b.val) % p) = zeta_R ^ (a.val + b.val).
    -- Use `pow_mod_orderOf` with the term-level rewrite to avoid type-correctness
    -- issues from rewriting `p` in dependent positions of the surrounding goal.
    have key := pow_mod_orderOf zeta_R
        ((finiteFieldExponent zeta_q hzeta_q hdiv x).val +
          (finiteFieldExponent zeta_q hzeta_q hdiv y).val)
    rwa [← hzeta_R.eq_orderOf] at key


-- @@ L94-102 verbatim
/-- The `p`-th-power residue `MulChar` at a finite field `k` equipped with
a chosen primitive `p`-th root of unity `ζ_q ∈ k` and a target primitive
`p`-th root of unity `ζ_R ∈ R'`. -/
def residueMulChar [NeZero p]
    (zeta_q : kˣ) (hzeta_q : IsPrimitiveRoot zeta_q p)
    (hdiv : p ∣ Fintype.card k - 1)
    (zeta_R : R'ˣ) (hzeta_R : IsPrimitiveRoot zeta_R p) :
    MulChar k R' :=
  MulChar.ofUnitHom (residueUnitHom zeta_q hzeta_q hdiv zeta_R hzeta_R)


-- @@ L104-111 verbatim
theorem residueMulChar_apply_unit [NeZero p]
    (zeta_q : kˣ) (hzeta_q : IsPrimitiveRoot zeta_q p)
    (hdiv : p ∣ Fintype.card k - 1)
    (zeta_R : R'ˣ) (hzeta_R : IsPrimitiveRoot zeta_R p) (x : kˣ) :
    residueMulChar zeta_q hzeta_q hdiv zeta_R hzeta_R (x : k) =
      ((zeta_R : R')) ^ (finiteFieldExponent zeta_q hzeta_q hdiv x).val := by
  rw [residueMulChar, MulChar.ofUnitHom_coe]
  exact Units.val_pow_eq_pow_val _ _


-- @@ L113-124 verbatim
/-- Unit values of the residue character lie in the multiplicative group
generated by the chosen primitive `p`-th root of unity, hence are themselves
`p`-th roots of unity in `R'`. -/
theorem residueMulChar_pow_eq_one [NeZero p]
    (zeta_q : kˣ) (hzeta_q : IsPrimitiveRoot zeta_q p)
    (hdiv : p ∣ Fintype.card k - 1)
    (zeta_R : R'ˣ) (hzeta_R : IsPrimitiveRoot zeta_R p) (x : kˣ) :
    (residueMulChar zeta_q hzeta_q hdiv zeta_R hzeta_R (x : k)) ^ p = 1 := by
  rw [residueMulChar_apply_unit, ← pow_mul, mul_comm, pow_mul]
  have hpow : ((zeta_R : R'ˣ) : R') ^ p = 1 := by
    rw [← Units.val_pow_eq_pow_val, hzeta_R.pow_eq_one, Units.val_one]
  rw [hpow, one_pow]


-- @@ L126-150 verbatim
/-- Bridge to REF-16's `primeExponent`: for an element `α : R` outside the
maximal ideal `q` (so `α` has a unit class in `R/q`), the value of the
residue character at the quotient class equals `zeta_R^(primeExponent ...).val`.

This is the link from REF-16's prime-ideal-level residue exponent
(`primeExponent`) to our residue MulChar form needed for Gauss sums. -/
theorem residueMulChar_apply_quotient
    {R : Type*} [CommRing R] (q : Ideal R) [q.IsMaximal]
    [Fintype (R ⧸ q)] [NeZero p]
    (zeta_q : (R ⧸ q)ˣ) (hzeta_q : IsPrimitiveRoot zeta_q p)
    (hdiv : p ∣ Fintype.card (R ⧸ q) - 1)
    (zeta_R : R'ˣ) (hzeta_R : IsPrimitiveRoot zeta_R p)
    {α : R} (hα : α ∉ q) :
    letI : Field (R ⧸ q) := Ideal.Quotient.field q
    residueMulChar zeta_q hzeta_q hdiv zeta_R hzeta_R
        ((Ideal.Quotient.mk q α : R ⧸ q)) =
      ((zeta_R : R')) ^
        (Reflection.ResidueSymbol.PowerResidue.primeExponent q
          zeta_q hzeta_q hdiv α hα).val := by
  letI : Field (R ⧸ q) := Ideal.Quotient.field q
  change residueMulChar zeta_q hzeta_q hdiv zeta_R hzeta_R
        ((Reflection.ResidueSymbol.PowerResidue.quotientUnitOfNotMem q α hα :
          (R ⧸ q)ˣ) : R ⧸ q) = _
  rw [residueMulChar_apply_unit]
  rfl


-- @@ L152-152 verbatim
end Furtwaengler


-- @@ L154-154 verbatim
end BernoulliRegular
