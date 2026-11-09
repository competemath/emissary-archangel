module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.KummerFurtwaengler
public import Mathlib.NumberTheory.NumberField.Ideal.Basic
public import Mathlib.RingTheory.Ideal.Int


-- @@ L7-32 verbatim
/-!
# Canonical primitive `p`-th root of unity in `(𝓞 K ⧸ q)ˣ`

For `K = ℚ(ζ_p)` cyclotomic and a maximal ideal `q ⊂ 𝓞 K` with
`(p : 𝓞 K) ∉ q`, the canonical primitive `p`-th root of unity in
`(𝓞 K ⧸ q)ˣ` is the residue of the canonical primitive `p`-th root
`cyclotomicZetaInteger K ∈ 𝓞 K`.

This avoids the `Classical.choose` obstacle in
`pthSymbolAtPrime`: the canonical choice is fixed by the cyclotomic
Galois action, hence the c.2 transformation
`pthSymbolAtPrime (σ_a α) (σ_a • q) = ? · pthSymbolAtPrime α q`
has unit factor `c = 1` unconditionally.

## Main definitions and theorems

* `canonicalResidueZetaP q hp_in_q` — the canonical primitive `p`-th
  root in `(𝓞 K ⧸ q)ˣ`, defined when `(p : 𝓞 K) ∉ q` (and `q` maximal).
* `canonicalResidueZetaP_isPrimitiveRoot` — primitivity: it is a
  primitive `p`-th root of unity.
* `cyclotomicRingOfIntegersEquiv_apply_zetaInteger` — Galois compatibility:
  `σ_a` acts on `cyclotomicZetaInteger` by raising to the `a.val` power.
* `canonicalResidueZetaP_galois_compat` — the canonical residue zeta at
  `σ_a • q` is the image of the canonical residue zeta at `q` under the
  quotient ring iso induced by `σ_a`, raised to the `a.val` power.
-/


-- @@ L34-34 verbatim
@[expose] public section


-- @@ L36-36 verbatim
noncomputable section


-- @@ L38-38 verbatim
open scoped NumberField


-- @@ L40-40 verbatim
namespace BernoulliRegular


-- @@ L42-42 verbatim
namespace Furtwaengler


-- @@ L44-44 verbatim
variable {p : ℕ} [Fact p.Prime]

-- @@ L45-45 verbatim
variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]


-- @@ L47-54 verbatim
/-! ### Step 1 — coprimality of `absNorm q` with `p`

If `q` is a maximal ideal of `𝓞 K` with `(p : 𝓞 K) ∉ q`, then
`(absNorm q).Coprime p`. The proof uses the Dedekind structure: the
prime `q.under ℤ` is `⟨ℓ⟩` for some rational prime `ℓ`, and
`absNorm q` is a power of `ℓ`. Since `p ∉ q` and `q` is prime, the
underlying prime is not `p`, so the coprimality follows.
-/


-- @@ L56-69 verbatim
omit [NumberField K] [IsCyclotomicExtension {p} ℚ K] [Fact p.Prime] in
/-- If `(p : 𝓞 K) ∉ q`, then the absolute norm of the rational prime
under `q` is not `p`. -/
theorem absNorm_under_ne_of_not_mem
    {q : Ideal (𝓞 K)}
    (hp_not_in_q : (p : 𝓞 K) ∉ q) :
    Ideal.absNorm (q.under ℤ) ≠ p := by
  intro h
  -- absNorm (q.under ℤ) = p ⟹ p ∈ q via cast_mem_ideal_iff.
  apply hp_not_in_q
  have : ((Ideal.absNorm (q.under ℤ) : ℤ) : 𝓞 K) ∈ q := by
    rw [Int.cast_mem_ideal_iff]
  rw [h] at this
  exact_mod_cast this


-- @@ L71-104 verbatim
omit [IsCyclotomicExtension {p} ℚ K] in
/-- If `(p : 𝓞 K) ∉ q` for a maximal `q ≠ ⊥`, then
`(absNorm q).Coprime p`. -/
theorem coprime_absNorm_p_of_not_mem
    {q : Ideal (𝓞 K)} [hq : q.IsPrime] (hq_ne_bot : q ≠ ⊥)
    (hp_not_in_q : (p : 𝓞 K) ∉ q) :
    (Ideal.absNorm q).Coprime p := by
  haveI : NeZero q := ⟨hq_ne_bot⟩
  -- The under-prime is a prime number ≠ p.
  have h_under_prime : (Ideal.absNorm (q.under ℤ)).Prime :=
    Nat.absNorm_under_prime q
  have h_under_ne_p : Ideal.absNorm (q.under ℤ) ≠ p :=
    absNorm_under_ne_of_not_mem hp_not_in_q
  -- absNorm q is a power of absNorm (q.under ℤ) (via inertiaDeg').
  have h_under_dvd : Ideal.absNorm (q.under ℤ) ∣ Ideal.absNorm q :=
    Int.absNorm_under_dvd_absNorm q
  have h_norm_pow : Ideal.absNorm q =
      Ideal.absNorm (q.under ℤ) ^
        ((Ideal.span ({(Ideal.absNorm (q.under ℤ) : ℤ)} : Set ℤ)).inertiaDeg' q) := by
    have := Ideal.absNorm_eq_pow_inertiaDeg
      (R := 𝓞 K) (P := q) (p := (Ideal.absNorm (q.under ℤ) : ℤ))
      (Nat.prime_iff_prime_int.mp h_under_prime)
    simpa using this
  -- p is prime, and the under-prime ≠ p, so they're coprime.
  have hp_prime : Nat.Prime p := Fact.out
  have h_cop_under_p : (Ideal.absNorm (q.under ℤ)).Coprime p := by
    rw [Nat.coprime_comm, hp_prime.coprime_iff_not_dvd]
    intro h_p_dvd
    -- p ∣ absNorm (q.under ℤ), both prime ⟹ equal. But we have ≠.
    exact h_under_ne_p
      ((Nat.prime_dvd_prime_iff_eq hp_prime h_under_prime).mp h_p_dvd).symm
  -- absNorm q = (under)^k, so coprime to p iff (under).Coprime p.
  rw [h_norm_pow]
  exact h_cop_under_p.pow_left _


-- @@ L106-112 verbatim
/-! ### Step 2 — canonical residue ζ_p definition and primitivity

We define the canonical primitive `p`-th root of unity in `(𝓞 K ⧸ q)ˣ`
as the residue of the canonical primitive `p`-th root of unity
`cyclotomicZetaInteger K ∈ 𝓞 K`. Primitivity follows from
`IsPrimitiveRoot.idealQuotient_mk` once coprimality is established.
-/


-- @@ L114-118 verbatim
/-- Canonical residue primitive `p`-th root in `𝓞 K ⧸ q`. This is the
"underlying" element; the unit version is `canonicalResidueZetaP`. -/
def canonicalResidueZetaPRing
    (q : Ideal (𝓞 K)) : 𝓞 K ⧸ q :=
  Ideal.Quotient.mk q (cyclotomicZetaInteger (p := p) K)


-- @@ L120-131 verbatim
/-- Canonical residue primitive `p`-th root in `(𝓞 K ⧸ q)ˣ`. Defined
as the residue of `cyclotomicZetaInteger K`, which is a primitive
`p`-th root of unity in `𝓞 K`, hence a unit. The image inherits the
unit structure from the surjective ring hom. -/
def canonicalResidueZetaP
    (q : Ideal (𝓞 K)) : (𝓞 K ⧸ q)ˣ :=
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  -- ζ_p ∈ 𝓞 K is a unit. Its image under the ring hom is also a unit.
  let hζ_unit : IsUnit (cyclotomicZetaInteger (p := p) K) :=
    (cyclotomicZetaInteger_isPrimitiveRoot (p := p) (K := K)).isUnit
      (Fact.out : p.Prime).ne_zero
  ((Ideal.Quotient.mk q).isUnit_map hζ_unit).unit


-- @@ L133-138 verbatim
@[simp] theorem canonicalResidueZetaP_val
    (q : Ideal (𝓞 K)) :
    haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    ((canonicalResidueZetaP (p := p) (K := K) q) : 𝓞 K ⧸ q) =
      Ideal.Quotient.mk q (cyclotomicZetaInteger (p := p) K) := by
  rfl


-- @@ L140-158 verbatim
/-- **Primitivity (underlying ring element form).**
For maximal `q` with `(p : 𝓞 K) ∉ q`, the residue of
`cyclotomicZetaInteger K` is a primitive `p`-th root in `𝓞 K ⧸ q`. -/
theorem canonicalResidueZetaPRing_isPrimitiveRoot
    {q : Ideal (𝓞 K)} [hq : q.IsPrime] (hq_ne_bot : q ≠ ⊥)
    (hp_not_in_q : (p : 𝓞 K) ∉ q) :
    haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    IsPrimitiveRoot (canonicalResidueZetaPRing (p := p) (K := K) q) p := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  -- Use IsPrimitiveRoot.idealQuotient_mk.
  -- Need: absNorm q ≠ 1 (q ≠ ⊤, automatic from prime) and Coprime.
  have habs_ne_one : Ideal.absNorm q ≠ 1 := by
    intro h
    rw [Ideal.absNorm_eq_one_iff] at h
    exact hq.ne_top h
  have hcop : (Ideal.absNorm q).Coprime p :=
    coprime_absNorm_p_of_not_mem hq_ne_bot hp_not_in_q
  exact (cyclotomicZetaInteger_isPrimitiveRoot (p := p) (K := K)).idealQuotient_mk
    habs_ne_one hcop


-- @@ L160-171 verbatim
/-- **Primitivity (unit form).**
For maximal `q` with `(p : 𝓞 K) ∉ q`, the canonical residue zeta is a
primitive `p`-th root in `(𝓞 K ⧸ q)ˣ`. -/
theorem canonicalResidueZetaP_isPrimitiveRoot
    {q : Ideal (𝓞 K)} [hq : q.IsPrime] (hq_ne_bot : q ≠ ⊥)
    (hp_not_in_q : (p : 𝓞 K) ∉ q) :
    haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    IsPrimitiveRoot (canonicalResidueZetaP (p := p) (K := K) q) p := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  -- Use coe_units_iff to reduce to the underlying ring element.
  rw [← IsPrimitiveRoot.coe_units_iff, canonicalResidueZetaP_val]
  exact canonicalResidueZetaPRing_isPrimitiveRoot hq_ne_bot hp_not_in_q


-- @@ L173-181 verbatim
/-- **Existence corollary.** For maximal `q` with `(p : 𝓞 K) ∉ q`, there
exists a primitive `p`-th root in `(𝓞 K ⧸ q)ˣ`. This bridges the
`Classical.choose` precondition of `pthSymbolAtPrime`. -/
theorem exists_isPrimitiveRoot_of_not_mem_p
    {q : Ideal (𝓞 K)} [hq : q.IsPrime] (hq_ne_bot : q ≠ ⊥)
    (hp_not_in_q : (p : 𝓞 K) ∉ q) :
    ∃ ζ : (𝓞 K ⧸ q)ˣ, IsPrimitiveRoot ζ p :=
  ⟨canonicalResidueZetaP (p := p) (K := K) q,
    canonicalResidueZetaP_isPrimitiveRoot hq_ne_bot hp_not_in_q⟩


-- @@ L183-188 verbatim
/-! ### Step 2b — basic API around primitivity

Convenience lemmas immediately derived from `IsPrimitiveRoot`:
`pow_eq_one`, `ne_one`, `orderOf_eq`, plus a `zpow` form and the
inverse-as-power identity `ζ⁻¹ = ζ ^ (p - 1)`.
-/


-- @@ L190-195 verbatim
/-- The canonical residue zeta raised to the `p`-th power is `1`. -/
theorem canonicalResidueZetaP_pow_eq_one
    {q : Ideal (𝓞 K)} [hq : q.IsPrime] (hq_ne_bot : q ≠ ⊥)
    (hp_not_in_q : (p : 𝓞 K) ∉ q) :
    canonicalResidueZetaP (p := p) (K := K) q ^ p = 1 :=
  (canonicalResidueZetaP_isPrimitiveRoot hq_ne_bot hp_not_in_q).pow_eq_one


-- @@ L197-203 verbatim
/-- The canonical residue zeta is not `1`. Uses `1 < p` from primality. -/
theorem canonicalResidueZetaP_ne_one
    {q : Ideal (𝓞 K)} [hq : q.IsPrime] (hq_ne_bot : q ≠ ⊥)
    (hp_not_in_q : (p : 𝓞 K) ∉ q) :
    canonicalResidueZetaP (p := p) (K := K) q ≠ 1 :=
  (canonicalResidueZetaP_isPrimitiveRoot hq_ne_bot hp_not_in_q).ne_one
    (Fact.out : p.Prime).one_lt


-- @@ L205-210 verbatim
/-- The canonical residue zeta has order exactly `p` in `(𝓞 K ⧸ q)ˣ`. -/
theorem canonicalResidueZetaP_orderOf_eq
    {q : Ideal (𝓞 K)} [hq : q.IsPrime] (hq_ne_bot : q ≠ ⊥)
    (hp_not_in_q : (p : 𝓞 K) ∉ q) :
    orderOf (canonicalResidueZetaP (p := p) (K := K) q) = p :=
  ((canonicalResidueZetaP_isPrimitiveRoot hq_ne_bot hp_not_in_q).eq_orderOf).symm


-- @@ L212-217 verbatim
/-- The canonical residue zeta raised to a power `l` equals `1` iff `p ∣ l`. -/
theorem canonicalResidueZetaP_pow_eq_one_iff
    {q : Ideal (𝓞 K)} [hq : q.IsPrime] (hq_ne_bot : q ≠ ⊥)
    (hp_not_in_q : (p : 𝓞 K) ∉ q) (l : ℕ) :
    canonicalResidueZetaP (p := p) (K := K) q ^ l = 1 ↔ p ∣ l :=
  (canonicalResidueZetaP_isPrimitiveRoot hq_ne_bot hp_not_in_q).pow_eq_one_iff_dvd l


-- @@ L219-224 verbatim
/-- Integer-power version: `ζ ^ (p : ℤ) = 1`. -/
theorem canonicalResidueZetaP_zpow_eq_one
    {q : Ideal (𝓞 K)} [hq : q.IsPrime] (hq_ne_bot : q ≠ ⊥)
    (hp_not_in_q : (p : 𝓞 K) ∉ q) :
    canonicalResidueZetaP (p := p) (K := K) q ^ (p : ℤ) = 1 :=
  (canonicalResidueZetaP_isPrimitiveRoot hq_ne_bot hp_not_in_q).zpow_eq_one


-- @@ L226-241 verbatim
/-- The inverse equals the `(p - 1)`-th power. Uses `ζ ^ p = 1` together with
`ζ ^ p = ζ * ζ ^ (p - 1)`. -/
theorem canonicalResidueZetaP_inv
    {q : Ideal (𝓞 K)} [hq : q.IsPrime] (hq_ne_bot : q ≠ ⊥)
    (hp_not_in_q : (p : 𝓞 K) ∉ q) :
    (canonicalResidueZetaP (p := p) (K := K) q)⁻¹ =
      canonicalResidueZetaP (p := p) (K := K) q ^ (p - 1) := by
  have hp_pos : 0 < p := (Fact.out : p.Prime).pos
  have hpow := canonicalResidueZetaP_pow_eq_one hq_ne_bot hp_not_in_q
  -- ζ * ζ^(p-1) = ζ^p = 1, so ζ⁻¹ = ζ^(p-1).
  refine (eq_inv_of_mul_eq_one_right ?_).symm
  have h_eq : canonicalResidueZetaP (p := p) (K := K) q *
      canonicalResidueZetaP (p := p) (K := K) q ^ (p - 1) =
      canonicalResidueZetaP (p := p) (K := K) q ^ p := by
    rw [← pow_succ', Nat.sub_one_add_one hp_pos.ne']
  rw [h_eq, hpow]


-- @@ L243-250 verbatim
/-- `ζ⁻¹` is also a primitive `p`-th root in `(𝓞 K ⧸ q)ˣ`. -/
theorem canonicalResidueZetaP_inv_isPrimitiveRoot
    {q : Ideal (𝓞 K)} [hq : q.IsPrime] (hq_ne_bot : q ≠ ⊥)
    (hp_not_in_q : (p : 𝓞 K) ∉ q) :
    haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    IsPrimitiveRoot (canonicalResidueZetaP (p := p) (K := K) q)⁻¹ p :=
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  (canonicalResidueZetaP_isPrimitiveRoot hq_ne_bot hp_not_in_q).inv


-- @@ L252-260 verbatim
/-- For `i` coprime to `p`, the `i`-th power of the canonical residue zeta is
also a primitive `p`-th root. Specialising `IsPrimitiveRoot.pow_of_coprime`. -/
theorem canonicalResidueZetaP_pow_isPrimitiveRoot
    {q : Ideal (𝓞 K)} [hq : q.IsPrime] (hq_ne_bot : q ≠ ⊥)
    (hp_not_in_q : (p : 𝓞 K) ∉ q) {i : ℕ} (hi : i.Coprime p) :
    haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    IsPrimitiveRoot (canonicalResidueZetaP (p := p) (K := K) q ^ i) p :=
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  (canonicalResidueZetaP_isPrimitiveRoot hq_ne_bot hp_not_in_q).pow_of_coprime i hi


-- @@ L262-268 verbatim
/-- The canonical residue zeta has finite order. -/
theorem canonicalResidueZetaP_isOfFinOrder
    {q : Ideal (𝓞 K)} [hq : q.IsPrime] (hq_ne_bot : q ≠ ⊥)
    (hp_not_in_q : (p : 𝓞 K) ∉ q) :
    IsOfFinOrder (canonicalResidueZetaP (p := p) (K := K) q) :=
  (canonicalResidueZetaP_isPrimitiveRoot hq_ne_bot hp_not_in_q).isOfFinOrder
    (Fact.out : p.Prime).ne_zero


-- @@ L270-275 verbatim
/-- `ζ ^ p = 1` at the underlying ring level. -/
theorem canonicalResidueZetaPRing_pow_eq_one
    {q : Ideal (𝓞 K)} [hq : q.IsPrime] (hq_ne_bot : q ≠ ⊥)
    (hp_not_in_q : (p : 𝓞 K) ∉ q) :
    canonicalResidueZetaPRing (p := p) (K := K) q ^ p = 1 :=
  (canonicalResidueZetaPRing_isPrimitiveRoot hq_ne_bot hp_not_in_q).pow_eq_one


-- @@ L277-283 verbatim
/-! ### Step 3 — Galois compatibility of canonical zeta

The cyclotomic Galois action `σ_a` on `𝓞 K` acts on
`cyclotomicZetaInteger` by raising to the `a.val` power.
Concretely, `σ_a • ζ = ζ^a.val` (Mathlib's `cyclotomicSigmaOfUnit_smul_zetaInteger`).
This translates to the residue level via the quotient ring iso.
-/


-- @@ L285-294 verbatim
/-- The action of `cyclotomicRingOfIntegersEquiv K a` on
`cyclotomicZetaInteger K` is exact exponentiation by `a.val`. This is
just the unfolding of the Galois action on a fixed element of `K`. -/
theorem cyclotomicRingOfIntegersEquiv_apply_zetaInteger
    (a : CyclotomicUnitDelta p) :
    cyclotomicRingOfIntegersEquiv (p := p) K a (cyclotomicZetaInteger (p := p) K) =
      cyclotomicZetaInteger (p := p) K ^ (a : ZMod p).val := by
  -- Unfolding cyclotomicRingOfIntegersEquiv reduces to the smul lemma.
  change cyclotomicSigmaOfUnit (p := p) K a • cyclotomicZetaInteger (p := p) K = _
  exact cyclotomicSigmaOfUnit_smul_zetaInteger (p := p) (K := K) a


-- @@ L296-319 verbatim
/-- The quotient ring iso induced by `σ_a` sends the canonical residue
zeta at `q` to the `a.val`-th power of the canonical residue zeta at
`σ_a • q`. This is the residue-level version of
`cyclotomicRingOfIntegersEquiv_apply_zetaInteger`.

This is the core compatibility used to make the c.2 `pthSymbolAtPrime`
Galois transformation unconditional with unit factor `c = 1` (after
inverting the `a.val` exponent). -/
theorem canonicalResidueZetaP_val_galois_compat
    (a : CyclotomicUnitDelta p) (q : Ideal (𝓞 K)) :
    haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    cyclotomicGaloisQuotientEquiv (p := p) (K := K) a q
      ((canonicalResidueZetaP (p := p) (K := K) q) : 𝓞 K ⧸ q) =
    ((canonicalResidueZetaP (p := p) (K := K)
      (cyclotomicGaloisConjugate (p := p) (K := K) a q)) :
      𝓞 K ⧸ cyclotomicGaloisConjugate (p := p) (K := K) a q) ^ (a : ZMod p).val := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  -- Both sides unfold to the same residue: σ_a (ζ_p) = ζ_p^a.val.
  rw [canonicalResidueZetaP_val, canonicalResidueZetaP_val,
    cyclotomicGaloisQuotientEquiv_mk]
  -- Now LHS: Ideal.Quotient.mk (σ_a • q) (σ_a (ζ_p)).
  -- RHS: (Ideal.Quotient.mk (σ_a • q) ζ_p)^a.val.
  -- Use that σ_a (ζ_p) = ζ_p^a.val and map_pow.
  rw [cyclotomicRingOfIntegersEquiv_apply_zetaInteger, map_pow]


-- @@ L321-346 verbatim
/-- Existence of primitive `p`-th root at the conjugate prime, derived from
the canonical residue zeta. -/
theorem exists_isPrimitiveRoot_at_galois_conjugate
    (a : CyclotomicUnitDelta p)
    {q : Ideal (𝓞 K)} [hq : q.IsPrime] (hq_ne_bot : q ≠ ⊥)
    (hp_not_in_q : (p : 𝓞 K) ∉ q) :
    ∃ ζ : (𝓞 K ⧸ cyclotomicGaloisConjugate (p := p) (K := K) a q)ˣ,
      IsPrimitiveRoot ζ p := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  haveI : (cyclotomicGaloisConjugate (p := p) (K := K) a q).IsPrime :=
    cyclotomicGaloisConjugate_isPrime a q
  refine exists_isPrimitiveRoot_of_not_mem_p
    (cyclotomicGaloisConjugate_ne_bot a hq_ne_bot) ?_
  -- Need: (p : 𝓞 K) ∉ σ_a • q.
  -- Strategy: σ_a (p) = p (since p ∈ ℚ ⊂ K is fixed by Galois),
  -- and σ_a is a ring isomorphism so σ_a (p) ∈ σ_a • q ↔ p ∈ q.
  intro hp_in_conj
  apply hp_not_in_q
  -- Show σ_a (p : 𝓞 K) = (p : 𝓞 K).
  have h_fix : cyclotomicRingOfIntegersEquiv (p := p) K a (p : 𝓞 K) = (p : 𝓞 K) := by
    -- p is a natural number, hence fixed by any ring hom.
    change (cyclotomicRingOfIntegersEquiv (p := p) K a).toRingHom (p : 𝓞 K) = (p : 𝓞 K)
    rw [map_natCast]
  -- Apply mem_cyclotomicGaloisConjugate_iff with α = (p : 𝓞 K).
  rw [← h_fix] at hp_in_conj
  exact (mem_cyclotomicGaloisConjugate_iff a).mp hp_in_conj


-- @@ L348-354 verbatim
/-- The canonical residue zeta squared equals `ζ^2`. -/
theorem canonicalResidueZetaP_sq
    (q : Ideal (𝓞 K)) :
    (canonicalResidueZetaP (p := p) (K := K) q) ^ 2 =
      (canonicalResidueZetaP (p := p) (K := K) q) *
        (canonicalResidueZetaP (p := p) (K := K) q) :=
  sq _


-- @@ L356-356 verbatim
end Furtwaengler


-- @@ L358-358 verbatim
end BernoulliRegular
