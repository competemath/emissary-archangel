module

public import
  BernoulliRegular.CyclotomicUnits.KummerLogNormalization.ArtinHasseFiniteLogDecomposition


-- @@ L6-21 verbatim
/-!
# Homogeneity of the Artin-Hasse normalized coordinate polynomial powers

The normalized coordinate polynomial at `x` is obtained from its value at `1` by
substituting `T ↦ x * T`. Consequently, each coefficient of a power factors as its
value at `x = 1` times the corresponding power of `x`.

## Main results

* `samePrimeFiniteArtinHasseNormalizedCoordPoly_eq_comp_C_mul_X` gives the substitution formula.
* `samePrimeFiniteArtinHasseNormalizedCoordPoly_pow_coeff_eq_mul_pow` gives coefficient
  homogeneity for powers.

## References
* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83, §8.4.
-/


-- @@ L23-23 verbatim
@[expose] public section


-- @@ L25-25 verbatim
noncomputable section


-- @@ L27-27 verbatim
open NumberField


-- @@ L29-29 verbatim
namespace BernoulliRegular

-- @@ L30-30 verbatim
namespace CyclotomicUnits


-- @@ L32-32 verbatim
open PadicLogSetup PadicLogSetup.DworkParameter


-- @@ L34-34 verbatim
variable (p : ℕ) [Fact p.Prime]

-- @@ L35-35 verbatim
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

-- @@ L36-36 verbatim
variable [NumberField.IsCMField K]


-- @@ L38-53 verbatim
omit [NumberField.IsCMField K] in
/-- The coordinate polynomial at `x` is obtained from its value at `1` by substituting
`T ↦ x * T`. -/
theorem samePrimeFiniteArtinHasseNormalizedCoordPoly_eq_comp_C_mul_X
    (N : ℕ) (x : ValuedIntegerRing p K) :
    samePrimeFiniteArtinHasseNormalizedCoordPoly (p := p) (K := K) N x =
      (samePrimeFiniteArtinHasseNormalizedCoordPoly (p := p) (K := K) N 1).comp
        (Polynomial.C x * Polynomial.X) := by
  rw [samePrimeFiniteArtinHasseNormalizedCoordPoly,
    samePrimeFiniteArtinHasseNormalizedCoordPoly, Polynomial.comp,
    Polynomial.eval₂_finsetSum]
  refine Finset.sum_congr rfl ?_
  intro n _hn
  rw [Polynomial.eval₂_monomial, mul_pow, ← Polynomial.C_pow, one_pow, mul_one,
    ← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.C_mul]
  ring


-- @@ L55-64 verbatim
omit [NumberField.IsCMField K] in
/-- The degree-`d` coefficient of the `a`-th power factors as its value at `x = 1`
times `x ^ d`. -/
theorem samePrimeFiniteArtinHasseNormalizedCoordPoly_pow_coeff_eq_mul_pow
    (N a d : ℕ) (x : ValuedIntegerRing p K) :
    ((samePrimeFiniteArtinHasseNormalizedCoordPoly (p := p) (K := K) N x) ^ a).coeff d =
      ((samePrimeFiniteArtinHasseNormalizedCoordPoly (p := p) (K := K) N 1) ^ a).coeff d *
        x ^ d := by
  rw [samePrimeFiniteArtinHasseNormalizedCoordPoly_eq_comp_C_mul_X (p := p) (K := K) N x,
    ← Polynomial.pow_comp, Polynomial.comp_C_mul_X_coeff]


-- @@ L66-66 verbatim
end CyclotomicUnits

-- @@ L67-67 verbatim
end BernoulliRegular


-- @@ L69-69 verbatim
end
