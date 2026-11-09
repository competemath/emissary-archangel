/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.KummerArtinHasseValuationLocalModel
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal


-- @@ L11-17 verbatim
/-!
# The rational `p`-adic base place for the lambda-local correction

This file records the rational height-one prime `(p)` and proves that the
cyclotomic `lambda` prime lies over it.  These are the concrete inputs for
extending the rational map `ℚ → K` to the corresponding valuation completions.
-/


-- @@ L19-19 verbatim
@[expose] public section


-- @@ L21-21 verbatim
noncomputable section


-- @@ L23-23 verbatim
open scoped NumberField


-- @@ L25-25 verbatim
namespace BernoulliRegular

-- @@ L26-26 verbatim
namespace Furtwaengler

-- @@ L27-27 verbatim
namespace KummerArtinHasse


-- @@ L29-29 verbatim
variable (p : ℕ) [Fact p.Prime]

-- @@ L30-30 verbatim
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]


-- @@ L32-34 verbatim
/-- The rational prime ideal `(p)` in `ℤ`. -/
def lambdaRationalPrimeIdeal : Ideal ℤ :=
  Ideal.span ({(p : ℤ)} : Set ℤ)


-- @@ L36-40 verbatim
omit [Fact p.Prime] in
@[simp]
theorem lambdaRationalPrimeIdeal_def :
    lambdaRationalPrimeIdeal p = Ideal.span ({(p : ℤ)} : Set ℤ) :=
  rfl


-- @@ L42-49 verbatim
/-- The height-one spectrum point of `ℤ` attached to the rational prime `p`. -/
def lambdaRationalHeightOneSpectrum :
    IsDedekindDomain.HeightOneSpectrum ℤ where
  asIdeal := lambdaRationalPrimeIdeal p
  isPrime := (Int.ideal_span_isMaximal_of_prime p).isPrime
  ne_bot := by
    rw [lambdaRationalPrimeIdeal, ne_eq, Ideal.span_singleton_eq_bot]
    exact_mod_cast (Fact.out : Nat.Prime p).ne_zero


-- @@ L51-54 verbatim
@[simp]
theorem lambdaRationalHeightOneSpectrum_asIdeal :
    (lambdaRationalHeightOneSpectrum p).asIdeal = lambdaRationalPrimeIdeal p :=
  rfl


-- @@ L56-70 verbatim
/-- The cyclotomic `lambda` prime lies over the rational prime `(p)`. -/
theorem zetaPrime_liesOver_lambdaRationalPrimeIdeal :
    (zetaPrime p K).LiesOver (lambdaRationalPrimeIdeal p) := by
  haveI : IsCyclotomicExtension {p ^ (0 + 1)} ℚ K := by
    simpa using (inferInstance : IsCyclotomicExtension {p} ℚ K)
  have hζpow :
      IsPrimitiveRoot (IsCyclotomicExtension.zeta p ℚ K) (p ^ (0 + 1)) := by
    simp
  have h :
      (Ideal.span
          ({((IsCyclotomicExtension.zeta_spec p ℚ K).toInteger - 1 : 𝓞 K)} :
            Set (𝓞 K))).LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ)) :=
    IsCyclotomicExtension.Rat.liesOver_span_zeta_sub_one
      (p := p) (k := 0) (K := K) (hζ := hζpow)
  simpa [zetaPrime, lambdaRationalPrimeIdeal] using h


-- @@ L72-76 verbatim
/-- Height-one-spectrum form of `lambda` lying over the rational `p`-place. -/
theorem lambdaHeightOneSpectrum_liesOver_rational :
    (lambdaHeightOneSpectrum p K).asIdeal.LiesOver
      (lambdaRationalHeightOneSpectrum p).asIdeal := by
  simpa using zetaPrime_liesOver_lambdaRationalPrimeIdeal (p := p) (K := K)


-- @@ L78-78 verbatim
end KummerArtinHasse

-- @@ L79-79 verbatim
end Furtwaengler

-- @@ L80-80 verbatim
end BernoulliRegular
