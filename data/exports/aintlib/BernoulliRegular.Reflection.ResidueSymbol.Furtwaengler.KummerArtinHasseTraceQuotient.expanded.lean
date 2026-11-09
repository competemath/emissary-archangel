/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.KummerArtinHasseTruncatedLog


-- @@ L10-17 verbatim
/-!
# The `pi`-quotient of the truncated Kummer--Artin--Hasse logarithm

The `A` term contains `pi^{-1} log_<p(u)`.  Since the completed local model is
currently exposed as an adic completion rather than an abstract DVR, this file
constructs the quotient using the already-proved theorem that the completed
maximal ideal is the span of the completed uniformizer `pi`.
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


-- @@ L32-41 verbatim
theorem exists_lambdaPi_mul_eq_truncatedLog
    (u : LambdaPrincipalUnitSubgroup p K 1) :
    ∃ y : LambdaLocalIntegerRing p K,
      lambdaPi p K * y = lambdaTruncatedLog p K u := by
  have hlog :
      lambdaTruncatedLog p K u ∈ (LambdaMaximalIdeal p K) ^ 1 := by
    simpa [pow_one] using lambdaTruncatedLog_mem_maximalIdeal (p := p) (K := K) u
  simpa [lambdaPi, LambdaMaximalIdeal, pow_one] using
    Reflection.Local.exists_uniformizer_pow_mul_eq_of_mem_completedLocalCyclotomicMaximalIdeal_pow
      (p := p) (K := K) (n := 1) (x := lambdaTruncatedLog p K u) hlog


-- @@ L43-46 verbatim
/-- A concrete quotient representing `pi^{-1} log_<p(u)`. -/
def lambdaTruncatedLogDivPi (u : LambdaPrincipalUnitSubgroup p K 1) :
    LambdaLocalIntegerRing p K :=
  Classical.choose (exists_lambdaPi_mul_eq_truncatedLog (p := p) (K := K) u)


-- @@ L48-53 verbatim
/-- The quotient `lambdaTruncatedLogDivPi` really divides the truncated log by
the completed uniformizer `pi`. -/
theorem lambdaPi_mul_truncatedLogDivPi_eq
    (u : LambdaPrincipalUnitSubgroup p K 1) :
    lambdaPi p K * lambdaTruncatedLogDivPi p K u = lambdaTruncatedLog p K u :=
  Classical.choose_spec (exists_lambdaPi_mul_eq_truncatedLog (p := p) (K := K) u)


-- @@ L55-55 verbatim
end KummerArtinHasse

-- @@ L56-56 verbatim
end Furtwaengler

-- @@ L57-57 verbatim
end BernoulliRegular
