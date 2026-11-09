/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import BernoulliRegular.TotallyRealSubfield.ZetaPrime
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace


-- @@ L11-25 verbatim
/-!
# Valuation-completion model for the lambda-local Kummer--Artin--Hasse trace

The existing `LambdaLocalIntegerRing` is an adic completion of the localized
cyclotomic integer ring.  It is the model already used by the principal-unit
filtration.  For the `Q_p`-linear trace in the explicit local correction,
mathlib's available field/DVR API is instead attached to
`HeightOneSpectrum.adicCompletion`.

This file exposes the valuation-completion model attached to the same prime
`lambda = zetaPrime p K`.  The final explicit Kummer--Artin--Hasse trace
source is routed through this valuation-completion model; the older
`LambdaLocalIntegerRing` stack is legacy infrastructure for the adic
principal-unit filtration, not the final trace API.
-/


-- @@ L27-27 verbatim
@[expose] public section


-- @@ L29-29 verbatim
noncomputable section


-- @@ L31-31 verbatim
open scoped NumberField


-- @@ L33-33 verbatim
namespace BernoulliRegular

-- @@ L34-34 verbatim
namespace Furtwaengler

-- @@ L35-35 verbatim
namespace KummerArtinHasse


-- @@ L37-37 verbatim
variable (p : ℕ) [Fact p.Prime]

-- @@ L38-38 verbatim
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]


-- @@ L40-45 verbatim
/-- The height-one prime of `𝓞 K` corresponding to `lambda = zeta_p - 1`. -/
def lambdaHeightOneSpectrum :
    IsDedekindDomain.HeightOneSpectrum (𝓞 K) where
  asIdeal := zetaPrime p K
  isPrime := zetaPrime_isPrime p K
  ne_bot := zetaPrime_ne_bot p K


-- @@ L47-50 verbatim
@[simp]
theorem lambdaHeightOneSpectrum_asIdeal :
    (lambdaHeightOneSpectrum p K).asIdeal = zetaPrime p K :=
  rfl


-- @@ L52-54 verbatim
/-- The valuation completion of `K` at `lambda`. -/
abbrev LambdaValuedCompletion : Type _ :=
  (lambdaHeightOneSpectrum p K).adicCompletion K


-- @@ L56-58 verbatim
/-- The valuation-completion integer ring at `lambda`. -/
abbrev LambdaValuedIntegerRing : Type _ :=
  (lambdaHeightOneSpectrum p K).adicCompletionIntegers K


-- @@ L60-62 verbatim
instance lambdaValuedCompletion_field :
    Field (LambdaValuedCompletion p K) :=
  inferInstance


-- @@ L64-66 verbatim
theorem lambdaValuedIntegerRing_isDomain :
    IsDomain (LambdaValuedIntegerRing p K) :=
  inferInstance


-- @@ L68-70 verbatim
theorem lambdaValuedIntegerRing_isDiscreteValuationRing :
    IsDiscreteValuationRing (LambdaValuedIntegerRing p K) :=
  inferInstance


-- @@ L72-74 verbatim
theorem lambdaValuedIntegerRing_isPrincipalIdealRing :
    IsPrincipalIdealRing (LambdaValuedIntegerRing p K) :=
  inferInstance


-- @@ L76-79 verbatim
/-- The global field embeds densely into the valuation completion. -/
theorem lambdaValuedCompletion_denseRange_algebraMap :
    DenseRange (algebraMap K (LambdaValuedCompletion p K)) :=
  (lambdaHeightOneSpectrum p K).denseRange_algebraMap K


-- @@ L81-81 verbatim
end KummerArtinHasse

-- @@ L82-82 verbatim
end Furtwaengler

-- @@ L83-83 verbatim
end BernoulliRegular
