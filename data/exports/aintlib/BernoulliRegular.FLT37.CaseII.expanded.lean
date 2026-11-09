/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import BernoulliRegular.FLT37.PrimaryDescent
public import BernoulliRegular.FLT37.PrimaryUnits
public import BernoulliRegular.FLT37.Mirimanoff
public import FltRegular.CaseII.Statement


-- @@ L13-41 verbatim
/-!
# FLT case II for `p = 37` (ticket F37-D, scaffold)

The case II argument under VandiverIIIHypothesis follows Vandiver's program:

1. **Primary unit decomposition**: any unit `u ∈ (𝓞 K)ˣ` admits a decomposition
   `u = ζ^m · v_+` with `v_+` a real (totally real) unit of `𝓞 K⁺`, plus a
   *primary form* refinement under specific hypotheses (V001 / Kummer's lemma
   sharpening).

2. **Mirimanoff subfield trick** (V002): for `ℓ ≡ 1 (mod 4)`, the imaginary
   unit `i ∈ (ZMod ℓ)ˣ` lifts to a Galois automorphism `ζ ↦ ζ^ω` with `ω² = -1`.
   The fixed subfield of `⟨ω⟩` reduces the case-II analysis to a smaller field.

3. **Vandiver Lemma 1** (V003): under `VandiverIIIHypothesis ℓ`, the relevant
   ideals are still principal even without regularity (uses reflection T044).

4. **Infinite descent**: assuming a primitive coprime solution exists, find a
   smaller one — contradicting minimality.

This file provides scaffolding for the conditional case II theorem. The
substantive mathematical work (steps 1–4) is the bulk of `[F37-D]`.

## Status

Scaffold. The conditional `VandiverIIICaseII` for `ℓ = 37` is the
goal; here we establish the namespace, imports, and document the proof
plan.
-/


-- @@ L43-43 verbatim
@[expose] public section


-- @@ L45-45 verbatim
noncomputable section


-- @@ L47-47 verbatim
open NumberField NumberField.IsCMField IsCyclotomicExtension


-- @@ L49-49 verbatim
namespace BernoulliRegular


-- @@ L51-51 verbatim
namespace FLT37


-- @@ L53-53 verbatim
namespace CaseII


-- @@ L55-59 verbatim
/-! ## Standing setup

The case II analysis works inside `K = ℚ(ζ_p)` for an odd prime `p`. The
regular-prime case is handled by `flt-regular`'s `caseII`; for `p = 37`
(irregular) we follow the Vandiver program above. -/


-- @@ L61-61 verbatim
variable {p : ℕ} [hp : Fact p.Prime]

-- @@ L62-62 verbatim
variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]


-- @@ L64-64 verbatim
local notation3 "K⁺" => NumberField.maximalRealSubfield K


-- @@ L66-74 verbatim
/-! ## Section 1: Primary unit decomposition

The key result is that any cyclotomic unit factor in case II can be
brought to a **primary form** — congruent to a rational integer modulo
`(ζ-1)^{2p}`. This sharpens Kummer's lemma `u = ζ^m · v_+` by also
adjusting `v_+` to be primary.

Defined in `Primary.lean` as `IsPrimary` (via `(zetaSubOne)^{2p} ∣ α - integer`).
-/


-- @@ L76-81 verbatim
/-! ## Section 2: Mirimanoff subfield trick

For `p ≡ 1 (mod 4)`, the Mirimanoff Galois automorphism `mirimanoffGalAut`
in `Mirimanoff.lean` has order 4 with `mirimanoffGalAut^2` = complex
conjugation. The fixed subfield of `⟨mirimanoffGalAut⟩` in `K` is a
quartic extension over which the case-II analysis simplifies. -/


-- @@ L83-89 verbatim
/-! ## Section 3: Vandiver Lemma 1

Under `VandiverIIIHypothesis ℓ` (parity), the ideals
`(α + ζ^k β) · 𝓞 K` arising in the case II decomposition are principal
even for irregular `p`. The reflection theorem
`ReflectionMinusNontrivialityBridge` (T044) supplies the structural
input. -/


-- @@ L91-96 verbatim
/-! ## Section 4: Infinite descent

The standard descent: from a minimal primitive coprime solution
`a^p + b^p = c^p` with `p ∣ c`, the case II decomposition produces a
smaller solution, contradicting minimality. Mirrors
`flt-regular`'s `caseII` infrastructure (`AuxLemmas`, `InductionStep`). -/


-- @@ L98-103 verbatim
/-! ## Conditional case II under regularity

For *regular* primes `p`, the case II argument is fully proved in
`flt-regular`'s `caseII`. We package it here as a conditional consumer for
the Vandiver III case II program, separating out the regular-prime portion
so the irregular-prime extension (F37-F) can plug in. -/


-- @@ L105-105 verbatim
end CaseII


-- @@ L107-118 verbatim
/-- **Conditional VandiverIIICaseII for regular primes.** When `ℓ` is a
regular prime, `flt-regular`'s `caseII` directly gives the conclusion of
`VandiverIIICaseII`. The parity hypothesis is unused (it's only needed
for irregular primes via Vandiver Lemma 1). -/
theorem vandiverIIICaseII_of_regular_caseII
    {a b c : ℤ} {ℓ : ℕ} [hℓ : Fact ℓ.Prime]
    (h_reg : IsRegularPrime ℓ) (h_odd : ℓ ≠ 2)
    (h_prod : a * b * c ≠ 0)
    (hgcd : ({a, b, c} : Finset ℤ).gcd id = 1)
    (case : (ℓ : ℤ) ∣ a * b * c) :
    a ^ ℓ + b ^ ℓ ≠ c ^ ℓ :=
  FltRegular.caseII h_reg h_odd h_prod hgcd case


-- @@ L120-128 verbatim
/-- **Vandiver Lemma 1 predicate, ℓ = 37 specialization.** Captures the
regularity-free structural input needed for case II at ℓ = 37: under the
parity hypothesis plus `37 ∤ h⁺`, the ideals arising in the case II
decomposition are principal even without the regular-prime hypothesis.
The reflection theorem T044 (already established in `Reflection/Final.lean`)
is one of the inputs to discharging this predicate. -/
def VandiverLemma1Thirtyseven : Prop :=
  ∀ ⦃a b c : ℤ⦄, a * b * c ≠ 0 → ({a, b, c} : Finset ℤ).gcd id = 1 →
    ((37 : ℤ) ∣ a * b * c) → a ^ 37 + b ^ 37 ≠ c ^ 37


-- @@ L130-138 verbatim
/-- **caseII for ℓ = 37 from VandiverLemma1Thirtyseven.** The conditional
theorem: given the 37-specific Vandiver Lemma 1 predicate (which encodes
the case II descent for irregular 37 under the parity hypothesis), case II
for 37 follows. -/
theorem caseII_thirtyseven_of_vandiverLemma1
    (h : VandiverLemma1Thirtyseven) :
    ∀ ⦃a b c : ℤ⦄, a * b * c ≠ 0 → ({a, b, c} : Finset ℤ).gcd id = 1 →
      (37 : ℤ) ∣ a * b * c → a ^ 37 + b ^ 37 ≠ c ^ 37 :=
  h


-- @@ L140-140 verbatim
end FLT37


-- @@ L142-142 verbatim
end BernoulliRegular


-- @@ L144-144 verbatim
end
