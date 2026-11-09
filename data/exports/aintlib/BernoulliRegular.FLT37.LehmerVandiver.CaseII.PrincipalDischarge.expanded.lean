/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import BernoulliRegular.FLT37.LehmerVandiver.CaseII.AuxiliaryIdeal
public import BernoulliRegular.FLT37.LehmerVandiver.CaseII.B0Principalization


-- @@ L11-32 verbatim
/-!
# LV-CaseII parametric principalization discharge

Mirror of `CaseIClassEqDischarge` but for case II. In case II, the
substantive use of regularity is in
`a_div_principal` (`FltRegular.CaseII.InductionStep:399`): under
regularity, the fractional ideal `𝔞 η₁ / 𝔞 η₂` is principal in
`FractionalIdeal (𝓞 K)⁰ K`.

To adapt this to `¬ p ∣ h⁺`, we package the principalization as a
`Prop` that can be discharged by a follow-up CFT argument (the
fractional-ideal analogue of LV010-A).

Combined with an adapted Kummer's lemma (the case-II analogue of
Stage 2), this gives a parametric `CaseIIBridge` constructor.

## References

* flt-regular's `FltRegular.CaseII.InductionStep.a_div_principal`.
* `BernoulliRegular.FLT37.LehmerVandiver.CaseI.CaseIClassEqDischarge`
  (the case-I analogue).
-/


-- @@ L34-34 verbatim
@[expose] public section


-- @@ L36-36 verbatim
noncomputable section


-- @@ L38-38 verbatim
open NumberField IsCyclotomicExtension Polynomial

-- @@ L39-39 verbatim
open scoped nonZeroDivisors


-- @@ L41-41 verbatim
namespace BernoulliRegular


-- @@ L43-43 verbatim
namespace FLT37


-- @@ L45-45 verbatim
namespace LehmerVandiver


-- @@ L47-47 verbatim
namespace CaseII


-- @@ L49-49 verbatim
variable (p : ℕ) [Fact p.Prime]

-- @@ L50-51 verbatim
variable (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
  [NumberField.IsCMField K]


-- @@ L53-78 verbatim
/-- **Adapted Kummer's lemma predicate**: Kummer's lemma for unit
ratios in `(𝓞 K)ˣ`, parametric on `¬ p ∣ h⁺` instead of regularity.
States: any unit `u ∈ (𝓞 K)ˣ` congruent to an integer mod `p` is a
`p`-th power in `(𝓞 K)ˣ`.

This is flt-regular's `eq_pow_prime_of_unit_of_congruent` (which
assumes regularity); the adapted version requires Hilbert 90 / Hilbert
92 / Hilbert 94 descent on unramified Kummer extensions over `K⁺` (via
the primary-form structure of `u`).

**Strength note (mathematical):** for irregular primes (where
`Cl(K)⁻[p]` is non-trivial), the universal-quantification form is
**unfillable**: counterexamples come from units in the kernel of
reduction mod `p` whose class in
`(𝓞 K)ˣ / ((𝓞 K)ˣ)^p` is non-trivial. Under just `¬ p ∣ h⁺`, the
relevant Kummer's lemma holds only for units with **specific
structure** (e.g., the case-II auxiliary units `ε₁/ε₂` after the
second-order Bernoulli refinement). A refined predicate restricted to
those specific units is the realistic mathematical target for filling.

Filling either form unconditionally is the substantive Vandiver
program (Washington Theorem 9.3 / 9.4), shipped as a follow-up. -/
def AdaptedKummersLemma : Prop :=
  ∀ (u : (𝓞 K)ˣ),
    (∃ n : ℤ, ((p : ℕ) : 𝓞 K) ∣ ((u : 𝓞 K) - (n : 𝓞 K))) →
    ∃ v : (𝓞 K)ˣ, u = v ^ p


-- @@ L80-106 verbatim
/-- **Case-II principalization discharge predicate**: parametric input
for the fractional-ideal principalization step in case II.

States: any pair of non-zero ideals `𝔞₁, 𝔞₂` with `(𝔞₁ / 𝔞₂)^p`
principal (as a fractional ideal in `K`) has `𝔞₁ / 𝔞₂` itself
principal.

Under regularity (`p ∤ |Cl(𝓞 K)|`), this follows from
`isPrincipal_of_isPrincipal_pow_of_Coprime'`. Under `¬ p ∣ h⁺(K)`, it
requires class-equality analysis at the fractional-ideal level (the
case-II analogue of LV010-A).

**Strength note (mathematical):** for irregular primes (where
`Cl(K)⁻[p]` is non-trivial), this universal-quantification form is
unfillable — counterexamples come from non-principal fractional ideals
of `p`-torsion class. The realistic mathematical target for filling
is the refined `CaseIIPrincipalDischargeOnSpecific` (in
`SpecificDischarge.lean`), which restricts the quantifier to fractional
ideals appearing in case-II setups. The general predicate is kept here
as the "ideal" abstract form; the specific form is what to fill.

Filling either predicate unconditionally is the substantive case-II
follow-up CFT work. -/
def CaseIIPrincipalDischarge : Prop :=
  ∀ (I : FractionalIdeal (𝓞 K)⁰ K),
    ((↑(I ^ p) : Submodule (𝓞 K) K).IsPrincipal) →
    (I : Submodule (𝓞 K) K).IsPrincipal


-- @@ L108-108 verbatim
end CaseII


-- @@ L110-110 verbatim
end LehmerVandiver


-- @@ L112-112 verbatim
end FLT37


-- @@ L114-114 verbatim
end BernoulliRegular


-- @@ L116-116 verbatim
end
