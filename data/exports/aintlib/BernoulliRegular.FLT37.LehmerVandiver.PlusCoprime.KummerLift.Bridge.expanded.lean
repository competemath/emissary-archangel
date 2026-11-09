/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import BernoulliRegular.FLT37.LehmerVandiver.PlusCoprime.KummerLift.CharacterIdentification
public import BernoulliRegular.FLT37.LehmerVandiver.PlusCoprime.Symmetrisation
public import BernoulliRegular.FLT37.LehmerVandiver.PollaczekLog.PthPower


-- @@ L12-36 verbatim
/-!
# LV005c bridge: Cor 8.19 (real Pollaczek unit)

Washington Corollary 8.19 states: if a *real* cyclotomic unit (such as
the σ-symmetrised `pollaczekUnitPlus = pollaczekUnit · σ(pollaczekUnit)`)
is a `p`-th power in `(𝓞 K)ˣ`, then `p ∣ h⁺(K)`.

**Important refactor (post-review)**: the bridge is stated on the
σ-symmetrised real unit `pollaczekUnitPlus`, NOT on bare `pollaczekUnit`.
For bare `pollaczekUnit`, the Galois action introduces a non-trivial
ζ-prefactor (numerically ζ^{23} for FLT37 at a=2, not a `p`-th power),
so the eigenvalue identity needed for Cor 8.19 only holds for the real
form. Since `pollaczekUnitPlus = η_Washington²` factor-wise (worked out
from `σ(cyclotomicUnit(b)) = ζ^{1-b} · cyclotomicUnit(b)`) and `gcd(2, p)
= 1` for `p` odd, `IsPthPower(pollaczekUnitPlus) ↔ IsPthPower(η_Washington)`,
so this formulation captures the right content without introducing a
separate "η_Washington" definition.

Bundle field: `(¬ ∃ α ∈ (𝓞 K)ˣ, pollaczekUnitPlus = α^p) → ¬ p ∣ h⁺(K)`.

The bridge content (Washington Cor 8.19 itself) requires Sinnott's
cyclotomic-unit-class-number formula `[(𝓞 K⁺)ˣ : C⁺] = h⁺(K)`. Filled
by follow-up CFT-level work; LV005's main chain threads parametrically
on this bridge.
-/


-- @@ L38-38 verbatim
@[expose] public section


-- @@ L40-40 verbatim
noncomputable section


-- @@ L42-42 verbatim
open NumberField NumberField.IsCMField


-- @@ L44-44 verbatim
namespace BernoulliRegular


-- @@ L46-46 verbatim
universe u


-- @@ L48-48 verbatim
variable (p : ℕ) [Fact p.Prime]

-- @@ L49-50 verbatim
variable (K : Type u) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
  [NumberField.IsCMField K]


-- @@ L52-68 verbatim
/-- **Cor 8.19 bridge (real form)**: data packaging the classical
implication `IsPthPower(pollaczekUnitPlus) → p ∣ h⁺` in the contrapositive
form `¬ IsPthPower(pollaczekUnitPlus) → ¬ p ∣ h⁺` consumed by LV005's
chain.

Stated on the σ-symmetrised real form `pollaczekUnitPlus` (LV005b):
`= pollaczekUnit · σ(pollaczekUnit)`, σ-fixed under complex conjugation.
This avoids the ζ-prefactor obstruction inherent to the bare K-side
form. -/
structure Cor8_19Bridge (i : ℕ) where
  /-- Cor 8.19 contrapositive: if `pollaczekUnitPlus p K i` is **not** a
  `p`-th power in `(𝓞 K)ˣ`, then `p ∤ h⁺(K)`. -/
  not_dvd_hPlus_of_not_isPthPower :
    (∀ α : (𝓞 K)ˣ,
      ((FLT37.pollaczekUnitPlus p K i : (𝓞 K)ˣ) : 𝓞 K) ≠
        ((α : (𝓞 K)ˣ) : 𝓞 K) ^ p) →
        ¬ (p : ℕ) ∣ hPlus K


-- @@ L70-70 verbatim
namespace Cor8_19Bridge


-- @@ L72-72 verbatim
variable {p K}


-- @@ L74-82 verbatim
/-- Apply the bridge: extract the Cor 8.19 contrapositive in the form
consumed by LV005's main theorem. -/
theorem apply {i : ℕ}
    (B : Cor8_19Bridge p K i)
    (h : ∀ α : (𝓞 K)ˣ,
      ((FLT37.pollaczekUnitPlus p K i : (𝓞 K)ˣ) : 𝓞 K) ≠
        ((α : (𝓞 K)ˣ) : 𝓞 K) ^ p) :
    ¬ (p : ℕ) ∣ hPlus K :=
  B.not_dvd_hPlus_of_not_isPthPower h


-- @@ L84-84 verbatim
end Cor8_19Bridge


-- @@ L86-86 verbatim
end BernoulliRegular


-- @@ L88-88 verbatim
end
