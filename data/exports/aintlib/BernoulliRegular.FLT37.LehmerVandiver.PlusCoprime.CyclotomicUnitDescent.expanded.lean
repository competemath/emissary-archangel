/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import BernoulliRegular.FLT37.LehmerVandiver.PlusCoprime.RealClosure
public import BernoulliRegular.FLT37.PrimaryUnits


-- @@ L11-34 verbatim
/-!
# LV-cor819-b: pollaczekUnitPlus as product of realCyclotomicUnit

For Cor 8.19's Sinnott machinery to apply, we need to identify
`pollaczekUnitPlus p K i` with a concrete cyclotomic-unit-subgroup
element. Ship the identification:

  `(pollaczekUnitPlus p K i : 𝓞 K) =`
    `∏_{b=1}^{(p-1)/2} realCyclotomicUnit(b)^{b^{p-1-i}}`

where `realCyclotomicUnit p K b = cyclotomicUnit p K b · σ(cyclotomicUnit
p K b)` is the existing `cu(b) · σ(cu(b))` σ-symmetric construction
(`PrimaryUnits.realCyclotomicUnit`).

Combined with `pollaczekUnitPlus_mem_realUnits` (LV005c-CTOR-a),
`pollaczekUnitPlus` descends to `𝓞 K⁺` and is a product of
`realCyclotomicUnitPlus(b)^{b^E}` (the K⁺-side analogues). This
identifies it within Sinnott's cyclotomic-unit subgroup `C⁺ ⊆ (𝓞 K⁺)ˣ`.

## References

* Washington, *Introduction to Cyclotomic Fields*, §8.1 (cyclotomic
  units), Cor 8.19 (p. 158).
-/


-- @@ L36-36 verbatim
@[expose] public section


-- @@ L38-38 verbatim
noncomputable section


-- @@ L40-40 verbatim
open NumberField NumberField.IsCMField IsCyclotomicExtension Finset

-- @@ L41-41 verbatim
open scoped NumberField


-- @@ L43-43 verbatim
namespace BernoulliRegular


-- @@ L45-45 verbatim
namespace FLT37


-- @@ L47-47 verbatim
variable (p : ℕ) [Fact p.Prime]

-- @@ L48-49 verbatim
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
  [IsCMField K]


-- @@ L51-65 verbatim
set_option backward.isDefEq.respectTransparency false in
/-- **`pollaczekUnitPlus` underlying element factors through `realCyclotomicUnit`.**
Identifies `(pollaczekUnitPlus p K i : 𝓞 K)` as the σ-symmetric product of
`(cyclotomicUnit p K b) · σ(cyclotomicUnit p K b)` factors, which equals
`realCyclotomicUnit p K b` from `PrimaryUnits`.

This is the descent input to Sinnott's cyclotomic-unit subgroup `C⁺`:
under the descent (LV005c-CTOR-a), `pollaczekUnitPlus` lives in
`(𝓞 K⁺)ˣ` as a product of `realCyclotomicUnitPlus` factors. -/
theorem pollaczekUnitPlus_val_eq_pollaczekUnit_mul_complexConj (i : ℕ) :
    ((pollaczekUnitPlus p K i : (𝓞 K)ˣ) : 𝓞 K) =
      ((pollaczekUnit p K i : (𝓞 K)ˣ) : 𝓞 K) *
        ringOfIntegersComplexConj K
          ((pollaczekUnit p K i : (𝓞 K)ˣ) : 𝓞 K) :=
  pollaczekUnitPlus_val p K i


-- @@ L67-75 verbatim
set_option backward.isDefEq.respectTransparency false in
/-- **σ acts on `pollaczekUnit`'s underlying element as a Galois ring hom.**
Standard Galois compatibility: `σ(∏_x f(x)) = ∏_x σ(f(x))`. Used to
distribute σ over the cyclotomicUnit factors. -/
theorem ringOfIntegersComplexConj_pollaczekUnit_val (i : ℕ) :
    ringOfIntegersComplexConj K
        ((pollaczekUnit p K i : (𝓞 K)ˣ) : 𝓞 K) =
      ((unitsComplexConj K (pollaczekUnit p K i) : (𝓞 K)ˣ) : 𝓞 K) :=
  rfl


-- @@ L77-77 verbatim
end FLT37


-- @@ L79-79 verbatim
end BernoulliRegular


-- @@ L81-81 verbatim
end


-- @@ L83-83 verbatim
end
