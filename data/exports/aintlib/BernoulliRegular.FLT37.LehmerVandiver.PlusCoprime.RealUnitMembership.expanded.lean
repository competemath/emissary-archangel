/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import BernoulliRegular.FLT37.LehmerVandiver.PlusCoprime.Symmetrisation


-- @@ L10-34 verbatim
/-!
# LV005c-CTOR-a: pollaczekUnitPlus lies in the real units subgroup

Foundational input to the Cor 8.19 (real form) bridge: the symmetrised
Pollaczek unit `pollaczekUnitPlus p K i` is fixed by complex conjugation
(`pollaczekUnitPlus_complexConj`), so it descends to an element of
`(𝓞 K⁺)ˣ`.

In mathlib's terms, this means `pollaczekUnitPlus ∈ NumberField.realUnits K`,
where `realUnits K = (Units.map (algebraMap (𝓞 K⁺) (𝓞 K)).toMonoidHom).range`
is the image of the real units of `K⁺`.

Threading. The Cor 8.19 contrapositive `¬ IsPthPower(pollaczekUnitPlus
in (𝓞 K)ˣ) → ¬ p ∣ h⁺(K)` works at the level of `(𝓞 K⁺)ˣ` (Sinnott's
index formula `[(𝓞 K⁺)ˣ : C⁺] = h⁺`); to plug `pollaczekUnitPlus` into
this machine we need it AS an element of `(𝓞 K⁺)ˣ`. This file packages
that descent.

## References

* Washington, *Introduction to Cyclotomic Fields*, 2nd ed. (Springer
  GTM 83), §8.3 (cyclotomic units), Cor 8.19 (p. 158).
* Mathlib `NumberField.IsCMField.realUnits`,
  `unitsComplexConj_eq_self_iff`.
-/


-- @@ L36-36 verbatim
@[expose] public section


-- @@ L38-38 verbatim
noncomputable section


-- @@ L40-40 verbatim
open NumberField NumberField.IsCMField IsCyclotomicExtension


-- @@ L42-42 verbatim
namespace BernoulliRegular


-- @@ L44-44 verbatim
namespace FLT37


-- @@ L46-46 verbatim
variable (p : ℕ) [Fact p.Prime]

-- @@ L47-48 verbatim
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
  [IsCMField K]


-- @@ L50-58 verbatim
set_option backward.isDefEq.respectTransparency false in
/-- **`pollaczekUnitPlus` is a real unit.** Direct from σ-fixedness
(`pollaczekUnitPlus_complexConj`) and `unitsComplexConj_eq_self_iff`.
Concretely, there exists `v : (𝓞 K⁺)ˣ` with `algebraMap (𝓞 K⁺) (𝓞 K) v
= pollaczekUnitPlus p K i`. -/
theorem pollaczekUnitPlus_mem_realUnits (i : ℕ) :
    (pollaczekUnitPlus p K i) ∈ realUnits K := by
  rw [← unitsComplexConj_eq_self_iff]
  exact pollaczekUnitPlus_complexConj p K i


-- @@ L60-67 verbatim
/-- **`pollaczekUnitPlus` descends to `(𝓞 K⁺)ˣ`.** Existential form
of `pollaczekUnitPlus_mem_realUnits`. -/
theorem exists_kPlus_unit_mapping_to_pollaczekUnitPlus (i : ℕ) :
    ∃ v : (𝓞 (NumberField.maximalRealSubfield K))ˣ,
      algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) v =
        pollaczekUnitPlus p K i :=
  (mem_realUnits_iff (K := K) (pollaczekUnitPlus p K i)).mp
    (pollaczekUnitPlus_mem_realUnits p K i)


-- @@ L69-69 verbatim
end FLT37


-- @@ L71-71 verbatim
end BernoulliRegular


-- @@ L73-73 verbatim
end
