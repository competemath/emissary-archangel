module

public import BernoulliRegular.FLT37.LehmerVandiver.PlusCoprime.Sinnott.CyclotomicUnitGroup
public import BernoulliRegular.FLT37.LehmerVandiver.PlusCoprime.Sinnott.SigmaPreservation
public import BernoulliRegular.FLT37.LehmerVandiver.PlusCoprime.Symmetrisation


-- @@ L7-17 verbatim
/-!
# Pollaczek units in cyclotomic-unit subgroups

This file records that Pollaczek units and their σ-symmetrisations lie in the
cyclotomic-unit subgroup, and that the symmetrised unit lies in the real plus
subgroup. This is Step (E) of the Sinnott / Corollary 8.19 bridge construction.

## References

* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., §8.3.
-/


-- @@ L19-19 verbatim
@[expose] public section


-- @@ L21-21 verbatim
noncomputable section


-- @@ L23-23 verbatim
open NumberField NumberField.IsCMField


-- @@ L25-25 verbatim
namespace BernoulliRegular


-- @@ L27-27 verbatim
namespace FLT37


-- @@ L29-29 verbatim
namespace Sinnott


-- @@ L31-31 verbatim
variable (p : ℕ) [hp : Fact p.Prime]

-- @@ L32-32 verbatim
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]


-- @@ L34-45 verbatim
/-- The Pollaczek unit belongs to the cyclotomic-units subgroup. -/
theorem pollaczekUnit_mem_cyclotomicUnitsSubgroup (hp_two : 2 ≤ p) (i : ℕ) :
    FLT37.pollaczekUnit p K i ∈ cyclotomicUnitsSubgroup p K hp_two := by
  simp only [FLT37.pollaczekUnit]
  apply Subgroup.prod_mem
  rintro ⟨b, hb⟩ _
  rw [FLT37.mem_pollaczek_range_iff] at hb
  obtain ⟨hb_pos, hb_le⟩ := hb
  apply Subgroup.pow_mem
  simp only [FLT37.pollaczekFactor]
  exact cyclotomicUnitUnit_mem_cyclotomicUnitsSubgroup p K _ hb_pos
    (FLT37.pollaczek_lt_of_le_half p hb_le) hp_two


-- @@ L47-47 verbatim
variable [IsCMField K]


-- @@ L49-56 verbatim
/-- The σ-symmetrised Pollaczek unit belongs to the cyclotomic-units subgroup. -/
theorem pollaczekUnitPlus_mem_cyclotomicUnitsSubgroup (hp_two : 2 ≤ p) (i : ℕ) :
    FLT37.pollaczekUnitPlus p K i ∈ cyclotomicUnitsSubgroup p K hp_two := by
  simp only [FLT37.pollaczekUnitPlus]
  apply Subgroup.mul_mem
  · exact pollaczekUnit_mem_cyclotomicUnitsSubgroup (p := p) (K := K) hp_two i
  · exact unitsComplexConj_mem_cyclotomicUnitsSubgroup_of_mem (p := p) (K := K) hp_two
      (pollaczekUnit_mem_cyclotomicUnitsSubgroup (p := p) (K := K) hp_two i)


-- @@ L58-65 verbatim
/-- The σ-symmetrised Pollaczek unit belongs to the plus cyclotomic-units subgroup. -/
theorem pollaczekUnitPlus_mem_cyclotomicUnitsPlus (hp_two : 2 ≤ p) (i : ℕ) :
    FLT37.pollaczekUnitPlus p K i ∈ cyclotomicUnitsPlus p K hp_two := by
  refine ⟨?_, ?_⟩
  · exact pollaczekUnitPlus_mem_cyclotomicUnitsSubgroup (p := p) (K := K) hp_two i
  · change FLT37.pollaczekUnitPlus p K i ∈ realUnits K
    rw [← unitsComplexConj_eq_self_iff]
    exact FLT37.pollaczekUnitPlus_complexConj p K i


-- @@ L67-67 verbatim
end Sinnott


-- @@ L69-69 verbatim
end FLT37


-- @@ L71-71 verbatim
end BernoulliRegular


-- @@ L73-73 verbatim
end
