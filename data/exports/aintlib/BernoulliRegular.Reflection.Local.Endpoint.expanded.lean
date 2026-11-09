/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import BernoulliRegular.Reflection.Local.PowerMap


-- @@ L10-16 verbatim
/-!
# Endpoint local-unit subgroups

This file starts the REF-10d endpoint layer.  It packages the formal subgroup
assembled from the cyclotomic `p`-th roots of unity and `U_2`, and records the
containment and `p`-power consequences that follow from REF-10b and REF-10c.
-/


-- @@ L18-18 verbatim
@[expose] public section


-- @@ L20-20 verbatim
noncomputable section


-- @@ L22-22 verbatim
open scoped NumberField


-- @@ L24-24 verbatim
namespace BernoulliRegular

-- @@ L25-25 verbatim
namespace Reflection

-- @@ L26-26 verbatim
namespace Local


-- @@ L28-28 verbatim
section CyclotomicSetup


-- @@ L30-31 verbatim
variable (p : ℕ) [Fact p.Prime]
  (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]


-- @@ L33-36 verbatim
/-- The endpoint subgroup `mu_p * U_2`, represented as a subgroup supremum. -/
noncomputable def localCyclotomicEndpointSubgroup :
    Subgroup (localCyclotomicUnitGroup p K) :=
  localCyclotomicMuP p K ⊔ principalUnitSubgroup p K 2


-- @@ L38-41 verbatim
theorem localCyclotomicMuP_le_endpointSubgroup :
    localCyclotomicMuP p K ≤ localCyclotomicEndpointSubgroup p K := by
  rw [localCyclotomicEndpointSubgroup]
  exact le_sup_left


-- @@ L43-46 verbatim
theorem principalUnitSubgroup_two_le_endpointSubgroup :
    principalUnitSubgroup p K 2 ≤ localCyclotomicEndpointSubgroup p K := by
  rw [localCyclotomicEndpointSubgroup]
  exact le_sup_right


-- @@ L48-54 verbatim
/-- The formal inclusion `mu_p * U_2 <= U_1`. -/
theorem localCyclotomicEndpointSubgroup_le_principalUnitSubgroup_one :
    localCyclotomicEndpointSubgroup p K ≤ principalUnitSubgroup p K 1 := by
  rw [localCyclotomicEndpointSubgroup]
  exact sup_le
    (localCyclotomicMuP_le_principalUnitSubgroup_one (p := p) (K := K))
    (principalUnitSubgroup_mono (p := p) (K := K) (by decide : 1 ≤ 2))


-- @@ L56-59 verbatim
/-- The subgroup of `p`-th powers of `mu_p * U_2`. -/
noncomputable def localCyclotomicEndpointPowerSubgroup :
    Subgroup (localCyclotomicUnitGroup p K) :=
  (localCyclotomicEndpointSubgroup p K).map (powMonoidHom p)


-- @@ L61-69 verbatim
theorem localCyclotomicMuPPowerSubgroup_le_principalUnitSubgroup_p_add_one :
    (localCyclotomicMuP p K).map (powMonoidHom p) ≤
      principalUnitSubgroup p K (p + 1) := by
  intro u hu
  rw [Subgroup.mem_map] at hu
  rcases hu with ⟨v, hv, rfl⟩
  change v ^ p ∈ principalUnitSubgroup p K (p + 1)
  rw [localCyclotomicMuP_pow_eq_one (p := p) (K := K) hv]
  exact one_mem_principalUnitSubgroup (p := p) (K := K) (p + 1)


-- @@ L71-79 verbatim
/-- The formal `p`-power endpoint inclusion `(mu_p * U_2)^p <= U_{p+1}`. -/
theorem localCyclotomicEndpointPowerSubgroup_le_principalUnitSubgroup_p_add_one :
    localCyclotomicEndpointPowerSubgroup p K ≤ principalUnitSubgroup p K (p + 1) := by
  rw [localCyclotomicEndpointPowerSubgroup, localCyclotomicEndpointSubgroup, Subgroup.map_sup]
  exact sup_le
    (localCyclotomicMuPPowerSubgroup_le_principalUnitSubgroup_p_add_one (p := p) (K := K))
    (by
      simpa [principalUnitPowerSubgroup] using
        principalUnitPowerSubgroup_two_le_p_add_one (p := p) (K := K))


-- @@ L81-86 verbatim
theorem pow_mem_principalUnitSubgroup_p_add_one_of_mem_endpoint
    {u : localCyclotomicUnitGroup p K}
    (hu : u ∈ localCyclotomicEndpointSubgroup p K) :
    u ^ p ∈ principalUnitSubgroup p K (p + 1) :=
  localCyclotomicEndpointPowerSubgroup_le_principalUnitSubgroup_p_add_one
    (p := p) (K := K) ⟨u, hu, rfl⟩


-- @@ L88-93 verbatim
/-- If the first endpoint equality is later supplied, then `U_1^p <= U_{p+1}` follows formally. -/
theorem principalUnitPowerSubgroup_one_le_p_add_one_of_endpoint_eq
    (h : principalUnitSubgroup p K 1 = localCyclotomicEndpointSubgroup p K) :
    principalUnitPowerSubgroup p K p 1 ≤ principalUnitSubgroup p K (p + 1) := by
  rw [principalUnitPowerSubgroup, h]
  exact localCyclotomicEndpointPowerSubgroup_le_principalUnitSubgroup_p_add_one (p := p) (K := K)


-- @@ L95-95 verbatim
end CyclotomicSetup


-- @@ L97-97 verbatim
end Local

-- @@ L98-98 verbatim
end Reflection

-- @@ L99-99 verbatim
end BernoulliRegular
