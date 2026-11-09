/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import BernoulliRegular.Reflection.Local.Basic


-- @@ L10-23 verbatim
/-!
# Principal-unit filtration API

This file proves the formal subgroup facts about the local principal-unit
filtration

```text
U_n = 1 + lambda^n O_F.
```

It is the REF-10a layer: no cyclotomic ramification calculation is used here.
The lemmas only use the local notation from `Local.Basic` and general facts
about powers of ideals and subgroups.
-/


-- @@ L25-25 verbatim
@[expose] public section


-- @@ L27-27 verbatim
noncomputable section


-- @@ L29-29 verbatim
open scoped NumberField


-- @@ L31-31 verbatim
namespace BernoulliRegular


-- @@ L33-33 verbatim
namespace Ideal


-- @@ L35-35 verbatim
section OneUnits


-- @@ L37-37 verbatim
variable {R : Type*} [CommRing R]


-- @@ L39-43 verbatim
/-- Congruence-one subgroups are monotone in the defining ideal. -/
theorem oneUnitsSubgroup_mono {I J : Ideal R} (hIJ : I ≤ J) :
    oneUnitsSubgroup I ≤ oneUnitsSubgroup J := by
  intro u hu
  exact hIJ hu


-- @@ L45-48 verbatim
@[simp]
theorem oneUnitsSubgroup_top : oneUnitsSubgroup (⊤ : Ideal R) = ⊤ := by
  ext u
  simp [oneUnitsSubgroup]


-- @@ L50-50 verbatim
end OneUnits


-- @@ L52-52 verbatim
end Ideal


-- @@ L54-54 verbatim
namespace Reflection

-- @@ L55-55 verbatim
namespace Local


-- @@ L57-57 verbatim
section CyclotomicSetup


-- @@ L59-60 verbatim
variable (p : ℕ) [Fact p.Prime]
  (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]


-- @@ L62-64 verbatim
@[simp]
theorem principalUnitSubgroup_zero : principalUnitSubgroup p K 0 = ⊤ := by
  simp [principalUnitSubgroup]


-- @@ L66-71 verbatim
/-- The principal-unit filtration is antitone in the index. -/
theorem principalUnitSubgroup_mono {m n : ℕ} (h : n ≤ m) :
    principalUnitSubgroup p K m ≤ principalUnitSubgroup p K n := by
  intro u hu
  rw [mem_principalUnitSubgroup_iff] at hu ⊢
  exact Ideal.pow_le_pow_right h hu


-- @@ L73-77 verbatim
/-- Bundled antitonicity of the principal-unit filtration. -/
theorem principalUnitSubgroup_antitone :
    Antitone (principalUnitSubgroup p K) := by
  intro n m h
  exact principalUnitSubgroup_mono (p := p) (K := K) h


-- @@ L79-82 verbatim
/-- Successive filtration steps are nested. -/
theorem principalUnitSubgroup_succ_le (n : ℕ) :
    principalUnitSubgroup p K (n + 1) ≤ principalUnitSubgroup p K n :=
  principalUnitSubgroup_mono (p := p) (K := K) (Nat.le_succ n)


-- @@ L84-88 verbatim
theorem mem_principalUnitSubgroup_of_le {m n : ℕ} (h : n ≤ m)
    {u : localCyclotomicUnitGroup p K}
    (hu : u ∈ principalUnitSubgroup p K m) :
    u ∈ principalUnitSubgroup p K n :=
  principalUnitSubgroup_mono (p := p) (K := K) h hu


-- @@ L90-94 verbatim
theorem mem_principalUnitSubgroup_succ {n : ℕ}
    {u : localCyclotomicUnitGroup p K}
    (hu : u ∈ principalUnitSubgroup p K (n + 1)) :
    u ∈ principalUnitSubgroup p K n :=
  mem_principalUnitSubgroup_of_le (p := p) (K := K) (Nat.le_succ n) hu


-- @@ L96-99 verbatim
@[simp]
theorem one_mem_principalUnitSubgroup (n : ℕ) :
    (1 : localCyclotomicUnitGroup p K) ∈ principalUnitSubgroup p K n :=
  (principalUnitSubgroup p K n).one_mem


-- @@ L101-106 verbatim
theorem mul_mem_principalUnitSubgroup {n : ℕ}
    {u v : localCyclotomicUnitGroup p K}
    (hu : u ∈ principalUnitSubgroup p K n)
    (hv : v ∈ principalUnitSubgroup p K n) :
    u * v ∈ principalUnitSubgroup p K n :=
  (principalUnitSubgroup p K n).mul_mem hu hv


-- @@ L108-112 verbatim
theorem inv_mem_principalUnitSubgroup {n : ℕ}
    {u : localCyclotomicUnitGroup p K}
    (hu : u ∈ principalUnitSubgroup p K n) :
    u⁻¹ ∈ principalUnitSubgroup p K n :=
  (principalUnitSubgroup p K n).inv_mem hu


-- @@ L114-121 verbatim
theorem div_mem_principalUnitSubgroup {n : ℕ}
    {u v : localCyclotomicUnitGroup p K}
    (hu : u ∈ principalUnitSubgroup p K n)
    (hv : v ∈ principalUnitSubgroup p K n) :
    u / v ∈ principalUnitSubgroup p K n := by
  simpa [div_eq_mul_inv] using
    mul_mem_principalUnitSubgroup (p := p) (K := K) hu
      (inv_mem_principalUnitSubgroup (p := p) (K := K) hv)


-- @@ L123-127 verbatim
theorem pow_mem_principalUnitSubgroup {n q : ℕ}
    {u : localCyclotomicUnitGroup p K}
    (hu : u ∈ principalUnitSubgroup p K n) :
    u ^ q ∈ principalUnitSubgroup p K n :=
  (principalUnitSubgroup p K n).pow_mem hu q


-- @@ L129-133 verbatim
theorem zpow_mem_principalUnitSubgroup {n : ℕ} (q : ℤ)
    {u : localCyclotomicUnitGroup p K}
    (hu : u ∈ principalUnitSubgroup p K n) :
    u ^ q ∈ principalUnitSubgroup p K n :=
  (principalUnitSubgroup p K n).zpow_mem hu q


-- @@ L135-138 verbatim
/-- The subgroup of `q`-th powers of `U_n`. -/
def principalUnitPowerSubgroup (q n : ℕ) :
    Subgroup (localCyclotomicUnitGroup p K) :=
  (principalUnitSubgroup p K n).map (powMonoidHom q)


-- @@ L140-145 verbatim
@[simp]
theorem mem_principalUnitPowerSubgroup_iff {q n : ℕ}
    {u : localCyclotomicUnitGroup p K} :
    u ∈ principalUnitPowerSubgroup p K q n ↔
      ∃ v, v ∈ principalUnitSubgroup p K n ∧ v ^ q = u := by
  rfl


-- @@ L147-153 verbatim
/-- Powers of elements of `U_n` still lie in `U_n`. -/
theorem principalUnitPowerSubgroup_le (q n : ℕ) :
    principalUnitPowerSubgroup p K q n ≤ principalUnitSubgroup p K n := by
  intro u hu
  rw [mem_principalUnitPowerSubgroup_iff] at hu
  rcases hu with ⟨v, hv, rfl⟩
  exact pow_mem_principalUnitSubgroup (p := p) (K := K) hv


-- @@ L155-158 verbatim
/-- The `q`-th-power subgroups inherit the filtration nesting. -/
theorem principalUnitPowerSubgroup_mono {m n q : ℕ} (h : n ≤ m) :
    principalUnitPowerSubgroup p K q m ≤ principalUnitPowerSubgroup p K q n :=
  Subgroup.map_mono (principalUnitSubgroup_mono (p := p) (K := K) h)


-- @@ L160-160 verbatim
end CyclotomicSetup


-- @@ L162-162 verbatim
end Local

-- @@ L163-163 verbatim
end Reflection


-- @@ L165-165 verbatim
end BernoulliRegular
