/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.GroupTheory.Archimedean


-- @@ L11-19 verbatim
/-!
# Congruence subgroups

This defines congruence subgroups of `SL(2, ℤ)` such as `Γ(N)`, `Γ₀(N)` and `Γ₁(N)` for `N` a
natural number.

It also contains basic results about congruence subgroups.

-/


-- @@ L21-21 verbatim
@[expose] public section


-- @@ L23-23 verbatim
open Matrix.SpecialLinearGroup Matrix ModularGroup CongruenceSubgroup


-- @@ L25-25 verbatim
open scoped MatrixGroups Real


-- @@ L27-27 verbatim
variable {Γ : Subgroup SL(2, ℤ)}


-- @@ L29-29 verbatim
namespace Subgroup

-- @@ L30-35 verbatim
/-!
## Width of a subgroup

These results are in the `Subgroup` namespace to enable dot-notation, although they are specific
to the case of subgroups of the modular group.
-/

-- @@ L36-36 verbatim
variable (Γ)


-- @@ L38-40 verbatim
/-- The width of the cusp `∞` for a subgroup of `SL(2, ℤ)`, i.e. the least `n > 0` such that
`[1, n; 0, 1] ∈ Γ`. -/
noncomputable def width : ℕ := Subgroup.relIndex Γ (.zpowers ModularGroup.T)


-- @@ L42-43 verbatim
lemma width_ne_zero [Γ.FiniteIndex] : Γ.width ≠ 0 :=
  FiniteIndex.index_ne_zero


-- @@ L45-46 verbatim
lemma T_pow_width_mem : T ^ Γ.width ∈ Γ :=
  (Γ.subgroupOf <| .zpowers T).pow_index_mem ⟨_, mem_zpowers _⟩


-- @@ L48-55 verbatim
/-- The integers `n` such that `[1, n; 0, 1] ∈ Γ` are precisely the multiples of `Γ.width`. -/
lemma T_zpow_mem_iff {n : ℤ} : T ^ n ∈ Γ ↔ ↑Γ.width ∣ n := by
  let A : AddSubgroup ℤ := (Γ.comap (zpowersHom _ T)).toAddSubgroup'
  obtain ⟨m, hm⟩ := Int.subgroup_cyclic A
  have h₁ : (Γ.comap (zpowersHom _ T)).index = Γ.width := Γ.index_comap _
  have h₂ : Γ.width = A.index := by simpa [A, h₁] using A.index_toSubgroup
  rw [h₂, (by rfl : T ^ n ∈ Γ ↔ n ∈ A), hm, ← AddSubgroup.zmultiples_eq_closure,
    Int.mem_zmultiples_iff, Int.index_zmultiples, Int.natAbs_dvd]


-- @@ L57-59 verbatim
/-- The integers `n` such that `[1, n; 0, 1] ∈ Γ` are precisely the multiples of `Γ.width`. -/
lemma T_pow_mem_iff (n : ℕ) : T ^ n ∈ Γ ↔ Γ.width ∣ n := by
  simpa [Int.natCast_dvd_natCast] using Γ.T_zpow_mem_iff (n := n)


-- @@ L61-61 verbatim
variable (N : ℕ)


-- @@ L63-65 verbatim
@[simp] lemma Gamma_width : Γ(N).width = N := by
  simp [← Nat.dvd_right_iff_eq, ← Subgroup.T_pow_mem_iff, ← zpow_natCast,
    ModularGroup.coe_T_zpow, ZMod.natCast_eq_zero_iff]


-- @@ L67-68 verbatim
lemma ModularGroup_T_pow_mem_Gamma (N M : ℤ) (hNM : N ∣ M) : T ^ M ∈ Gamma N.natAbs := by
  rwa [Subgroup.T_zpow_mem_iff, Gamma_width, Int.natAbs_dvd]


-- @@ L70-70 verbatim
end Subgroup
