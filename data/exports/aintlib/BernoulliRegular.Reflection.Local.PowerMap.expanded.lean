module

public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
public import BernoulliRegular.Reflection.Local.RootsOfUnity


-- @@ L7-13 verbatim
/-!
# The `p`-power map on local principal units

This file proves the REF-10c1 filtration estimate for the local principal-unit
filtration at `lambda`: for positive `n`, taking `p`-th powers sends `U_n` into
`U_{n+1}`.
-/


-- @@ L15-15 verbatim
@[expose] public section


-- @@ L17-17 verbatim
noncomputable section


-- @@ L19-19 verbatim
open scoped NumberField


-- @@ L21-21 verbatim
namespace BernoulliRegular

-- @@ L22-22 verbatim
namespace Reflection

-- @@ L23-23 verbatim
namespace Local


-- @@ L25-25 verbatim
section CyclotomicSetup


-- @@ L27-28 verbatim
variable (p : ℕ) [Fact p.Prime]
  (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]


-- @@ L30-39 verbatim
/-- The rational prime `p` lies in the local maximal ideal above `p`. -/
theorem natCast_prime_mem_localCyclotomicMaximalIdeal :
    (p : localCyclotomicRing p K) ∈ localCyclotomicMaximalIdeal p K := by
  have : IsCyclotomicExtension {p ^ (0 + 1)} ℚ K := by simpa using ‹_›
  have hp_global : (p : 𝓞 K) ∈ cyclotomicLambda p K := by
    simpa [cyclotomicLambda, zetaPrime] using
      IsCyclotomicExtension.Rat.p_mem_span_zeta_sub_one p 0 (by simp)
  rw [← localCyclotomicMaximalIdeal_eq_map p K]
  simpa using
    Ideal.mem_map_of_mem (algebraMap (𝓞 K) (localCyclotomicRing p K)) hp_global


-- @@ L41-56 verbatim
/-- Globally, `p` lies in `lambda^(p-1)` in the prime cyclotomic field. -/
theorem natCast_prime_mem_cyclotomicLambda_pow_pred :
    (p : 𝓞 K) ∈ cyclotomicLambda p K ^ (p - 1) := by
  have : IsCyclotomicExtension {p ^ (0 + 1)} ℚ K := by simpa using ‹_›
  have hζ : IsPrimitiveRoot (IsCyclotomicExtension.zeta p ℚ K) (p ^ (0 + 1)) := by
    simp
  have : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
  have hfin : Module.finrank ℚ K = p - 1 := by
    rw [IsCyclotomicExtension.finrank (K := ℚ) (L := K)
      (Polynomial.cyclotomic.irreducible_rat (NeZero.pos p)),
      Nat.totient_prime (Fact.out : Nat.Prime p)]
  have hp_span : (algebraMap ℤ (𝓞 K)) (p : ℤ) ∈
      Ideal.map (algebraMap ℤ (𝓞 K)) (Ideal.span {(p : ℤ)}) :=
    Ideal.mem_map_of_mem _ (Ideal.mem_span_singleton_self (p : ℤ))
  rw [IsCyclotomicExtension.Rat.map_eq_span_zeta_sub_one_pow p 0 hζ] at hp_span
  simpa [cyclotomicLambda, zetaPrime, hfin] using hp_span


-- @@ L58-63 verbatim
/-- Locally, `p` has `lambda`-adic order at least `p - 1`. -/
theorem natCast_prime_mem_localCyclotomicMaximalIdeal_pow_pred :
    (p : localCyclotomicRing p K) ∈ (localCyclotomicMaximalIdeal p K) ^ (p - 1) := by
  rw [← localCyclotomicMaximalIdeal_eq_map p K, ← Ideal.map_pow]
  simpa using Ideal.mem_map_of_mem (algebraMap (𝓞 K) (localCyclotomicRing p K))
    (natCast_prime_mem_cyclotomicLambda_pow_pred (p := p) (K := K))


-- @@ L65-94 verbatim
/-- For positive filtration steps, the `p`-power map raises the filtration by one. -/
theorem pow_mem_principalUnitSubgroup_succ_of_pos {n : ℕ} (hn : 1 ≤ n)
    {u : localCyclotomicUnitGroup p K}
    (hu : u ∈ principalUnitSubgroup p K n) :
    u ^ p ∈ principalUnitSubgroup p K (n + 1) := by
  rw [mem_principalUnitSubgroup_iff] at hu ⊢
  rw [Units.val_pow_eq_pow_val]
  let R := localCyclotomicRing p K
  let M := localCyclotomicMaximalIdeal p K
  let x : R := (u : R) - 1
  have hx : x ∈ M ^ n := by
    simpa [x, M, R] using hu
  have hpM : (p : R) ∈ M := by
    simpa [R, M] using natCast_prime_mem_localCyclotomicMaximalIdeal (p := p) (K := K)
  have hu_eq : (u : R) = 1 + x := by
    simp [x]
  obtain ⟨r, hr⟩ := exists_add_pow_prime_eq (R := R) (p := p)
    (Fact.out : Nat.Prime p) (1 : R) x
  have hpow_formula : (1 + x) ^ p - 1 = x ^ p + (p : R) * x * r := by
    linear_combination hr
  rw [hu_eq, hpow_formula]
  apply Ideal.add_mem
  · have hxpow_np : x ^ p ∈ M ^ (n * p) := by
      simpa [pow_mul] using Ideal.pow_mem_pow hx p
    refine Ideal.pow_le_pow_right ?_ hxpow_np
    calc n + 1 ≤ n * 2 := by lia
      _ ≤ n * p := Nat.mul_le_mul_left n (Fact.out : Nat.Prime p).two_le
  · have hpx_succ : (p : R) * x ∈ M ^ (n + 1) := by
      simpa [pow_succ'] using Ideal.mul_mem_mul hpM hx
    simpa [mul_assoc] using Ideal.mul_mem_right r (M ^ (n + 1)) hpx_succ


-- @@ L96-102 verbatim
/-- The subgroup of `p`-th powers of `U_n` lies in `U_{n+1}` for positive `n`. -/
theorem principalUnitPowerSubgroup_le_succ_of_pos {n : ℕ} (hn : 1 ≤ n) :
    principalUnitPowerSubgroup p K p n ≤ principalUnitSubgroup p K (n + 1) := by
  intro u hu
  rw [mem_principalUnitPowerSubgroup_iff] at hu
  rcases hu with ⟨v, hv, rfl⟩
  exact pow_mem_principalUnitSubgroup_succ_of_pos (p := p) (K := K) hn hv


-- @@ L104-136 verbatim
/-- For `n >= 2`, the cyclotomic ramification estimate raises `U_n` by `p - 1`. -/
theorem pow_mem_principalUnitSubgroup_add_pred_of_two_le {n : ℕ} (hn : 2 ≤ n)
    {u : localCyclotomicUnitGroup p K}
    (hu : u ∈ principalUnitSubgroup p K n) :
    u ^ p ∈ principalUnitSubgroup p K (n + (p - 1)) := by
  rw [mem_principalUnitSubgroup_iff] at hu ⊢
  rw [Units.val_pow_eq_pow_val]
  let R := localCyclotomicRing p K
  let M := localCyclotomicMaximalIdeal p K
  let x : R := (u : R) - 1
  have hx : x ∈ M ^ n := by
    simpa [x, M, R] using hu
  have hpM : (p : R) ∈ M ^ (p - 1) := by
    simpa [R, M] using
      natCast_prime_mem_localCyclotomicMaximalIdeal_pow_pred (p := p) (K := K)
  have hu_eq : (u : R) = 1 + x := by
    simp [x]
  obtain ⟨r, hr⟩ := exists_add_pow_prime_eq (R := R) (p := p)
    (Fact.out : Nat.Prime p) (1 : R) x
  have hpow_formula : (1 + x) ^ p - 1 = x ^ p + (p : R) * x * r := by
    linear_combination hr
  rw [hu_eq, hpow_formula]
  apply Ideal.add_mem
  · have hp_one : 1 ≤ p := (Fact.out : Nat.Prime p).one_le
    have hnp : n + (p - 1) ≤ n * p := by
      have h2 : p - 1 ≤ n * (p - 1) := Nat.le_mul_of_pos_left _ (by lia)
      have h1 : n * (p - 1) + n = n * p := by
        rw [← Nat.mul_succ, Nat.succ_eq_add_one, Nat.sub_add_cancel hp_one]
      lia
    exact Ideal.pow_le_pow_right hnp (by simpa [pow_mul] using Ideal.pow_mem_pow hx p)
  · have hpx_step : (p : R) * x ∈ M ^ (n + (p - 1)) := by
      simpa [pow_add, mul_comm] using Ideal.mul_mem_mul hx hpM
    simpa [mul_assoc] using Ideal.mul_mem_right r (M ^ (n + (p - 1))) hpx_step


-- @@ L138-144 verbatim
/-- The subgroup of `p`-th powers of `U_n` lies in `U_{n+p-1}` for `n >= 2`. -/
theorem principalUnitPowerSubgroup_le_add_pred_of_two_le {n : ℕ} (hn : 2 ≤ n) :
    principalUnitPowerSubgroup p K p n ≤ principalUnitSubgroup p K (n + (p - 1)) := by
  intro u hu
  rw [mem_principalUnitPowerSubgroup_iff] at hu
  rcases hu with ⟨v, hv, rfl⟩
  exact pow_mem_principalUnitSubgroup_add_pred_of_two_le (p := p) (K := K) hn hv


-- @@ L146-155 verbatim
/-- For `u ∈ U_2`, taking `p`-th powers lands in `U_{p+1}`. -/
theorem pow_mem_principalUnitSubgroup_p_add_one_of_mem_two
    {u : localCyclotomicUnitGroup p K}
    (hu : u ∈ principalUnitSubgroup p K 2) :
    u ^ p ∈ principalUnitSubgroup p K (p + 1) := by
  have hp_one : 1 ≤ p := (Fact.out : Nat.Prime p).one_le
  have hidx : 2 + (p - 1) = p + 1 := by lia
  simpa [hidx] using
    pow_mem_principalUnitSubgroup_add_pred_of_two_le (p := p) (K := K)
      (n := 2) (by decide) hu


-- @@ L157-163 verbatim
/-- The subgroup of `p`-th powers of `U_2` lies in `U_{p+1}`. -/
theorem principalUnitPowerSubgroup_two_le_p_add_one :
    principalUnitPowerSubgroup p K p 2 ≤ principalUnitSubgroup p K (p + 1) := by
  intro u hu
  rw [mem_principalUnitPowerSubgroup_iff] at hu
  rcases hu with ⟨v, hv, rfl⟩
  exact pow_mem_principalUnitSubgroup_p_add_one_of_mem_two (p := p) (K := K) hv


-- @@ L165-165 verbatim
end CyclotomicSetup


-- @@ L167-167 verbatim
end Local

-- @@ L168-168 verbatim
end Reflection

-- @@ L169-169 verbatim
end BernoulliRegular
