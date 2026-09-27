/-
Copyright (c) 2026 Seewoo Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seewoo Lee
-/
module

public import Mathlib.Algebra.Polynomial.FieldDivision


-- @@ L10-12 verbatim
/-!
# LeanPool.LeanPolyABC.Lib.Radical
-/


-- @@ L14-14 verbatim
@[expose] public section


-- @@ L16-16 verbatim
noncomputable section


-- @@ L18-18 verbatim
open Polynomial UniqueFactorizationMonoid


-- @@ L20-20 verbatim
namespace LeanPolyABC


-- @@ L22-22 verbatim
variable {k : Type*} [Field k] [DecidableEq k]

-- @@ L23-23 verbatim
variable {α : Type*} [CommMonoidWithZero α] [NormalizationMonoid α] [UniqueFactorizationMonoid α]


-- @@ L25-28 verbatim
open scoped Classical in
/-- Prime factors of `a` are monic factors of `a` without duplication. -/
def primeFactors (a : α) : Finset α :=
  (normalizedFactors a).toFinset


-- @@ L30-33 verbatim
open scoped Classical in
/-- Radical of `a` is a product of prime factors of `a`. -/
def radical (a : α) : α :=
  (primeFactors a).prod id


-- @@ L35-37 verbatim
theorem radical_zero_eq_one : radical (0 : α) = 1 := by
  classical
  rw [radical, primeFactors, normalizedFactors_zero, Multiset.toFinset_zero, Finset.prod_empty]


-- @@ L39-41 verbatim
theorem radical_one_eq_one : radical (1 : α) = 1 := by
  classical
  rw [radical, primeFactors, normalizedFactors_one, Multiset.toFinset_zero, Finset.prod_empty]


-- @@ L43-48 verbatim
theorem radical_associated_eq {a b : α} (h : Associated a b) : radical a = radical b := by
  classical
  rcases iff_iff_and_or_not_and_not.mp h.eq_zero_iff with (⟨rfl, rfl⟩ | ⟨ha, hb⟩)
  · rfl
  · simp_rw [radical, primeFactors]
    rw [(associated_iff_normalizedFactors_eq_normalizedFactors ha hb).mp h]


-- @@ L50-51 verbatim
theorem radical_unit_eq_one {a : α} (h : IsUnit a) : radical a = 1 :=
  (radical_associated_eq (associated_one_iff_isUnit.mpr h)).trans radical_one_eq_one


-- @@ L53-54 verbatim
theorem radical_mul_unit_left {u a : α} (h : IsUnit u) : radical (u * a) = radical a :=
  radical_associated_eq (associated_unit_mul_left _ _ h)


-- @@ L56-57 verbatim
theorem radical_mul_unit_right {u a : α} (h : IsUnit u) : radical (a * u) = radical a :=
  radical_associated_eq (associated_mul_unit_left _ _ h)


-- @@ L59-63 verbatim
theorem primeFactors_pow (a : α) {n : ℕ} (hn : 0 < n) : primeFactors (a ^ n) = primeFactors a := by
  classical
  simp_rw [primeFactors]
  simp only [normalizedFactors_pow]
  rw [Multiset.toFinset_nsmul _ _ (ne_of_gt hn)]


-- @@ L65-66 verbatim
theorem radical_pow (a : α) {n : Nat} (hn : 0 < n) : radical (a ^ n) = radical a := by
  simp_rw [radical, primeFactors_pow a hn]


-- @@ L68-75 verbatim
theorem radical_dvd_self (a : α) : radical a ∣ a := by
  classical
  by_cases ha : a = 0
  · simp_all
  · rw [radical, ← Finset.prod_val, ← (prod_normalizedFactors ha).dvd_iff_dvd_right]
    apply Multiset.prod_dvd_prod_of_le
    rw [primeFactors, Multiset.toFinset_val]
    apply Multiset.dedup_le


-- @@ L77-85 verbatim
theorem radical_dvd_radical_self_mul {a b : α} (hb : b ≠ 0) : radical a ∣ radical (a * b) := by
  classical
  by_cases ha : a = 0
  · rw [ha, zero_mul]
  · rw [radical, ← Finset.prod_val, radical, ← Finset.prod_val]
    apply Multiset.prod_dvd_prod_of_le
    repeat rw [primeFactors]
    rw [normalizedFactors_mul ha hb, Finset.val_le_iff, Multiset.toFinset_add]
    exact Finset.subset_union_left


-- @@ L87-89 verbatim
theorem radical_dvd_radical_mul_self {a b : α} (hb : b ≠ 0) : radical a ∣ radical (b * a) := by
  rw [mul_comm b a]
  exact radical_dvd_radical_self_mul hb


-- @@ L91-96 verbatim
theorem radical_dvd_radical_of_dvd {a b : α} (hb : b ≠ 0) (h : a ∣ b) :
    radical a ∣ radical b := by
  rcases h with ⟨c, hc⟩
  rw [hc]
  rw [hc, mul_ne_zero_iff] at hb
  exact radical_dvd_radical_self_mul hb.right


-- @@ L98-107 verbatim
theorem radical_mul_dvd_mul_radical (a b : α) : radical (a * b) ∣ radical a * radical b := by
  classical
  by_cases ha : a = 0
  · simp_all
  by_cases hb : b = 0
  · simp_all
  rw [radical, primeFactors, normalizedFactors_mul ha hb, Multiset.toFinset_add, radical,
    primeFactors, radical, primeFactors]
  exact ⟨((normalizedFactors a).toFinset ∩ (normalizedFactors b).toFinset).prod id,
    (Finset.prod_union_inter).symm⟩


-- @@ L109-113 verbatim
theorem radical_prime {a : α} (ha : Prime a) : radical a = normalize a := by
  classical
  rw [radical, primeFactors]
  rw [normalizedFactors_irreducible ha.irreducible]
  simp only [Multiset.toFinset_singleton, id, Finset.prod_singleton]


-- @@ L115-118 verbatim
theorem radical_prime_pow {a : α} (ha : Prime a) {n : ℕ} (hn : 1 ≤ n) :
    radical (a ^ n) = normalize a := by
  rw [radical_pow a hn]
  exact radical_prime ha


-- @@ L120-128 verbatim
theorem prime_dvd_radical_iff {a p : α} (ha : a ≠ 0) (hp : Prime p) :
    p ∣ radical a ↔ p ∣ a := by
  classical
  constructor
  · exact fun h => h.trans <| radical_dvd_self a
  · intro hpa
    rcases exists_mem_normalizedFactors_of_dvd ha hp.irreducible hpa with ⟨q, ⟨hqf, hpq⟩⟩
    rw [hpq.dvd_iff_dvd_left, radical, primeFactors]
    exact Finset.dvd_prod_of_mem id (Multiset.mem_toFinset.mpr hqf)


-- @@ L130-142 verbatim
theorem radical_isUnit_iff {a : α} (h : a ≠ 0) : IsUnit (radical a) ↔ IsUnit a := by
  constructor
  · contrapose
    intro ha
    rcases exists_mem_factors h ha with ⟨p, hpf⟩
    have hpp := prime_of_factor _ hpf
    have hpd := dvd_of_mem_factors hpf
    exact not_isUnit_of_not_isUnit_dvd hpp.not_isUnit ((prime_dvd_radical_iff h hpp).mpr hpd)
  · intro ha
    rw [radical_unit_eq_one ha]
    exact isUnit_one

-- Theorems for commutative rings

-- @@ L143-144 verbatim
variable {R : Type _} [CommRing R] [IsDomain R] [NormalizationMonoid R]
  [UniqueFactorizationMonoid R]


-- @@ L146-146 verbatim
namespace IsCoprime


-- @@ L148-157 verbatim
omit [IsDomain R] in
/-- coprime polynomials have disjoint prime factors (as multisets). -/
private theorem disjoint_normalizedFactors {a b : R} (hc : IsCoprime a b) :
    Disjoint (normalizedFactors a) (normalizedFactors b) := by
  rw [Multiset.disjoint_left]
  intro x hxa hxb
  have x_dvd_a := dvd_of_mem_normalizedFactors hxa
  have x_dvd_b := dvd_of_mem_normalizedFactors hxb
  have xp := prime_of_normalized_factor x hxa
  exact xp.not_isUnit (hc.isUnit_of_dvd' x_dvd_a x_dvd_b)


-- @@ L159-164 verbatim
omit [IsDomain R] in
-- coprime polynomials have disjoint prime factors (as finsets)
private theorem disjoint_primeFactors {a b : R} (hc : IsCoprime a b) :
    Disjoint (primeFactors a) (primeFactors b) := by
  classical
  exact Multiset.disjoint_toFinset.mpr (disjoint_normalizedFactors hc)


-- @@ L166-174 verbatim
omit [IsDomain R] in
private theorem hMul_primeFactors_disjUnion {a b : R} (ha : a ≠ 0) (hb : b ≠ 0)
    (hc : IsCoprime a b) :
    primeFactors (a * b) =
      (primeFactors a).disjUnion (primeFactors b) (disjoint_primeFactors hc) := by
  classical
  rw [Finset.disjUnion_eq_union]
  simp_rw [primeFactors]
  rw [normalizedFactors_mul ha hb, Multiset.toFinset_add]


-- @@ L176-176 verbatim
end IsCoprime


-- @@ L178-182 verbatim
omit [IsDomain R] in
-- possible TODO: the proof is unnecessarily long
@[simp]
theorem radical_neg_one : radical (-1 : R) = 1 :=
  radical_unit_eq_one isUnit_one.neg


-- @@ L184-196 verbatim
omit [IsDomain R] in
theorem radical_hMul {a b : R} (hc : IsCoprime a b) :
    radical (a * b) = radical a * radical b := by
  classical
  by_cases ha : a = 0
  · subst ha; rw [isCoprime_zero_left] at hc
    simp only [MulZeroClass.zero_mul, radical_zero_eq_one, one_mul, radical_unit_eq_one hc]
  by_cases hb : b = 0
  · subst hb; rw [isCoprime_zero_right] at hc
    simp only [MulZeroClass.mul_zero, radical_zero_eq_one, mul_one, radical_unit_eq_one hc]
  simp_rw [radical]
  rw [IsCoprime.hMul_primeFactors_disjUnion ha hb hc]
  rw [Finset.prod_disjUnion (IsCoprime.disjoint_primeFactors hc)]


-- @@ L198-202 verbatim
omit [IsDomain R] in
theorem radical_neg {a : R} : radical (-a) = radical a :=
  neg_one_mul a ▸ (radical_associated_eq <| associated_unit_mul_left a (-1) isUnit_one.neg)

-- This actually holds for nontrivial monoids - do not need ring assumption.

-- @@ L203-209 verbatim
theorem radical_ne_zero (a : R) : radical a ≠ 0 := by
  classical
  rw [radical, ← Finset.prod_val]
  apply Multiset.prod_ne_zero
  rw [primeFactors]
  simp only [Multiset.toFinset_val, Multiset.mem_dedup]
  exact zero_notMem_normalizedFactors _


-- @@ L211-211 verbatim
namespace Polynomial


-- @@ L213-214 verbatim
theorem radical_degree_le {a : k[X]} (ha : a ≠ 0) : (radical a).degree ≤ a.degree :=
  degree_le_of_dvd (radical_dvd_self a) ha


-- @@ L216-219 verbatim
theorem radical_natDegree_le (a : k[X]) : (radical a).natDegree ≤ a.natDegree := by
  by_cases ha : a = 0
  · rw [ha, radical_zero_eq_one, natDegree_one, natDegree_zero]
  · exact natDegree_le_of_dvd (radical_dvd_self a) ha


-- @@ L221-225 verbatim
theorem radical_natDegree_mul_le (a b : k[X]) :
    (radical (a * b)).natDegree ≤ (radical a).natDegree + (radical b).natDegree := by
  rw [← natDegree_mul (radical_ne_zero _) (radical_ne_zero _)]
  exact natDegree_le_of_dvd (radical_mul_dvd_mul_radical a b)
    (mul_ne_zero (radical_ne_zero _) (radical_ne_zero _))


-- @@ L227-227 verbatim
end Polynomial


-- @@ L229-229 verbatim
end LeanPolyABC
