/-
Copyright (c) 2026 Arav Paladiya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arav Paladiya
-/
module

public import Mathlib.Order.Lattice.Nat
public import FactorizationTheory.Mathlib.RingTheory.Factorization.Monoid


-- @@ L11-35 verbatim
/-!
# Delta sets

This file defines the set of distances (delta set) `Δ(a)` of an element and the set of
distances `Δ(H)` of a monoid, from Chapter 1.4 of
[Geroldinger and Halter-Koch][geroldingerhalterkoch2006]. It also proves that a monoid is
half-factorial exactly when it is atomic with empty set of distances.

## Main results

* `deltaSet_eq_empty_iff`: an element has empty set of distances if and only if its set of
  lengths is a subsingleton.
* `halfFactorialMonoid_iff_monoidDeltaSet_eq_empty`: a monoid is half-factorial if and only
  if it is atomic and `Monoid.deltaSet α = ∅`.

## Implementation notes

In a monoid with zero divisors, `deltaSet 0` can be nonempty because a product of irreducibles may
vanish. Thus `Monoid.deltaSet` ranges only over nonzero elements.

## References

* [A. Geroldinger, F. Halter-Koch, *Non-Unique Factorizations: Algebraic, Combinatorial and
  Analytic Theory*][geroldingerhalterkoch2006]
-/


-- @@ L37-37 verbatim
public section


-- @@ L39-39 verbatim
assert_not_exists Field Ideal


-- @@ L41-41 verbatim
variable {α : Type*}


-- @@ L43-43 verbatim
local infixl:50 " ~ᵤ " => Associated


-- @@ L45-45 verbatim
section CommMonoid


-- @@ L47-47 verbatim
variable [CommMonoid α] {a b : α} {d k m n : ℕ}


-- @@ L49-52 verbatim
/-- The positive gaps between consecutive factorization lengths of `a`, denoted `Δ(a)`. -/
def deltaSet (a : α) : Set ℕ :=
  {d | 0 < d ∧ ∃ m ∈ factorizationLengths a, m + d ∈ factorizationLengths a ∧
    ∀ k, m < k → k < m + d → k ∉ factorizationLengths a}


-- @@ L54-59 verbatim
@[simp]
theorem mem_deltaSet :
    d ∈ deltaSet a ↔ 0 < d ∧
      ∃ m ∈ factorizationLengths a, m + d ∈ factorizationLengths a ∧
        ∀ k, m < k → k < m + d → k ∉ factorizationLengths a := by
  rfl


-- @@ L61-61 verbatim
theorem pos_of_mem_deltaSet (h : d ∈ deltaSet a) : 0 < d := h.1


-- @@ L63-64 expanded
theorem Associated.deltaSet_eq (h : Associated a b) : deltaSet a = deltaSet b := by
  rw [deltaSet, deltaSet, h.factorizationLengths_eq]


-- @@ L66-82 verbatim
/-- Two lengths of `a` with `m < n` are separated by at least one distance: there is a
distance `d` of `a` with `m + d` again a length of `a` and `m + d ≤ n`. -/
theorem exists_mem_deltaSet_of_lt (hm : m ∈ factorizationLengths a)
    (hn : n ∈ factorizationLengths a) (hmn : m < n) :
    ∃ d ∈ deltaSet a, m + d ∈ factorizationLengths a ∧ m + d ≤ n := by
  have hne : {k ∈ factorizationLengths a | m < k}.Nonempty := ⟨n, hn, hmn⟩
  set k₀ := sInf {k ∈ factorizationLengths a | m < k}
  obtain ⟨hk₀mem, hmk₀⟩ := Nat.sInf_mem hne
  have hle : k₀ ≤ n := Nat.sInf_le ⟨hn, hmn⟩
  have heq : m + (k₀ - m) = k₀ := by lia
  have hmem₀ : m + (k₀ - m) ∈ factorizationLengths a := by
    rw [heq]
    exact hk₀mem
  refine ⟨k₀ - m, ⟨by lia, m, hm, hmem₀, fun k h1 h2 hmem ↦ ?_⟩, hmem₀, by lia⟩
  have hk : k₀ ≤ k :=
    Nat.sInf_le (show k ∈ {k ∈ factorizationLengths a | m < k} from ⟨hmem, h1⟩)
  lia


-- @@ L84-94 verbatim
/-- An element has no distances exactly when it has at most one factorization length. -/
theorem deltaSet_eq_empty_iff : deltaSet a = ∅ ↔ (factorizationLengths a).Subsingleton := by
  refine ⟨fun h m hm n hn ↦ ?_, fun h ↦ Set.eq_empty_iff_forall_notMem.mpr ?_⟩
  · by_contra hne
    obtain hlt | hlt := lt_or_gt_of_ne hne
    · obtain ⟨d, hd, -, -⟩ := exists_mem_deltaSet_of_lt hm hn hlt
      exact absurd h (Set.nonempty_iff_ne_empty.mp ⟨d, hd⟩)
    · obtain ⟨d, hd, -, -⟩ := exists_mem_deltaSet_of_lt hn hm hlt
      exact absurd h (Set.nonempty_iff_ne_empty.mp ⟨d, hd⟩)
  · rintro d ⟨hd, m, hm, hmd, -⟩
    exact absurd (h hm hmd) (by lia)


-- @@ L96-98 verbatim
theorem deltaSet_nonempty_iff :
    (deltaSet a).Nonempty ↔ ¬(factorizationLengths a).Subsingleton := by
  rw [Set.nonempty_iff_ne_empty, ne_eq, deltaSet_eq_empty_iff]


-- @@ L100-102 verbatim
/-- The least distance is attained whenever `deltaSet a` is nonempty. -/
theorem sInf_mem_deltaSet (h : (deltaSet a).Nonempty) : sInf (deltaSet a) ∈ deltaSet a :=
  Nat.sInf_mem h


-- @@ L104-105 verbatim
theorem one_le_sInf_deltaSet (h : (deltaSet a).Nonempty) : 1 ≤ sInf (deltaSet a) :=
  pos_of_mem_deltaSet (sInf_mem_deltaSet h)


-- @@ L107-110 verbatim
@[simp]
theorem deltaSet_of_isUnit (h : IsUnit a) : deltaSet a = ∅ := by
  rw [deltaSet_eq_empty_iff, factorizationLengths_of_isUnit h]
  exact Set.subsingleton_singleton


-- @@ L112-115 verbatim
@[simp]
theorem deltaSet_of_irreducible (h : Irreducible a) : deltaSet a = ∅ := by
  rw [deltaSet_eq_empty_iff, factorizationLengths_of_irreducible h]
  exact Set.subsingleton_singleton


-- @@ L117-117 verbatim
end CommMonoid


-- @@ L119-119 verbatim
section CommMonoidWithZero


-- @@ L121-121 verbatim
variable [CommMonoidWithZero α] {a : α} {d : ℕ}


-- @@ L123-128 verbatim
/-- In the absence of zero divisors, the set of distances of `0` is empty. -/
theorem deltaSet_zero [NoZeroDivisors α] : deltaSet (0 : α) = ∅ := by
  obtain _ | _ := subsingleton_or_nontrivial α
  · exact deltaSet_of_isUnit (isUnit_of_subsingleton _)
  · rw [deltaSet_eq_empty_iff, factorizationLengths_zero]
    exact Set.subsingleton_empty


-- @@ L130-134 verbatim
variable (α) in
/-- The set of distances of the monoid: the union of the sets of distances of its nonzero
elements. This is `Δ(H)` of [geroldingerhalterkoch2006]. -/
def Monoid.deltaSet : Set ℕ :=
  ⋃ (a : α) (_ : a ≠ 0), _root_.deltaSet a


-- @@ L136-138 verbatim
theorem Monoid.mem_deltaSet_iff :
    d ∈ Monoid.deltaSet α ↔ ∃ a : α, a ≠ 0 ∧ d ∈ _root_.deltaSet a := by
  simp only [Monoid.deltaSet, Set.mem_iUnion, exists_prop]


-- @@ L140-141 verbatim
theorem deltaSet_subset_monoidDeltaSet (ha : a ≠ 0) : deltaSet a ⊆ Monoid.deltaSet α :=
  fun _ hd ↦ Monoid.mem_deltaSet_iff.mpr ⟨a, ha, hd⟩


-- @@ L143-151 verbatim
theorem Monoid.deltaSet_eq_empty_iff :
    Monoid.deltaSet α = ∅ ↔
      ∀ ⦃a : α⦄, a ≠ 0 → (factorizationLengths a).Subsingleton := by
  refine ⟨fun h a ha ↦ _root_.deltaSet_eq_empty_iff.mp ?_,
    fun h ↦ Set.eq_empty_iff_forall_notMem.mpr fun d hd ↦ ?_⟩
  · exact Set.subset_empty_iff.mp (h ▸ deltaSet_subset_monoidDeltaSet ha)
  · obtain ⟨a, ha, hd⟩ := Monoid.mem_deltaSet_iff.mp hd
    rw [_root_.deltaSet_eq_empty_iff.mpr (h ha)] at hd
    exact hd


-- @@ L153-156 verbatim
/-- A monoid is half-factorial if and only if it is atomic and has no distances. -/
theorem halfFactorialMonoid_iff_monoidDeltaSet_eq_empty :
    HalfFactorialMonoid α ↔ AtomicMonoid α ∧ Monoid.deltaSet α = ∅ := by
  rw [halfFactorialMonoid_iff, Monoid.deltaSet_eq_empty_iff]


-- @@ L158-159 verbatim
theorem Monoid.deltaSet_eq_empty [HalfFactorialMonoid α] : Monoid.deltaSet α = ∅ :=
  (halfFactorialMonoid_iff_monoidDeltaSet_eq_empty.mp inferInstance).2


-- @@ L161-161 verbatim
end CommMonoidWithZero
