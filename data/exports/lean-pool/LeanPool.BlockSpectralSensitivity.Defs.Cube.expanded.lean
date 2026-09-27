/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import Mathlib.InformationTheory.Hamming


-- @@ L10-21 verbatim
/-!
# The Boolean cube

An *input* on a finite coordinate set `V` is a map `V → Bool`.  For `A : Finset V`
we write `flipSet x A` for the input `x^A` of Section 1 of `bs_lambda.txt`, obtained by
flipping every coordinate of `A`.

Hamming distance is taken from Mathlib (`hammingDist`).

Adapted for Lean Pool from `Timeroot/BS_Lam` at commit
`7bd39a8d41ee7910d3296d0477ad18f8fff9d870`; ported to Lean Pool with proof and dependency cleanup.
-/


-- @@ L23-23 verbatim
@[expose] public section


-- @@ L25-30 verbatim
/-- The symmetric difference of two distinct singletons is the corresponding pair.  This is a
general `Finset` fact, stated here because Mathlib does not have it. -/
theorem Finset.symmDiff_singleton_singleton {α : Type*} [DecidableEq α] {p q : α} (hpq : p ≠ q) :
    symmDiff ({p} : Finset α) {q} = {p, q} := by
  ext v
  by_cases h1 : v = p <;> by_cases h2 : v = q <;> simp_all [Finset.mem_symmDiff]


-- @@ L32-32 verbatim
namespace BSLambda


-- @@ L34-35 verbatim
/-- An input to a Boolean function on the coordinate set `V`. -/
abbrev Input (V : Type*) : Type _ := V → Bool


-- @@ L37-38 verbatim
/-- The all-zero input, written `0^V` in `bs_lambda.txt`. -/
def zeroInput (V : Type*) : Input V := fun _ ↦ false


-- @@ L40-40 verbatim
@[simp] lemma zeroInput_apply {V : Type*} (v : V) : zeroInput V v = false := rfl


-- @@ L42-42 verbatim
variable {V : Type*}


-- @@ L44-44 verbatim
section DecEq

-- @@ L45-45 verbatim
variable [DecidableEq V]


-- @@ L47-49 verbatim
/-- `flipSet x A` is the input written `x^A` in the source document: it flips every
coordinate lying in `A` and leaves all other coordinates unchanged. -/
def flipSet (x : Input V) (A : Finset V) : Input V := fun v ↦ if v ∈ A then !x v else x v


-- @@ L51-52 verbatim
@[simp] lemma flipSet_apply_of_mem {x : Input V} {A : Finset V} {v : V} (hv : v ∈ A) :
    flipSet x A v = !x v := by simp [flipSet, hv]


-- @@ L54-55 verbatim
@[simp] lemma flipSet_apply_of_notMem {x : Input V} {A : Finset V} {v : V} (hv : v ∉ A) :
    flipSet x A v = x v := by simp [flipSet, hv]


-- @@ L57-60 verbatim
/-- A coordinate survives `flipSet` exactly when it lies outside the flipped set. -/
@[simp] lemma flipSet_apply_eq_self_iff {x : Input V} {A : Finset V} {v : V} :
    flipSet x A v = x v ↔ v ∉ A := by
  by_cases hv : v ∈ A <;> simp [flipSet, hv]


-- @@ L62-65 verbatim
/-- A coordinate is changed by `flipSet` exactly when it lies in the flipped set. -/
lemma flipSet_apply_ne_self_iff {x : Input V} {A : Finset V} {v : V} :
    flipSet x A v ≠ x v ↔ v ∈ A := by
  simp


-- @@ L67-69 verbatim
/-- An input differs from its flip at every flipped coordinate. -/
lemma ne_flipSet_apply {x : Input V} {A : Finset V} {v : V} (hv : v ∈ A) :
    x v ≠ flipSet x A v := (flipSet_apply_ne_self_iff.2 hv).symm


-- @@ L71-73 verbatim
@[simp] lemma flipSet_empty (x : Input V) : flipSet x ∅ = x := by
  funext v
  simp [flipSet]


-- @@ L75-79 verbatim
/-- Flipping `A` and then `B` flips exactly the coordinates of the symmetric difference. -/
lemma flipSet_flipSet_symmDiff (x : Input V) (A B : Finset V) :
    flipSet (flipSet x A) B = flipSet x (symmDiff A B) := by
  funext v
  by_cases hA : v ∈ A <;> by_cases hB : v ∈ B <;> simp [flipSet, hA, hB, Finset.mem_symmDiff]


-- @@ L81-82 verbatim
@[simp] lemma flipSet_flipSet (x : Input V) (A : Finset V) : flipSet (flipSet x A) A = x := by
  rw [flipSet_flipSet_symmDiff, symmDiff_self, Finset.bot_eq_empty, flipSet_empty]


-- @@ L84-88 verbatim
/-- Flipping two distinct coordinates one after the other is the same as flipping the pair
at once. -/
lemma flipSet_singleton_flipSet_singleton (x : Input V) {p q : V} (hpq : p ≠ q) :
    flipSet (flipSet x {p}) {q} = flipSet x {p, q} := by
  rw [flipSet_flipSet_symmDiff, Finset.symmDiff_singleton_singleton hpq]


-- @@ L90-94 verbatim
/-- Undoing one half of a pair flip leaves the single flip at the other coordinate: this is
the "other midpoint" identity behind every two-midpoint argument. -/
lemma flipSet_pair_flipSet_singleton (x : Input V) {p q : V} (hpq : p ≠ q) :
    flipSet (flipSet x {p, q}) {q} = flipSet x {p} := by
  rw [← flipSet_singleton_flipSet_singleton x hpq, flipSet_flipSet]


-- @@ L96-99 verbatim
/-- Flipping a fixed set of coordinates is injective in the input. -/
lemma flipSet_left_injective (A : Finset V) : Function.Injective (flipSet · A) := by
  intro x y h
  simpa using congrArg (flipSet · A) h


-- @@ L101-103 verbatim
@[simp] lemma flipSet_left_inj {x y : Input V} {A : Finset V} :
    flipSet x A = flipSet y A ↔ x = y :=
  (flipSet_left_injective A).eq_iff


-- @@ L105-109 verbatim
/-- Distinct coordinates give distinct single-coordinate flips of a fixed input. -/
lemma flipSet_singleton_injective (x : Input V) :
    Function.Injective fun v : V ↦ flipSet x {v} := fun v w h ↦ by
  by_contra hvw
  simpa [hvw] using congrFun h v


-- @@ L111-113 verbatim
/-- The flipped coordinate of a single-coordinate flip. -/
lemma flipSet_singleton_self (x : Input V) (v : V) : flipSet x {v} v = !x v := by
  simp


-- @@ L115-118 verbatim
/-- Flipping a set of coordinates of the all-zero input yields its indicator function. -/
@[simp] lemma flipSet_zeroInput_apply (A : Finset V) (v : V) :
    flipSet (zeroInput V) A v = decide (v ∈ A) := by
  simp [flipSet]


-- @@ L120-120 verbatim
end DecEq


-- @@ L122-122 verbatim
section Fintype

-- @@ L123-123 verbatim
variable [Fintype V] [DecidableEq V]


-- @@ L125-129 verbatim
/-- The Hamming distance from `x` to `x^A` is exactly `A.card`. -/
@[simp] lemma hammingDist_flipSet (x : Input V) (A : Finset V) :
    hammingDist x (flipSet x A) = A.card := by
  simp only [hammingDist, ne_comm (a := x _), flipSet_apply_ne_self_iff,
    Finset.filter_mem_eq_inter, Finset.univ_inter]


-- @@ L131-137 verbatim
/-- Two flips of the same input differ exactly on the symmetric difference of the flipped
sets. -/
lemma hammingDist_flipSet_flipSet (x : Input V) (A B : Finset V) :
    hammingDist (flipSet x A) (flipSet x B) = (symmDiff A B).card := by
  have h : flipSet x B = flipSet (flipSet x A) (symmDiff A B) := by
    rw [flipSet_flipSet_symmDiff, symmDiff_symmDiff_cancel_left]
  rw [h, hammingDist_flipSet]


-- @@ L139-143 verbatim
/-- Every input is a flip of every other, at the set of coordinates where they differ. -/
lemma flipSet_filter_ne (x y : Input V) :
    flipSet x (Finset.univ.filter fun v ↦ x v ≠ y v) = y := by
  funext v
  by_cases h : x v = y v <;> simp [flipSet, h, Bool.eq_not_iff]


-- @@ L145-149 verbatim
/-- Two inputs at Hamming distance `1` differ in exactly one coordinate. -/
lemma exists_eq_flipSet_singleton_of_hammingDist_eq_one {x y : Input V}
    (h : hammingDist x y = 1) : ∃ v, y = flipSet x {v} := by
  obtain ⟨v, hv⟩ := Finset.card_eq_one.1 h
  exact ⟨v, (hv ▸ flipSet_filter_ne x y).symm⟩


-- @@ L151-152 verbatim
lemma hammingDist_flipSet_singleton (x : Input V) (v : V) : hammingDist x (flipSet x {v}) = 1 := by
  simp


-- @@ L154-154 verbatim
end Fintype


-- @@ L156-156 verbatim
end BSLambda
