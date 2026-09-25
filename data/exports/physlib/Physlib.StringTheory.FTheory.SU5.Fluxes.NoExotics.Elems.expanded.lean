/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.StringTheory.FTheory.SU5.Fluxes.Basic

-- @@ L9-56 verbatim
/-!

# Terms of `FluxesFive` and `FluxesTen` with no chiral exotics

## i. Overview

In this module we give the terms of type `FluxesFive` and `FluxesTen`
which obey the `NoExotics` and `HasNoZero` propositions.

In each case, there is only a finite set of such elements, which we give explicitly.
We show that these sets are complete in the module
`StringTheory.FTheory.SU5.Fluxes.NoExotics.Completeness`.

This module is reserved for the explicit sets of elements, and simple lemmas about the
elements of those elements.

## ii. Key results

- `FluxesFive.elemsNoExotics` : The multiset of elements of `FluxesFive` which obey `NoExotics`
  and `HasNoZero`.
- `FluxesTen.elemsNoExotics` : The multiset of elements of `FluxesTen` which obey `NoExotics`
  and `HasNoZero`.

## iii. Table of contents

- A. The multiset sets of `FluxesFive` with no chiral exotics and no zero fluxes
  - A.1. The definition of the multiset
  - A.2. The cardinality of the multiset is 31
  - A.3. The multiset has no duplicates
  - A.4. Every element of the multiset obeys `NoExotics`
  - A.5. Every element of the multiset has at most 4 distinct flux pairs
  - A.6. Every element of the multiset has at most 6 flux pairs
  - A.7. The sum of all flux-pairs in any element of the multiset is (3, 0)
  - A.8. Every element of the multiset obeys `HasNoZero`
  - A.9. A sum relation for subsets of elements of the multiset
- B. The multiset sets of `FluxesFive` with no chiral exotics and no zero fluxes
  - B.1. The definition of the multiset
  - B.2. The cardinality of the multiset is 6
  - B.3. The multiset has no duplicates
  - B.4. Every element of the multiset obeys `NoExotics`
  - B.5. Every element of the multiset has at most 3 distinct flux pairs
  - B.6. The sum of all flux-pairs in any element of the multiset is (3, 0)
  - B.7. Every element of the multiset obeys `HasNoZero`

## iv. References

* None.
-/


-- @@ L58-58 verbatim
@[expose] public section

-- @@ L59-59 verbatim
namespace FTheory


-- @@ L61-61 verbatim
namespace SU5


-- @@ L63-67 verbatim
/-!

## A. The multiset sets of `FluxesFive` with no chiral exotics and no zero fluxes

-/


-- @@ L69-69 verbatim
namespace FluxesFive


-- @@ L71-75 verbatim
/-!

### A.1. The definition of the multiset

-/


-- @@ L77-100 verbatim
/-- The elements of `FluxesFive` for which the `NoExotics` condition holds. -/
def elemsNoExotics : Multiset FluxesFive := {
    {⟨1, -1⟩, ⟨1, -1⟩, ⟨1, -1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩},
    {⟨1, -1⟩, ⟨1, -1⟩, ⟨1, -1⟩, ⟨0, 1⟩, ⟨0, 2⟩},
    {⟨1, -1⟩, ⟨1, -1⟩, ⟨1, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩},
    {⟨1, 1⟩, ⟨1, -1⟩, ⟨1, -1⟩, ⟨0, 1⟩},
    {⟨1, 0⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 1⟩},
    {⟨1, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 2⟩},
    {⟨1, -1⟩, ⟨1, -1⟩, ⟨1, -1⟩, ⟨0, 3⟩},
    {⟨1, -1⟩, ⟨1, -1⟩, ⟨1, 2⟩},
    {⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 1⟩}, {⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩},
    {⟨1, -1⟩, ⟨2, -2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩},
    {⟨1, -1⟩, ⟨2, -2⟩, ⟨0, 1⟩, ⟨0, 2⟩},
    {⟨1, -1⟩, ⟨2, -1⟩, ⟨0, 1⟩, ⟨0, 1⟩},
    {⟨1, 0⟩, ⟨2, -2⟩, ⟨0, 1⟩, ⟨0, 1⟩},
    {⟨1, 1⟩, ⟨2, -2⟩, ⟨0, 1⟩}, {⟨1, 0⟩, ⟨2, -1⟩, ⟨0, 1⟩},
    {⟨1, 0⟩, ⟨2, -2⟩, ⟨0, 2⟩}, {⟨1, -1⟩, ⟨2, 0⟩, ⟨0, 1⟩},
    {⟨1, -1⟩, ⟨2, -1⟩, ⟨0, 2⟩}, {⟨1, -1⟩, ⟨2, -2⟩, ⟨0, 3⟩},
    {⟨1, -1⟩, ⟨2, 1⟩}, {⟨1, 0⟩, ⟨2, 0⟩}, {⟨1, 1⟩, ⟨2, -1⟩},
    {⟨1, 2⟩, ⟨2, -2⟩},
    {⟨3, -3⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩},
    {⟨3, -3⟩, ⟨0, 1⟩, ⟨0, 2⟩}, {⟨3, -2⟩, ⟨0, 1⟩, ⟨0, 1⟩},
    {⟨3, -3⟩, ⟨0, 3⟩}, {⟨3, -2⟩, ⟨0, 2⟩}, {⟨3, -1⟩, ⟨0, 1⟩},
    {⟨3, 0⟩}}


-- @@ L102-106 verbatim
/-!

### A.2. The cardinality of the multiset is 31

-/


-- @@ L108-109 verbatim
lemma elemsNoExotics_card : elemsNoExotics.card = 31 := by
  decide


-- @@ L111-115 verbatim
/-!

### A.3. The multiset has no duplicates

-/


-- @@ L117-118 verbatim
lemma elemsNoExotics_nodup : elemsNoExotics.Nodup := by
  decide


-- @@ L120-124 verbatim
/-!

### A.4. Every element of the multiset obeys `NoExotics`

-/


-- @@ L126-129 verbatim
lemma noExotics_of_mem_elemsNoExotics (F : FluxesFive) (h : F ∈ elemsNoExotics) :
    NoExotics F := by
  revert F
  decide


-- @@ L131-135 verbatim
/-!

### A.5. Every element of the multiset has at most 4 distinct flux pairs

-/


-- @@ L137-140 verbatim
lemma toFinset_card_le_four_mem_elemsNoExotics (F : FluxesFive) (h : F ∈ elemsNoExotics) :
    F.toFinset.card ≤ 4 := by
  revert F h
  decide


-- @@ L142-146 verbatim
/-!

### A.6. Every element of the multiset has at most 6 flux pairs

-/


-- @@ L148-151 verbatim
lemma card_le_six_mem_elemsNoExotics (F : FluxesFive) (h : F ∈ elemsNoExotics) :
    F.card ≤ 6 := by
  revert F h
  decide


-- @@ L153-157 verbatim
/-!

### A.7. The sum of all flux-pairs in any element of the multiset is (3, 0)

-/


-- @@ L159-162 verbatim
lemma sum_of_mem_elemsNoExotics (F : FluxesFive) (h : F ∈ elemsNoExotics) :
    F.sum = ⟨3, 0⟩ := by
  revert F h
  decide


-- @@ L164-168 verbatim
/-!

### A.8. Every element of the multiset obeys `HasNoZero`

-/


-- @@ L170-173 verbatim
lemma hasNoZero_of_mem_elemsNoExotics (F : FluxesFive) (h : F ∈ elemsNoExotics) :
    F.HasNoZero := by
  revert F h
  decide


-- @@ L175-179 verbatim
/-!

### A.9. A sum relation for subsets of elements of the multiset

-/


-- @@ L181-186 verbatim
lemma map_sum_add_of_mem_powerset_elemsNoExotics (F S : FluxesFive)
    (hf : F ∈ FluxesFive.elemsNoExotics)
    (hS: S ∈ Multiset.powerset F) :
    (S.map (fun x => ⟨|x.1|, -|x.1|⟩)).sum +
    (S.map (fun x => ⟨(0 : ℤ), |x.1 + x.2|⟩)).sum = S.sum := by
  fin_cases hf <;> fin_cases hS <;> decide


-- @@ L188-188 verbatim
end FluxesFive


-- @@ L190-194 verbatim
/-!

## B. The multiset sets of `FluxesFive` with no chiral exotics and no zero fluxes

-/

-- @@ L195-195 verbatim
namespace FluxesTen


-- @@ L197-201 verbatim
/-!

### B.1. The definition of the multiset

-/


-- @@ L203-207 verbatim
/-- The elements of `FluxesTen` for which the `NoExotics` condition holds. -/
def elemsNoExotics : Multiset FluxesTen := {{⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩},
  {⟨1, 1⟩, ⟨1, -1⟩, ⟨1, 0⟩}, {⟨1, 0⟩, ⟨2, 0⟩},
  {⟨1, -1⟩, ⟨2, 1⟩}, {⟨1, 1⟩, ⟨2, -1⟩},
  {⟨3, 0⟩}}


-- @@ L209-213 verbatim
/-!

### B.2. The cardinality of the multiset is 6

-/


-- @@ L215-216 verbatim
lemma elemsNoExotics_card : elemsNoExotics.card = 6 := by
  decide


-- @@ L218-222 verbatim
/-!

### B.3. The multiset has no duplicates

-/


-- @@ L224-225 verbatim
lemma elemsNoExotics_nodup : elemsNoExotics.Nodup := by
  decide


-- @@ L227-231 verbatim
/-!

### B.4. Every element of the multiset obeys `NoExotics`

-/


-- @@ L233-236 verbatim
lemma noExotics_of_mem_elemsNoExotics (F : FluxesTen) (h : F ∈ elemsNoExotics) :
    NoExotics F := by
  revert F
  decide


-- @@ L238-242 verbatim
/-!

### B.5. Every element of the multiset has at most 3 distinct flux pairs

-/


-- @@ L244-247 verbatim
lemma toFinset_card_le_three_mem_elemsNoExotics (F : FluxesTen) (h : F ∈ elemsNoExotics) :
    F.toFinset.card ≤ 3 := by
  revert F h
  decide


-- @@ L249-253 verbatim
/-!

### B.6. The sum of all flux-pairs in any element of the multiset is (3, 0)

-/


-- @@ L255-258 verbatim
lemma sum_of_mem_elemsNoExotics (F : FluxesTen) (h : F ∈ elemsNoExotics) :
    F.sum = ⟨3, 0⟩ := by
  revert F h
  decide


-- @@ L260-264 verbatim
/-!

### B.7. Every element of the multiset obeys `HasNoZero`

-/


-- @@ L266-269 verbatim
lemma hasNoZero_of_mem_elemsNoExotics (F : FluxesTen) (h : F ∈ elemsNoExotics) :
    F.HasNoZero := by
  revert F h
  decide


-- @@ L271-271 verbatim
end FluxesTen


-- @@ L273-273 verbatim
end SU5


-- @@ L275-275 verbatim
end FTheory
