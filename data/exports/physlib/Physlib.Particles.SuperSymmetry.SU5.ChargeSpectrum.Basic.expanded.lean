/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Finset.Option

-- @@ L12-57 verbatim
/-!

# Charge Spectrum

## i. Overview

In this module we define the charge spectrum of a `SU(5)` SUSY GUT theory with
additional charges (usually `U(1)`) valued in `𝓩` satisfying the condition of:
- The optional existence of a `Hd` particle in the `bar 5` representation.
- The optional existence of a `Hu` particle in the `5` representation.
- The optional existence of matter in the `bar 5` representation.
- The optional existence of matter in the `10` representation.

The charge spectrum contains the information of the *unique* charges of each type of particle
present in theory. Importantly, the charge spectrum does not contain information
about the multiplicity of those charges.

With just the charge spectrum of the theory it is possible to put a number of constraints
on the theory, most notably phenomenological constraints.

By keeping the presence of `Hd` and `Hu` optional, we can define a number of useful properties
of the charge spectrum, which can help in searching for viable theories.

## ii. Key results

- `ChargeSpectrum 𝓩` : The type of charge spectra with charges of type `𝓩`, which is usually
  `ℤ`.

## iii. Table of contents

- A. The definition of the charge spectrum
  - A.1. Extensionality properties
  - A.2. Relation to products
  - A.3. Rendering
- B. The subset relation
- C. The empty charge spectrum
- D. The cardinality of a charge spectrum
- E. The power set of a charge spectrum
- F. Finite sets of charge spectra with values
  - F.1. Cardinality of finite sets of charge spectra with values

## iv. References

* None — these charge spectra were created specifically for the purpose of
  Physlib; there is no external reference.
-/


-- @@ L59-59 verbatim
@[expose] public section


-- @@ L61-61 verbatim
namespace SuperSymmetry


-- @@ L63-63 verbatim
namespace SU5


-- @@ L65-69 verbatim
/-!

## A. The definition of the charge spectrum

-/


-- @@ L71-92 verbatim
/-- The type such that an element corresponds to the collection of
  charges associated with the matter content of the theory.
  The order of charges is implicitly taken to be `qHd`, `qHu`, `Q5`, `Q10`.

  The `Q5` and `Q10` charges are represented by `Finset` rather than
  `Multiset`, so multiplicity is not included.

  This is defined for a general type `𝓩`, which could be e.g.
- `ℤ` in the case of `U(1)`,
- `ℤ × ℤ` in the case of `U(1) × U(1)`,
- `Fin 2` in the case of `ℤ₂` etc.
-/
structure ChargeSpectrum (𝓩 : Type := ℤ) where
  /-- The charge of the `Hd` particle. -/
  qHd : Option 𝓩
  /-- The negative of the charge of the `Hu` particle. That is to say,
    the charge of the `Hu` when considered in the 5-bar representation. -/
  qHu : Option 𝓩
  /-- The finite set of charges of the matter fields in the `Q5` representation. -/
  Q5 : Finset 𝓩
  /-- The finite set of charges of the matter fields in the `Q10` representation. -/
  Q10 : Finset 𝓩


-- @@ L94-94 verbatim
namespace ChargeSpectrum


-- @@ L96-96 verbatim
variable {𝓩 : Type}


-- @@ L98-106 verbatim
/-!

### A.1. Extensionality properties

We prove extensionality properties for `ChargeSpectrum 𝓩`, that is
conditions of when two elements of `ChargeSpectrum 𝓩` are equal.
We also show that when `𝓩` has decidable equality, so does `ChargeSpectrum 𝓩`.

-/


-- @@ L108-112 verbatim
lemma eq_of_parts {x y : ChargeSpectrum 𝓩} (h1 : x.qHd = y.qHd) (h2 : x.qHu = y.qHu)
    (h3 : x.Q5 = y.Q5) (h4 : x.Q10 = y.Q10) : x = y := by
  cases x
  cases y
  simp_all


-- @@ L114-117 verbatim
lemma eq_iff {x y : ChargeSpectrum 𝓩} :
    x = y ↔ x.qHd = y.qHd ∧ x.qHu = y.qHu ∧ x.Q5 = y.Q5 ∧ x.Q10 = y.Q10 :=
  ⟨fun h => ⟨congrArg qHd h, congrArg qHu h, congrArg Q5 h, congrArg Q10 h⟩,
    fun ⟨h1, h2, h3, h4⟩ => eq_of_parts h1 h2 h3 h4⟩


-- @@ L119-120 verbatim
instance [DecidableEq 𝓩] : DecidableEq (ChargeSpectrum 𝓩) := fun _ _ =>
  decidable_of_iff _ eq_iff.symm


-- @@ L122-131 verbatim
/-!

### A.2. Relation to products

We show that `ChargeSpectrum 𝓩` is equivalent to the product
`Option 𝓩 × Option 𝓩 × Finset 𝓩 × Fin 𝓩`.

In an old implementation this was definitionally true, it is not so now.

-/


-- @@ L133-139 verbatim
/-- The explicit casting of a term of type `Charges 𝓩` to a term of
  `Option 𝓩 × Option 𝓩 × Finset 𝓩 × Finset 𝓩`. -/
def toProd : ChargeSpectrum 𝓩 ≃ Option 𝓩 × Option 𝓩 × Finset 𝓩 × Finset 𝓩 where
  toFun x := (x.qHd, x.qHu, x.Q5, x.Q10)
  invFun x := ⟨x.1, x.2.1, x.2.2.1, x.2.2.2⟩
  left_inv x := by cases x; rfl
  right_inv x := by cases x; rfl


-- @@ L141-145 verbatim
/-!

### A.3. Rendering

-/


-- @@ L147-154 verbatim
unsafe instance [Repr 𝓩] : Repr (ChargeSpectrum 𝓩) where
  reprPrec x _ := match x with
    | ⟨qHd, qHu, Q5, Q10⟩ =>
      let s1 := reprStr qHd
      let s2 := reprStr qHu
      let s5 := reprStr Q5
      let s10 := reprStr Q10
      s!"⟨{s1}, {s2}, {s5}, {s10}⟩"


-- @@ L156-162 verbatim
/-!

## B. The subset relation

We define a `HasSubset` and `HasSSubset` instance on `ChargeSpectrum 𝓩`.

-/


-- @@ L164-169 verbatim
instance hasSubset : HasSubset (ChargeSpectrum 𝓩) where
  Subset x y :=
    x.qHd.toFinset ⊆ y.qHd.toFinset ∧
    x.qHu.toFinset ⊆ y.qHu.toFinset ∧
    x.Q5 ⊆ y.Q5 ∧
    x.Q10 ⊆ y.Q10


-- @@ L171-172 verbatim
instance hasSSubset : HasSSubset (ChargeSpectrum 𝓩) where
  SSubset x y := x ⊆ y ∧ x ≠ y


-- @@ L174-175 verbatim
instance subsetDecidable [DecidableEq 𝓩] (x y : ChargeSpectrum 𝓩) : Decidable (x ⊆ y) :=
  instDecidableAnd


-- @@ L177-179 verbatim
lemma subset_def {x y : ChargeSpectrum 𝓩} : x ⊆ y ↔ x.qHd.toFinset ⊆ y.qHd.toFinset ∧
    x.qHu.toFinset ⊆ y.qHu.toFinset ∧ x.Q5 ⊆ y.Q5 ∧ x.Q10 ⊆ y.Q10 := by
  rfl


-- @@ L181-182 verbatim
@[simp, refl]
lemma subset_refl (x : ChargeSpectrum 𝓩) : x ⊆ x := ⟨by rfl, by rfl, by rfl, by rfl⟩


-- @@ L184-186 verbatim
lemma _root_.Option.toFinset_inj {x y : Option 𝓩} :
    x = y ↔ x.toFinset = y.toFinset := by
  cases x <;> cases y <;> simp [Option.toFinset]


-- @@ L188-191 verbatim
lemma subset_trans {x y z : ChargeSpectrum 𝓩} (hxy : x ⊆ y) (hyz : y ⊆ z) : x ⊆ z := by
  rw [subset_def] at hxy hyz ⊢
  exact ⟨Finset.Subset.trans hxy.1 hyz.1, Finset.Subset.trans hxy.2.1 hyz.2.1,
    Finset.Subset.trans hxy.2.2.1 hyz.2.2.1, Finset.Subset.trans hxy.2.2.2 hyz.2.2.2⟩


-- @@ L193-198 verbatim
lemma subset_antisymm {x y : ChargeSpectrum 𝓩} (hxy : x ⊆ y) (hyx : y ⊆ x) : x = y :=
  eq_of_parts
    (Option.toFinset_inj.mpr (Finset.Subset.antisymm hxy.1 hyx.1))
    (Option.toFinset_inj.mpr (Finset.Subset.antisymm hxy.2.1 hyx.2.1))
    (Finset.Subset.antisymm hxy.2.2.1 hyx.2.2.1)
    (Finset.Subset.antisymm hxy.2.2.2 hyx.2.2.2)


-- @@ L200-204 verbatim
/-!

## C. The empty charge spectrum

-/


-- @@ L206-207 verbatim
instance emptyInst : EmptyCollection (ChargeSpectrum 𝓩) where
  emptyCollection := ⟨none, none, {}, {}⟩


-- @@ L209-209 verbatim
lemma empty_eq : (∅ : ChargeSpectrum 𝓩) = ⟨none, none, {}, {}⟩ := rfl


-- @@ L211-213 verbatim
@[simp]
lemma empty_subset (x : ChargeSpectrum 𝓩) : ∅ ⊆ x := by
  simp [Subset, empty_eq]


-- @@ L215-220 verbatim
@[simp]
lemma subset_of_empty_iff_empty {x : ChargeSpectrum 𝓩} :
    x ⊆ ∅ ↔ x = ∅ := by
  refine ⟨fun h => subset_antisymm h (empty_subset x), ?_⟩
  rintro rfl
  simp


-- @@ L222-224 verbatim
@[simp]
lemma empty_qHd : (∅ : ChargeSpectrum 𝓩).qHd = none := by
  simp [empty_eq]


-- @@ L226-228 verbatim
@[simp]
lemma empty_qHu : (∅ : ChargeSpectrum 𝓩).qHu = none := by
  simp [empty_eq]


-- @@ L230-232 verbatim
@[simp]
lemma empty_Q5 : (∅ : ChargeSpectrum 𝓩).Q5 = ∅ := by
  simp [empty_eq]


-- @@ L234-236 verbatim
@[simp]
lemma empty_Q10 : (∅ : ChargeSpectrum 𝓩).Q10 = ∅ := by
  simp [empty_eq]


-- @@ L238-242 verbatim
/-!

## D. The cardinality of a charge spectrum

-/


-- @@ L244-247 verbatim
/-- The cardinality of a `Charges` is defined to be the sum of the cardinalities
  of each of the underlying finite sets of charges, with `Option ℤ` turned to finsets. -/
def card (x : ChargeSpectrum 𝓩) : Nat :=
  x.qHu.toFinset.card + x.qHd.toFinset.card + x.Q5.card + x.Q10.card


-- @@ L249-251 verbatim
@[simp]
lemma card_empty : card (∅ : ChargeSpectrum 𝓩) = 0 := by
  simp [card, empty_eq]


-- @@ L253-259 verbatim
lemma card_mono {x y : ChargeSpectrum 𝓩} (h : x ⊆ y) : card x ≤ card y := by
  have h1 := Finset.card_le_card h.1
  have h2 := Finset.card_le_card h.2.1
  have h3 := Finset.card_le_card h.2.2.1
  have h4 := Finset.card_le_card h.2.2.2
  simp only [card]
  omega


-- @@ L261-271 verbatim
lemma eq_of_subset_card {x y : ChargeSpectrum 𝓩} (h : x ⊆ y) (hcard : card x = card y) : x = y := by
  simp only [card] at hcard
  have c1 := Finset.card_le_card h.1
  have c2 := Finset.card_le_card h.2.1
  have c3 := Finset.card_le_card h.2.2.1
  have c4 := Finset.card_le_card h.2.2.2
  refine eq_of_parts (Option.toFinset_inj.mpr ?_) (Option.toFinset_inj.mpr ?_) ?_ ?_
  · exact Finset.eq_of_subset_of_card_le h.1 (by omega)
  · exact Finset.eq_of_subset_of_card_le h.2.1 (by omega)
  · exact Finset.eq_of_subset_of_card_le h.2.2.1 (by omega)
  · exact Finset.eq_of_subset_of_card_le h.2.2.2 (by omega)


-- @@ L273-277 verbatim
/-!

## E. The power set of a charge spectrum

-/


-- @@ L279-279 verbatim
variable [DecidableEq 𝓩]


-- @@ L281-286 verbatim
/-- The powerset of `x : Option 𝓩` defined as `{none}` if `x` is `none`
  and `{none, some y}` is `x` is `some y`. -/
def _root_.Option.powerset (x : Option 𝓩) : Finset (Option 𝓩) :=
  match x with
  | none => {none}
  | some x => {none, some x}


-- @@ L288-291 verbatim
@[simp]
lemma _root_.Option.mem_powerset_iff {x : Option 𝓩} (y : Option 𝓩) :
    y ∈ x.powerset ↔ y.toFinset ⊆ x.toFinset := by
  cases x <;> cases y <;> simp [Option.powerset]


-- @@ L293-297 verbatim
/-- The powerset of a charge spectrum. Given a charge spectrum `x : ChargeSpectrum 𝓩`
  its powerset is the finite set of all `ChargeSpectrum 𝓩` which are subsets of `x`. -/
def powerset (x : ChargeSpectrum 𝓩) : Finset (ChargeSpectrum 𝓩) :=
  (x.qHd.powerset.product <| x.qHu.powerset.product <| x.Q5.powerset.product <|
    x.Q10.powerset).map toProd.symm.toEmbedding


-- @@ L299-305 verbatim
lemma mem_powerset_iff {x y : ChargeSpectrum 𝓩} :
    x ∈ powerset y ↔
    x.qHd ∈ y.qHd.powerset ∧
    x.qHu ∈ y.qHu.powerset ∧
    x.Q5 ∈ y.Q5.powerset ∧
    x.Q10 ∈ y.Q10.powerset := by
  simp [powerset, Finset.mem_product, toProd]


-- @@ L307-310 verbatim
@[simp]
lemma mem_powerset_iff_subset {x y : ChargeSpectrum 𝓩} :
    x ∈ powerset y ↔ x ⊆ y := by
  simp [mem_powerset_iff, subset_def]


-- @@ L312-313 verbatim
lemma self_mem_powerset (x : ChargeSpectrum 𝓩) :
    x ∈ powerset x := by simp


-- @@ L315-316 verbatim
lemma empty_mem_powerset (x : ChargeSpectrum 𝓩) :
    ∅ ∈ powerset x := by simp


-- @@ L318-322 verbatim
@[simp]
lemma powerset_of_empty :
    powerset (∅ : ChargeSpectrum 𝓩) = {∅} := by
  ext x
  simp


-- @@ L324-333 verbatim
lemma powerset_mono {x y : ChargeSpectrum 𝓩} :
    powerset x ⊆ powerset y ↔ x ⊆ y := by
  constructor
  · intro h
    exact mem_powerset_iff_subset.mp (h (self_mem_powerset x))
  · intro h z hz
    exact mem_powerset_iff_subset.mpr (subset_trans (mem_powerset_iff_subset.mp hz) h)

-- `unusedArguments` (newly flagged under v4.32.0): `hn` names the induction
-- target but the proof discharges it directly via `exists_min_image`.

-- @@ L334-347 verbatim
@[nolint unusedArguments]
lemma min_exists_inductive (S : Finset (ChargeSpectrum 𝓩)) (hS : S ≠ ∅) :
    (n : ℕ) → (hn : S.card = n) →
    ∃ y ∈ S, powerset y ∩ S = {y} := by
  intro _ _
  obtain ⟨y, hyS, hy⟩ := S.exists_min_image card (Finset.nonempty_iff_ne_empty.mpr hS)
  refine ⟨y, hyS, ?_⟩
  ext z
  simp only [Finset.mem_inter, mem_powerset_iff_subset, Finset.mem_singleton]
  constructor
  · rintro ⟨hzy, hzS⟩
    exact eq_of_subset_card hzy (le_antisymm (card_mono hzy) (hy z hzS))
  · rintro rfl
    exact ⟨subset_refl z, hyS⟩


-- @@ L349-350 verbatim
lemma min_exists (S : Finset (ChargeSpectrum 𝓩)) (hS : S ≠ ∅) :
    ∃ y ∈ S, powerset y ∩ S = {y} := min_exists_inductive S hS S.card rfl


-- @@ L352-359 verbatim
/-!

## F. Finite sets of charge spectra with values

We define the finite set of `ChargeSpectrum` with 5-bar and 10d representation
charges in a given finite set.

-/


-- @@ L361-369 verbatim
/-- Given `S5 S10 : Finset 𝓩` the finite set of charges associated with
  for which the 5-bar representation charges sit in `S5` and
  the 10d representation charges sit in `S10`. -/
def ofFinset (S5 S10 : Finset 𝓩) : Finset (ChargeSpectrum 𝓩) :=
  let SqHd := {none} ∪ S5.map ⟨Option.some, Option.some_injective 𝓩⟩
  let SqHu := {none} ∪ S5.map ⟨Option.some, Option.some_injective 𝓩⟩
  let SQ5 := S5.powerset
  let SQ10 := S10.powerset
  (SqHd.product (SqHu.product (SQ5.product SQ10))).map toProd.symm.toEmbedding


-- @@ L371-378 verbatim
lemma mem_ofFinset_iff {S5 S10 : Finset 𝓩} {x : ChargeSpectrum 𝓩} :
    x ∈ ofFinset S5 S10 ↔ x.qHd.toFinset ⊆ S5 ∧ x.qHu.toFinset ⊆ S5 ∧
      x.Q5 ⊆ S5 ∧ x.Q10 ⊆ S10 := by
  have hoption (a : Option 𝓩) (S : Finset 𝓩) :
      a ∈ ({none} : Finset (Option 𝓩)) ∪ S.map ⟨Option.some, Option.some_injective 𝓩⟩ ↔
      a.toFinset ⊆ S := by cases a <;> simp
  simp only [ofFinset, Finset.mem_map_equiv, Equiv.symm_symm, toProd, Equiv.coe_fn_mk,
    Finset.product_eq_sprod, Finset.mem_product, hoption, Finset.mem_powerset]


-- @@ L380-384 verbatim
lemma mem_ofFinset_antitone (S5 S10 : Finset 𝓩)
    {x y : ChargeSpectrum 𝓩} (h : x ⊆ y) (hy : y ∈ ofFinset S5 S10) :
    x ∈ ofFinset S5 S10 := by
  rw [mem_ofFinset_iff] at hy ⊢
  exact ⟨h.1.trans hy.1, h.2.1.trans hy.2.1, h.2.2.1.trans hy.2.2.1, h.2.2.2.trans hy.2.2.2⟩


-- @@ L386-391 verbatim
lemma ofFinset_subset_of_subset {S5 S5' S10 S10' : Finset 𝓩}
    (h5 : S5 ⊆ S5') (h10 : S10 ⊆ S10') :
    ofFinset S5 S10 ⊆ ofFinset S5' S10' := by
  intro x hx
  rw [mem_ofFinset_iff] at hx ⊢
  exact ⟨hx.1.trans h5, hx.2.1.trans h5, hx.2.2.1.trans h5, hx.2.2.2.trans h10⟩


-- @@ L393-396 verbatim
lemma ofFinset_univ [Fintype 𝓩] (x : ChargeSpectrum 𝓩) :
    x ∈ ofFinset (Finset.univ : Finset 𝓩) (Finset.univ : Finset 𝓩) := by
  rw [mem_ofFinset_iff]
  simp


-- @@ L398-402 verbatim
/-!

### F.1. Cardinality of finite sets of charge spectra with values

-/


-- @@ L404-406 verbatim
/-- The cardinality of `ofFinset S5 S10`. -/
def ofFinsetCard (S5 S10 : Finset 𝓩) : ℕ :=
    (S5.card + 1) * (S5.card + 1) * (2 ^ S5.card : ℕ) * (2 ^ S10.card : ℕ)


-- @@ L408-411 verbatim
lemma ofFinset_card_eq_ofFinsetCard (S5 S10 : Finset 𝓩) :
    (ofFinset S5 S10).card = ofFinsetCard S5 S10 := by
  simp [ofFinset, Finset.card_map, Finset.card_product, Finset.card_powerset, ofFinsetCard]
  grind


-- @@ L413-413 verbatim
end ChargeSpectrum


-- @@ L415-415 verbatim
end SU5


-- @@ L417-417 verbatim
end SuperSymmetry
