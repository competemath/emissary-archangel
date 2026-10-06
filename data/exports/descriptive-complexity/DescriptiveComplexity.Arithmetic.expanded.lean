/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Ordered
import DescriptiveComplexity.OrderWalk


-- @@ L9-77 verbatim
/-!
# The numeric predicates: the arithmetic expansion of a vocabulary

The vocabulary of the bottom class of the ordered world. A finite linearly
ordered universe *is* an initial segment of `ℕ`, by the rank of an element
(`DescriptiveComplexity.orank`, the number of its strict predecessors), and this
file makes the arithmetic of that segment available to formulas: the language
`FirstOrder.Language.arith` has a binary `≤` and two **ternary** symbols
`plus` and `times`, interpreted on a finite linear order by

* `plus x y z` – `orank x + orank y = orank z`,
* `times x y z` – `orank x * orank y = orank z`.

Relations, not functions, and therefore *truncated*: a sum or product that does
not fit in the universe simply has no witness, and “`x + y` overflows” is the
first-order `¬∃z, plus x y z` (`DescriptiveComplexity.no_plus_iff_card_le`).

## Why relations of the *order*, and not a new sort of data

The numeric predicates are not extra input relations that an instance happens
to carry: they are **functions of the linear order**, computed by `orank`. Three
consequences, all of them design constraints rather than remarks.

* The canonical structure needs `[LinearOrder A] [Finite A]`, where Mathlib's
  `FirstOrder.Language.orderStructure` needs only `[LE A]`. It is still an
  `instance`; it simply does not fire on an infinite type, which is correct –
  the arithmetic of an infinite universe is not what this vocabulary means.
* There is no order-free reading of this vocabulary at all. Every logic built
  on it is intrinsically a logic of ordered structures, and the class
  `DescriptiveComplexity.AC0Definable` accordingly has no `…Free` variant,
  unlike ∃SO, `SO(LFP)` or `SO(PFP)`.
* Because the interpretation is canonical, an *interpretation* of one
  vocabulary in another does not get the numeric predicates for free: it must
  define the arithmetic of the interpreted universe, which is why the arithmetic
  analogue of `DescriptiveComplexity.FOInterpretation.ordExtend` is real work
  and not plumbing.

## The transport from the ordered expansion

`DescriptiveComplexity.sumOrderToArith` is the language map
`L.sum Language.order →ᴸ L.sum Language.arith` sending `≤` to `≤`, with its
`FirstOrder.Language.LHom.IsExpansionOn` instance, so that every FO(≤) sentence
and every FO(≤) gadget formula of this library can be read as an arithmetic one
(`DescriptiveComplexity.FODefinable.ac0Definable` is the consumer).

It is stated at the level of the *sum* rather than as a map
`Language.order →ᴸ Language.arith` lifted by `LHom.sumMap`, deliberately:
`Language.order.Structure` is not an instance in Mathlib (it would fire on every
`LE`), so the generic `sumMap` instance would have to be fed a `letI`-supplied
structure at every use site, whereas the sum-level map has both structures
available by instance search.

## What is here, and what needs it

Besides the vocabulary and its semantics: the formula builders (`aLeF`, `aLtF`,
`aPlusF`, `aTimesF`, `aMaxF`, `aMinF`) with their realization lemmas, the
overflow characterization, and one worked sentence –
`DescriptiveComplexity.evenCardSentence`, which says that the universe has an
even number of elements, by reading the parity of the rank of its greatest
element. That sentence is what separates FO(≤) from AC⁰
(`DescriptiveComplexity.Problems.Even`), and it is the smallest example of the
one thing the numeric predicates buy over a bare order: access to the *size* of
the universe, one bit at a time.
-/

/- The language of arithmetic lives in Mathlib's `FirstOrder.Language`
namespace, next to `Language.order` and the vocabularies of the problem
catalog – a project-local `Language` namespace would shadow Mathlib's under
`open Language`. -/

-- @@ L78-78 verbatim
namespace FirstOrder


-- @@ L80-80 verbatim
namespace Language


-- @@ L82-90 verbatim
/-- Relation symbols of the arithmetic vocabulary. -/
inductive arithRel : ℕ → Type
  /-- `le x y`: the rank of `x` is at most the rank of `y`, i.e., `x ≤ y`. -/
  | le : arithRel 2
  /-- `plus x y z`: the ranks satisfy `orank x + orank y = orank z`. -/
  | plus : arithRel 3
  /-- `times x y z`: the ranks satisfy `orank x * orank y = orank z`. -/
  | times : arithRel 3
  deriving DecidableEq


-- @@ L92-97 verbatim
/-- The relational vocabulary of the numeric predicates: a linear order and the
graphs of addition and multiplication of ranks. Interpreted canonically on every
finite linear order by `DescriptiveComplexity.arithStructure`. -/
protected def arith : Language :=
  ⟨fun _ => Empty, arithRel⟩
  deriving IsRelational


-- @@ L99-100 verbatim
/-- The order symbol of the arithmetic vocabulary. -/
abbrev arithLe : Language.arith.Relations 2 := .le


-- @@ L102-103 verbatim
/-- The addition symbol of the arithmetic vocabulary. -/
abbrev arithPlus : Language.arith.Relations 3 := .plus


-- @@ L105-106 verbatim
/-- The multiplication symbol of the arithmetic vocabulary. -/
abbrev arithTimes : Language.arith.Relations 3 := .times


-- @@ L108-108 verbatim
end Language


-- @@ L110-110 verbatim
end FirstOrder


-- @@ L112-112 verbatim
namespace DescriptiveComplexity


-- @@ L114-114 verbatim
open FirstOrder


-- @@ L116-116 verbatim
open Language Structure


-- @@ L118-118 verbatim
/-! ### The canonical interpretation on a finite linear order -/


-- @@ L120-120 verbatim
section Structures


-- @@ L122-122 verbatim
variable (A : Type) [LinearOrder A] [Finite A]


-- @@ L124-134 verbatim
/-- **The numeric predicates of a finite linear order**: `≤` is the order, and
`plus`/`times` are the graphs of addition and multiplication of ranks. Both are
truncated: a value that is not the rank of an element of `A` is not related to
anything. -/
instance arithStructure : Language.arith.Structure A where
  funMap f := isEmptyElim f
  RelMap {n} R :=
    match n, R with
    | _, .le => fun x => x 0 ≤ x 1
    | _, .plus => fun x => orank (x 0) + orank (x 1) = orank (x 2)
    | _, .times => fun x => orank (x 0) * orank (x 1) = orank (x 2)


-- @@ L136-136 verbatim
variable {A}


-- @@ L138-141 verbatim
omit [Finite A] in
@[simp]
theorem relMap_arithLe (x : Fin 2 → A) :
    RelMap (L := Language.arith) arithLe x ↔ x 0 ≤ x 1 := Iff.rfl


-- @@ L143-147 verbatim
omit [Finite A] in
@[simp]
theorem relMap_arithPlus (x : Fin 3 → A) :
    RelMap (L := Language.arith) arithPlus x ↔ orank (x 0) + orank (x 1) = orank (x 2) :=
  Iff.rfl


-- @@ L149-153 verbatim
omit [Finite A] in
@[simp]
theorem relMap_arithTimes (x : Fin 3 → A) :
    RelMap (L := Language.arith) arithTimes x ↔ orank (x 0) * orank (x 1) = orank (x 2) :=
  Iff.rfl


-- @@ L155-155 verbatim
end Structures


-- @@ L157-157 verbatim
/-! ### The symbols of the arithmetic expansion of a vocabulary -/


-- @@ L159-159 verbatim
section Symbols


-- @@ L161-161 verbatim
variable (L : Language.{0, 0})


-- @@ L163-164 verbatim
/-- The order symbol, in the arithmetic expansion of `L`. -/
abbrev aLeSym : (L.sum Language.arith).Relations 2 := Sum.inr arithLe


-- @@ L166-167 verbatim
/-- The addition symbol, in the arithmetic expansion of `L`. -/
abbrev aPlusSym : (L.sum Language.arith).Relations 3 := Sum.inr arithPlus


-- @@ L169-170 verbatim
/-- The multiplication symbol, in the arithmetic expansion of `L`. -/
abbrev aTimesSym : (L.sum Language.arith).Relations 3 := Sum.inr arithTimes


-- @@ L172-172 verbatim
end Symbols


-- @@ L174-174 verbatim
/-! ### The numeric predicates of the arithmetic expansion -/


-- @@ L176-176 verbatim
section ExpansionSemantics


-- @@ L178-178 verbatim
variable {L : Language.{0, 0}} {A : Type} [L.Structure A] [LinearOrder A] [Finite A]


-- @@ L180-183 verbatim
omit [Finite A] in
@[simp]
theorem relMap_aLeSym (x : Fin 2 → A) :
    RelMap (aLeSym L) x ↔ x 0 ≤ x 1 := Iff.rfl


-- @@ L185-188 verbatim
omit [Finite A] in
@[simp]
theorem relMap_aPlusSym (x : Fin 3 → A) :
    RelMap (aPlusSym L) x ↔ orank (x 0) + orank (x 1) = orank (x 2) := Iff.rfl


-- @@ L190-193 verbatim
omit [Finite A] in
@[simp]
theorem relMap_aTimesSym (x : Fin 3 → A) :
    RelMap (aTimesSym L) x ↔ orank (x 0) * orank (x 1) = orank (x 2) := Iff.rfl


-- @@ L195-195 verbatim
end ExpansionSemantics


-- @@ L197-197 verbatim
/-! ### The transport of an ordered formula into the arithmetic expansion -/


-- @@ L199-199 verbatim
section Transport


-- @@ L201-201 verbatim
variable (L : Language.{0, 0}) [L.IsRelational]


-- @@ L203-210 verbatim
/-- **The arithmetic expansion extends the ordered one**: the language map
sending the order symbol of `Language.order` to the order symbol of
`Language.arith`, and every input symbol to itself. -/
def sumOrderToArith : L.sum Language.order →ᴸ L.sum Language.arith where
  onRelation := fun {_} R =>
    match R with
    | Sum.inl r => Sum.inl r
    | Sum.inr .le => aLeSym L


-- @@ L212-212 verbatim
variable {L}

-- @@ L213-213 verbatim
variable (A : Type) [L.Structure A] [LinearOrder A] [Finite A]


-- @@ L215-221 verbatim
/-- The transport is an expansion: both vocabularies read `≤` as the order and
the input symbols as themselves. -/
instance sumOrderToArith_isExpansionOn : (sumOrderToArith L).IsExpansionOn A where
  map_onRelation := fun {_} R x => by
    cases R with
    | inl r => rfl
    | inr r => cases r with | le => rfl


-- @@ L223-223 verbatim
end Transport


-- @@ L225-225 verbatim
/-! ### Formula builders -/


-- @@ L227-227 verbatim
section Formulas


-- @@ L229-229 verbatim
variable {L : Language.{0, 0}} {α : Type}


-- @@ L231-233 verbatim
/-- `x ≤ y`, as a formula over the arithmetic expansion. -/
noncomputable def aLeF (x y : α) : (L.sum Language.arith).Formula α :=
  Relations.formula₂ (aLeSym L) (Term.var x) (Term.var y)


-- @@ L235-237 verbatim
/-- `x < y`, as a formula over the arithmetic expansion. -/
noncomputable def aLtF (x y : α) : (L.sum Language.arith).Formula α :=
  aLeF x y ⊓ ∼(aLeF y x)


-- @@ L239-241 verbatim
/-- `x + y = z`, as a formula over the arithmetic expansion. -/
noncomputable def aPlusF (x y z : α) : (L.sum Language.arith).Formula α :=
  Relations.formula (aPlusSym L) ![Term.var x, Term.var y, Term.var z]


-- @@ L243-245 verbatim
/-- `x * y = z`, as a formula over the arithmetic expansion. -/
noncomputable def aTimesF (x y z : α) : (L.sum Language.arith).Formula α :=
  Relations.formula (aTimesSym L) ![Term.var x, Term.var y, Term.var z]


-- @@ L247-249 verbatim
/-- The variable `x` holds a minimum. -/
noncomputable def aMinF (x : α) : (L.sum Language.arith).Formula α :=
  (aLeF (Sum.inl x) (Sum.inr 0)).iAlls (Fin 1)


-- @@ L251-253 verbatim
/-- The variable `x` holds a maximum. -/
noncomputable def aMaxF (x : α) : (L.sum Language.arith).Formula α :=
  (aLeF (Sum.inr 0) (Sum.inl x)).iAlls (Fin 1)


-- @@ L255-255 verbatim
variable {A : Type} [L.Structure A] [LinearOrder A] [Finite A] {v : α → A}


-- @@ L257-261 verbatim
omit [Finite A] in
@[simp]
theorem realize_aLeF (x y : α) : (aLeF (L := L) x y).Realize v ↔ v x ≤ v y := by
  rw [aLeF, Formula.realize_rel₂]
  exact Iff.rfl


-- @@ L263-267 verbatim
omit [Finite A] in
@[simp]
theorem realize_aLtF (x y : α) : (aLtF (L := L) x y).Realize v ↔ v x < v y := by
  rw [aLtF, Formula.realize_inf, Formula.realize_not, realize_aLeF, realize_aLeF]
  exact lt_iff_le_not_ge.symm


-- @@ L269-274 verbatim
omit [Finite A] in
@[simp]
theorem realize_aPlusF (x y z : α) :
    (aPlusF (L := L) x y z).Realize v ↔ orank (v x) + orank (v y) = orank (v z) := by
  rw [aPlusF, Formula.realize_rel]
  exact Iff.rfl


-- @@ L276-281 verbatim
omit [Finite A] in
@[simp]
theorem realize_aTimesF (x y z : α) :
    (aTimesF (L := L) x y z).Realize v ↔ orank (v x) * orank (v y) = orank (v z) := by
  rw [aTimesF, Formula.realize_rel]
  exact Iff.rfl


-- @@ L283-288 verbatim
omit [Finite A] in
@[simp]
theorem realize_aMinF (x : α) : (aMinF (L := L) x).Realize v ↔ ∀ a : A, v x ≤ a := by
  rw [aMinF]
  simp only [Formula.realize_iAlls, realize_aLeF, Sum.elim_inl, Sum.elim_inr]
  exact ⟨fun h a => h fun _ => a, fun h i => h (i 0)⟩


-- @@ L290-295 verbatim
omit [Finite A] in
@[simp]
theorem realize_aMaxF (x : α) : (aMaxF (L := L) x).Realize v ↔ ∀ a : A, a ≤ v x := by
  rw [aMaxF]
  simp only [Formula.realize_iAlls, realize_aLeF, Sum.elim_inl, Sum.elim_inr]
  exact ⟨fun h a => h fun _ => a, fun h i => h (i 0)⟩


-- @@ L297-297 verbatim
end Formulas


-- @@ L299-304 verbatim
/-! ### Ranks, minima and covers

The order facts every walk over the ranks needs, stated once here because both
routes to a complexity bound use them: the induction of
`DescriptiveComplexity.ArithmeticFixedPoint` and the head programs of
`DescriptiveComplexity.HeadArith`. -/


-- @@ L306-306 verbatim
section Ranks


-- @@ L308-308 verbatim
variable {A : Type} [LinearOrder A] [Finite A]


-- @@ L310-313 verbatim
/-- An element of rank `0` is least. -/
theorem isMin_of_orank_eq_zero {z : A} (h : orank z = 0) (a : A) : z ≤ a := by
  by_contra hlt
  exact absurd (orank_lt_orank (lt_of_not_ge hlt)) (by omega)


-- @@ L315-318 verbatim
/-- The rank of an element with an immediate predecessor is one more. -/
theorem orank_eq_succ_of_pred {y' y : A} (h1 : y' < y) (h2 : ∀ a : A, ¬(y' < a ∧ a < y)) :
    orank y = orank y' + 1 :=
  orank_covBy ⟨h1, fun a ha hb => h2 a ⟨ha, hb⟩⟩


-- @@ L320-328 verbatim
/-- **A rank one higher is a cover**: the converse of
`DescriptiveComplexity.orank_covBy`, which is what lets a walk step a head by
choosing the element of the next rank. -/
theorem covBy_of_orank_succ {w z : A} (h : orank z = orank w + 1) : w ⋖ z := by
  refine ⟨lt_of_le_of_ne (orank_le_iff.mp (by omega)) (fun he => by rw [he] at h; omega), ?_⟩
  intro e h1 h2
  have := orank_lt_orank h1
  have := orank_lt_orank h2
  omega


-- @@ L330-339 verbatim
/-- An element of positive rank has an immediate predecessor, of the rank
below. -/
theorem exists_pred_of_orank_succ {z : A} {k : ℕ} (h : orank z = k + 1) :
    ∃ z' : A, orank z' = k ∧ z' < z ∧ ∀ a : A, ¬(z' < a ∧ a < z) := by
  have hk : k < Nat.card A := by
    have := orank_lt_card z
    omega
  obtain ⟨z', hz'⟩ := exists_orank_eq (A := A) hk
  have hcov : z' ⋖ z := covBy_of_orank_succ (by omega)
  exact ⟨z', hz', hcov.lt, fun a ha => hcov.2 ha.1 ha.2⟩


-- @@ L341-341 verbatim
end Ranks


-- @@ L343-343 verbatim
/-! ### Truncation, and the size of the universe -/


-- @@ L345-345 verbatim
section Truncation


-- @@ L347-347 verbatim
variable {A : Type} [LinearOrder A] [Finite A]


-- @@ L349-360 verbatim
/-- **Addition is truncated at the size of the universe**: a sum has a witness
exactly when it is small enough to be a rank. This is what makes “`x + y`
overflows” a first-order statement. -/
theorem no_plus_iff_card_le (x y : A) :
    (¬∃ z : A, orank x + orank y = orank z) ↔ Nat.card A ≤ orank x + orank y := by
  constructor
  · intro h
    by_contra hlt
    obtain ⟨z, hz⟩ := exists_orank_eq (A := A) (m := orank x + orank y) (by omega)
    exact h ⟨z, hz.symm⟩
  · rintro hle ⟨z, hz⟩
    exact absurd (orank_lt_card z) (by omega)


-- @@ L362-362 verbatim
variable [Nonempty A]


-- @@ L364-389 verbatim
/-- **The parity of the universe is a numeric predicate.** The greatest element
has rank `Nat.card A - 1`, so the universe has an even number of elements
exactly when no element doubles to the greatest one. The order alone cannot say
this (`DescriptiveComplexity.even_not_foDefinable`); addition can. -/
theorem even_card_iff_forall_isTop :
    Even (Nat.card A) ↔
      ∀ z : A, (∀ a : A, a ≤ z) → ¬∃ h : A, orank h + orank h = orank z := by
  have hpos : 0 < Nat.card A := Nat.card_pos
  obtain ⟨m, hm⟩ : ∃ z : A, ∀ a : A, a ≤ z := by
    obtain ⟨z, hz⟩ := exists_orank_eq (A := A) (m := Nat.card A - 1) (by omega)
    exact ⟨z, fun a => orank_le_iff.mp (by have := orank_lt_card a; omega)⟩
  constructor
  · rintro hev z hz ⟨h, hh⟩
    rw [orank_isTop hz] at hh
    obtain ⟨k, hk⟩ := hev
    omega
  · intro h
    by_contra hodd
    have hev : Even (Nat.card A - 1) := by
      rcases Nat.even_or_odd (Nat.card A) with he | ho
      · exact absurd he hodd
      · obtain ⟨k, hk⟩ := ho
        exact ⟨k, by omega⟩
    obtain ⟨k, hk⟩ := hev
    obtain ⟨w, hw⟩ := exists_orank_eq (m := k) (A := A) (by omega)
    exact h m hm ⟨w, by rw [orank_isTop hm, hw, hk]⟩


-- @@ L391-391 verbatim
end Truncation


-- @@ L393-393 verbatim
/-! ### A sentence for the parity of the universe -/


-- @@ L395-395 verbatim
section EvenCard


-- @@ L397-397 verbatim
variable (L : Language.{0, 0})


-- @@ L399-406 verbatim
/-- **The universe has an even number of elements**, as a sentence of the
arithmetic expansion: no maximum is the double of anything. The two quantifiers
are the whole sentence – nothing about the input vocabulary is read, so this is
a statement about the *size* of the instance, which is exactly what a bare order
cannot express and the numeric predicates can. -/
noncomputable def evenCardSentence : (L.sum Language.arith).Sentence :=
  ((aMaxF (Sum.inr 0)).imp
      (∼((aPlusF (Sum.inr 0) (Sum.inr 0) (Sum.inl (Sum.inr 0))).iExs (Fin 1)))).iAlls (Fin 1)


-- @@ L408-408 verbatim
variable {L}

-- @@ L409-409 verbatim
variable (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A]


-- @@ L411-421 verbatim
@[simp]
theorem realize_evenCardSentence : A ⊨ evenCardSentence L ↔ Even (Nat.card A) := by
  rw [even_card_iff_forall_isTop (A := A)]
  simp only [Sentence.Realize, evenCardSentence, Formula.realize_iAlls, Formula.realize_imp,
    realize_aMaxF, Formula.realize_not, Formula.realize_iExs, realize_aPlusF, Sum.elim_inl,
    Sum.elim_inr]
  constructor
  · rintro h z hz ⟨w, hw⟩
    exact h (fun _ => z) hz ⟨fun _ => w, hw⟩
  · rintro h i hi ⟨w, hw⟩
    exact h (i 0) hi ⟨w 0, hw⟩


-- @@ L423-423 verbatim
end EvenCard


-- @@ L425-425 verbatim
end DescriptiveComplexity
