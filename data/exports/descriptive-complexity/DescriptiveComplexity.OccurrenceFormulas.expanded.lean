/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.OccurrenceOrder
import DescriptiveComplexity.Ordered


-- @@ L9-25 verbatim
/-!
# First-order formulas for literal occurrences, over the ordered expansion

First-order counterpart of `DescriptiveComplexity.OccurrenceOrder`, shared by the
reductions *from* SAT (to 3-colorability, to 3SAT…): parameterized formula
builders over the ordered expansion `Language.sat.sum Language.order`
(`DescriptiveComplexity.SatOcc.satOrd`) mirroring the semantic predicates on literal
occurrences – `occF` for `OccIn`, `minOccF`/`maxOccF` for `MinOcc`/`MaxOcc`,
`succOccF` for `SuccOcc`, `chainedF` for `Chained`, `emptyClF` for `EmptyCl`,
… – together with their realization lemmas (`realize_occF`…).

All builders are parameterized by the indices of their free variables, so that
they can be instantiated at any variable type (in particular under
quantifiers). Occurrence *signs* are static (Lean-level) `Bool` parameters:
a quantification over signs becomes a finite conjunction or disjunction of
formulas.
-/


-- @@ L27-27 verbatim
namespace DescriptiveComplexity


-- @@ L29-29 verbatim
open FirstOrder


-- @@ L31-31 verbatim
namespace SatOcc


-- @@ L33-33 verbatim
open Language Structure


-- @@ L35-36 verbatim
/-- The ordered expansion of the language of CNF instances. -/
abbrev satOrd : Language := Language.sat.sum Language.order


-- @@ L38-39 verbatim
/-- The symbol for “is a clause” in the ordered expansion. -/
abbrev clSym : satOrd.Relations 1 := Sum.inl satIsClause


-- @@ L41-42 verbatim
/-- The symbol for “occurs positively in” in the ordered expansion. -/
abbrev posSym : satOrd.Relations 2 := Sum.inl satPosIn


-- @@ L44-45 verbatim
/-- The symbol for “occurs negatively in” in the ordered expansion. -/
abbrev negSym : satOrd.Relations 2 := Sum.inl satNegIn


-- @@ L47-47 verbatim
/-! ### Formula builders -/


-- @@ L49-49 verbatim
section Builders


-- @@ L51-51 verbatim
variable {α : Type}


-- @@ L53-55 verbatim
/-- `c` is a clause, as a formula. -/
def clF (c : α) : satOrd.Formula α :=
  Relations.formula₁ clSym (Term.var c)


-- @@ L57-59 verbatim
/-- `x` occurs positively in `c`, as a formula. -/
def posF (c x : α) : satOrd.Formula α :=
  Relations.formula₂ posSym (Term.var c) (Term.var x)


-- @@ L61-63 verbatim
/-- `x` occurs negatively in `c`, as a formula. -/
def negF (c x : α) : satOrd.Formula α :=
  Relations.formula₂ negSym (Term.var c) (Term.var x)


-- @@ L65-67 verbatim
/-- `x ≤ y`, as a formula. -/
def leF (x y : α) : satOrd.Formula α :=
  Relations.formula₂ leSymb (Term.var x) (Term.var y)


-- @@ L69-71 verbatim
/-- `x = y`, as a formula. -/
def eqF (x y : α) : satOrd.Formula α :=
  Term.equal (Term.var x) (Term.var y)


-- @@ L73-75 verbatim
/-- `x < y`, as a formula. -/
def ltF (x y : α) : satOrd.Formula α :=
  leF x y ⊓ ∼(eqF x y)


-- @@ L77-79 verbatim
/-- The literal `(x, s)` occurs in the clause `c`, as a formula. -/
def occF (s : Bool) (c x : α) : satOrd.Formula α :=
  clF c ⊓ if s then posF c x else negF c x


-- @@ L81-84 verbatim
/-- The occurrence position `(x, s)` precedes `(y, t)`, as a formula (the
signs are fixed parameters, so this is just `≤` or `<` on the variables). -/
def occLtF (s t : Bool) (x y : α) : satOrd.Formula α :=
  if s < t then leF x y else ltF x y


-- @@ L86-89 verbatim
/-- Some occurrence of `c` lies strictly before `(x, s)`, as a formula. -/
noncomputable def existsEarlierF (s : Bool) (c x : α) : satOrd.Formula α :=
  ((occF false (.inl c) (.inr ()) ⊓ occLtF false s (.inr ()) (.inl x)) ⊔
    (occF true (.inl c) (.inr ()) ⊓ occLtF true s (.inr ()) (.inl x))).iExs Unit


-- @@ L91-94 verbatim
/-- Some occurrence of `c` lies strictly after `(x, s)`, as a formula. -/
noncomputable def existsLaterF (s : Bool) (c x : α) : satOrd.Formula α :=
  ((occF false (.inl c) (.inr ()) ⊓ occLtF s false (.inl x) (.inr ())) ⊔
    (occF true (.inl c) (.inr ()) ⊓ occLtF s true (.inl x) (.inr ()))).iExs Unit


-- @@ L96-98 verbatim
/-- `(x, s)` is the first occurrence of `c`, as a formula. -/
noncomputable def minOccF (s : Bool) (c x : α) : satOrd.Formula α :=
  occF s c x ⊓ ∼(existsEarlierF s c x)


-- @@ L100-102 verbatim
/-- `(x, s)` is the last occurrence of `c`, as a formula. -/
noncomputable def maxOccF (s : Bool) (c x : α) : satOrd.Formula α :=
  occF s c x ⊓ ∼(existsLaterF s c x)


-- @@ L104-106 verbatim
/-- `(x, s)` is a non-first occurrence of `c`, as a formula. -/
noncomputable def chainedF (s : Bool) (c x : α) : satOrd.Formula α :=
  occF s c x ⊓ ∼(minOccF s c x)


-- @@ L108-115 verbatim
/-- `(x, s)` is an occurrence of `c` immediately preceded by the occurrence
`(y, t)`, as a formula. -/
noncomputable def succOccF (t s : Bool) (c y x : α) : satOrd.Formula α :=
  occF t c y ⊓ occF s c x ⊓ occLtF t s y x ⊓
    ∼((((occF false (.inl c) (.inr ()) ⊓ occLtF t false (.inl y) (.inr ())) ⊓
          occLtF false s (.inr ()) (.inl x)) ⊔
        ((occF true (.inl c) (.inr ()) ⊓ occLtF t true (.inl y) (.inr ())) ⊓
          occLtF true s (.inr ()) (.inl x))).iExs Unit)


-- @@ L117-119 verbatim
/-- `(x, s)` is the unique literal of some clause, as a formula. -/
noncomputable def unitLitF (s : Bool) (x : α) : satOrd.Formula α :=
  (minOccF s (.inr ()) (.inl x) ⊓ maxOccF s (.inr ()) (.inl x)).iExs Unit


-- @@ L121-123 verbatim
/-- `c` is an empty clause, as a formula. -/
noncomputable def emptyClF (c : α) : satOrd.Formula α :=
  clF c ⊓ ∼((occF false (.inl c) (.inr ()) ⊔ occF true (.inl c) (.inr ())).iExs Unit)


-- @@ L125-128 verbatim
/-- Some clause is empty, as a (closed) formula: the standard spoiler
condition of reductions from SAT, making the whole CNF unsatisfiable. -/
noncomputable def exEmptyClF : satOrd.Formula α :=
  (emptyClF (Sum.inr ())).iExs Unit


-- @@ L130-130 verbatim
end Builders


-- @@ L132-132 verbatim
/-! ### Realization lemmas -/


-- @@ L134-134 verbatim
section Realize


-- @@ L136-136 verbatim
variable {A : Type} [Language.sat.Structure A] [LinearOrder A] {α : Type} {v : α → A}


-- @@ L138-145 verbatim
omit [Language.sat.Structure A] in
private theorem occLt_iff_le {x y : A} {s t : Bool} (h : s < t) : occLt x s y t ↔ x ≤ y := by
  constructor
  · rintro (h' | ⟨rfl, -⟩)
    exacts [h'.le, le_rfl]
  · intro h'
    rcases h'.lt_or_eq with h'' | rfl
    exacts [Or.inl h'', Or.inr ⟨rfl, h⟩]


-- @@ L147-152 verbatim
omit [Language.sat.Structure A] in
private theorem occLt_iff_lt {x y : A} {s t : Bool} (h : ¬s < t) : occLt x s y t ↔ x < y := by
  constructor
  · rintro (h' | ⟨-, h''⟩)
    exacts [h', absurd h'' h]
  · exact Or.inl


-- @@ L154-157 verbatim
@[simp]
theorem realize_clF {c : α} : (clF c).Realize v ↔ IsCl (v c) := by
  rw [clF, Formula.realize_rel₁]
  exact Iff.rfl


-- @@ L159-162 verbatim
@[simp]
theorem realize_posF {c x : α} : (posF c x).Realize v ↔ PosIn (v c) (v x) := by
  rw [posF, Formula.realize_rel₂]
  exact Iff.rfl


-- @@ L164-167 verbatim
@[simp]
theorem realize_negF {c x : α} : (negF c x).Realize v ↔ NegIn (v c) (v x) := by
  rw [negF, Formula.realize_rel₂]
  exact Iff.rfl


-- @@ L169-171 verbatim
@[simp]
theorem realize_leF {x y : α} : (leF x y).Realize v ↔ v x ≤ v y := by
  simp [leF, Formula.realize_rel₂]


-- @@ L173-175 verbatim
@[simp]
theorem realize_eqF {x y : α} : (eqF x y).Realize v ↔ v x = v y := by
  simp [eqF]


-- @@ L177-179 verbatim
@[simp]
theorem realize_ltF {x y : α} : (ltF x y).Realize v ↔ v x < v y := by
  simp [ltF, lt_iff_le_and_ne]


-- @@ L181-184 verbatim
@[simp]
theorem realize_occF {s : Bool} {c x : α} :
    (occF s c x).Realize v ↔ OccIn (v c) (v x) s := by
  cases s <;> simp [occF, OccIn]


-- @@ L186-191 verbatim
@[simp]
theorem realize_occLtF {s t : Bool} {x y : α} :
    (occLtF s t x y).Realize v ↔ occLt (v x) s (v y) t := by
  by_cases h : s < t
  · simp [occLtF, h, occLt_iff_le h]
  · simp [occLtF, h, occLt_iff_lt h]


-- @@ L193-203 verbatim
@[simp]
theorem realize_existsEarlierF {s : Bool} {c x : α} :
    (existsEarlierF s c x).Realize v ↔ ∃ y t, OccIn (v c) y t ∧ occLt y t (v x) s := by
  simp only [existsEarlierF, Formula.realize_iExs, Formula.realize_sup, Formula.realize_inf,
    realize_occF, realize_occLtF, Sum.elim_inl, Sum.elim_inr]
  constructor
  · rintro ⟨i, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
    exacts [⟨i (), false, h1, h2⟩, ⟨i (), true, h1, h2⟩]
  · rintro ⟨y, t, h1, h2⟩
    cases t
    exacts [⟨fun _ => y, Or.inl ⟨h1, h2⟩⟩, ⟨fun _ => y, Or.inr ⟨h1, h2⟩⟩]


-- @@ L205-215 verbatim
@[simp]
theorem realize_existsLaterF {s : Bool} {c x : α} :
    (existsLaterF s c x).Realize v ↔ ∃ y t, OccIn (v c) y t ∧ occLt (v x) s y t := by
  simp only [existsLaterF, Formula.realize_iExs, Formula.realize_sup, Formula.realize_inf,
    realize_occF, realize_occLtF, Sum.elim_inl, Sum.elim_inr]
  constructor
  · rintro ⟨i, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
    exacts [⟨i (), false, h1, h2⟩, ⟨i (), true, h1, h2⟩]
  · rintro ⟨y, t, h1, h2⟩
    cases t
    exacts [⟨fun _ => y, Or.inl ⟨h1, h2⟩⟩, ⟨fun _ => y, Or.inr ⟨h1, h2⟩⟩]


-- @@ L217-226 verbatim
@[simp]
theorem realize_minOccF {s : Bool} {c x : α} :
    (minOccF s c x).Realize v ↔ MinOcc (v c) (v x) s := by
  simp only [minOccF, Formula.realize_inf, Formula.realize_not, realize_occF,
    realize_existsEarlierF]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun y t hyt hlt => h2 ⟨y, t, hyt, hlt⟩⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun ⟨y, t, hyt, hlt⟩ => h2 y t hyt hlt⟩


-- @@ L228-237 verbatim
@[simp]
theorem realize_maxOccF {s : Bool} {c x : α} :
    (maxOccF s c x).Realize v ↔ MaxOcc (v c) (v x) s := by
  simp only [maxOccF, Formula.realize_inf, Formula.realize_not, realize_occF,
    realize_existsLaterF]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun y t hyt hlt => h2 ⟨y, t, hyt, hlt⟩⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun ⟨y, t, hyt, hlt⟩ => h2 y t hyt hlt⟩


-- @@ L239-242 verbatim
@[simp]
theorem realize_chainedF {s : Bool} {c x : α} :
    (chainedF s c x).Realize v ↔ Chained (v c) (v x) s := by
  simp [chainedF, Chained]


-- @@ L244-257 verbatim
@[simp]
theorem realize_succOccF {t s : Bool} {c y x : α} :
    (succOccF t s c y x).Realize v ↔ SuccOcc (v c) (v y) t (v x) s := by
  simp only [succOccF, Formula.realize_inf, Formula.realize_not, Formula.realize_iExs,
    Formula.realize_sup, realize_occF, realize_occLtF, Sum.elim_inl, Sum.elim_inr]
  constructor
  · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
    refine ⟨h1, h2, h3, fun z u hz hb => h4 ?_⟩
    cases u
    exacts [⟨fun _ => z, Or.inl ⟨⟨hz, hb.1⟩, hb.2⟩⟩, ⟨fun _ => z, Or.inr ⟨⟨hz, hb.1⟩, hb.2⟩⟩]
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨⟨⟨h1, h2⟩, h3⟩, ?_⟩
    rintro ⟨i, ⟨⟨hz, hl1⟩, hl2⟩ | ⟨⟨hz, hl1⟩, hl2⟩⟩
    exacts [h4 (i ()) false hz ⟨hl1, hl2⟩, h4 (i ()) true hz ⟨hl1, hl2⟩]


-- @@ L259-268 verbatim
@[simp]
theorem realize_unitLitF {s : Bool} {x : α} :
    (unitLitF s x).Realize v ↔ ∃ c, MinOcc c (v x) s ∧ MaxOcc c (v x) s := by
  simp only [unitLitF, Formula.realize_iExs, Formula.realize_inf, realize_minOccF,
    realize_maxOccF, Sum.elim_inl, Sum.elim_inr]
  constructor
  · rintro ⟨i, h1, h2⟩
    exact ⟨i (), h1, h2⟩
  · rintro ⟨c, h1, h2⟩
    exact ⟨fun _ => c, h1, h2⟩


-- @@ L270-282 verbatim
@[simp]
theorem realize_emptyClF {c : α} : (emptyClF c).Realize v ↔ EmptyCl (v c) := by
  simp only [emptyClF, Formula.realize_inf, Formula.realize_not, Formula.realize_iExs,
    Formula.realize_sup, realize_clF, realize_occF, Sum.elim_inl, Sum.elim_inr]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun x s hxs => h2 ?_⟩
    cases s
    exacts [⟨fun _ => x, Or.inl hxs⟩, ⟨fun _ => x, Or.inr hxs⟩]
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    rintro ⟨i, h | h⟩
    exacts [h2 (i ()) false h, h2 (i ()) true h]


-- @@ L284-287 verbatim
@[simp]
theorem realize_exEmptyClF : (exEmptyClF (α := α)).Realize v ↔ ∃ c : A, EmptyCl c := by
  simp only [exEmptyClF, Formula.realize_iExs, realize_emptyClF, Sum.elim_inr]
  exact ⟨fun ⟨i, h⟩ => ⟨i (), h⟩, fun ⟨c, h⟩ => ⟨fun _ => c, h⟩⟩


-- @@ L289-289 verbatim
end Realize


-- @@ L291-291 verbatim
end SatOcc


-- @@ L293-293 verbatim
end DescriptiveComplexity
