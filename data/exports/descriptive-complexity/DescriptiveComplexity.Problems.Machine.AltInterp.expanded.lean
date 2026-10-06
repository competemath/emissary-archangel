/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Syntax
import DescriptiveComplexity.Problems.Machine.AltRounds
import DescriptiveComplexity.Problems.Machine.AltDefs
import DescriptiveComplexity.OrderedComposition


-- @@ L11-36 verbatim
/-!
# The machine of a formula, written in first-order logic

`DescriptiveComplexity.AltQbf.altAccepts_iff_qbf` says that the alternating machine
built in an ordered QBF instance accepts exactly when the formula is true. This
file writes that machine down: an `FOInterpretation` of the alternating-machine
vocabulary in the ordered QBF vocabulary, dimension two, tagged by
`DescriptiveComplexity.AltQbf.AltTag`.

The shape is the one of `DescriptiveComplexity.SatTM.satTuringInterp`:

* every defining formula matches on the **base** tag of its arguments, the
  sweep index being a static number – so a side condition like “this is a real
  sweep” is `⊤` or `⊥`, decided when the formula is built, not a subformula;
* the payload conditions are the three shapes a tag can have: both coordinates
  least (`DescriptiveComplexity.AltQbf.acstF`), one element carried
  (`DescriptiveComplexity.AltQbf.aoneF`), or a clause condition read off the
  instance;
* the order is `DescriptiveComplexity.lexLeF`, whose linearity is inherited
  from the `LinearOrder` on `DescriptiveComplexity.AltQbf.AltTag`, which is the very
  order the machine runs on.

The block marks are new here: `blk i` holds of a state exactly when
`DescriptiveComplexity.AltQbf.altBlockOf` returns `i`, which is a function of the tag
alone, so those formulas are `⊤` or `⊥` too.
-/


-- @@ L38-38 verbatim
namespace DescriptiveComplexity


-- @@ L40-40 verbatim
namespace AltQbf


-- @@ L42-42 verbatim
open FirstOrder


-- @@ L44-44 verbatim
open Language Structure


-- @@ L46-46 verbatim
/-! ### The ordered vocabulary of the source -/


-- @@ L48-48 verbatim
variable {k : ℕ}


-- @@ L50-52 verbatim
variable (k) in
/-- The vocabulary of ordered QBF instances. -/
abbrev qbfOrd (k : ℕ) : Language := (Language.qbf k).sum Language.order


-- @@ L54-55 verbatim
/-- Being a clause. -/
abbrev isClSym : (qbfOrd k).Relations 1 := Sum.inl qbfIsClause


-- @@ L57-58 verbatim
/-- Occurring positively. -/
abbrev posInSym : (qbfOrd k).Relations 2 := Sum.inl qbfPosIn


-- @@ L60-61 verbatim
/-- Occurring negatively. -/
abbrev negInSym : (qbfOrd k).Relations 2 := Sum.inl qbfNegIn


-- @@ L63-64 verbatim
/-- Carrying the mark of the `i`-th block. -/
abbrev blkSym (i : Fin k) : (qbfOrd k).Relations 1 := Sum.inl (qbfBlock i)


-- @@ L66-67 verbatim
/-- The ambient order. -/
abbrev ordSym : (qbfOrd k).Relations 2 := Sum.inr leSymb


-- @@ L69-69 verbatim
/-! ### The formula builders -/


-- @@ L71-71 verbatim
section Builders


-- @@ L73-73 verbatim
variable {α : Type}


-- @@ L75-76 expanded
/-- `x` is a clause. -/
def clF (x : α) : (qbfOrd k).Formula α :=
  FirstOrder.Language.Relations.formula₁ isClSym (FirstOrder.Language.Term.var x)


-- @@ L78-79 expanded
/-- `x` occurs positively in `c`. -/
def posF (c x : α) : (qbfOrd k).Formula α :=
  FirstOrder.Language.Relations.formula₂ posInSym (FirstOrder.Language.Term.var c)
    (FirstOrder.Language.Term.var x)


-- @@ L81-82 expanded
/-- `x` occurs negatively in `c`. -/
def negF (c x : α) : (qbfOrd k).Formula α :=
  FirstOrder.Language.Relations.formula₂ negInSym (FirstOrder.Language.Term.var c)
    (FirstOrder.Language.Term.var x)


-- @@ L84-85 expanded
/-- `x` carries the mark of the `i`-th block. -/
def blkF (i : Fin k) (x : α) : (qbfOrd k).Formula α :=
  FirstOrder.Language.Relations.formula₁ (blkSym i) (FirstOrder.Language.Term.var x)


-- @@ L87-88 expanded
/-- `x ≤ y` in the ambient order. -/
def ordF (x y : α) : (qbfOrd k).Formula α :=
  FirstOrder.Language.Relations.formula₂ ordSym (FirstOrder.Language.Term.var x)
    (FirstOrder.Language.Term.var y)


-- @@ L90-91 expanded
/-- `x = y`. -/
def eqF (x y : α) : (qbfOrd k).Formula α :=
  FirstOrder.Language.Term.equal (FirstOrder.Language.Term.var x) (FirstOrder.Language.Term.var y)


-- @@ L93-94 verbatim
/-- `x < y` in the ambient order. -/
def ordLtF (x y : α) : (qbfOrd k).Formula α := ordF x y ⊓ ∼(eqF x y)


-- @@ L96-98 expanded
/-- `x` is the least element. -/
noncomputable def minF (x : α) : (qbfOrd k).Formula α :=
  FirstOrder.Language.Formula.iAlls (Fin 1) (ordF (Sum.inl x) (Sum.inr 0))


-- @@ L100-102 expanded
/-- `c` is the lowest clause. -/
noncomputable def minClF (c : α) : (qbfOrd k).Formula α :=
  clF c ⊓
    FirstOrder.Language.Formula.iAlls (Fin 1) ((clF (Sum.inr 0)).imp (ordF (Sum.inl c) (Sum.inr 0)))


-- @@ L104-106 expanded
/-- `c` is the highest clause. -/
noncomputable def maxClF (c : α) : (qbfOrd k).Formula α :=
  clF c ⊓
    FirstOrder.Language.Formula.iAlls (Fin 1) ((clF (Sum.inr 0)).imp (ordF (Sum.inr 0) (Sum.inl c)))


-- @@ L108-110 expanded
/-- `c'` is the clause immediately above `c`. -/
noncomputable def nextClF (c c' : α) : (qbfOrd k).Formula α :=
  clF c ⊓
    (clF c' ⊓
      (ordLtF c c' ⊓
        FirstOrder.Language.Formula.iAlls (Fin 1)
          ((clF (Sum.inr 0)).imp
            ((ordLtF (Sum.inl c) (Sum.inr 0)).imp (ordF (Sum.inl c') (Sum.inr 0))))))


-- @@ L112-114 expanded
/-- There is no clause at all. -/
noncomputable def noClF : (qbfOrd k).Formula α :=
  FirstOrder.Language.Formula.iAlls (Fin 1)
    (FirstOrder.Language.BoundedFormula.not (clF (Sum.inr 0)))


-- @@ L116-118 verbatim
/-- The cell of `x` holding the value `v` satisfies the clause `c`: the literal
test the check phase performs. -/
def litF (v : Bool) (c x : α) : (qbfOrd k).Formula α := if v then posF c x else negF c x


-- @@ L120-120 verbatim
end Builders


-- @@ L122-122 verbatim
/-! ### Realization of the builders -/


-- @@ L124-124 verbatim
section BuilderRealize


-- @@ L126-126 verbatim
variable {α A : Type} [(Language.qbf k).Structure A] [LinearOrder A]

-- @@ L127-127 verbatim
variable {v : α → A}


-- @@ L129-130 verbatim
@[simp] theorem realize_clF {x : α} : (clF (k := k) x).Realize v ↔ QbfCl k (v x) := by
  simp [clF, QbfCl, Formula.realize_rel₁]


-- @@ L132-133 verbatim
@[simp] theorem realize_posF {c x : α} : (posF (k := k) c x).Realize v ↔ QbfPos k (v c) (v x) := by
  simp [posF, QbfPos, Formula.realize_rel₂]


-- @@ L135-136 verbatim
@[simp] theorem realize_negF {c x : α} : (negF (k := k) c x).Realize v ↔ QbfNeg k (v c) (v x) := by
  simp [negF, QbfNeg, Formula.realize_rel₂]


-- @@ L138-139 verbatim
@[simp] theorem realize_blkF {i : Fin k} {x : α} : (blkF i x).Realize v ↔ QbfBlk i (v x) := by
  simp [blkF, QbfBlk, Formula.realize_rel₁]


-- @@ L141-143 verbatim
@[simp] theorem realize_ordF {x y : α} : (ordF (k := k) x y).Realize v ↔ v x ≤ v y := by
  simp [ordF, Formula.realize_rel₂]
  rfl


-- @@ L145-146 verbatim
@[simp] theorem realize_eqF {x y : α} : (eqF (k := k) x y).Realize v ↔ v x = v y := by
  simp [eqF]


-- @@ L148-151 verbatim
@[simp] theorem realize_ordLtF {x y : α} : (ordLtF (k := k) x y).Realize v ↔ v x < v y := by
  rw [ordLtF]
  simp only [Formula.realize_inf, realize_ordF, Formula.realize_not, realize_eqF]
  exact ⟨fun h => lt_of_le_of_ne h.1 h.2, fun h => ⟨le_of_lt h, ne_of_lt h⟩⟩


-- @@ L153-156 verbatim
@[simp] theorem realize_minF {x : α} : (minF (k := k) x).Realize v ↔ ∀ a : A, v x ≤ a := by
  rw [minF]
  simp only [Formula.realize_iAlls, realize_ordF, Sum.elim_inl, Sum.elim_inr]
  exact ⟨fun h a => h ![a], fun h i => h (i 0)⟩


-- @@ L158-162 verbatim
@[simp] theorem realize_minClF {c : α} : (minClF (k := k) c).Realize v ↔ QbfMinCl k (v c) := by
  rw [minClF, QbfMinCl]
  simp only [Formula.realize_inf, realize_clF, Formula.realize_iAlls, Formula.realize_imp,
    realize_ordF, Sum.elim_inl, Sum.elim_inr]
  exact and_congr Iff.rfl ⟨fun h e he => h ![e] he, fun h i hi => h (i 0) hi⟩


-- @@ L164-168 verbatim
@[simp] theorem realize_maxClF {c : α} : (maxClF (k := k) c).Realize v ↔ QbfMaxCl k (v c) := by
  rw [maxClF, QbfMaxCl]
  simp only [Formula.realize_inf, realize_clF, Formula.realize_iAlls, Formula.realize_imp,
    realize_ordF, Sum.elim_inl, Sum.elim_inr]
  exact and_congr Iff.rfl ⟨fun h e he => h ![e] he, fun h i hi => h (i 0) hi⟩


-- @@ L170-176 verbatim
@[simp] theorem realize_nextClF {c c' : α} :
    (nextClF (k := k) c c').Realize v ↔ QbfNextCl k (v c) (v c') := by
  rw [nextClF, QbfNextCl]
  simp only [Formula.realize_inf, realize_clF, realize_ordLtF, Formula.realize_iAlls,
    Formula.realize_imp, realize_ordF, realize_ordLtF, Sum.elim_inl, Sum.elim_inr]
  refine and_congr Iff.rfl (and_congr Iff.rfl (and_congr Iff.rfl ?_))
  exact ⟨fun h e he hlt => h ![e] he hlt, fun h i hi hlt => h (i 0) hi hlt⟩


-- @@ L178-181 verbatim
@[simp] theorem realize_noClF : (noClF (α := α) (k := k)).Realize v ↔ ∀ e : A, ¬QbfCl k e := by
  rw [noClF]
  simp only [Formula.realize_iAlls, Formula.realize_not, realize_clF, Sum.elim_inr]
  exact ⟨fun h e => h ![e], fun h i => h (i 0)⟩


-- @@ L183-199 verbatim
@[simp] theorem realize_litF {b : Bool} {c x : α} :
    (litF (k := k) b c x).Realize v ↔ QbfLit k (v c) (v x) b := by
  cases b with
  | true =>
    have hlit : litF (k := k) true c x = posF c x := rfl
    rw [hlit, realize_posF, QbfLit]
    refine ⟨fun h => Or.inl ⟨h, rfl⟩, fun h => ?_⟩
    rcases h with ⟨h, -⟩ | ⟨-, h⟩
    · exact h
    · exact Bool.noConfusion h
  | false =>
    have hlit : litF (k := k) false c x = negF c x := rfl
    rw [hlit, realize_negF, QbfLit]
    refine ⟨fun h => Or.inr ⟨h, rfl⟩, fun h => ?_⟩
    rcases h with ⟨-, h⟩ | ⟨h, -⟩
    · exact Bool.noConfusion h
    · exact h


-- @@ L201-201 verbatim
end BuilderRealize


-- @@ L203-203 verbatim
/-! ### The shapes of the machine's elements, as formulas -/


-- @@ L205-205 verbatim
section Shapes


-- @@ L207-207 verbatim
variable {α : Type}


-- @@ L209-211 verbatim
/-- A side condition decided when the formula is built: the sweep indices are
static, so “this is a real sweep” is a truth value, not a subformula. -/
def sideF (α : Type) (p : Prop) [Decidable p] : (qbfOrd k).Formula α := if p then ⊤ else ⊥


-- @@ L213-213 verbatim
variable {A : Type} [(Language.qbf k).Structure A] [LinearOrder A]


-- @@ L215-217 verbatim
@[simp] theorem realize_sideF {p : Prop} [Decidable p] {v : α → A} :
    (sideF (k := k) α p).Realize v ↔ p := by
  by_cases h : p <;> simp [sideF, h]


-- @@ L219-219 verbatim
end Shapes


-- @@ L221-221 verbatim
section Shapes₂


-- @@ L223-226 verbatim
/-- The second argument is the constant of the tag `s`: the right tag, and both
coordinates least. -/
noncomputable def acstF (s t' : AltTag k) : (qbfOrd k).Formula (Fin 2 × Fin 2) :=
  if t' = s then minF (1, 0) ⊓ minF (1, 1) else ⊥


-- @@ L228-231 verbatim
/-- The second argument is the tag `s` carrying the value of `x`. -/
noncomputable def aoneF (s : AltTag k) (x : Fin 2 × Fin 2) (t' : AltTag k) :
    (qbfOrd k).Formula (Fin 2 × Fin 2) :=
  if t' = s then eqF (1, 0) x ⊓ minF (1, 1) else ⊥


-- @@ L233-233 verbatim
variable {A : Type} [(Language.qbf k).Structure A] [LinearOrder A] [Finite A] [Nonempty A]

-- @@ L234-234 verbatim
variable {v : Fin 2 × Fin 2 → A}


-- @@ L236-251 verbatim
theorem realize_acstF {s : AltTag k} {q : AltV k A}
    (h0 : v (1, 0) = q.2 0) (h1 : v (1, 1) = q.2 1) :
    (acstF s q.1).Realize v ↔ q = acstI s.1 s.2 := by
  rw [acstF]
  by_cases hs : q.1 = s
  · rw [ite_eq_left hs]
    simp only [Formula.realize_inf, realize_minF, h0, h1]
    constructor
    · rintro ⟨ha, hb⟩
      exact altV_ext hs (le_antisymm (ha qbotA) (qbotA_le _))
        (le_antisymm (hb qbotA) (qbotA_le _))
    · rintro rfl
      exact ⟨fun a => qbotA_le a, fun a => qbotA_le a⟩
  · rw [ite_eq_right hs]
    simp only [Formula.realize_bot, false_iff]
    exact fun hq => hs (congrArg Prod.fst hq)


-- @@ L253-268 verbatim
theorem realize_aoneF {s : AltTag k} {x : Fin 2 × Fin 2} {a : A} {q : AltV k A}
    (h0 : v (1, 0) = q.2 0) (h1 : v (1, 1) = q.2 1) (hx : v x = a) :
    (aoneF s x q.1).Realize v ↔ q = aoneI s.1 s.2 a := by
  subst hx
  rw [aoneF]
  by_cases hs : q.1 = s
  · rw [ite_eq_left hs]
    simp only [Formula.realize_inf, realize_eqF, realize_minF, h0, h1]
    constructor
    · rintro ⟨ha, hb⟩
      exact altV_ext hs ha (le_antisymm (hb qbotA) (qbotA_le _))
    · rintro rfl
      exact ⟨rfl, fun a => qbotA_le a⟩
  · rw [ite_eq_right hs]
    simp only [Formula.realize_bot, false_iff]
    exact fun hq => hs (congrArg Prod.fst hq)


-- @@ L270-270 verbatim
end Shapes₂


-- @@ L272-272 verbatim
/-! ### The block of a state, read off its tag -/


-- @@ L274-281 verbatim
/-- The quantifier block of a state, as a function of its tag alone: this is
what makes the block marks statically decided formulas. -/
def altBlockOfTag (t : AltTag k) : ℕ :=
  match t.1 with
  | .qG _ => if (t.2 : ℕ) < k then (t.2 : ℕ) else 0
  | .qChk _ _ => k - 1
  | .qAcc => k - 1
  | _ => 0


-- @@ L283-283 verbatim
variable {A : Type} [(Language.qbf k).Structure A] [LinearOrder A] [Finite A] [Nonempty A]


-- @@ L285-288 verbatim
omit [(Language.qbf k).Structure A] [LinearOrder A] [Finite A] [Nonempty A] in
theorem altBlockOf_eq_tag (q : AltV k A) : altBlockOf q = altBlockOfTag q.1 := by
  obtain ⟨⟨t, j⟩, w⟩ := q
  cases t <;> rfl


-- @@ L290-294 verbatim
/-! ### The defining formulas

One per symbol of `FirstOrder.Language.turingAlt`, each matching on the base
tag of its arguments. The sweep index is static: a condition on it is `sideF`,
and so is the block a state belongs to. -/


-- @@ L296-296 verbatim
section Formulas


-- @@ L298-298 verbatim
variable (cnf : Bool)


-- @@ L300-307 verbatim
/-- Defining formula for `posn`. -/
noncomputable def posnF : AltTag k → (qbfOrd k).Formula (Fin 1 × Fin 2) := fun t =>
  match t.1 with
  | .pStart => sideF _ ((t.2 : ℕ) = 0) ⊓ (minF (0, 0) ⊓ minF (0, 1))
  | .pCell => sideF _ ((t.2 : ℕ) = 0) ⊓ minF (0, 1)
  | .pEnd => sideF _ ((t.2 : ℕ) = 0) ⊓ (minF (0, 0) ⊓ minF (0, 1))
  | .pFill _ => ⊤
  | _ => ⊥


-- @@ L309-327 verbatim
/-- Defining formula for `tr`: the payload promises of
`DescriptiveComplexity.AltQbf.AltTr`, the index conditions decided statically. -/
noncomputable def trF : AltTag k → (qbfOrd k).Formula (Fin 1 × Fin 2) := fun t =>
  match t.1 with
  | .tGStart => (minF (0, 0) ⊓ minF (0, 1)) ⊓ sideF _ ((t.2 : ℕ) = 0 ∧ 0 < k)
  | .tGKeep _ => minF (0, 1) ⊓ sideF _ ((t.2 : ℕ) < k)
  | .tGSet => minF (0, 1) ⊓
      (if h : (t.2 : ℕ) < k then blkF ⟨(t.2 : ℕ), h⟩ (0, 0) else ⊥)
  | .tGTurn => (minF (0, 0) ⊓ minF (0, 1)) ⊓ sideF _ ((t.2 : ℕ) < k)
  | .tGBack _ => minF (0, 1) ⊓ sideF _ ((t.2 : ℕ) < k)
  | .tGNext => (minF (0, 0) ⊓ minF (0, 1)) ⊓ sideF _ ((t.2 : ℕ) + 1 < k)
  | .tGEndAcc => (minF (0, 0) ⊓ minF (0, 1)) ⊓
      (sideF _ ((t.2 : ℕ) + 1 = k ∧ cnf = true) ⊓ noClF)
  | .tGEndChk => minF (0, 1) ⊓ (sideF _ ((t.2 : ℕ) + 1 = k) ⊓ minClF (0, 0))
  | .tChk _ _ _ => clF (0, 0) ⊓ sideF _ ((t.2 : ℕ) = 0)
  | .tTurnNext _ => nextClF (0, 0) (0, 1) ⊓ sideF _ ((t.2 : ℕ) = 0)
  | .tTurnAcc _ => minF (0, 1) ⊓ (sideF _ ((t.2 : ℕ) = 0) ⊓ (clF (0, 0) ⊓
      (sideF _ (cnf = true)).imp (maxClF (0, 0))))
  | _ => ⊥


-- @@ L329-333 verbatim
/-- Defining formula for `start`. -/
noncomputable def startF : AltTag k → (qbfOrd k).Formula (Fin 1 × Fin 2) := fun t =>
  match t.1 with
  | .qG d => sideF _ (d = true ∧ (t.2 : ℕ) = 0) ⊓ (minF (0, 0) ⊓ minF (0, 1))
  | _ => ⊥


-- @@ L335-339 verbatim
/-- Defining formula for `acc`: acceptance is read off the base tag alone. -/
noncomputable def accF : AltTag k → (qbfOrd k).Formula (Fin 1 × Fin 2) := fun t =>
  match t.1 with
  | .qAcc => ⊤
  | _ => ⊥


-- @@ L341-345 verbatim
/-- Defining formula for `blank`. -/
noncomputable def blankF : AltTag k → (qbfOrd k).Formula (Fin 1 × Fin 2) := fun t =>
  match t.1 with
  | .sBlank => sideF _ ((t.2 : ℕ) = 0) ⊓ (minF (0, 0) ⊓ minF (0, 1))
  | _ => ⊥


-- @@ L347-361 verbatim
/-- Defining formula for `right`: a static condition on the tag. -/
noncomputable def rightF : AltTag k → (qbfOrd k).Formula (Fin 1 × Fin 2) := fun t =>
  match t.1 with
  | .tGStart => ⊤
  | .tGKeep _ => ⊤
  | .tGSet => ⊤
  | .tGTurn => ⊥
  | .tGBack _ => ⊥
  | .tGNext => ⊤
  | .tGEndAcc => ⊤
  | .tGEndChk => ⊤
  | .tChk _ _ d => if d then ⊤ else ⊥
  | .tTurnNext d => if d then ⊥ else ⊤
  | .tTurnAcc d => if d then ⊥ else ⊤
  | _ => ⊥


-- @@ L363-369 verbatim
/-- Defining formula for `inp`, the initial tape. -/
noncomputable def inpF : AltTag k → AltTag k → (qbfOrd k).Formula (Fin 2 × Fin 2) := fun t t' =>
  match t.1 with
  | .pStart => acstF (.sStart, 0) t'
  | .pCell => aoneF (.sVal false, 0) (0, 0) t'
  | .pEnd => acstF (.sEnd, 0) t'
  | _ => ⊥


-- @@ L371-385 verbatim
/-- Defining formula for `tsrc`. -/
noncomputable def tsrcF : AltTag k → AltTag k → (qbfOrd k).Formula (Fin 2 × Fin 2) := fun t t' =>
  match t.1 with
  | .tGStart => acstF (.qG true, t.2) t'
  | .tGKeep _ => acstF (.qG true, t.2) t'
  | .tGSet => acstF (.qG true, t.2) t'
  | .tGTurn => acstF (.qG true, t.2) t'
  | .tGBack _ => acstF (.qG false, t.2) t'
  | .tGNext => acstF (.qG false, t.2) t'
  | .tGEndAcc => acstF (.qG false, t.2) t'
  | .tGEndChk => acstF (.qG false, t.2) t'
  | .tChk _ f d => aoneF (.qChk f d, 0) (0, 0) t'
  | .tTurnNext d => aoneF (.qChk true d, 0) (0, 0) t'
  | .tTurnAcc d => aoneF (.qChk cnf d, 0) (0, 0) t'
  | _ => ⊥


-- @@ L387-401 verbatim
/-- Defining formula for `tread`. -/
noncomputable def treadF : AltTag k → AltTag k → (qbfOrd k).Formula (Fin 2 × Fin 2) := fun t t' =>
  match t.1 with
  | .tGStart => acstF (.sStart, 0) t'
  | .tGKeep b => aoneF (.sVal b, 0) (0, 0) t'
  | .tGSet => aoneF (.sVal false, 0) (0, 0) t'
  | .tGTurn => acstF (.sEnd, 0) t'
  | .tGBack b => aoneF (.sVal b, 0) (0, 0) t'
  | .tGNext => acstF (.sStart, 0) t'
  | .tGEndAcc => acstF (.sStart, 0) t'
  | .tGEndChk => acstF (.sStart, 0) t'
  | .tChk b _ _ => aoneF (.sVal b, 0) (0, 1) t'
  | .tTurnNext d => acstF (if d then (.sEnd, 0) else (.sStart, 0)) t'
  | .tTurnAcc d => acstF (if d then (.sEnd, 0) else (.sStart, 0)) t'
  | _ => ⊥


-- @@ L403-422 verbatim
/-- Defining formula for `tdst`: the one place the instance is consulted, in
the check clause, through `DescriptiveComplexity.AltQbf.litF`. -/
noncomputable def tdstF : AltTag k → AltTag k → (qbfOrd k).Formula (Fin 2 × Fin 2) := fun t t' =>
  match t.1 with
  | .tGStart => acstF (.qG true, t.2) t'
  | .tGKeep _ => acstF (.qG true, t.2) t'
  | .tGSet => acstF (.qG true, t.2) t'
  | .tGTurn => acstF (.qG false, t.2) t'
  | .tGBack _ => acstF (.qG false, t.2) t'
  | .tGNext => acstF (.qG true, t.2 + 1) t'
  | .tGEndAcc => acstF (.qAcc, 0) t'
  | .tGEndChk => aoneF (.qChk false true, 0) (0, 0) t'
  | .tChk b f d =>
      (aoneF (.qChk true d, 0) (0, 0) t' ⊓
          (if f then ⊤ else litF (xorB cnf b) (0, 0) (0, 1))) ⊔
        (aoneF (.qChk false d, 0) (0, 0) t' ⊓
          (if f then ⊥ else ∼(litF (xorB cnf b) (0, 0) (0, 1))))
  | .tTurnNext d => aoneF (.qChk false (!d), 0) (0, 1) t'
  | .tTurnAcc _ => acstF (.qAcc, 0) t'
  | _ => ⊥


-- @@ L424-438 verbatim
/-- Defining formula for `twrite`. -/
noncomputable def twriteF : AltTag k → AltTag k → (qbfOrd k).Formula (Fin 2 × Fin 2) := fun t t' =>
  match t.1 with
  | .tGStart => acstF (.sStart, 0) t'
  | .tGKeep b => aoneF (.sVal b, 0) (0, 0) t'
  | .tGSet => aoneF (.sVal true, 0) (0, 0) t'
  | .tGTurn => acstF (.sEnd, 0) t'
  | .tGBack b => aoneF (.sVal b, 0) (0, 0) t'
  | .tGNext => acstF (.sStart, 0) t'
  | .tGEndAcc => acstF (.sStart, 0) t'
  | .tGEndChk => acstF (.sStart, 0) t'
  | .tChk b _ _ => aoneF (.sVal b, 0) (0, 1) t'
  | .tTurnNext d => acstF (if d then (.sEnd, 0) else (.sStart, 0)) t'
  | .tTurnAcc d => acstF (if d then (.sEnd, 0) else (.sStart, 0)) t'
  | _ => ⊥


-- @@ L440-443 verbatim
/-- Defining formula for the `i`-th block mark: the block of a state is a
function of its tag. -/
noncomputable def blkStF (i : Fin k) : AltTag k → (qbfOrd k).Formula (Fin 1 × Fin 2) := fun t =>
  sideF _ ((i : ℕ) = altBlockOfTag t)


-- @@ L445-464 verbatim
variable (k) in
/-- **The interpretation of alternating machine instances in ordered QBF
instances**: the machine `M_φ` of the formula, written down. -/
noncomputable def altTuringInterp : FOInterpretation (qbfOrd k) (Language.turingAlt k)
    (AltTag k) 2 where
  relFormula {n} R :=
    match n, R with
    | _, .base .posn => fun t => posnF (t 0)
    | _, .base .tr => fun t => trF cnf (t 0)
    | _, .base .start => fun t => startF (t 0)
    | _, .base .acc => fun t => accF (t 0)
    | _, .base .blank => fun t => blankF (t 0)
    | _, .base .right => fun t => rightF (t 0)
    | _, .base .le => fun t => lexLeF (Language.qbf k) 2 (t 0) (t 1)
    | _, .base .tsrc => fun t => tsrcF cnf (t 0) (t 1)
    | _, .base .tread => fun t => treadF (t 0) (t 1)
    | _, .base .tdst => fun t => tdstF cnf (t 0) (t 1)
    | _, .base .twrite => fun t => twriteF (t 0) (t 1)
    | _, .base .inp => fun t => inpF (t 0) (t 1)
    | _, .blk i => fun t => blkStF i (t 0)


-- @@ L466-466 verbatim
end Formulas


-- @@ L468-473 verbatim
/-! ### The realization lemmas

One per symbol, each saying that its defining formula defines the
corresponding predicate of `DescriptiveComplexity.AltQbf.altMachine`. The universe of
the interpreted structure is definitionally `DescriptiveComplexity.AltV k A`.
-/


-- @@ L475-475 verbatim
section Characterize


-- @@ L477-477 verbatim
variable {A : Type} [(Language.qbf k).Structure A] [LinearOrder A] [Finite A] [Nonempty A]


-- @@ L479-481 verbatim
/-- The identity equivalence between the tagged tuples and the interpreted
universe. -/
def altMapEquiv (cnf : Bool) : AltV k A ≃ (altTuringInterp k cnf).Map A := Equiv.refl (AltV k A)


-- @@ L483-484 verbatim
omit [(Language.qbf k).Structure A] [LinearOrder A] [Finite A] [Nonempty A] in
@[simp] theorem altMapEquiv_apply (cnf : Bool) (p : AltV k A) : altMapEquiv cnf p = p := rfl


-- @@ L486-499 verbatim
omit [Finite A] [Nonempty A] in
/-- The block mark of a sweep index, read as a formula. -/
theorem realize_blkAtF {j : Fin (k + 1)} {x : A} {v : Fin 1 × Fin 2 → A} (hx : v (0, 0) = x) :
    ((if h : (j : ℕ) < k then blkF ⟨(j : ℕ), h⟩ (0, 0) else ⊥ :
      (qbfOrd k).Formula (Fin 1 × Fin 2))).Realize v ↔ QbfBlkAt j x := by
  by_cases h : (j : ℕ) < k
  · rw [dite_eq_left h]
    simp only [realize_blkF, hx, QbfBlkAt]
    exact ⟨fun hb => ⟨⟨(j : ℕ), h⟩, rfl, hb⟩, fun ⟨i, hi, hb⟩ => by
      rwa [show (⟨(j : ℕ), h⟩ : Fin k) = i from Fin.ext hi.symm]⟩
  · rw [dite_eq_right h]
    simp only [Formula.realize_bot, false_iff, QbfBlkAt]
    rintro ⟨i, hi, -⟩
    exact absurd (hi ▸ i.isLt) h


-- @@ L501-501 verbatim
variable (cnf : Bool)


-- @@ L503-514 verbatim
omit [Finite A] [Nonempty A] in
theorem relMap_posn (p : AltV k A) :
    ATMPosn (k := k) (altMapEquiv (A := A) cnf p) ↔ AltPosn p := by
  rw [ATMPosn, FOInterpretation.relMap_map]
  obtain ⟨⟨t, j⟩, w⟩ := p
  have key : ∀ (t : AltBase) (v : Fin 1 × Fin 2 → A), v (0, 0) = w 0 → v (0, 1) = w 1 →
      ((posnF ((t, j) : AltTag k)).Realize v ↔ AltPosn (((t, j), w) : AltV k A)) := by
    intro t v h0 h1
    cases t <;>
      simp only [posnF, AltPosn, Formula.realize_inf, Formula.realize_bot, Formula.realize_top,
        realize_minF, realize_sideF, h0, h1, forall_and]
  exact key t _ rfl rfl


-- @@ L516-530 verbatim
omit [Finite A] [Nonempty A] in
theorem relMap_tr (p : AltV k A) :
    ATMTr (k := k) (altMapEquiv (A := A) cnf p) ↔ AltTr cnf p := by
  rw [ATMTr, FOInterpretation.relMap_map]
  obtain ⟨⟨t, j⟩, w⟩ := p
  have key : ∀ (t : AltBase) (v : Fin 1 × Fin 2 → A), v (0, 0) = w 0 → v (0, 1) = w 1 →
      ((trF cnf ((t, j) : AltTag k)).Realize v ↔ AltTr cnf (((t, j), w) : AltV k A)) := by
    intro t v h0 h1
    cases t <;>
      simp only [trF, AltTr, IsMinTup2, Formula.realize_inf, Formula.realize_bot,
        realize_minF, realize_sideF, realize_clF, realize_minClF,
        realize_maxClF, realize_nextClF, realize_noClF, Formula.realize_imp, h0, h1] <;>
      try tauto
    exact and_congr Iff.rfl (realize_blkAtF h0)
  exact key t _ rfl rfl


-- @@ L532-545 verbatim
omit [Finite A] [Nonempty A] in
theorem relMap_start (p : AltV k A) :
    ATMStart (k := k) (altMapEquiv (A := A) cnf p) ↔ AltStartSt p := by
  rw [ATMStart, FOInterpretation.relMap_map]
  obtain ⟨⟨t, j⟩, w⟩ := p
  have key : ∀ (t : AltBase) (v : Fin 1 × Fin 2 → A), v (0, 0) = w 0 → v (0, 1) = w 1 →
      ((startF ((t, j) : AltTag k)).Realize v ↔ AltStartSt (((t, j), w) : AltV k A)) := by
    intro t v h0 h1
    cases t <;>
      simp only [startF, AltStartSt, IsMinTup2, Formula.realize_inf, Formula.realize_bot,
        realize_minF, realize_sideF, Prod.mk.injEq, AltBase.qG.injEq, Fin.ext_iff, Fin.val_zero,
        h0, h1] <;>
      tauto
  exact key t _ rfl rfl


-- @@ L547-556 verbatim
omit [Finite A] [Nonempty A] in
theorem relMap_acc (p : AltV k A) :
    ATMAcc (k := k) (altMapEquiv (A := A) cnf p) ↔ AltAccSt p := by
  rw [ATMAcc, FOInterpretation.relMap_map]
  obtain ⟨⟨t, j⟩, w⟩ := p
  have key : ∀ (t : AltBase) (v : Fin 1 × Fin 2 → A),
      ((accF ((t, j) : AltTag k)).Realize v ↔ AltAccSt (((t, j), w) : AltV k A)) := by
    intro t v
    cases t <;> simp [accF, AltAccSt]
  exact key t _


-- @@ L558-570 verbatim
omit [Finite A] [Nonempty A] in
theorem relMap_blank (p : AltV k A) :
    ATMBlank (k := k) (altMapEquiv (A := A) cnf p) ↔ AltBlank p := by
  rw [ATMBlank, FOInterpretation.relMap_map]
  obtain ⟨⟨t, j⟩, w⟩ := p
  have key : ∀ (t : AltBase) (v : Fin 1 × Fin 2 → A), v (0, 0) = w 0 → v (0, 1) = w 1 →
      ((blankF ((t, j) : AltTag k)).Realize v ↔ AltBlank (((t, j), w) : AltV k A)) := by
    intro t v h0 h1
    cases t <;>
      simp only [blankF, AltBlank, IsMinTup2, Formula.realize_inf, Formula.realize_bot,
        realize_minF, realize_sideF, Prod.mk.injEq, Fin.ext_iff, Fin.val_zero, h0, h1] <;>
      tauto
  exact key t _ rfl rfl


-- @@ L572-581 verbatim
omit [Finite A] [Nonempty A] in
theorem relMap_right (p : AltV k A) :
    ATMRight (k := k) (altMapEquiv (A := A) cnf p) ↔ AltRight p := by
  rw [ATMRight, FOInterpretation.relMap_map]
  obtain ⟨⟨t, j⟩, w⟩ := p
  have key : ∀ (t : AltBase) (v : Fin 1 × Fin 2 → A),
      ((rightF ((t, j) : AltTag k)).Realize v ↔ AltRight (((t, j), w) : AltV k A)) := by
    intro t v
    cases t <;> try (rename_i d; cases d <;> simp [rightF, AltRight])
  exact key t _


-- @@ L583-587 verbatim
omit [Finite A] [Nonempty A] in
theorem relMap_le (p q : AltV k A) :
    ATMLe (k := k) (altMapEquiv (A := A) cnf p) (altMapEquiv cnf q) ↔ tagTupleLe p q := by
  rw [ATMLe, FOInterpretation.relMap_map]
  exact realize_lexLeF


-- @@ L589-633 verbatim
theorem relMap_inp (p q : AltV k A) :
    ATMInp (k := k) (altMapEquiv (A := A) cnf p) (altMapEquiv cnf q) ↔ AltInp p q := by
  rw [ATMInp, FOInterpretation.relMap_map]
  obtain ⟨⟨t, j⟩, w⟩ := p
  have key : ∀ (t : AltBase) (v : Fin 2 × Fin 2 → A), v (0, 0) = w 0 → v (1, 0) = q.2 0 →
      v (1, 1) = q.2 1 →
      ((inpF ((t, j) : AltTag k) q.1).Realize v ↔ AltInp (((t, j), w) : AltV k A) q) := by
    intro t v h00 h10 h11
    cases t
    case pStart =>
      refine (realize_acstF h10 h11).trans ?_
      simp only [AltInp, IsMinTup2]
      constructor
      · rintro rfl
        exact Or.inl ⟨trivial, rfl, fun a => qbotA_le a, fun a => qbotA_le a⟩
      · rintro (⟨-, ht, hm⟩ | ⟨h, -⟩ | ⟨h, -⟩)
        · exact altV_ext ht (le_antisymm (hm.1 qbotA) (qbotA_le _))
            (le_antisymm (hm.2 qbotA) (qbotA_le _))
        · exact absurd h (by simp)
        · exact absurd h (by simp)
    case pCell =>
      refine (realize_aoneF h10 h11 h00).trans ?_
      simp only [AltInp]
      constructor
      · rintro rfl
        exact Or.inr (Or.inl ⟨trivial, rfl, rfl, fun a => qbotA_le a⟩)
      · rintro (⟨h, -⟩ | ⟨-, ht, h0, h1⟩ | ⟨h, -⟩)
        · exact absurd h (by simp)
        · exact altV_ext ht h0 (le_antisymm (h1 qbotA) (qbotA_le _))
        · exact absurd h (by simp)
    case pEnd =>
      refine (realize_acstF h10 h11).trans ?_
      simp only [AltInp, IsMinTup2]
      constructor
      · rintro rfl
        exact Or.inr (Or.inr ⟨trivial, rfl, fun a => qbotA_le a, fun a => qbotA_le a⟩)
      · rintro (⟨h, -⟩ | ⟨h, -⟩ | ⟨-, ht, hm⟩)
        · exact absurd h (by simp)
        · exact absurd h (by simp)
        · exact altV_ext ht (le_antisymm (hm.1 qbotA) (qbotA_le _))
            (le_antisymm (hm.2 qbotA) (qbotA_le _))
    all_goals
      refine iff_of_false (by exact fun h => h) ?_
      rintro (⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩) <;> exact AltBase.noConfusion h
  exact key t _ rfl rfl rfl


-- @@ L635-651 verbatim
theorem relMap_tsrc (p q : AltV k A) :
    ATMSrc (k := k) (altMapEquiv (A := A) cnf p) (altMapEquiv cnf q) ↔ AltSrc cnf p q := by
  rw [ATMSrc, FOInterpretation.relMap_map]
  obtain ⟨⟨t, j⟩, w⟩ := p
  cases t
  case tGStart => exact realize_acstF rfl rfl
  case tGKeep _ => exact realize_acstF rfl rfl
  case tGSet => exact realize_acstF rfl rfl
  case tGTurn => exact realize_acstF rfl rfl
  case tGBack _ => exact realize_acstF rfl rfl
  case tGNext => exact realize_acstF rfl rfl
  case tGEndAcc => exact realize_acstF rfl rfl
  case tGEndChk => exact realize_acstF rfl rfl
  case tChk _ _ _ => exact realize_aoneF rfl rfl rfl
  case tTurnNext _ => exact realize_aoneF rfl rfl rfl
  case tTurnAcc _ => exact realize_aoneF rfl rfl rfl
  all_goals exact Iff.rfl


-- @@ L653-669 verbatim
theorem relMap_tread (p q : AltV k A) :
    ATMRead (k := k) (altMapEquiv (A := A) cnf p) (altMapEquiv cnf q) ↔ AltRead p q := by
  rw [ATMRead, FOInterpretation.relMap_map]
  obtain ⟨⟨t, j⟩, w⟩ := p
  cases t
  case tGStart => exact realize_acstF rfl rfl
  case tGKeep _ => exact realize_aoneF rfl rfl rfl
  case tGSet => exact realize_aoneF rfl rfl rfl
  case tGTurn => exact realize_acstF rfl rfl
  case tGBack _ => exact realize_aoneF rfl rfl rfl
  case tGNext => exact realize_acstF rfl rfl
  case tGEndAcc => exact realize_acstF rfl rfl
  case tGEndChk => exact realize_acstF rfl rfl
  case tChk _ _ _ => exact realize_aoneF rfl rfl rfl
  case tTurnNext d => cases d <;> exact realize_acstF rfl rfl
  case tTurnAcc d => cases d <;> exact realize_acstF rfl rfl
  all_goals exact Iff.rfl


-- @@ L671-687 verbatim
theorem relMap_twrite (p q : AltV k A) :
    ATMWrite (k := k) (altMapEquiv (A := A) cnf p) (altMapEquiv cnf q) ↔ AltWrite p q := by
  rw [ATMWrite, FOInterpretation.relMap_map]
  obtain ⟨⟨t, j⟩, w⟩ := p
  cases t
  case tGStart => exact realize_acstF rfl rfl
  case tGKeep _ => exact realize_aoneF rfl rfl rfl
  case tGSet => exact realize_aoneF rfl rfl rfl
  case tGTurn => exact realize_acstF rfl rfl
  case tGBack _ => exact realize_aoneF rfl rfl rfl
  case tGNext => exact realize_acstF rfl rfl
  case tGEndAcc => exact realize_acstF rfl rfl
  case tGEndChk => exact realize_acstF rfl rfl
  case tChk _ _ _ => exact realize_aoneF rfl rfl rfl
  case tTurnNext d => cases d <;> exact realize_acstF rfl rfl
  case tTurnAcc d => cases d <;> exact realize_acstF rfl rfl
  all_goals exact Iff.rfl


-- @@ L689-716 verbatim
theorem relMap_tdst (p q : AltV k A) :
    ATMDst (k := k) (altMapEquiv (A := A) cnf p) (altMapEquiv cnf q) ↔ AltDst cnf p q := by
  rw [ATMDst, FOInterpretation.relMap_map]
  obtain ⟨⟨t, j⟩, w⟩ := p
  have key : ∀ (t : AltBase) (v : Fin 2 × Fin 2 → A), v (0, 0) = w 0 → v (0, 1) = w 1 →
      v (1, 0) = q.2 0 → v (1, 1) = q.2 1 →
      ((tdstF cnf ((t, j) : AltTag k) q.1).Realize v ↔
        AltDst cnf (((t, j), w) : AltV k A) q) := by
    intro t v h00 h01 h10 h11
    cases t
    case tGStart => exact realize_acstF h10 h11
    case tGKeep _ => exact realize_acstF h10 h11
    case tGSet => exact realize_acstF h10 h11
    case tGTurn => exact realize_acstF h10 h11
    case tGBack _ => exact realize_acstF h10 h11
    case tGNext => exact realize_acstF h10 h11
    case tGEndAcc => exact realize_acstF h10 h11
    case tGEndChk => exact realize_aoneF h10 h11 h00
    case tChk b f d =>
      have hone : ∀ fl : Bool,
          ((aoneF ((AltBase.qChk fl d, 0) : AltTag k) (0, 0) q.1).Realize v ↔
            q = aoneI (AltBase.qChk fl d) 0 (w 0)) := fun fl => realize_aoneF h10 h11 h00
      simp only [tdstF, AltDst, Formula.realize_sup, Formula.realize_inf, hone]
      cases f <;> simp [h00, h01]
    case tTurnNext d => exact realize_aoneF h10 h11 h01
    case tTurnAcc _ => exact realize_acstF h10 h11
    all_goals exact Iff.rfl
  exact key t _ rfl rfl rfl rfl


-- @@ L718-736 verbatim
omit [Finite A] [Nonempty A] in
theorem relMap_blk (hk : 0 < k) (j : ℕ) (p : AltV k A) :
    ATMBlk (k := k) j (altMapEquiv (A := A) cnf p) ↔ AltBlkOf j p := by
  have key : ∀ (h : j < k) (v : Fin 1 × Fin 2 → A),
      ((blkStF (⟨j, h⟩ : Fin k) p.1).Realize v ↔ j = altBlockOfTag p.1) := by
    intro h v
    simp only [blkStF, realize_sideF]
  rw [ATMBlk, AltBlkOf, altBlockOf_eq_tag]
  constructor
  · rintro ⟨h, hb⟩
    rw [FOInterpretation.relMap_map] at hb
    exact (key h _).mp hb
  · intro hbl
    have hlt : j < k := by
      rw [hbl, ← altBlockOf_eq_tag]
      exact altBlockOf_lt hk p
    refine ⟨hlt, ?_⟩
    rw [FOInterpretation.relMap_map]
    exact (key hlt _).mpr hbl


-- @@ L738-738 verbatim
/-! ### The machines agree, and the reduction -/


-- @@ L740-759 verbatim
/-- **The interpreted structure describes the machine of the instance**: every
field of `DescriptiveComplexity.atmData` on the interpreted structure agrees,
along the identity equivalence, with `DescriptiveComplexity.AltQbf.altMachine`. -/
theorem altAgree_altMachine (hk : 0 < k) :
    ATMData.AltAgree (altMapEquiv (A := A) cnf) (altMachine k A cnf)
      (atmData k ((altTuringInterp k cnf).Map A)) where
  base :=
    { posn := fun b => (relMap_posn cnf b).symm
      le := fun b b' => (relMap_le cnf b b').symm
      tr := fun b => (relMap_tr cnf b).symm
      start := fun b => (relMap_start cnf b).symm
      acc := fun b => (relMap_acc cnf b).symm
      blank := fun b => (relMap_blank cnf b).symm
      right := fun b => (relMap_right cnf b).symm
      src := fun b b' => (relMap_tsrc cnf b b').symm
      read := fun b b' => (relMap_tread cnf b b').symm
      dst := fun b b' => (relMap_tdst cnf b b').symm
      write := fun b b' => (relMap_twrite cnf b b').symm
      inp := fun b b' => (relMap_inp cnf b b').symm }
  blk := fun j b => (relMap_blk cnf hk j b).symm


-- @@ L761-776 verbatim
/-- **Correctness of the interpretation**: the interpreted structure is a
yes-instance of alternating acceptance exactly when the quantified formula is
true. Both promises hold unconditionally, and acceptance is
`DescriptiveComplexity.AltQbf.altAccepts_iff_qbf`, transported along the
agreement. -/
theorem atmAccept_map_iff (hk : 0 < k) (start : Bool) :
    (ATMAccept k start).Holds ((altTuringInterp k cnf).Map A) ↔
      altQuant A k (QbfMatrix cnf) start := by
  have hag := altAgree_altMachine (A := A) cnf hk
  constructor
  · rintro ⟨-, -, hacc⟩
    exact (altAccepts_iff_qbf hk).mp ((hag.altAccepts start).mpr hacc)
  · intro hq
    exact ⟨hag.base.wellFormed.mp (altMachine_wellFormed cnf),
      (hag.blocksWellFormed k).mp (altMachine_blocksWellFormed cnf hk),
      (hag.altAccepts start).mp ((altAccepts_iff_qbf hk).mpr hq)⟩


-- @@ L778-778 verbatim
end Characterize


-- @@ L780-788 verbatim
/-- **A quantified Boolean formula reduces to acceptance by an alternating
machine**: the ordered first-order reduction building `M_φ` inside the
instance. -/
noncomputable def qbf_ordered_fo_reduction_atmAccept (hk : 0 < k) (start cnf : Bool) :
    QbfProblem k start cnf ≤ᶠᵒ[≤] ATMAccept k start where
  Tag := AltTag k
  dim := 2
  toInterpretation := altTuringInterp k cnf
  correct _ _ _ _ _ := (atmAccept_map_iff cnf hk start).symm


-- @@ L790-790 verbatim
end AltQbf


-- @@ L792-792 verbatim
end DescriptiveComplexity
