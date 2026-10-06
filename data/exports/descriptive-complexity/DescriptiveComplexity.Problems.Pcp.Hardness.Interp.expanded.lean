/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Syntax
import DescriptiveComplexity.Problems.Pcp.Hardness.Match
import DescriptiveComplexity.Ordered


-- @@ L10-31 verbatim
/-!
# The interpretation: drawing the domino system first-order

The first-order half of `HALT ≤ᶠᵒ[≤] PCP`: the defining formulas of an
interpretation of `Language.pcp` in ordered machine instances, each realizing
exactly the corresponding semantic predicate of
`DescriptiveComplexity.Problems.Pcp.Hardness.Draw` – which is all the
correctness proof of `DescriptiveComplexity.Problems.Pcp.Hardness.Match`
consumes, through `DescriptiveComplexity.HaltPcp.Reads`.

## Method

As in the QSAT machine interpretation, every static decision is taken in Lean
rather than in the formula: the tags of the arguments are pattern-matched, and
`⊤`/`⊥` close the cases the tables decide. The one genuinely recursive piece
is `DescriptiveComplexity.HaltPcp.specListF`, which turns a word table of
`DescriptiveComplexity.HaltPcp.LSpec` entries into a disjunction of “argument
`1` is the `i`-th shared position and argument `2` is the specified letter”
clauses – realized, by one induction over the table, as membership of the
zipped table, which is verbatim the semantic letter relation
`DescriptiveComplexity.HaltPcp.PUAt`.
-/


-- @@ L33-33 verbatim
namespace DescriptiveComplexity


-- @@ L35-35 verbatim
namespace HaltPcp


-- @@ L37-37 verbatim
open FirstOrder


-- @@ L39-39 verbatim
open Language Structure


-- @@ L41-43 verbatim
/-- The vocabulary the reduction reads: machine instances with the ambient
order. -/
abbrev haltOrd : Language := Language.turing.sum Language.order


-- @@ L45-45 verbatim
/-! ### The symbols of the ordered expansion -/


-- @@ L47-48 verbatim
/-- The position symbol. -/
abbrev hPosnSym : haltOrd.Relations 1 := Sum.inl .posn


-- @@ L50-51 verbatim
/-- The transition symbol. -/
abbrev hTrSym : haltOrd.Relations 1 := Sum.inl .tr


-- @@ L53-54 verbatim
/-- The start-state symbol. -/
abbrev hStartSym : haltOrd.Relations 1 := Sum.inl .start


-- @@ L56-57 verbatim
/-- The accepting-state symbol. -/
abbrev hAccSym : haltOrd.Relations 1 := Sum.inl .acc


-- @@ L59-60 verbatim
/-- The blank symbol. -/
abbrev hBlankSym : haltOrd.Relations 1 := Sum.inl .blank


-- @@ L62-63 verbatim
/-- The move-right symbol. -/
abbrev hRightSym : haltOrd.Relations 1 := Sum.inl .right


-- @@ L65-66 verbatim
/-- The machine's order symbol. -/
abbrev hLeSym : haltOrd.Relations 2 := Sum.inl .le


-- @@ L68-69 verbatim
/-- The transition-source symbol. -/
abbrev hSrcSym : haltOrd.Relations 2 := Sum.inl .tsrc


-- @@ L71-72 verbatim
/-- The transition-read symbol. -/
abbrev hReadSym : haltOrd.Relations 2 := Sum.inl .tread


-- @@ L74-75 verbatim
/-- The transition-destination symbol. -/
abbrev hDstSym : haltOrd.Relations 2 := Sum.inl .tdst


-- @@ L77-78 verbatim
/-- The transition-write symbol. -/
abbrev hWriteSym : haltOrd.Relations 2 := Sum.inl .twrite


-- @@ L80-81 verbatim
/-- The input symbol. -/
abbrev hInpSym : haltOrd.Relations 2 := Sum.inl .inp


-- @@ L83-84 verbatim
/-- The ambient order symbol. -/
abbrev hOrdSym : haltOrd.Relations 2 := Sum.inr leSymb


-- @@ L86-86 verbatim
/-! ### The builders -/


-- @@ L88-88 verbatim
section Builders


-- @@ L90-90 verbatim
variable {α : Type}


-- @@ L92-93 expanded
/-- `x` is a position. -/
def posnF (x : α) : haltOrd.Formula α :=
  FirstOrder.Language.Relations.formula₁ hPosnSym (FirstOrder.Language.Term.var x)


-- @@ L95-96 expanded
/-- `x` is a transition. -/
def trF (x : α) : haltOrd.Formula α :=
  FirstOrder.Language.Relations.formula₁ hTrSym (FirstOrder.Language.Term.var x)


-- @@ L98-99 expanded
/-- `x` is a start state. -/
def startF (x : α) : haltOrd.Formula α :=
  FirstOrder.Language.Relations.formula₁ hStartSym (FirstOrder.Language.Term.var x)


-- @@ L101-102 expanded
/-- `x` is an accepting state. -/
def accF (x : α) : haltOrd.Formula α :=
  FirstOrder.Language.Relations.formula₁ hAccSym (FirstOrder.Language.Term.var x)


-- @@ L104-105 expanded
/-- `x` is the blank symbol. -/
def blankF (x : α) : haltOrd.Formula α :=
  FirstOrder.Language.Relations.formula₁ hBlankSym (FirstOrder.Language.Term.var x)


-- @@ L107-108 expanded
/-- `x` moves the head right. -/
def rightF (x : α) : haltOrd.Formula α :=
  FirstOrder.Language.Relations.formula₁ hRightSym (FirstOrder.Language.Term.var x)


-- @@ L110-111 expanded
/-- `x ≤ y` in the machine's order. -/
def mLeF (x y : α) : haltOrd.Formula α :=
  FirstOrder.Language.Relations.formula₂ hLeSym (FirstOrder.Language.Term.var x)
    (FirstOrder.Language.Term.var y)


-- @@ L113-114 expanded
/-- `x` applies in the state `y`. -/
def srcF (x y : α) : haltOrd.Formula α :=
  FirstOrder.Language.Relations.formula₂ hSrcSym (FirstOrder.Language.Term.var x)
    (FirstOrder.Language.Term.var y)


-- @@ L116-117 expanded
/-- `x` reads the symbol `y`. -/
def readF (x y : α) : haltOrd.Formula α :=
  FirstOrder.Language.Relations.formula₂ hReadSym (FirstOrder.Language.Term.var x)
    (FirstOrder.Language.Term.var y)


-- @@ L119-120 expanded
/-- `x` moves to the state `y`. -/
def dstF (x y : α) : haltOrd.Formula α :=
  FirstOrder.Language.Relations.formula₂ hDstSym (FirstOrder.Language.Term.var x)
    (FirstOrder.Language.Term.var y)


-- @@ L122-123 expanded
/-- `x` writes the symbol `y`. -/
def writeF (x y : α) : haltOrd.Formula α :=
  FirstOrder.Language.Relations.formula₂ hWriteSym (FirstOrder.Language.Term.var x)
    (FirstOrder.Language.Term.var y)


-- @@ L125-126 expanded
/-- The cell `x` initially holds the symbol `y`. -/
def inpF (x y : α) : haltOrd.Formula α :=
  FirstOrder.Language.Relations.formula₂ hInpSym (FirstOrder.Language.Term.var x)
    (FirstOrder.Language.Term.var y)


-- @@ L128-129 expanded
/-- `x ≤ y` in the ambient order. -/
def ordF (x y : α) : haltOrd.Formula α :=
  FirstOrder.Language.Relations.formula₂ hOrdSym (FirstOrder.Language.Term.var x)
    (FirstOrder.Language.Term.var y)


-- @@ L131-132 expanded
/-- `x = y`. -/
def eqF (x y : α) : haltOrd.Formula α :=
  FirstOrder.Language.Term.equal (FirstOrder.Language.Term.var x) (FirstOrder.Language.Term.var y)


-- @@ L134-135 expanded
/-- `x < y` in the ambient order. -/
def ordLtF (x y : α) : haltOrd.Formula α :=
  ordF x y ⊓ FirstOrder.Language.BoundedFormula.not (eqF x y)


-- @@ L137-138 expanded
/-- `x < y` in the machine's order. -/
def mLtF (x y : α) : haltOrd.Formula α :=
  mLeF x y ⊓ FirstOrder.Language.BoundedFormula.not (eqF x y)


-- @@ L140-141 expanded
/-- `x` is the least element of the ambient order. -/
noncomputable def minF (x : α) : haltOrd.Formula α :=
  FirstOrder.Language.Formula.iAlls (Fin 1) (ordF (Sum.inl x) (Sum.inr 0))


-- @@ L143-146 expanded
/-- The cell `x` initially holds `y`: its input symbol, or the blank if it has
none. -/
noncomputable def initTapeF (x y : α) : haltOrd.Formula α :=
  inpF x y ⊔
    FirstOrder.Language.Formula.iAlls (Fin 1)
        (FirstOrder.Language.BoundedFormula.not (inpF (Sum.inl x) (Sum.inr 0))) ⊓
      blankF y


-- @@ L148-156 expanded
/-- Well-formedness of the machine, as a formula with unused free variables:
the machine's order is linear, there is a position, the input is functional,
and there is exactly one blank. -/
noncomputable def wfF : haltOrd.Formula α :=
  FirstOrder.Language.Formula.iAlls (Fin 3)
      (mLeF (Sum.inr 0) (Sum.inr 0) ⊓
        ((mLeF (Sum.inr 0) (Sum.inr 1)).imp
            ((mLeF (Sum.inr 1) (Sum.inr 2)).imp (mLeF (Sum.inr 0) (Sum.inr 2))) ⊓
          ((mLeF (Sum.inr 0) (Sum.inr 1)).imp
              ((mLeF (Sum.inr 1) (Sum.inr 0)).imp (eqF (Sum.inr 0) (Sum.inr 1))) ⊓
            ((mLeF (Sum.inr 0) (Sum.inr 1) ⊔ mLeF (Sum.inr 1) (Sum.inr 0)) ⊓
              ((inpF (Sum.inr 0) (Sum.inr 1)).imp
                  ((inpF (Sum.inr 0) (Sum.inr 2)).imp (eqF (Sum.inr 1) (Sum.inr 2))) ⊓
                (blankF (Sum.inr 0)).imp
                  ((blankF (Sum.inr 1)).imp (eqF (Sum.inr 0) (Sum.inr 1)))))))) ⊓
    (FirstOrder.Language.Formula.iExs (Fin 1) (posnF (Sum.inr 0)) ⊓
      FirstOrder.Language.Formula.iExs (Fin 1) (blankF (Sum.inr 0)))


-- @@ L158-162 expanded
/-- Some transition with the given attributes exists; the direction of the
move is a static decision. -/
noncomputable def existsMoveF (right : Bool) (q a b q' : α) : haltOrd.Formula α :=
  FirstOrder.Language.Formula.iExs (Fin 1)
    (trF (Sum.inr 0) ⊓
      ((if right then rightF (Sum.inr 0)
        else FirstOrder.Language.BoundedFormula.not (rightF (Sum.inr 0))) ⊓
        (srcF (Sum.inr 0) (Sum.inl q) ⊓
          (readF (Sum.inr 0) (Sum.inl a) ⊓
            (dstF (Sum.inr 0) (Sum.inl q') ⊓ writeF (Sum.inr 0) (Sum.inl b))))))


-- @@ L164-164 verbatim
/-! ### Realization of the builders -/


-- @@ L166-166 verbatim
section BuilderRealize


-- @@ L168-168 verbatim
variable {α A : Type} [Language.turing.Structure A] [LinearOrder A]

-- @@ L169-169 verbatim
variable {v : α → A}


-- @@ L171-173 verbatim
@[simp] theorem realize_posnF {x : α} : (posnF x).Realize v ↔ TMPosn (v x) := by
  rw [posnF, Formula.realize_rel₁]
  exact Iff.rfl


-- @@ L175-177 verbatim
@[simp] theorem realize_trF {x : α} : (trF x).Realize v ↔ TMTr (v x) := by
  rw [trF, Formula.realize_rel₁]
  exact Iff.rfl


-- @@ L179-181 verbatim
@[simp] theorem realize_startF {x : α} : (startF x).Realize v ↔ TMStart (v x) := by
  rw [startF, Formula.realize_rel₁]
  exact Iff.rfl


-- @@ L183-185 verbatim
@[simp] theorem realize_accF {x : α} : (accF x).Realize v ↔ TMAcc (v x) := by
  rw [accF, Formula.realize_rel₁]
  exact Iff.rfl


-- @@ L187-189 verbatim
@[simp] theorem realize_blankF {x : α} : (blankF x).Realize v ↔ TMBlank (v x) := by
  rw [blankF, Formula.realize_rel₁]
  exact Iff.rfl


-- @@ L191-193 verbatim
@[simp] theorem realize_rightF {x : α} : (rightF x).Realize v ↔ TMRight (v x) := by
  rw [rightF, Formula.realize_rel₁]
  exact Iff.rfl


-- @@ L195-197 verbatim
@[simp] theorem realize_mLeF {x y : α} : (mLeF x y).Realize v ↔ TMLe (v x) (v y) := by
  rw [mLeF, Formula.realize_rel₂]
  exact Iff.rfl


-- @@ L199-201 verbatim
@[simp] theorem realize_srcF {x y : α} : (srcF x y).Realize v ↔ TMSrc (v x) (v y) := by
  rw [srcF, Formula.realize_rel₂]
  exact Iff.rfl


-- @@ L203-205 verbatim
@[simp] theorem realize_readF {x y : α} : (readF x y).Realize v ↔ TMRead (v x) (v y) := by
  rw [readF, Formula.realize_rel₂]
  exact Iff.rfl


-- @@ L207-209 verbatim
@[simp] theorem realize_dstF {x y : α} : (dstF x y).Realize v ↔ TMDst (v x) (v y) := by
  rw [dstF, Formula.realize_rel₂]
  exact Iff.rfl


-- @@ L211-213 verbatim
@[simp] theorem realize_writeF {x y : α} : (writeF x y).Realize v ↔ TMWrite (v x) (v y) := by
  rw [writeF, Formula.realize_rel₂]
  exact Iff.rfl


-- @@ L215-217 verbatim
@[simp] theorem realize_inpF {x y : α} : (inpF x y).Realize v ↔ TMInp (v x) (v y) := by
  rw [inpF, Formula.realize_rel₂]
  exact Iff.rfl


-- @@ L219-221 verbatim
@[simp] theorem realize_ordF {x y : α} : (ordF x y).Realize v ↔ v x ≤ v y := by
  rw [ordF, Formula.realize_rel₂]
  exact Iff.rfl


-- @@ L223-224 verbatim
@[simp] theorem realize_eqF {x y : α} : (eqF x y).Realize v ↔ v x = v y := by
  simp [eqF]


-- @@ L226-229 verbatim
@[simp] theorem realize_ordLtF {x y : α} : (ordLtF x y).Realize v ↔ v x < v y := by
  rw [ordLtF]
  simp only [Formula.realize_inf, realize_ordF, Formula.realize_not, realize_eqF]
  exact ⟨fun h => lt_of_le_of_ne h.1 h.2, fun h => ⟨le_of_lt h, ne_of_lt h⟩⟩


-- @@ L231-233 verbatim
@[simp] theorem realize_mLtF {x y : α} : (mLtF x y).Realize v ↔ MLt (v x) (v y) := by
  rw [mLtF, MLt]
  simp only [Formula.realize_inf, realize_mLeF, Formula.realize_not, realize_eqF]


-- @@ L235-238 verbatim
@[simp] theorem realize_minF {x : α} : (minF x).Realize v ↔ ∀ a : A, v x ≤ a := by
  rw [minF]
  simp only [Formula.realize_iAlls, realize_ordF, Sum.elim_inl, Sum.elim_inr]
  exact ⟨fun h a => h ![a], fun h i => h (i 0)⟩


-- @@ L240-245 verbatim
@[simp] theorem realize_initTapeF {x y : α} :
    (initTapeF x y).Realize v ↔ (tmData A).InitTape (v x) (v y) := by
  rw [initTapeF, TMData.InitTape]
  simp only [Formula.realize_sup, realize_inpF, Formula.realize_inf, Formula.realize_iAlls,
    Formula.realize_not, Sum.elim_inl, Sum.elim_inr, realize_blankF]
  refine or_congr Iff.rfl (and_congr ⟨fun h a ha => h ![a] ha, fun h i => h (i 0)⟩ Iff.rfl)


-- @@ L247-267 verbatim
@[simp] theorem realize_wfF : (wfF (α := α)).Realize v ↔ (tmData A).WellFormed := by
  rw [wfF, TMData.WellFormed, IsLinOrd]
  simp only [Formula.realize_inf, Formula.realize_iAlls, Formula.realize_imp,
    Formula.realize_sup, Formula.realize_iExs, realize_mLeF, realize_eqF, realize_inpF,
    realize_blankF, realize_posnF, Sum.elim_inr]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨⟨fun a => (h1 ![a, a, a]).1,
      fun a b c hab hbc => (h1 ![a, b, c]).2.1 hab hbc,
      fun a b hab hba => (h1 ![a, b, a]).2.2.1 hab hba,
      fun a b => (h1 ![a, b, a]).2.2.2.1⟩,
      ?_, fun p a b ha hb => (h1 ![p, a, b]).2.2.2.2.1 ha hb, ?_,
      fun a b ha hb => (h1 ![a, b, a]).2.2.2.2.2 ha hb⟩
    · obtain ⟨i, hi⟩ := h2
      exact ⟨i 0, hi⟩
    · obtain ⟨i, hi⟩ := h3
      exact ⟨i 0, hi⟩
  · rintro ⟨⟨hr, ht, ha, hto⟩, ⟨p, hp⟩, hinp, ⟨b, hb⟩, hbu⟩
    exact ⟨fun i => ⟨hr _, fun h1 h2 => ht _ _ _ h1 h2, fun h1 h2 => ha _ _ h1 h2,
      hto _ _, fun h1 h2 => hinp _ _ _ h1 h2, fun h1 h2 => hbu _ _ h1 h2⟩,
      ⟨![p], hp⟩, ⟨![b], hb⟩⟩


-- @@ L269-286 verbatim
@[simp] theorem realize_existsMoveF {right : Bool} {q a b q' : α} :
    (existsMoveF right q a b q').Realize v ↔
      ∃ τ, TMTr τ ∧ (if right then TMRight τ else ¬TMRight τ) ∧ TMSrc τ (v q) ∧
        TMRead τ (v a) ∧ TMDst τ (v q') ∧ TMWrite τ (v b) := by
  rw [existsMoveF]
  simp only [Formula.realize_iExs, Formula.realize_inf, realize_trF, realize_srcF,
    realize_readF, realize_dstF, realize_writeF, Sum.elim_inl, Sum.elim_inr]
  constructor
  · rintro ⟨i, h1, h2, h3, h4, h5, h6⟩
    refine ⟨i 0, h1, ?_, h3, h4, h5, h6⟩
    cases right
    · simpa using h2
    · simpa using h2
  · rintro ⟨τ, h1, h2, h3, h4, h5, h6⟩
    refine ⟨![τ], h1, ?_, h3, h4, h5, h6⟩
    cases right
    · simpa using h2
    · simpa using h2


-- @@ L288-288 verbatim
end BuilderRealize


-- @@ L290-290 verbatim
end Builders


-- @@ L292-296 verbatim
/-! ### The letter formulas

The word tables of `DescriptiveComplexity.Problems.Pcp.Hardness.Draw` are
turned into formulas entry by entry: “argument `1` is the `i`-th shared
position and argument `2` is the specified letter”. -/


-- @@ L298-307 verbatim
/-- The tag of the `i`-th shared position. -/
def posTagN : ℕ → PTag
  | 0 => .pos0
  | 1 => .pos1
  | 2 => .pos2
  | 3 => .pos3
  | 4 => .pos4
  | 5 => .pos5
  | 6 => .pos6
  | _ => .pos7


-- @@ L309-320 verbatim
/-- The shared positions are the constants of their tags. -/
theorem posE_eq {A : Type} [LinearOrder A] [Finite A] [Nonempty A] :
    ∀ i : ℕ, posE (A := A) i = cstE (posTagN i)
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | 4 => rfl
  | 5 => rfl
  | 6 => rfl
  | 7 => rfl
  | (_ + 8) => rfl


-- @@ L322-322 verbatim
section LetterFormulas


-- @@ L324-326 verbatim
/-- All five coordinates of the argument `k` are minimal. -/
noncomputable def minAllF (k : Fin 3) : haltOrd.Formula (Fin 3 × Fin 5) :=
  minF (k, 0) ⊓ (minF (k, 1) ⊓ (minF (k, 2) ⊓ (minF (k, 3) ⊓ minF (k, 4))))


-- @@ L328-330 verbatim
/-- The four last coordinates of the argument `k` are minimal. -/
noncomputable def minTailF (k : Fin 3) : haltOrd.Formula (Fin 3 × Fin 5) :=
  minF (k, 1) ⊓ (minF (k, 2) ⊓ (minF (k, 3) ⊓ minF (k, 4)))


-- @@ L332-334 verbatim
/-- The letter argument is the constant letter of the tag `s`. -/
noncomputable def cstLF (s tc : PTag) : haltOrd.Formula (Fin 3 × Fin 5) :=
  if tc = s then minAllF 2 else ⊥


-- @@ L336-340 verbatim
/-- The letter argument carries the `j`-th coordinate of the domino
argument. -/
noncomputable def idxLF (s : PTag) (j : Fin 5) (tc : PTag) :
    haltOrd.Formula (Fin 3 × Fin 5) :=
  if tc = s then eqF (2, 0) (0, j) ⊓ minTailF 2 else ⊥


-- @@ L342-345 verbatim
/-- The formula of one table entry. -/
noncomputable def specF : LSpec → PTag → haltOrd.Formula (Fin 3 × Fin 5)
  | .cst s, tc => cstLF s tc
  | .idx s j, tc => idxLF s j tc


-- @@ L347-349 verbatim
/-- The position argument is the `i`-th shared position. -/
noncomputable def posIsF (i : ℕ) (tp : PTag) : haltOrd.Formula (Fin 3 × Fin 5) :=
  if tp = posTagN i then minAllF 1 else ⊥


-- @@ L351-355 verbatim
/-- **The formula of a word table**, entry by entry from the `i`-th shared
position on. -/
noncomputable def specListF : List LSpec → ℕ → PTag → PTag → haltOrd.Formula (Fin 3 × Fin 5)
  | [], _, _, _ => ⊥
  | sp :: rest, i, tp, tc => (posIsF i tp ⊓ specF sp tc) ⊔ specListF rest (i + 1) tp tc


-- @@ L357-359 verbatim
/-- The formula of the top word of a domino tag. -/
noncomputable def uAtF (td tp tc : PTag) : haltOrd.Formula (Fin 3 × Fin 5) :=
  specListF (uSpec td) 0 tp tc


-- @@ L361-379 verbatim
/-- The formula of the start domino's bottom word, by the tag of the
position. -/
noncomputable def startBotF (tp tc : PTag) : haltOrd.Formula (Fin 3 × Fin 5) :=
  match tp with
  | .pos0 => minAllF 1 ⊓ cstLF .ltStar tc
  | .pos1 => minAllF 1 ⊓ cstLF .ltTri tc
  | .pos2 => minAllF 1 ⊓ cstLF .ltStar tc
  | .pos3 => minAllF 1 ⊓ cstLF .ltLft tc
  | .pos4 => minAllF 1 ⊓ cstLF .ltStar tc
  | .pos5 => minAllF 1 ⊓ cstLF .ltBoot tc
  | .pos6 => minAllF 1 ⊓ cstLF .ltStar tc
  | .pairSym => posnF (1, 0) ⊓ (minTailF 1 ⊓
      (if tc = .ltSym then initTapeF (1, 0) (2, 0) ⊓ minTailF 2 else ⊥))
  | .pairStar => posnF (1, 0) ⊓ (minTailF 1 ⊓ cstLF .ltStar tc)
  | .hi0 => minAllF 1 ⊓ cstLF .ltRgt tc
  | .hi1 => minAllF 1 ⊓ cstLF .ltStar tc
  | .hi2 => minAllF 1 ⊓ cstLF .ltSep tc
  | .hi3 => minAllF 1 ⊓ cstLF .ltStar tc
  | _ => ⊥


-- @@ L381-385 verbatim
/-- The formula of the bottom word of a domino tag. -/
noncomputable def vAtF (td tp tc : PTag) : haltOrd.Formula (Fin 3 × Fin 5) :=
  match td with
  | .dStart => startBotF tp tc
  | _ => specListF (vSpec td) 0 tp tc


-- @@ L387-387 verbatim
end LetterFormulas


-- @@ L389-389 verbatim
/-! ### The domino and order formulas -/


-- @@ L391-404 expanded
/-- The formula marking the dominoes: well-formedness of the machine and the
side condition of the tag. -/
noncomputable def domF : PTag → haltOrd.Formula (Fin 1 × Fin 5)
  | .dStart | .dClose | .dCopySep => wfF
  | .dCopyLft | .dCopyRgt | .dCopyBoot | .dCopyHalt => wfF
  | .dCopySym | .dCopyState => wfF
  | .dEraseSymL | .dEraseLft | .dEraseSymR | .dEraseRgt => wfF
  | .dBoot => wfF ⊓ startF (0, 0)
  | .dAcc => wfF ⊓ accF (0, 0)
  | .dMoveR => wfF ⊓ (existsMoveF true) (0, 0) (0, 1) (0, 2) (0, 3)
  | .dMoveREnd => wfF ⊓ ((existsMoveF true) (0, 0) (0, 1) (0, 2) (0, 3) ⊓ blankF (0, 4))
  | .dMoveL => wfF ⊓ (existsMoveF false) (0, 0) (0, 1) (0, 2) (0, 3)
  | .dMoveLEnd => wfF ⊓ ((existsMoveF false) (0, 0) (0, 1) (0, 2) (0, 3) ⊓ blankF (0, 4))
  | _ => ⊥


-- @@ L406-411 expanded
/-- The ambient lexicographic order of the last four coordinates, as a
formula. -/
noncomputable def tupLeF : haltOrd.Formula (Fin 2 × Fin 5) :=
  ordLtF (0, 1) (1, 1) ⊔
    eqF (0, 1) (1, 1) ⊓
      (ordLtF (0, 2) (1, 2) ⊔
        eqF (0, 2) (1, 2) ⊓ (ordLtF (0, 3) (1, 3) ⊔ eqF (0, 3) (1, 3) ⊓ ordF (0, 4) (1, 4)))


-- @@ L413-419 expanded
/-- The order of the drawn instance: the static comparisons are decided in
Lean, the dynamic ones written out. -/
noncomputable def leF (t t' : PTag) : haltOrd.Formula (Fin 2 × Fin 5) :=
  if t.bIdx < t'.bIdx then ⊤
  else
    if t'.bIdx < t.bIdx then ⊥
    else
      mLtF (0, 0) (1, 0) ⊔
        eqF (0, 0) (1, 0) ⊓
          if t.sIdx < t'.sIdx then Top.top else if t'.sIdx < t.sIdx then Bot.bot else tupLeF


-- @@ L421-429 verbatim
/-- **The interpretation of the PCP vocabulary in an ordered machine
instance.** -/
noncomputable def haltPcpInterp : FOInterpretation haltOrd Language.pcp PTag 5 where
  relFormula {n} R ts :=
    match n, R with
    | _, .le => leF (ts 0) (ts 1)
    | _, .dom => domF (ts 0)
    | _, .uAt => uAtF (ts 0) (ts 1) (ts 2)
    | _, .vAt => vAtF (ts 0) (ts 1) (ts 2)


-- @@ L431-431 verbatim
/-! ### Realization of the letter formulas -/


-- @@ L433-433 verbatim
section LetterRealize


-- @@ L435-435 verbatim
variable {A : Type} [Language.turing.Structure A] [LinearOrder A] [Finite A] [Nonempty A]

-- @@ L436-436 verbatim
variable {v : Fin 3 × Fin 5 → A} {wd wp wc : Fin 5 → A}


-- @@ L438-448 verbatim
theorem realize_minAllF {k : Fin 3} {w : Fin 5 → A} (hv : ∀ j, v (k, j) = w j) :
    (minAllF k).Realize v ↔ w = fun _ => pbot := by
  rw [minAllF]
  simp only [Formula.realize_inf, realize_minF, hv]
  constructor
  · rintro ⟨h0, h1, h2, h3, h4⟩
    funext j
    fin_cases j <;> rw [eq_pbot_iff] <;> assumption
  · intro h
    rw [h]
    exact ⟨pbot_le, pbot_le, pbot_le, pbot_le, pbot_le⟩


-- @@ L450-455 verbatim
theorem realize_minTailF {k : Fin 3} {w : Fin 5 → A} (hv : ∀ j, v (k, j) = w j) :
    (minTailF k).Realize v ↔ (w 1 = pbot ∧ w 2 = pbot ∧ w 3 = pbot ∧ w 4 = pbot) := by
  rw [minTailF]
  simp only [Formula.realize_inf, realize_minF, hv]
  refine and_congr eq_pbot_iff.symm (and_congr eq_pbot_iff.symm
    (and_congr eq_pbot_iff.symm eq_pbot_iff.symm))


-- @@ L457-462 verbatim
omit [Language.turing.Structure A] in
/-- A pair with the right tag is a constant element exactly when its tuple is
padding. -/
theorem eq_cstE_iff {t t' : PTag} {w : Fin 5 → A} :
    ((t, w) : PV A) = cstE t' ↔ t = t' ∧ w = fun _ => pbot := by
  rw [cstE, Prod.mk.injEq]


-- @@ L464-476 verbatim
omit [Language.turing.Structure A] in
/-- A pair with the right tag carries an element exactly when its head
coordinate is it and its tail is padding. -/
theorem eq_idxE_iff {t t' : PTag} {w : Fin 5 → A} {a : A} :
    ((t, w) : PV A) = idxE t' a ↔
      t = t' ∧ w 0 = a ∧ w 1 = pbot ∧ w 2 = pbot ∧ w 3 = pbot ∧ w 4 = pbot := by
  rw [idxE, Prod.mk.injEq]
  refine and_congr Iff.rfl ⟨fun h => ?_, fun h => ?_⟩
  · rw [h]
    exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  · obtain ⟨h0, h1, h2, h3, h4⟩ := h
    funext j
    fin_cases j <;> simpa
  


-- @@ L479-488 verbatim
theorem realize_cstLF {s tc : PTag} (hv2 : ∀ j, v (2, j) = wc j) :
    (cstLF s tc).Realize v ↔ ((tc, wc) : PV A) = cstE s := by
  rw [cstLF]
  by_cases htc : tc = s
  · rw [ite_eq_left htc, eq_cstE_iff]
    exact (realize_minAllF hv2).trans ⟨fun h => ⟨htc, h⟩, fun h => h.2⟩
  · rw [ite_eq_right htc]
    simp only [Formula.realize_bot, false_iff]
    rw [eq_cstE_iff]
    exact fun h => htc h.1


-- @@ L490-505 verbatim
theorem realize_idxLF {s : PTag} {j : Fin 5} {tc : PTag}
    (hv0 : ∀ i, v (0, i) = wd i) (hv2 : ∀ i, v (2, i) = wc i) :
    (idxLF s j tc).Realize v ↔ ((tc, wc) : PV A) = idxE s (wd j) := by
  rw [idxLF]
  by_cases htc : tc = s
  · rw [ite_eq_left htc, eq_idxE_iff]
    rw [Formula.realize_inf, realize_eqF, hv0, hv2, realize_minTailF hv2]
    constructor
    · rintro ⟨h0, h⟩
      exact ⟨htc, h0, h⟩
    · rintro ⟨-, h0, h⟩
      exact ⟨h0, h⟩
  · rw [ite_eq_right htc]
    simp only [Formula.realize_bot, false_iff]
    rw [eq_idxE_iff]
    exact fun h => htc h.1


-- @@ L507-512 verbatim
theorem realize_specF {sp : LSpec} {tc : PTag}
    (hv0 : ∀ i, v (0, i) = wd i) (hv2 : ∀ i, v (2, i) = wc i) :
    (specF sp tc).Realize v ↔ ((tc, wc) : PV A) = sp.eval wd := by
  cases sp with
  | cst s => exact realize_cstLF hv2
  | idx s j => exact realize_idxLF hv0 hv2


-- @@ L514-523 verbatim
theorem realize_posIsF {i : ℕ} {tp : PTag} (hv1 : ∀ j, v (1, j) = wp j) :
    (posIsF i tp).Realize v ↔ ((tp, wp) : PV A) = posE i := by
  rw [posIsF, posE_eq]
  by_cases htp : tp = posTagN i
  · rw [ite_eq_left htp, eq_cstE_iff]
    exact (realize_minAllF hv1).trans ⟨fun h => ⟨htp, h⟩, fun h => h.2⟩
  · rw [ite_eq_right htp]
    simp only [Formula.realize_bot, false_iff]
    rw [eq_cstE_iff]
    exact fun h => htp h.1


-- @@ L525-537 verbatim
theorem realize_specListF {specs : List LSpec} {i : ℕ} {tp tc : PTag}
    (hv0 : ∀ j, v (0, j) = wd j) (hv1 : ∀ j, v (1, j) = wp j)
    (hv2 : ∀ j, v (2, j) = wc j) :
    (specListF specs i tp tc).Realize v ↔
      (((tp, wp) : PV A), ((tc, wc) : PV A)) ∈
        ((List.range' i specs.length).map posE).zip (specs.map (LSpec.eval wd)) := by
  induction specs generalizing i with
  | nil => simp [specListF]
  | cons sp rest ih =>
    rw [specListF, Formula.realize_sup, Formula.realize_inf]
    rw [List.length_cons, List.range', List.map_cons, List.map_cons, List.zip_cons_cons]
    rw [List.mem_cons, Prod.mk.injEq]
    exact or_congr (and_congr (realize_posIsF hv1) (realize_specF hv0 hv2)) ih


-- @@ L539-546 verbatim
omit [Language.turing.Structure A] in
/-- The top table relation, in terms of `List.range'`. -/
theorem pUAt_iff_range' {d p c : PV A} :
    PUAt d p c ↔ (p, c) ∈
      ((List.range' 0 (uSpec d.1).length).map posE).zip
        ((uSpec d.1).map (LSpec.eval d.2)) := by
  rw [PUAt, posPrefix, List.range_eq_range']
  exact Iff.rfl


-- @@ L548-553 verbatim
theorem realize_uAtF {td tp tc : PTag}
    (hv0 : ∀ j, v (0, j) = wd j) (hv1 : ∀ j, v (1, j) = wp j)
    (hv2 : ∀ j, v (2, j) = wc j) :
    (uAtF td tp tc).Realize v ↔ PUAt ((td, wd) : PV A) (tp, wp) (tc, wc) := by
  rw [uAtF, pUAt_iff_range']
  exact realize_specListF hv0 hv1 hv2


-- @@ L555-561 verbatim
/-- The bottom table relation, in terms of `List.range'`. -/
theorem pVAt_iff_range' {d p c : PV A} (hne : d.1 ≠ .dStart) :
    PVAt d p c ↔ (p, c) ∈
      ((List.range' 0 (vSpec d.1).length).map posE).zip
        ((vSpec d.1).map (LSpec.eval d.2)) := by
  rw [pVAt_of_ne hne, posPrefix, List.range_eq_range']
  exact Iff.rfl


-- @@ L563-642 verbatim
theorem realize_startBotF {tp tc : PTag}
    (hv1 : ∀ j, v (1, j) = wp j) (hv2 : ∀ j, v (2, j) = wc j) :
    (startBotF tp tc).Realize v ↔ StartBotAt ((tp, wp) : PV A) (tc, wc) := by
  have hcst : ∀ s s' : PTag,
      ((minAllF 1 ⊓ cstLF s' tc : haltOrd.Formula (Fin 3 × Fin 5)).Realize v ↔
        (((s, wp) : PV A) = cstE s ∧ ((tc, wc) : PV A) = cstE s')) := by
    intro s s'
    rw [Formula.realize_inf]
    refine and_congr ?_ (realize_cstLF hv2)
    rw [eq_cstE_iff]
    exact (realize_minAllF hv1).trans ⟨fun h => ⟨rfl, h⟩, fun h => h.2⟩
  cases tp with
  | pos0 => exact hcst _ _
  | pos1 => exact hcst _ _
  | pos2 => exact hcst _ _
  | pos3 => exact hcst _ _
  | pos4 => exact hcst _ _
  | pos5 => exact hcst _ _
  | pos6 => exact hcst _ _
  | hi0 => exact hcst _ _
  | hi1 => exact hcst _ _
  | hi2 => exact hcst _ _
  | hi3 => exact hcst _ _
  | pairSym =>
    rw [startBotF, Formula.realize_inf, Formula.realize_inf]
    change _ ↔ TMPosn (wp 0) ∧ ((PTag.pairSym, wp) : PV A) = idxE .pairSym (wp 0) ∧
      ∃ a, (tmData A).InitTape (wp 0) a ∧ ((tc, wc) : PV A) = idxE .ltSym a
    refine and_congr (by rw [realize_posnF, hv1]) (and_congr ?_ ?_)
    · rw [realize_minTailF hv1, eq_idxE_iff]
      exact ⟨fun h => ⟨rfl, rfl, h⟩, fun h => h.2.2⟩
    · by_cases htc : tc = .ltSym
      · rw [ite_eq_left htc, Formula.realize_inf, realize_initTapeF, hv1, hv2,
          realize_minTailF hv2]
        constructor
        · rintro ⟨ha, h⟩
          exact ⟨wc 0, ha, eq_idxE_iff.mpr ⟨htc, rfl, h⟩⟩
        · rintro ⟨a, ha, hc⟩
          obtain ⟨-, h0, h⟩ := eq_idxE_iff.mp hc
          exact ⟨h0 ▸ ha, h⟩
      · rw [ite_eq_right htc]
        simp only [Formula.realize_bot, false_iff]
        rintro ⟨a, -, hc⟩
        exact htc (eq_idxE_iff.mp hc).1
  | pairStar =>
    rw [startBotF, Formula.realize_inf, Formula.realize_inf]
    change _ ↔ TMPosn (wp 0) ∧ ((PTag.pairStar, wp) : PV A) = idxE .pairStar (wp 0) ∧
      ((tc, wc) : PV A) = cstE .ltStar
    refine and_congr (by rw [realize_posnF, hv1]) (and_congr ?_ (realize_cstLF hv2))
    rw [realize_minTailF hv1, eq_idxE_iff]
    exact ⟨fun h => ⟨rfl, rfl, h⟩, fun h => h.2.2⟩
  | ltStar => exact iff_of_false (fun h => h) (fun h => h)
  | ltSep => exact iff_of_false (fun h => h) (fun h => h)
  | ltTri => exact iff_of_false (fun h => h) (fun h => h)
  | ltDia => exact iff_of_false (fun h => h) (fun h => h)
  | ltLft => exact iff_of_false (fun h => h) (fun h => h)
  | ltRgt => exact iff_of_false (fun h => h) (fun h => h)
  | ltBoot => exact iff_of_false (fun h => h) (fun h => h)
  | ltHalt => exact iff_of_false (fun h => h) (fun h => h)
  | ltSym => exact iff_of_false (fun h => h) (fun h => h)
  | ltState => exact iff_of_false (fun h => h) (fun h => h)
  | pos7 => exact iff_of_false (fun h => h) (fun h => h)
  | dStart => exact iff_of_false (fun h => h) (fun h => h)
  | dClose => exact iff_of_false (fun h => h) (fun h => h)
  | dCopySep => exact iff_of_false (fun h => h) (fun h => h)
  | dCopyLft => exact iff_of_false (fun h => h) (fun h => h)
  | dCopyRgt => exact iff_of_false (fun h => h) (fun h => h)
  | dCopyBoot => exact iff_of_false (fun h => h) (fun h => h)
  | dCopyHalt => exact iff_of_false (fun h => h) (fun h => h)
  | dCopySym => exact iff_of_false (fun h => h) (fun h => h)
  | dCopyState => exact iff_of_false (fun h => h) (fun h => h)
  | dBoot => exact iff_of_false (fun h => h) (fun h => h)
  | dAcc => exact iff_of_false (fun h => h) (fun h => h)
  | dMoveR => exact iff_of_false (fun h => h) (fun h => h)
  | dMoveREnd => exact iff_of_false (fun h => h) (fun h => h)
  | dMoveL => exact iff_of_false (fun h => h) (fun h => h)
  | dMoveLEnd => exact iff_of_false (fun h => h) (fun h => h)
  | dEraseSymL => exact iff_of_false (fun h => h) (fun h => h)
  | dEraseLft => exact iff_of_false (fun h => h) (fun h => h)
  | dEraseSymR => exact iff_of_false (fun h => h) (fun h => h)
  | dEraseRgt => exact iff_of_false (fun h => h) (fun h => h)


-- @@ L644-653 verbatim
theorem realize_vAtF {td tp tc : PTag}
    (hv0 : ∀ j, v (0, j) = wd j) (hv1 : ∀ j, v (1, j) = wp j)
    (hv2 : ∀ j, v (2, j) = wc j) :
    (vAtF td tp tc).Realize v ↔ PVAt ((td, wd) : PV A) (tp, wp) (tc, wc) := by
  cases td with
  | dStart => exact (realize_startBotF hv1 hv2).trans (pVAt_start rfl).symm
  | _ =>
    rw [show vAtF _ tp tc = specListF (vSpec _) 0 tp tc from rfl,
      pVAt_iff_range' (by simp)]
    exact realize_specListF hv0 hv1 hv2


-- @@ L655-655 verbatim
end LetterRealize


-- @@ L657-657 verbatim
/-! ### Realization of the domino and order formulas -/


-- @@ L659-659 verbatim
section DomOrdRealize


-- @@ L661-661 verbatim
variable {A : Type} [Language.turing.Structure A] [LinearOrder A] [Finite A] [Nonempty A]


-- @@ L663-701 verbatim
omit [Finite A] [Nonempty A] in
theorem realize_domF {t : PTag} {v : Fin 1 × Fin 5 → A} {wd : Fin 5 → A}
    (hv : ∀ j, v (0, j) = wd j) :
    (domF t).Realize v ↔ PDom ((t, wd) : PV A) := by
  have hwfonly : ∀ h : (wfF (α := Fin 1 × Fin 5)).Realize v ↔ (tmData A).WellFormed,
      ((wfF (α := Fin 1 × Fin 5)).Realize v ↔ (tmData A).WellFormed ∧ True) :=
    fun h => h.trans ⟨fun hh => ⟨hh, trivial⟩, fun hh => hh.1⟩
  cases t <;> first
    | exact iff_of_false (fun h => h) (fun h => h.2)
    | exact hwfonly realize_wfF
    | skip
  case dBoot =>
    refine Formula.realize_inf.trans (and_congr realize_wfF ?_)
    rw [realize_startF, hv 0]
    exact Iff.rfl
  case dAcc =>
    refine Formula.realize_inf.trans (and_congr realize_wfF ?_)
    rw [realize_accF, hv 0]
    exact Iff.rfl
  case dMoveR =>
    refine Formula.realize_inf.trans (and_congr realize_wfF ?_)
    rw [realize_existsMoveF]
    simp only [hv, ite_true]
    exact Iff.rfl
  case dMoveREnd =>
    refine Formula.realize_inf.trans (and_congr realize_wfF ?_)
    rw [Formula.realize_inf, realize_existsMoveF, realize_blankF, hv 4]
    simp only [hv, ite_true]
    exact Iff.rfl
  case dMoveL =>
    refine Formula.realize_inf.trans (and_congr realize_wfF ?_)
    rw [realize_existsMoveF]
    simp only [hv, Bool.false_eq_true, ite_false]
    exact Iff.rfl
  case dMoveLEnd =>
    refine Formula.realize_inf.trans (and_congr realize_wfF ?_)
    rw [Formula.realize_inf, realize_existsMoveF, realize_blankF, hv 4]
    simp only [hv, Bool.false_eq_true, ite_false]
    exact Iff.rfl


-- @@ L703-709 verbatim
omit [Finite A] [Nonempty A] in
theorem realize_tupLeF {v : Fin 2 × Fin 5 → A} {w w' : Fin 5 → A}
    (hv0 : ∀ j, v (0, j) = w j) (hv1 : ∀ j, v (1, j) = w' j) :
    (tupLeF).Realize v ↔ TupLe w w' := by
  rw [tupLeF, TupLe]
  simp only [Formula.realize_sup, Formula.realize_inf, realize_ordLtF, realize_eqF,
    realize_ordF, hv0, hv1]


-- @@ L711-753 verbatim
omit [Finite A] [Nonempty A] in
theorem realize_leF {t t' : PTag} {v : Fin 2 × Fin 5 → A} {w w' : Fin 5 → A}
    (hv0 : ∀ j, v (0, j) = w j) (hv1 : ∀ j, v (1, j) = w' j) :
    (leF t t').Realize v ↔ PLe ((t, w) : PV A) (t', w') := by
  rw [leF, show PLe ((t, w) : PV A) ((t', w') : PV A) ↔
      (t.bIdx < t'.bIdx ∨ (t.bIdx = t'.bIdx ∧ (MLt (w 0) (w' 0) ∨ (w 0 = w' 0 ∧
        (t.sIdx < t'.sIdx ∨ (t.sIdx = t'.sIdx ∧ TupLe w w')))))) from Iff.rfl]
  by_cases h1 : t.bIdx < t'.bIdx
  · rw [ite_eq_left h1]
    simp only [Formula.realize_top, true_iff]
    exact Or.inl h1
  · rw [ite_eq_right h1]
    by_cases h2 : t'.bIdx < t.bIdx
    · rw [ite_eq_left h2]
      simp only [Formula.realize_bot, false_iff]
      rintro (h | ⟨heq, -⟩) <;> omega
    · rw [ite_eq_right h2]
      have heq : t.bIdx = t'.bIdx := by omega
      rw [Formula.realize_sup, Formula.realize_inf, realize_mLtF, realize_eqF,
        hv0, hv1]
      constructor
      · rintro (hm | ⟨he, hrest⟩)
        · exact Or.inr ⟨heq, Or.inl hm⟩
        · refine Or.inr ⟨heq, Or.inr ⟨he, ?_⟩⟩
          by_cases h3 : t.sIdx < t'.sIdx
          · exact Or.inl h3
          · rw [ite_eq_right h3] at hrest
            by_cases h4 : t'.sIdx < t.sIdx
            · rw [ite_eq_left h4] at hrest
              exact absurd hrest (fun h => h)
            · rw [ite_eq_right h4] at hrest
              exact Or.inr ⟨by omega, (realize_tupLeF hv0 hv1).mp hrest⟩
      · rintro (h | ⟨-, hrest⟩)
        · exact absurd h h1
        rcases hrest with hm | ⟨he, hsub⟩
        · exact Or.inl hm
        · refine Or.inr ⟨he, ?_⟩
          rcases hsub with h3 | ⟨h34, htup⟩
          · rw [ite_eq_left h3]
            exact Formula.realize_top.mpr trivial
          · rw [ite_eq_right (by omega : ¬t.sIdx < t'.sIdx),
              ite_eq_right (by omega : ¬t'.sIdx < t.sIdx)]
            exact (realize_tupLeF hv0 hv1).mpr htup


-- @@ L755-755 verbatim
end DomOrdRealize


-- @@ L757-757 verbatim
/-! ### The reads -/


-- @@ L759-759 verbatim
section Reads


-- @@ L761-761 verbatim
variable (A : Type) [Language.turing.Structure A] [LinearOrder A] [Finite A] [Nonempty A]


-- @@ L763-779 verbatim
/-- **The interpreted structure reads as the drawn instance**: each relation
of `Language.pcp`, realized through the defining formulas, is the semantic
predicate of the drawing. -/
theorem reads_haltPcp :
    Reads (B := haltPcpInterp.Map A) (Equiv.refl (PV A)) where
  ord x y := by
    rw [Pcp.Ord, FOInterpretation.relMap_map]
    exact realize_leF (fun j => rfl) (fun j => rfl)
  dom x := by
    rw [Pcp.DomG, FOInterpretation.relMap_map]
    exact realize_domF (fun j => rfl)
  uAt d p c := by
    rw [Pcp.UAt, FOInterpretation.relMap_map]
    exact realize_uAtF (fun j => rfl) (fun j => rfl) (fun j => rfl)
  vAt d p c := by
    rw [Pcp.VAt, FOInterpretation.relMap_map]
    exact realize_vAtF (fun j => rfl) (fun j => rfl) (fun j => rfl)


-- @@ L781-784 verbatim
/-- **The image is a yes-instance exactly when the machine halts.** -/
theorem pcp_map_iff :
    PCP (haltPcpInterp.Map A) ↔ (tmData A).WellFormed ∧ (tmData A).AcceptsU :=
  pcpOn_iff_of_reads (reads_haltPcp A)


-- @@ L786-786 verbatim
end Reads


-- @@ L788-788 verbatim
end HaltPcp


-- @@ L790-790 verbatim
end DescriptiveComplexity
