/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Syntax
import DescriptiveComplexity.Problems.Partition.Defs
import DescriptiveComplexity.Problems.Knapsack.Chain
import DescriptiveComplexity.Numbers.Wide
import DescriptiveComplexity.SecondOrder


-- @@ L12-35 verbatim
/-!
# Partition is in NP

The certificate guesses the split and *two* ripple-carry walks, one along the
chosen items and one along the items left out, and asks that they end on the
same number. Two things differ from Knapsack
(`DescriptiveComplexity.Problems.Knapsack.Membership`):

* the walks run on the **wide positions** of `DescriptiveComplexity.Numbers.Wide` –
  pairs `(x, p)` with `p` a position of the instance – because each half is
  `total / 2`, which the instance's own positions need not be able to write.
  A wide position is therefore two variables, guarded by `posn p` alone, and
  the step from one to the next is either inside a block or from the top of
  one block to the bottom of the next (`DescriptiveComplexity.succPos_wide`);
* there is no target to reach and no number to guess: the two walks are simply
  required to agree at the last item, and with no items at all both sums are
  empty, so Knapsack's degenerate clause has no counterpart here.

The two walks are the same clauses read twice, once for the side `b = true`
(the chosen items) and once for `b = false` (the others), so the whole clause
family is written as a function of `b`, and so is the semantic argument, which
is `DescriptiveComplexity.chain_sound` and `DescriptiveComplexity.exists_chain`
(`DescriptiveComplexity.Problems.Knapsack.Chain`) applied twice.
-/


-- @@ L37-37 verbatim
namespace DescriptiveComplexity


-- @@ L39-39 verbatim
open FirstOrder


-- @@ L41-41 verbatim
open Language Structure SOBlock


-- @@ L43-43 verbatim
section SigmaOne


-- @@ L45-54 verbatim
/-- The relation variables of the certificate: the chosen items, and the
running totals and carries of the two walks. -/
inductive PIdx : Type
  /-- The chosen items. -/
  | sel
  /-- The running total of the walk on the side `b`. -/
  | ps (b : Bool)
  /-- The carries of the walk on the side `b`. -/
  | cy (b : Bool)
  deriving DecidableEq


-- @@ L56-63 verbatim
instance : Fintype PIdx where
  elems := {PIdx.sel, PIdx.ps true, PIdx.ps false, PIdx.cy true, PIdx.cy false}
  complete := by
    intro t
    cases t with
    | sel => decide
    | ps b => cases b <;> decide
    | cy b => cases b <;> decide


-- @@ L65-73 verbatim
/-- The single existential block of the `Σ₁` definition of Partition: the
chosen items (unary), and, for each side, the running totals and the carries
(ternary: an item and a wide position, itself a pair). -/
def partitionGuessBlock : SOBlock where
  ι := PIdx
  arity := fun i => match i with
    | .sel => 1
    | .ps _ => 3
    | .cy _ => 3


-- @@ L75-76 verbatim
/-- The symbol of the chosen-items relation variable. -/
def ptSelRel : partitionGuessBlock.lang.Relations 1 := ⟨.sel, rfl⟩


-- @@ L78-79 verbatim
/-- The symbol of the running total of the side `b`. -/
def ptPSRel (b : Bool) : partitionGuessBlock.lang.Relations 3 := ⟨.ps b, rfl⟩


-- @@ L81-82 verbatim
/-- The symbol of the carries of the side `b`. -/
def ptCyRel (b : Bool) : partitionGuessBlock.lang.Relations 3 := ⟨.cy b, rfl⟩


-- @@ L84-85 verbatim
/-- The vocabulary of the kernel. -/
abbrev ptSOLang : Language := Language.binWeights.sum partitionGuessBlock.lang


-- @@ L87-88 verbatim
/-- The item symbol in the kernel's vocabulary. -/
abbrev ptItemSym : ptSOLang.Relations 1 := Sum.inl bwItem


-- @@ L90-91 verbatim
/-- The position symbol in the kernel's vocabulary. -/
abbrev ptPosnSym : ptSOLang.Relations 1 := Sum.inl bwPosn


-- @@ L93-94 verbatim
/-- The bit symbol in the kernel's vocabulary. -/
abbrev ptBitSym : ptSOLang.Relations 2 := Sum.inl bwBit


-- @@ L96-97 verbatim
/-- The order symbol in the kernel's vocabulary. -/
abbrev ptLeSym : ptSOLang.Relations 2 := Sum.inl bwLe


-- @@ L99-100 verbatim
/-- The chosen-items symbol in the kernel's vocabulary. -/
abbrev ptSelSym : ptSOLang.Relations 1 := Sum.inr ptSelRel


-- @@ L102-103 verbatim
/-- The running-total symbol of the side `b` in the kernel's vocabulary. -/
abbrev ptPSSym (b : Bool) : ptSOLang.Relations 3 := Sum.inr (ptPSRel b)


-- @@ L105-106 verbatim
/-- The carry symbol of the side `b` in the kernel's vocabulary. -/
abbrev ptCySym (b : Bool) : ptSOLang.Relations 3 := Sum.inr (ptCyRel b)


-- @@ L108-108 verbatim
/-! ### Formula builders -/


-- @@ L110-110 verbatim
section Builders


-- @@ L112-112 verbatim
variable {α : Type}


-- @@ L114-115 verbatim
/-- `x` is an item, as a formula. -/
def ptItemF (x : α) : ptSOLang.Formula α := Relations.formula₁ ptItemSym (Term.var x)


-- @@ L117-118 verbatim
/-- `x` is a bit position, as a formula. -/
def ptPosnF (x : α) : ptSOLang.Formula α := Relations.formula₁ ptPosnSym (Term.var x)


-- @@ L120-122 verbatim
/-- The weight of `i` has bit 1 at `p`, as a formula. -/
def ptBitF (i p : α) : ptSOLang.Formula α :=
  Relations.formula₂ ptBitSym (Term.var i) (Term.var p)


-- @@ L124-126 verbatim
/-- `x ≤ y`, as a formula. -/
def ptLeF (x y : α) : ptSOLang.Formula α :=
  Relations.formula₂ ptLeSym (Term.var x) (Term.var y)


-- @@ L128-129 verbatim
/-- `x = y`, as a formula. -/
def ptEqF (x y : α) : ptSOLang.Formula α := Term.equal (Term.var x) (Term.var y)


-- @@ L131-132 verbatim
/-- `x` is chosen, as a formula. -/
def ptSelF (x : α) : ptSOLang.Formula α := Relations.formula₁ ptSelSym (Term.var x)


-- @@ L134-136 verbatim
/-- Bit `(x, p)` of the running total of the side `b` at `i`, as a formula. -/
def ptPSF (b : Bool) (i x p : α) : ptSOLang.Formula α :=
  (ptPSSym b).formula ![Term.var i, Term.var x, Term.var p]


-- @@ L138-140 verbatim
/-- The carry at `(x, p)` of the step appending `i`, as a formula. -/
def ptCyF (b : Bool) (i x p : α) : ptSOLang.Formula α :=
  (ptCySym b).formula ![Term.var i, Term.var x, Term.var p]


-- @@ L142-146 verbatim
/-- `i` belongs to the side `b`, as a formula. -/
def ptSideF (b : Bool) (i : α) : ptSOLang.Formula α :=
  match b with
  | true => ptSelF i
  | false => ptItemF i ⊓ ∼(ptSelF i)


-- @@ L148-150 expanded
/-- `x` is a minimum of the order, as a formula. -/
noncomputable def ptBotF (x : α) : ptSOLang.Formula α :=
  FirstOrder.Language.Formula.iAlls (Fin 1) (ptLeF (Sum.inl x) (Sum.inr 0))


-- @@ L152-154 expanded
/-- `x` is a maximum of the order, as a formula. -/
noncomputable def ptTopF (x : α) : ptSOLang.Formula α :=
  FirstOrder.Language.Formula.iAlls (Fin 1) (ptLeF (Sum.inr 0) (Sum.inl x))


-- @@ L156-159 verbatim
/-- The bit that the item `i` contributes at the wide position `(x, p)`: its
weight's bit, in the lowest block, if it is on the side `b`. -/
noncomputable def ptAddF (b : Bool) (i x p : α) : ptSOLang.Formula α :=
  ptSideF b i ⊓ (ptBotF x ⊓ ptBitF i p)


-- @@ L161-162 verbatim
/-- The exclusive or of three formulas, as `x ↔ (y ↔ z)`. -/
def ptXor3F (x y z : ptSOLang.Formula α) : ptSOLang.Formula α := x.iff (y.iff z)


-- @@ L164-166 verbatim
/-- The majority of three formulas. -/
def ptMaj3F (x y z : ptSOLang.Formula α) : ptSOLang.Formula α :=
  (x ⊓ y) ⊔ ((x ⊓ z) ⊔ (y ⊓ z))


-- @@ L168-170 expanded
/-- `i` is the first item, as a formula. -/
noncomputable def ptMinItemF (i : α) : ptSOLang.Formula α :=
  ptItemF i ⊓
    FirstOrder.Language.Formula.iAlls (Fin 1)
      ((ptItemF (Sum.inr 0)).imp (ptLeF (Sum.inl i) (Sum.inr 0)))


-- @@ L172-174 expanded
/-- `i` is the last item, as a formula. -/
noncomputable def ptMaxItemF (i : α) : ptSOLang.Formula α :=
  ptItemF i ⊓
    FirstOrder.Language.Formula.iAlls (Fin 1)
      ((ptItemF (Sum.inr 0)).imp (ptLeF (Sum.inr 0) (Sum.inl i)))


-- @@ L176-179 expanded
/-- `j` is the item right after `i`, as a formula. -/
noncomputable def ptSuccItemF (i j : α) : ptSOLang.Formula α :=
  ptItemF i ⊓
    (ptItemF j ⊓
      (ptLeF i j ⊓
        (FirstOrder.Language.BoundedFormula.not (ptEqF i j) ⊓
          FirstOrder.Language.Formula.iAlls (Fin 1)
            ((ptItemF (Sum.inr 0)).imp
              ((ptLeF (Sum.inl i) (Sum.inr 0)).imp
                ((ptLeF (Sum.inr 0) (Sum.inl j)).imp
                  (ptEqF (Sum.inr 0) (Sum.inl i) ⊔ ptEqF (Sum.inr 0) (Sum.inl j))))))))


-- @@ L181-183 expanded
/-- `p` is the lowest position, as a formula. -/
noncomputable def ptMinPosnF (p : α) : ptSOLang.Formula α :=
  ptPosnF p ⊓
    FirstOrder.Language.Formula.iAlls (Fin 1)
      ((ptPosnF (Sum.inr 0)).imp (ptLeF (Sum.inl p) (Sum.inr 0)))


-- @@ L185-187 expanded
/-- `p` is the highest position, as a formula. -/
noncomputable def ptMaxPosnF (p : α) : ptSOLang.Formula α :=
  ptPosnF p ⊓
    FirstOrder.Language.Formula.iAlls (Fin 1)
      ((ptPosnF (Sum.inr 0)).imp (ptLeF (Sum.inr 0) (Sum.inl p)))


-- @@ L189-192 expanded
/-- `q` is the position right above `p`, as a formula. -/
noncomputable def ptSuccPosnF (p q : α) : ptSOLang.Formula α :=
  ptPosnF p ⊓
    (ptPosnF q ⊓
      (ptLeF p q ⊓
        (FirstOrder.Language.BoundedFormula.not (ptEqF p q) ⊓
          FirstOrder.Language.Formula.iAlls (Fin 1)
            ((ptPosnF (Sum.inr 0)).imp
              ((ptLeF (Sum.inl p) (Sum.inr 0)).imp
                ((ptLeF (Sum.inr 0) (Sum.inl q)).imp
                  (ptEqF (Sum.inr 0) (Sum.inl p) ⊔ ptEqF (Sum.inr 0) (Sum.inl q))))))))


-- @@ L194-197 expanded
/-- `y` is the element right after `x` in the whole universe, as a formula. -/
noncomputable def ptSuccAllF (x y : α) : ptSOLang.Formula α :=
  ptLeF x y ⊓
    (FirstOrder.Language.BoundedFormula.not (ptEqF x y) ⊓
      FirstOrder.Language.Formula.iAlls (Fin 1)
        ((ptLeF (Sum.inl x) (Sum.inr 0)).imp
          ((ptLeF (Sum.inr 0) (Sum.inl y)).imp
            (ptEqF (Sum.inr 0) (Sum.inl x) ⊔ ptEqF (Sum.inr 0) (Sum.inl y)))))


-- @@ L199-200 verbatim
/-- `(x, p)` is the lowest wide position, as a formula. -/
noncomputable def ptMinWideF (x p : α) : ptSOLang.Formula α := ptBotF x ⊓ ptMinPosnF p


-- @@ L202-203 verbatim
/-- `(x, p)` is the highest wide position, as a formula. -/
noncomputable def ptMaxWideF (x p : α) : ptSOLang.Formula α := ptTopF x ⊓ ptMaxPosnF p


-- @@ L205-208 verbatim
/-- `(y, q)` is the wide position right above `(x, p)`, as a formula: a step
inside a block, or from the top of one block to the bottom of the next. -/
noncomputable def ptSuccWideF (x p y q : α) : ptSOLang.Formula α :=
  (ptEqF x y ⊓ ptSuccPosnF p q) ⊔ (ptSuccAllF x y ⊓ (ptMaxPosnF p ⊓ ptMinPosnF q))


-- @@ L210-210 verbatim
end Builders


-- @@ L212-212 verbatim
/-! ### The clauses -/


-- @@ L214-216 expanded
/-- Kernel clause: the order is reflexive. -/
private noncomputable def ptReflClause : ptSOLang.Sentence :=
  FirstOrder.Language.Formula.iAlls (Fin 1) (ptLeF (Sum.inr 0) (Sum.inr 0))


-- @@ L218-220 expanded
/-- Kernel clause: the order is transitive. -/
private noncomputable def ptTransClause : ptSOLang.Sentence :=
  FirstOrder.Language.Formula.iAlls (Fin 3)
    ((ptLeF (Sum.inr 0) (Sum.inr 1) ⊓ ptLeF (Sum.inr 1) (Sum.inr 2)).imp
      (ptLeF (Sum.inr 0) (Sum.inr 2)))


-- @@ L222-224 expanded
/-- Kernel clause: the order is antisymmetric. -/
private noncomputable def ptAntisymmClause : ptSOLang.Sentence :=
  FirstOrder.Language.Formula.iAlls (Fin 2)
    ((ptLeF (Sum.inr 0) (Sum.inr 1) ⊓ ptLeF (Sum.inr 1) (Sum.inr 0)).imp
      (ptEqF (Sum.inr 0) (Sum.inr 1)))


-- @@ L226-228 expanded
/-- Kernel clause: the order is total. -/
private noncomputable def ptTotalClause : ptSOLang.Sentence :=
  FirstOrder.Language.Formula.iAlls (Fin 2)
    (ptLeF (Sum.inr 0) (Sum.inr 1) ⊔ ptLeF (Sum.inr 1) (Sum.inr 0))


-- @@ L230-232 expanded
/-- Kernel clause: only items are chosen. -/
private noncomputable def ptSelClause : ptSOLang.Sentence :=
  FirstOrder.Language.Formula.iAlls (Fin 1) ((ptSelF (Sum.inr 0)).imp (ptItemF (Sum.inr 0)))


-- @@ L234-237 expanded
/-- Kernel clause: at the first item the running total is that item's
contribution. -/
private noncomputable def ptBaseClause (b : Bool) : ptSOLang.Sentence :=
  FirstOrder.Language.Formula.iAlls (Fin 3)
    ((ptMinItemF (Sum.inr 0) ⊓ ptPosnF (Sum.inr 2)).imp
      (((ptPSF b) (Sum.inr 0) (Sum.inr 1) (Sum.inr 2)).iff
        ((ptAddF b) (Sum.inr 0) (Sum.inr 1) (Sum.inr 2))))


-- @@ L239-243 expanded
/-- Kernel clause: each step adds a bit. -/
private noncomputable def ptSumClause (b : Bool) : ptSOLang.Sentence :=
  FirstOrder.Language.Formula.iAlls (Fin 4)
    ((ptSuccItemF (Sum.inr 0) (Sum.inr 1) ⊓ ptPosnF (Sum.inr 3)).imp
      (((ptPSF b) (Sum.inr 1) (Sum.inr 2) (Sum.inr 3)).iff
        (ptXor3F ((ptPSF b) (Sum.inr 0) (Sum.inr 2) (Sum.inr 3))
          ((ptAddF b) (Sum.inr 1) (Sum.inr 2) (Sum.inr 3))
          ((ptCyF b) (Sum.inr 1) (Sum.inr 2) (Sum.inr 3)))))


-- @@ L245-249 expanded
/-- Kernel clause: each step propagates its carry. -/
private noncomputable def ptCarryClause (b : Bool) : ptSOLang.Sentence :=
  FirstOrder.Language.Formula.iAlls (Fin 6)
    ((ptSuccItemF (Sum.inr 0) (Sum.inr 1) ⊓
          ptSuccWideF (Sum.inr 2) (Sum.inr 3) (Sum.inr 4) (Sum.inr 5)).imp
      (((ptCyF b) (Sum.inr 1) (Sum.inr 4) (Sum.inr 5)).iff
        (ptMaj3F ((ptPSF b) (Sum.inr 0) (Sum.inr 2) (Sum.inr 3))
          ((ptAddF b) (Sum.inr 1) (Sum.inr 2) (Sum.inr 3))
          ((ptCyF b) (Sum.inr 1) (Sum.inr 2) (Sum.inr 3)))))


-- @@ L251-253 expanded
/-- Kernel clause: nothing is carried into the lowest wide position. -/
private noncomputable def ptBottomClause (b : Bool) : ptSOLang.Sentence :=
  FirstOrder.Language.Formula.iAlls (Fin 4)
    ((ptSuccItemF (Sum.inr 0) (Sum.inr 1) ⊓ ptMinWideF (Sum.inr 2) (Sum.inr 3)).imp
      (FirstOrder.Language.BoundedFormula.not ((ptCyF b) (Sum.inr 1) (Sum.inr 2) (Sum.inr 3))))


-- @@ L255-258 expanded
/-- Kernel clause: nothing is carried out of the highest wide position. -/
private noncomputable def ptTopClause (b : Bool) : ptSOLang.Sentence :=
  FirstOrder.Language.Formula.iAlls (Fin 4)
    ((ptSuccItemF (Sum.inr 0) (Sum.inr 1) ⊓ ptMaxWideF (Sum.inr 2) (Sum.inr 3)).imp
      (FirstOrder.Language.BoundedFormula.not
        (ptMaj3F ((ptPSF b) (Sum.inr 0) (Sum.inr 2) (Sum.inr 3))
          ((ptAddF b) (Sum.inr 1) (Sum.inr 2) (Sum.inr 3))
          ((ptCyF b) (Sum.inr 1) (Sum.inr 2) (Sum.inr 3)))))


-- @@ L260-263 expanded
/-- Kernel clause: at the last item the two walks agree – the two sides weigh
the same. -/
private noncomputable def ptFinalClause : ptSOLang.Sentence :=
  FirstOrder.Language.Formula.iAlls (Fin 3)
    ((ptMaxItemF (Sum.inr 0) ⊓ ptPosnF (Sum.inr 2)).imp
      (((ptPSF true) (Sum.inr 0) (Sum.inr 1) (Sum.inr 2)).iff
        ((ptPSF false) (Sum.inr 0) (Sum.inr 1) (Sum.inr 2))))


-- @@ L265-268 verbatim
/-- The clauses of one walk. -/
private noncomputable def ptWalkClauses (b : Bool) : ptSOLang.Sentence :=
  ptBaseClause b ⊓ (ptSumClause b ⊓ (ptCarryClause b ⊓
    (ptBottomClause b ⊓ ptTopClause b)))


-- @@ L270-273 verbatim
/-- The first-order kernel of the `Σ₁` definition of Partition. -/
noncomputable def partitionKernel : ptSOLang.Sentence :=
  (ptReflClause ⊓ (ptTransClause ⊓ (ptAntisymmClause ⊓ ptTotalClause))) ⊓
    (ptSelClause ⊓ (ptWalkClauses true ⊓ (ptWalkClauses false ⊓ ptFinalClause)))


-- @@ L275-275 verbatim
/-! ### Realization -/


-- @@ L277-277 verbatim
section Realize


-- @@ L279-279 verbatim
variable {A : Type} [Language.binWeights.Structure A]

-- @@ L280-280 verbatim
variable (ρ : partitionGuessBlock.Assignment A)


-- @@ L282-283 verbatim
/-- The chosen items, read off an assignment of the block. -/
def PSel (i : A) : Prop := ρ .sel ![i]


-- @@ L285-286 verbatim
/-- The running total of the side `b`, read off an assignment of the block. -/
def PPS (b : Bool) (i : A) (u : A × A) : Prop := ρ (.ps b) ![i, u.1, u.2]


-- @@ L288-289 verbatim
/-- The carries of the side `b`, read off an assignment of the block. -/
def PCy (b : Bool) (i : A) (u : A × A) : Prop := ρ (.cy b) ![i, u.1, u.2]


-- @@ L291-295 verbatim
/-- The items of the side `b`: the chosen ones, or the others. -/
def PSide (b : Bool) (i : A) : Prop :=
  match b with
  | true => PSel ρ i
  | false => BWItem i ∧ ¬PSel ρ i


-- @@ L297-302 verbatim
/-- The bit an item contributes at a wide position: its own bit, in the lowest
block. The minimality of the block is written with the `Fin 1`-indexed
quantifier the kernel's `∀` produces; `DescriptiveComplexity.pWt_iff` reads it
back. -/
def PWt (i : A) (u : A × A) : Prop :=
  (∀ y : Fin 1 → A, BWLe u.1 (y 0)) ∧ BWBit i u.2


-- @@ L304-306 verbatim
theorem pWt_iff {i : A} {u : A × A} :
    PWt (A := A) i u ↔ ((∀ y : A, BWLe u.1 y) ∧ BWBit i u.2) :=
  and_congr ⟨fun h y => h fun _ => y, fun h y => h (y 0)⟩ Iff.rfl


-- @@ L308-438 verbatim
private theorem realize_partitionKernel :
    (@Sentence.Realize ptSOLang A
        (@sumStructure _ _ A _ (partitionGuessBlock.structure ρ)) partitionKernel) ↔
      IsLinOrd (BWLe (A := A)) ∧
        (∀ i : A, PSel ρ i → BWItem i) ∧
        (∀ b : Bool,
          (∀ i x p : A, MinPos BWLe BWItem i → BWPosn p →
            (PPS ρ b i (x, p) ↔ ChainAdd (PSide ρ b) PWt i (x, p))) ∧
          (∀ i j x p : A, SuccPos BWLe BWItem i j → BWPosn p →
            (PPS ρ b j (x, p) ↔ (PPS ρ b i (x, p) ↔
              (ChainAdd (PSide ρ b) PWt j (x, p) ↔ PCy ρ b j (x, p))))) ∧
          (∀ i j x p y q : A, SuccPos BWLe BWItem i j →
            ((x = y ∧ SuccPos BWLe BWPosn p q) ∨
              (SuccPos BWLe (fun _ => True) x y ∧ MaxPos BWLe BWPosn p ∧
                MinPos BWLe BWPosn q)) →
            (PCy ρ b j (y, q) ↔ maj (PPS ρ b i (x, p))
              (ChainAdd (PSide ρ b) PWt j (x, p)) (PCy ρ b j (x, p)))) ∧
          (∀ i j x p : A, SuccPos BWLe BWItem i j →
            ((∀ y : A, BWLe x y) ∧ MinPos BWLe BWPosn p) → ¬PCy ρ b j (x, p)) ∧
          (∀ i j x p : A, SuccPos BWLe BWItem i j →
            ((∀ y : A, BWLe y x) ∧ MaxPos BWLe BWPosn p) →
            ¬maj (PPS ρ b i (x, p)) (ChainAdd (PSide ρ b) PWt j (x, p))
              (PCy ρ b j (x, p)))) ∧
        (∀ i x p : A, MaxPos BWLe BWItem i → BWPosn p →
          (PPS ρ true i (x, p) ↔ PPS ρ false i (x, p))) := by
  let := partitionGuessBlock.structure ρ
  have hsubS : ∀ w : Fin 1 → A,
      RelMap (L := ptSOLang) (M := A) ptSelSym w ↔ ρ .sel w := fun _ => Iff.rfl
  have hsubP : ∀ (b : Bool) (w : Fin 3 → A),
      RelMap (L := ptSOLang) (M := A) (ptPSSym b) w ↔ ρ (.ps b) w := fun _ _ => Iff.rfl
  have hsubC : ∀ (b : Bool) (w : Fin 3 → A),
      RelMap (L := ptSOLang) (M := A) (ptCySym b) w ↔ ρ (.cy b) w := fun _ _ => Iff.rfl
  rw [partitionKernel]
  simp only [ptReflClause, ptTransClause, ptAntisymmClause, ptTotalClause, ptSelClause,
    ptWalkClauses, ptBaseClause, ptSumClause, ptCarryClause, ptBottomClause, ptTopClause,
    ptFinalClause, ptItemF, ptPosnF, ptBitF, ptLeF, ptEqF, ptSelF, ptPSF, ptCyF, ptAddF,
    ptSideF, ptBotF, ptTopF, ptXor3F, ptMaj3F, ptMinItemF, ptMaxItemF, ptSuccItemF,
    ptMinPosnF, ptMaxPosnF, ptSuccPosnF, ptSuccAllF, ptMinWideF, ptMaxWideF, ptSuccWideF,
    Sentence.Realize, Formula.realize_inf, Formula.realize_sup, Formula.realize_imp,
    Formula.realize_iff, Formula.realize_not, Formula.realize_iAlls, Formula.realize_rel₁,
    Formula.realize_rel₂, realize_rel₃, Formula.realize_equal, Term.realize_var,
    Sum.elim_inr, Sum.elim_inl, Language.relMap_sumInl, hsubS, hsubP, hsubC]
  constructor
  · rintro ⟨⟨hrefl, htrans, hanti, htot⟩, hsel, ⟨hb1, hs1, hc1, hbo1, ht1⟩,
      ⟨hb0, hs0, hc0, hbo0, ht0⟩, hfin⟩
    have hminU : ∀ (P : A → Prop) (x : A), MinPos BWLe P x →
        P x ∧ ∀ y : Fin 1 → A, P (y 0) → BWLe x (y 0) :=
      fun P x h => ⟨h.1, fun y hy => h.2 (y 0) hy⟩
    have hmaxU : ∀ (P : A → Prop) (x : A), MaxPos BWLe P x →
        P x ∧ ∀ y : Fin 1 → A, P (y 0) → BWLe (y 0) x :=
      fun P x h => ⟨h.1, fun y hy => h.2 (y 0) hy⟩
    have hsuccU : ∀ (P : A → Prop) (x y : A), SuccPos BWLe P x y →
        P x ∧ (P y ∧ (BWLe x y ∧ (¬x = y ∧ ∀ r : Fin 1 → A,
          P (r 0) → BWLe x (r 0) → BWLe (r 0) y → r 0 = x ∨ r 0 = y))) :=
      fun P x y h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1,
        fun r hr h1 h2 => h.2.2.2.2 (r 0) hr h1 h2⟩
    have hsallU : ∀ x y : A, SuccPos BWLe (fun _ => True) x y →
        BWLe x y ∧ (¬x = y ∧ ∀ r : Fin 1 → A,
          BWLe x (r 0) → BWLe (r 0) y → r 0 = x ∨ r 0 = y) :=
      fun x y h => ⟨h.2.2.1, h.2.2.2.1, fun r h1 h2 => h.2.2.2.2 (r 0) trivial h1 h2⟩
    refine ⟨⟨fun a => hrefl (fun _ => a), fun a b c hab hbc => htrans ![a, b, c] ⟨hab, hbc⟩,
      fun a b hab hba => hanti ![a, b] ⟨hab, hba⟩, fun a b => htot ![a, b]⟩,
      fun i hi => hsel (fun _ => i) hi, fun b => ?_,
      fun i x p hi hp => hfin ![i, x, p] ⟨hmaxU _ _ hi, hp⟩⟩
    cases b
    · exact ⟨fun i x p hi hp => hb0 ![i, x, p] ⟨hminU _ _ hi, hp⟩,
        fun i j x p hij hp => hs0 ![i, j, x, p] ⟨hsuccU _ _ _ hij, hp⟩,
        fun i j x p y q hij hpq => hc0 ![i, j, x, p, y, q] ⟨hsuccU _ _ _ hij, by
          rcases hpq with ⟨rfl, h⟩ | ⟨h1, h2, h3⟩
          · exact Or.inl ⟨rfl, hsuccU _ _ _ h⟩
          · exact Or.inr ⟨hsallU _ _ h1, hmaxU _ _ h2, hminU _ _ h3⟩⟩,
        fun i j x p hij hp => hbo0 ![i, j, x, p]
          ⟨hsuccU _ _ _ hij, fun y => hp.1 (y 0), hminU _ _ hp.2⟩,
        fun i j x p hij hp => ht0 ![i, j, x, p]
          ⟨hsuccU _ _ _ hij, fun y => hp.1 (y 0), hmaxU _ _ hp.2⟩⟩
    · exact ⟨fun i x p hi hp => hb1 ![i, x, p] ⟨hminU _ _ hi, hp⟩,
        fun i j x p hij hp => hs1 ![i, j, x, p] ⟨hsuccU _ _ _ hij, hp⟩,
        fun i j x p y q hij hpq => hc1 ![i, j, x, p, y, q] ⟨hsuccU _ _ _ hij, by
          rcases hpq with ⟨rfl, h⟩ | ⟨h1, h2, h3⟩
          · exact Or.inl ⟨rfl, hsuccU _ _ _ h⟩
          · exact Or.inr ⟨hsallU _ _ h1, hmaxU _ _ h2, hminU _ _ h3⟩⟩,
        fun i j x p hij hp => hbo1 ![i, j, x, p]
          ⟨hsuccU _ _ _ hij, fun y => hp.1 (y 0), hminU _ _ hp.2⟩,
        fun i j x p hij hp => ht1 ![i, j, x, p]
          ⟨hsuccU _ _ _ hij, fun y => hp.1 (y 0), hmaxU _ _ hp.2⟩⟩
  · rintro ⟨⟨hrefl, htrans, hanti, htot⟩, hsel, hwalk, hfin⟩
    have hminM : ∀ (P : A → Prop) (x : A),
        (P x ∧ ∀ y : Fin 1 → A, P (y 0) → BWLe x (y 0)) → MinPos BWLe P x :=
      fun P x h => ⟨h.1, fun y hy => h.2 (fun _ => y) hy⟩
    have hmaxM : ∀ (P : A → Prop) (x : A),
        (P x ∧ ∀ y : Fin 1 → A, P (y 0) → BWLe (y 0) x) → MaxPos BWLe P x :=
      fun P x h => ⟨h.1, fun y hy => h.2 (fun _ => y) hy⟩
    have hsuccM : ∀ (P : A → Prop) (x y : A),
        (P x ∧ (P y ∧ (BWLe x y ∧ (¬x = y ∧ ∀ r : Fin 1 → A,
          P (r 0) → BWLe x (r 0) → BWLe (r 0) y → r 0 = x ∨ r 0 = y)))) →
        SuccPos BWLe P x y :=
      fun P x y h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1,
        fun r hr h1 h2 => h.2.2.2.2 (fun _ => r) hr h1 h2⟩
    have hsallM : ∀ x y : A,
        (BWLe x y ∧ (¬x = y ∧ ∀ r : Fin 1 → A,
          BWLe x (r 0) → BWLe (r 0) y → r 0 = x ∨ r 0 = y)) →
        SuccPos BWLe (fun _ => True) x y :=
      fun x y h => ⟨trivial, trivial, h.1, h.2.1,
        fun r _ h1 h2 => h.2.2 (fun _ => r) h1 h2⟩
    have hstep : ∀ b : Bool, _ := hwalk
    exact ⟨⟨fun w => hrefl (w 0), fun w h => htrans (w 0) (w 1) (w 2) h.1 h.2,
        fun w h => hanti (w 0) (w 1) h.1 h.2, fun w => htot (w 0) (w 1)⟩,
      fun w h => hsel (w 0) h,
      ⟨fun w h => (hstep true).1 (w 0) (w 1) (w 2) (hminM _ _ h.1) h.2,
        fun w h => (hstep true).2.1 (w 0) (w 1) (w 2) (w 3) (hsuccM _ _ _ h.1) h.2,
        fun w h => (hstep true).2.2.1 (w 0) (w 1) (w 2) (w 3) (w 4) (w 5)
          (hsuccM _ _ _ h.1) (by
            rcases h.2 with ⟨he, h'⟩ | ⟨h1, h2, h3⟩
            · exact Or.inl ⟨he, hsuccM _ _ _ h'⟩
            · exact Or.inr ⟨hsallM _ _ h1, hmaxM _ _ h2, hminM _ _ h3⟩),
        fun w h => (hstep true).2.2.2.1 (w 0) (w 1) (w 2) (w 3) (hsuccM _ _ _ h.1)
          ⟨fun y => h.2.1 (fun _ => y), hminM _ _ h.2.2⟩,
        fun w h => (hstep true).2.2.2.2 (w 0) (w 1) (w 2) (w 3) (hsuccM _ _ _ h.1)
          ⟨fun y => h.2.1 (fun _ => y), hmaxM _ _ h.2.2⟩⟩,
      ⟨fun w h => (hstep false).1 (w 0) (w 1) (w 2) (hminM _ _ h.1) h.2,
        fun w h => (hstep false).2.1 (w 0) (w 1) (w 2) (w 3) (hsuccM _ _ _ h.1) h.2,
        fun w h => (hstep false).2.2.1 (w 0) (w 1) (w 2) (w 3) (w 4) (w 5)
          (hsuccM _ _ _ h.1) (by
            rcases h.2 with ⟨he, h'⟩ | ⟨h1, h2, h3⟩
            · exact Or.inl ⟨he, hsuccM _ _ _ h'⟩
            · exact Or.inr ⟨hsallM _ _ h1, hmaxM _ _ h2, hminM _ _ h3⟩),
        fun w h => (hstep false).2.2.2.1 (w 0) (w 1) (w 2) (w 3) (hsuccM _ _ _ h.1)
          ⟨fun y => h.2.1 (fun _ => y), hminM _ _ h.2.2⟩,
        fun w h => (hstep false).2.2.2.2 (w 0) (w 1) (w 2) (w 3) (hsuccM _ _ _ h.1)
          ⟨fun y => h.2.1 (fun _ => y), hmaxM _ _ h.2.2⟩⟩,
      fun w h => hfin (w 0) (w 1) (w 2) (hmaxM _ _ h.1) h.2⟩


-- @@ L440-440 verbatim
end Realize


-- @@ L442-442 verbatim
/-! ### Membership -/


-- @@ L444-444 verbatim
section Membership


-- @@ L446-446 verbatim
variable {A : Type} [Finite A] [Language.binWeights.Structure A]


-- @@ L448-458 verbatim
omit [Finite A] in
/-- Read on the wide positions, an item still weighs its weight. -/
private theorem binNum_pWt (hlin : IsLinOrd (BWLe (A := A))) {a₀ : A}
    (h₀ : ∀ y : A, BWLe a₀ y) (i : A) :
    binNum (wideLe BWLe) (WidePosn BWPosn) (PWt i) = BWWeight i := by
  have hcongr : binNum (wideLe BWLe) (WidePosn BWPosn) (PWt i) =
      binNum (wideLe BWLe) (WidePosn BWPosn)
        (fun u => (∀ y : A, BWLe u.1 y) ∧ BWBit i u.2) :=
    binNum_congr fun _ => pWt_iff
  rw [hcongr]
  exact binNum_wide_bot hlin h₀ (BWBit i)


-- @@ L460-466 verbatim
omit [Finite A] in
/-- The same, for a sum over any set of items. -/
private theorem finsum_pWt (hlin : IsLinOrd (BWLe (A := A))) {a₀ : A}
    (h₀ : ∀ y : A, BWLe a₀ y) (T : A → Prop) :
    (∑ᶠ j ∈ {j : A | T j}, binNum (wideLe BWLe) (WidePosn BWPosn) (PWt j)) =
      ∑ᶠ j ∈ {j : A | T j}, BWWeight j :=
  finsum_mem_congr rfl fun j _ => binNum_pWt hlin h₀ j


-- @@ L468-565 verbatim
/-- **Partition is `Σ₁`-definable**: guess the split and the two ripple-carry
walks, one along the chosen items and one along the others, and check
first-order that they end on the same number. Since NP is defined as
`Σ₁`-definability, this is the membership half of the NP-completeness of
Partition. -/
theorem partition_sigmaSODefinable : SigmaSODefinable 1 Partition := by
  refine ⟨[partitionGuessBlock], rfl, partitionKernel, ?_⟩
  intro A _ _ _
  constructor
  · -- a split yields a certificate: two walks, one per side
    rintro ⟨hfin, hlin, S, hSitem, hsumeq⟩
    obtain ⟨a₀, -, h₀'⟩ := exists_minPos (Le := BWLe (A := A)) (Posn := fun _ => True) hlin
      ⟨Classical.arbitrary A, trivial⟩
    have h₀ : ∀ y : A, BWLe a₀ y := fun y => h₀' y trivial
    have hwlin : IsLinOrd (wideLe (BWLe (A := A))) := isLinOrd_wideLe hlin
    have hbound : ∀ T : A → Prop,
        (∑ᶠ j ∈ {j : A | T j}, binNum (wideLe BWLe) (WidePosn BWPosn) (PWt j)) <
          2 ^ ({u : A × A | WidePosn BWPosn u} : Set (A × A)).ncard := by
      intro T
      rw [finsum_pWt hlin h₀ T]
      exact finsum_binNum_lt_wide hlin BWBit {j : A | T j}
    obtain ⟨PS1, Cy1, hchain1⟩ :=
      exists_chain (wt := PWt) (S := S) hlin hwlin hSitem (hbound S)
    obtain ⟨PS0, Cy0, hchain0⟩ :=
      exists_chain (wt := PWt) (S := fun i => BWItem i ∧ ¬S i) hlin hwlin
        (fun i hi => hi.1) (hbound _)
    refine ⟨fun idx => match idx with
      | .sel => fun w : Fin 1 → A => S (w 0)
      | .ps b => fun w : Fin 3 → A =>
          (match b with | true => PS1 | false => PS0) (w 0) (w 1, w 2)
      | .cy b => fun w : Fin 3 → A =>
          (match b with | true => Cy1 | false => Cy0) (w 0) (w 1, w 2), ?_⟩
    refine (realize_partitionKernel _).mpr ⟨hlin, hSitem, fun b => ?_, ?_⟩
    · cases b
      · exact ⟨fun i x p hi hp => hchain0.1 i (x, p) hi hp,
          fun i j x p hij hp => hchain0.2.1 i j (x, p) hij hp,
          fun i j x p y q hij hpq =>
            hchain0.2.2.1 i j (x, p) (y, q) hij ((succPos_wide hlin).mpr hpq),
          fun i j x p hij hp =>
            hchain0.2.2.2.1 i j (x, p) hij ((minPos_wide hlin).mpr hp),
          fun i j x p hij hp =>
            hchain0.2.2.2.2 i j (x, p) hij ((maxPos_wide hlin).mpr hp)⟩
      · exact ⟨fun i x p hi hp => hchain1.1 i (x, p) hi hp,
          fun i j x p hij hp => hchain1.2.1 i j (x, p) hij hp,
          fun i j x p y q hij hpq =>
            hchain1.2.2.1 i j (x, p) (y, q) hij ((succPos_wide hlin).mpr hpq),
          fun i j x p hij hp =>
            hchain1.2.2.2.1 i j (x, p) hij ((minPos_wide hlin).mpr hp),
          fun i j x p hij hp =>
            hchain1.2.2.2.2 i j (x, p) hij ((maxPos_wide hlin).mpr hp)⟩
    · -- at the last item the two walks agree, both weighing one side
      intro i x p hi hp
      refine binNum_inj_on hwlin _ (WidePosn BWPosn) rfl (PS1 i) (PS0 i) ?_ (x, p) hp
      rw [chain_sound hlin hwlin hSitem hchain1 i hi.1,
        chain_sound hlin hwlin (fun i hi => hi.1) hchain0 i hi.1,
        partSum_max hSitem hi, partSum_max (fun i hi => hi.1) hi,
        finsum_pWt hlin h₀, finsum_pWt hlin h₀]
      exact hsumeq
  · -- a certificate yields a split: both walks are sound
    rintro ⟨ρ, hρ⟩
    obtain ⟨hlin, hsel, hwalk, hfin⟩ := (realize_partitionKernel ρ).mp hρ
    obtain ⟨a₀, -, h₀'⟩ := exists_minPos (Le := BWLe (A := A)) (Posn := fun _ => True) hlin
      ⟨Classical.arbitrary A, trivial⟩
    have h₀ : ∀ y : A, BWLe a₀ y := fun y => h₀' y trivial
    have hwlin : IsLinOrd (wideLe (BWLe (A := A))) := isLinOrd_wideLe hlin
    have hchain : ∀ b : Bool,
        IsChain BWLe BWItem (wideLe BWLe) (WidePosn BWPosn) (PSide ρ b) PWt (PPS ρ b)
          (PCy ρ b) :=
      fun b => ⟨fun i u hi hp => (hwalk b).1 i u.1 u.2 hi hp,
        fun i j u hij hp => (hwalk b).2.1 i j u.1 u.2 hij hp,
        fun i j u v hij hpq =>
          (hwalk b).2.2.1 i j u.1 u.2 v.1 v.2 hij ((succPos_wide hlin).mp hpq),
        fun i j u hij hp =>
          (hwalk b).2.2.2.1 i j u.1 u.2 hij ((minPos_wide hlin).mp hp),
        fun i j u hij hp =>
          (hwalk b).2.2.2.2 i j u.1 u.2 hij ((maxPos_wide hlin).mp hp)⟩
    refine ⟨‹Finite A›, hlin, PSel ρ, hsel, ?_⟩
    by_cases hitems : ∃ i : A, BWItem i
    · obtain ⟨imax, himax⟩ := exists_maxPos hlin hitems
      have h1 := chain_sound hlin hwlin hsel (hchain true) imax himax.1
      have h0 := chain_sound hlin hwlin (fun i hi => hi.1) (hchain false) imax himax.1
      rw [partSum_max hsel himax] at h1
      rw [partSum_max (fun i hi => hi.1) himax] at h0
      have heq : binNum (wideLe BWLe) (WidePosn BWPosn) (PPS ρ true imax) =
          binNum (wideLe BWLe) (WidePosn BWPosn) (PPS ρ false imax) :=
        binNum_congr_on fun u hu => hfin imax u.1 u.2 himax hu
      rw [h1, h0, finsum_pWt hlin h₀, finsum_pWt hlin h₀] at heq
      exact heq
    · have hno : ∀ i : A, ¬BWItem i := fun i hi => hitems ⟨i, hi⟩
      have hS : {i : A | PSel ρ i} = (∅ : Set A) := by
        ext i
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        exact fun hi => hno i (hsel i hi)
      have hS' : {i : A | BWItem i ∧ ¬PSel ρ i} = (∅ : Set A) := by
        ext i
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        exact fun hi => hno i hi.1
      rw [hS, hS', finsum_mem_empty]


-- @@ L567-567 verbatim
end Membership


-- @@ L569-569 verbatim
end SigmaOne


-- @@ L571-571 verbatim
end DescriptiveComplexity
