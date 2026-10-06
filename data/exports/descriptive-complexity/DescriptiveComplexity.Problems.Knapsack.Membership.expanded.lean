/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Block
import DescriptiveComplexity.Syntax
import DescriptiveComplexity.Problems.Knapsack.Chain
import DescriptiveComplexity.SecondOrder


-- @@ L11-31 verbatim
/-!
# Knapsack is in NP

The `Σ₁` definition of `DescriptiveComplexity.Knapsack`. Verifying that a set of
binary weights sums to the target is the one place in the catalog where the
certificate has to carry *arithmetic*: the guess is

* `sel`, the chosen items;
* `psum i p`, the bits of the running total over the chosen items up to `i`;
* `carry i p`, the carries of the addition that appends `i` to that total,

and the kernel checks, first-order, that each step is a ripple-carry addition
– every bit the exclusive or of the three inputs, every carry their majority –
with no carry into the lowest position and none out of the highest. That the
chain really computes the sum is `DescriptiveComplexity.binNum_ripple`, and that a
chain exists whenever the sum fits is `DescriptiveComplexity.exists_ripple`
(`DescriptiveComplexity.Numbers.BinRel`).

Walking the items in order is what makes a *single* relation `psum` enough, and
it is why the vocabulary orders the items and not only the bit positions.
-/


-- @@ L33-33 verbatim
namespace DescriptiveComplexity


-- @@ L35-35 verbatim
open FirstOrder


-- @@ L37-37 verbatim
open Language Structure SOBlock


-- @@ L39-39 verbatim
section SigmaOne


-- @@ L41-51 verbatim
/-- The single existential block of the `Σ₁` definition of Knapsack: the
chosen items (unary), the running partial sums and the carries (binary, an
item and a bit position). -/
fo_block knapsackGuessBlock over Language.binWeights bw into ksSOLang with ks where
  /-- The chosen items. -/
  sel : 1
  /-- The running partial sums: `pS i p` is the bit `p` of the total up to
  the item `i`. -/
  pS : 2
  /-- The carries of the step appending an item. -/
  carry : 2


-- @@ L53-53 verbatim
/-! ### Formula builders -/


-- @@ L55-55 verbatim
section Builders


-- @@ L57-57 verbatim
variable {α : Type}


-- @@ L59-60 verbatim
/-- `x` is an item, as a formula. -/
def kItemF (x : α) : ksSOLang.Formula α := Relations.formula₁ ksItemSym (Term.var x)


-- @@ L62-63 verbatim
/-- `x` is a bit position, as a formula. -/
def kPosnF (x : α) : ksSOLang.Formula α := Relations.formula₁ ksPosnSym (Term.var x)


-- @@ L65-67 verbatim
/-- The weight of `i` has bit 1 at `p`, as a formula. -/
def kBitF (i p : α) : ksSOLang.Formula α :=
  Relations.formula₂ ksBitSym (Term.var i) (Term.var p)


-- @@ L69-70 verbatim
/-- The target has bit 1 at `p`, as a formula. -/
def kTgtF (p : α) : ksSOLang.Formula α := Relations.formula₁ ksTgtSym (Term.var p)


-- @@ L72-74 verbatim
/-- `x ≤ y`, as a formula. -/
def kLeF (x y : α) : ksSOLang.Formula α :=
  Relations.formula₂ ksLeSym (Term.var x) (Term.var y)


-- @@ L76-77 verbatim
/-- `x` is chosen, as a formula. -/
def kSelF (x : α) : ksSOLang.Formula α := Relations.formula₁ ksSelSym (Term.var x)


-- @@ L79-81 verbatim
/-- Bit `p` of the running total at `i`, as a formula. -/
def kPSF (i p : α) : ksSOLang.Formula α :=
  Relations.formula₂ ksPSSym (Term.var i) (Term.var p)


-- @@ L83-85 verbatim
/-- The carry at `p` of the step appending `i`, as a formula. -/
def kCarryF (i p : α) : ksSOLang.Formula α :=
  Relations.formula₂ ksCarrySym (Term.var i) (Term.var p)


-- @@ L87-88 verbatim
/-- `x = y`, as a formula. -/
def kEqF (x y : α) : ksSOLang.Formula α := Term.equal (Term.var x) (Term.var y)


-- @@ L90-92 verbatim
/-- The bit that the item `i` contributes at `p`: its weight's bit, if it is
chosen. -/
def kAddF (i p : α) : ksSOLang.Formula α := kSelF i ⊓ kBitF i p


-- @@ L94-95 verbatim
/-- The exclusive or of three formulas, as `x ↔ (y ↔ z)`. -/
def kXor3F (x y z : ksSOLang.Formula α) : ksSOLang.Formula α := x.iff (y.iff z)


-- @@ L97-99 verbatim
/-- The majority of three formulas. -/
def kMaj3F (x y z : ksSOLang.Formula α) : ksSOLang.Formula α :=
  (x ⊓ y) ⊔ ((x ⊓ z) ⊔ (y ⊓ z))


-- @@ L101-103 expanded
/-- `i` is the first item, as a formula. -/
noncomputable def kMinItemF (i : α) : ksSOLang.Formula α :=
  kItemF i ⊓
    FirstOrder.Language.Formula.iAlls (Fin 1)
      ((kItemF (Sum.inr 0)).imp (kLeF (Sum.inl i) (Sum.inr 0)))


-- @@ L105-107 expanded
/-- `i` is the last item, as a formula. -/
noncomputable def kMaxItemF (i : α) : ksSOLang.Formula α :=
  kItemF i ⊓
    FirstOrder.Language.Formula.iAlls (Fin 1)
      ((kItemF (Sum.inr 0)).imp (kLeF (Sum.inr 0) (Sum.inl i)))


-- @@ L109-112 expanded
/-- `j` is the item right after `i`, as a formula. -/
noncomputable def kSuccItemF (i j : α) : ksSOLang.Formula α :=
  kItemF i ⊓
    (kItemF j ⊓
      (kLeF i j ⊓
        (FirstOrder.Language.BoundedFormula.not (kEqF i j) ⊓
          FirstOrder.Language.Formula.iAlls (Fin 1)
            ((kItemF (Sum.inr 0)).imp
              ((kLeF (Sum.inl i) (Sum.inr 0)).imp
                ((kLeF (Sum.inr 0) (Sum.inl j)).imp
                  (kEqF (Sum.inr 0) (Sum.inl i) ⊔ kEqF (Sum.inr 0) (Sum.inl j))))))))


-- @@ L114-116 expanded
/-- `p` is the lowest position, as a formula. -/
noncomputable def kMinPosnF (p : α) : ksSOLang.Formula α :=
  kPosnF p ⊓
    FirstOrder.Language.Formula.iAlls (Fin 1)
      ((kPosnF (Sum.inr 0)).imp (kLeF (Sum.inl p) (Sum.inr 0)))


-- @@ L118-120 expanded
/-- `p` is the highest position, as a formula. -/
noncomputable def kMaxPosnF (p : α) : ksSOLang.Formula α :=
  kPosnF p ⊓
    FirstOrder.Language.Formula.iAlls (Fin 1)
      ((kPosnF (Sum.inr 0)).imp (kLeF (Sum.inr 0) (Sum.inl p)))


-- @@ L122-125 expanded
/-- `q` is the position right above `p`, as a formula. -/
noncomputable def kSuccPosnF (p q : α) : ksSOLang.Formula α :=
  kPosnF p ⊓
    (kPosnF q ⊓
      (kLeF p q ⊓
        (FirstOrder.Language.BoundedFormula.not (kEqF p q) ⊓
          FirstOrder.Language.Formula.iAlls (Fin 1)
            ((kPosnF (Sum.inr 0)).imp
              ((kLeF (Sum.inl p) (Sum.inr 0)).imp
                ((kLeF (Sum.inr 0) (Sum.inl q)).imp
                  (kEqF (Sum.inr 0) (Sum.inl p) ⊔ kEqF (Sum.inr 0) (Sum.inl q))))))))


-- @@ L127-127 verbatim
end Builders


-- @@ L129-129 verbatim
/-! ### The clauses -/


-- @@ L131-133 expanded
/-- Kernel clause: the order is reflexive. -/
private noncomputable def ksReflClause : ksSOLang.Sentence :=
  FirstOrder.Language.Formula.iAlls (Fin 1) (kLeF (Sum.inr 0) (Sum.inr 0))


-- @@ L135-137 expanded
/-- Kernel clause: the order is transitive. -/
private noncomputable def ksTransClause : ksSOLang.Sentence :=
  FirstOrder.Language.Formula.iAlls (Fin 3)
    ((kLeF (Sum.inr 0) (Sum.inr 1) ⊓ kLeF (Sum.inr 1) (Sum.inr 2)).imp
      (kLeF (Sum.inr 0) (Sum.inr 2)))


-- @@ L139-141 expanded
/-- Kernel clause: the order is antisymmetric. -/
private noncomputable def ksAntisymmClause : ksSOLang.Sentence :=
  FirstOrder.Language.Formula.iAlls (Fin 2)
    ((kLeF (Sum.inr 0) (Sum.inr 1) ⊓ kLeF (Sum.inr 1) (Sum.inr 0)).imp
      (kEqF (Sum.inr 0) (Sum.inr 1)))


-- @@ L143-145 expanded
/-- Kernel clause: the order is total. -/
private noncomputable def ksTotalClause : ksSOLang.Sentence :=
  FirstOrder.Language.Formula.iAlls (Fin 2)
    (kLeF (Sum.inr 0) (Sum.inr 1) ⊔ kLeF (Sum.inr 1) (Sum.inr 0))


-- @@ L147-149 expanded
/-- Kernel clause: only items are chosen. -/
private noncomputable def ksSelClause : ksSOLang.Sentence :=
  FirstOrder.Language.Formula.iAlls (Fin 1) ((kSelF (Sum.inr 0)).imp (kItemF (Sum.inr 0)))


-- @@ L151-154 expanded
/-- Kernel clause: at the first item the running total is that item's
contribution. -/
private noncomputable def ksBaseClause : ksSOLang.Sentence :=
  FirstOrder.Language.Formula.iAlls (Fin 2)
    ((kMinItemF (Sum.inr 0) ⊓ kPosnF (Sum.inr 1)).imp
      ((kPSF (Sum.inr 0) (Sum.inr 1)).iff (kAddF (Sum.inr 0) (Sum.inr 1))))


-- @@ L156-159 expanded
/-- Kernel clause: each step adds a bit. -/
private noncomputable def ksSumClause : ksSOLang.Sentence :=
  FirstOrder.Language.Formula.iAlls (Fin 3)
    ((kSuccItemF (Sum.inr 0) (Sum.inr 1) ⊓ kPosnF (Sum.inr 2)).imp
      ((kPSF (Sum.inr 1) (Sum.inr 2)).iff
        (kXor3F (kPSF (Sum.inr 0) (Sum.inr 2)) (kAddF (Sum.inr 1) (Sum.inr 2))
          (kCarryF (Sum.inr 1) (Sum.inr 2)))))


-- @@ L161-164 expanded
/-- Kernel clause: each step propagates its carry. -/
private noncomputable def ksCarryClause : ksSOLang.Sentence :=
  FirstOrder.Language.Formula.iAlls (Fin 4)
    ((kSuccItemF (Sum.inr 0) (Sum.inr 1) ⊓ kSuccPosnF (Sum.inr 2) (Sum.inr 3)).imp
      ((kCarryF (Sum.inr 1) (Sum.inr 3)).iff
        (kMaj3F (kPSF (Sum.inr 0) (Sum.inr 2)) (kAddF (Sum.inr 1) (Sum.inr 2))
          (kCarryF (Sum.inr 1) (Sum.inr 2)))))


-- @@ L166-168 expanded
/-- Kernel clause: nothing is carried into the lowest position. -/
private noncomputable def ksBottomClause : ksSOLang.Sentence :=
  FirstOrder.Language.Formula.iAlls (Fin 3)
    ((kSuccItemF (Sum.inr 0) (Sum.inr 1) ⊓ kMinPosnF (Sum.inr 2)).imp
      (FirstOrder.Language.BoundedFormula.not (kCarryF (Sum.inr 1) (Sum.inr 2))))


-- @@ L170-173 expanded
/-- Kernel clause: nothing is carried out of the highest position. -/
private noncomputable def ksTopClause : ksSOLang.Sentence :=
  FirstOrder.Language.Formula.iAlls (Fin 3)
    ((kSuccItemF (Sum.inr 0) (Sum.inr 1) ⊓ kMaxPosnF (Sum.inr 2)).imp
      (FirstOrder.Language.BoundedFormula.not
        (kMaj3F (kPSF (Sum.inr 0) (Sum.inr 2)) (kAddF (Sum.inr 1) (Sum.inr 2))
          (kCarryF (Sum.inr 1) (Sum.inr 2)))))


-- @@ L175-177 expanded
/-- Kernel clause: at the last item the running total is the target. -/
private noncomputable def ksFinalClause : ksSOLang.Sentence :=
  FirstOrder.Language.Formula.iAlls (Fin 2)
    ((kMaxItemF (Sum.inr 0) ⊓ kPosnF (Sum.inr 1)).imp
      ((kPSF (Sum.inr 0) (Sum.inr 1)).iff (kTgtF (Sum.inr 1))))


-- @@ L179-181 expanded
/-- Kernel clause: with no item at all, the target must be zero. -/
private noncomputable def ksEmptyClause : ksSOLang.Sentence :=
  (FirstOrder.Language.Formula.iAlls (Fin 1)
        (FirstOrder.Language.BoundedFormula.not (kItemF (Sum.inr 0)))).imp
    (FirstOrder.Language.Formula.iAlls (Fin 1)
      ((kPosnF (Sum.inr 0)).imp (FirstOrder.Language.BoundedFormula.not (kTgtF (Sum.inr 0)))))


-- @@ L183-187 verbatim
/-- The first-order kernel of the `Σ₁` definition of Knapsack. -/
noncomputable def knapsackKernel : ksSOLang.Sentence :=
  (ksReflClause ⊓ (ksTransClause ⊓ (ksAntisymmClause ⊓ ksTotalClause))) ⊓
    (ksSelClause ⊓ (ksBaseClause ⊓ (ksSumClause ⊓ (ksCarryClause ⊓
      (ksBottomClause ⊓ (ksTopClause ⊓ (ksFinalClause ⊓ ksEmptyClause)))))))


-- @@ L189-192 expanded
/-- Kernel clause of the counting kernel: the running totals are stored at
items and positions only. -/
private noncomputable def ksPinPSClause : ksSOLang.Sentence :=
  FirstOrder.Language.Formula.iAlls (Fin 2)
    ((kPSF (Sum.inr 0) (Sum.inr 1)).imp (kItemF (Sum.inr 0) ⊓ kPosnF (Sum.inr 1)))


-- @@ L194-197 expanded
/-- Kernel clause of the counting kernel: the carries are stored at positions
and at the items that are not the first one only. -/
private noncomputable def ksPinCarryClause : ksSOLang.Sentence :=
  FirstOrder.Language.Formula.iAlls (Fin 2)
    ((kCarryF (Sum.inr 0) (Sum.inr 1)).imp
      (kItemF (Sum.inr 0) ⊓ kPosnF (Sum.inr 1) ⊓
        FirstOrder.Language.BoundedFormula.not (kMinItemF (Sum.inr 0))))


-- @@ L199-203 verbatim
/-- **The counting kernel of Knapsack**: the kernel of its `Σ₁` definition, and
the two clauses that leave nothing of a certificate unconstrained, so that a
solution has exactly one. -/
noncomputable def sharpKnapsackKernel : ksSOLang.Sentence :=
  knapsackKernel ⊓ (ksPinPSClause ⊓ ksPinCarryClause)


-- @@ L205-205 verbatim
/-! ### Realization -/


-- @@ L207-207 verbatim
section Realize


-- @@ L209-209 verbatim
variable {A : Type} [Language.binWeights.Structure A] (ρ : knapsackGuessBlock.Assignment A)


-- @@ L211-212 verbatim
/-- The chosen items, read off an assignment of the block. -/
private def Sel (i : A) : Prop := ρ .sel ![i]


-- @@ L214-215 verbatim
/-- The running total, read off an assignment of the block. -/
private def PSum (i p : A) : Prop := ρ .pS ![i, p]


-- @@ L217-218 verbatim
/-- The carries, read off an assignment of the block. -/
private def Cy (i p : A) : Prop := ρ .carry ![i, p]


-- @@ L220-221 verbatim
/-- The bit that an item contributes. -/
private def Add (i p : A) : Prop := Sel ρ i ∧ BWBit i p


-- @@ L223-298 verbatim
private theorem realize_knapsackKernel :
    (@Sentence.Realize ksSOLang A
        (@sumStructure _ _ A _ (knapsackGuessBlock.structure ρ)) knapsackKernel) ↔
      IsLinOrd (BWLe (A := A)) ∧
        (∀ i : A, Sel ρ i → BWItem i) ∧
        (∀ i p : A, MinPos BWLe BWItem i → BWPosn p →
          (PSum ρ i p ↔ Add ρ i p)) ∧
        (∀ i j p : A, SuccPos BWLe BWItem i j → BWPosn p →
          (PSum ρ j p ↔ (PSum ρ i p ↔ (Add ρ j p ↔ Cy ρ j p)))) ∧
        (∀ i j p q : A, SuccPos BWLe BWItem i j → SuccPos BWLe BWPosn p q →
          (Cy ρ j q ↔ maj (PSum ρ i p) (Add ρ j p) (Cy ρ j p))) ∧
        (∀ i j p : A, SuccPos BWLe BWItem i j → MinPos BWLe BWPosn p → ¬Cy ρ j p) ∧
        (∀ i j p : A, SuccPos BWLe BWItem i j → MaxPos BWLe BWPosn p →
          ¬maj (PSum ρ i p) (Add ρ j p) (Cy ρ j p)) ∧
        (∀ i p : A, MaxPos BWLe BWItem i → BWPosn p → (PSum ρ i p ↔ BWTgt p)) ∧
        ((∀ i : A, ¬BWItem i) → ∀ p : A, BWPosn p → ¬BWTgt p) := by
  let := knapsackGuessBlock.structure ρ
  have hsubS : ∀ w : Fin 1 → A,
      RelMap (L := ksSOLang) (M := A) ksSelSym w ↔ ρ .sel w := fun _ => Iff.rfl
  have hsubP : ∀ w : Fin 2 → A,
      RelMap (L := ksSOLang) (M := A) ksPSSym w ↔ ρ .pS w := fun _ => Iff.rfl
  have hsubC : ∀ w : Fin 2 → A,
      RelMap (L := ksSOLang) (M := A) ksCarrySym w ↔ ρ .carry w := fun _ => Iff.rfl
  rw [knapsackKernel]
  simp only [ksReflClause, ksTransClause, ksAntisymmClause, ksTotalClause, ksSelClause,
    ksBaseClause, ksSumClause, ksCarryClause, ksBottomClause, ksTopClause, ksFinalClause,
    ksEmptyClause, kItemF, kPosnF, kBitF, kTgtF, kLeF, kSelF, kPSF, kCarryF, kEqF, kAddF,
    kXor3F, kMaj3F, kMinItemF, kMaxItemF, kSuccItemF, kMinPosnF, kMaxPosnF, kSuccPosnF,
    Sentence.Realize, Formula.realize_inf, Formula.realize_sup, Formula.realize_imp,
    Formula.realize_iff, Formula.realize_not, Formula.realize_iAlls, Formula.realize_rel₁,
    Formula.realize_rel₂, Formula.realize_equal, Term.realize_var, Sum.elim_inr,
    Sum.elim_inl, Language.relMap_sumInl, hsubS, hsubP, hsubC]
  constructor
  · rintro ⟨⟨hrefl, htrans, hanti, htot⟩, hsel, hbase, hsum, hcarry, hbot, htop, hfin, hemp⟩
    have hmin : ∀ (P : A → Prop) (x : A),
        (P x ∧ ∀ y : Fin 1 → A, P (y 0) → BWLe x (y 0)) → MinPos BWLe P x :=
      fun P x h => ⟨h.1, fun y hy => h.2 (fun _ => y) hy⟩
    have hmax : ∀ (P : A → Prop) (x : A),
        (P x ∧ ∀ y : Fin 1 → A, P (y 0) → BWLe (y 0) x) → MaxPos BWLe P x :=
      fun P x h => ⟨h.1, fun y hy => h.2 (fun _ => y) hy⟩
    have hsucc : ∀ (P : A → Prop) (x y : A), SuccPos BWLe P x y →
        (P x ∧ (P y ∧ (BWLe x y ∧ (¬x = y ∧ ∀ r : Fin 1 → A,
          P (r 0) → BWLe x (r 0) → BWLe (r 0) y → r 0 = x ∨ r 0 = y)))) :=
      fun P x y h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1,
        fun r hr h1 h2 => h.2.2.2.2 (r 0) hr h1 h2⟩
    refine ⟨⟨fun a => hrefl (fun _ => a), fun a b c hab hbc => htrans ![a, b, c] ⟨hab, hbc⟩,
      fun a b hab hba => hanti ![a, b] ⟨hab, hba⟩, fun a b => htot ![a, b]⟩,
      fun i hi => hsel (fun _ => i) hi,
      fun i p hi hp => hbase ![i, p] ⟨⟨hi.1, fun j hj => hi.2 (j 0) hj⟩, hp⟩,
      fun i j p hij hp => hsum ![i, j, p] ⟨hsucc _ i j hij, hp⟩,
      fun i j p q hij hpq => hcarry ![i, j, p, q] ⟨hsucc _ i j hij, hsucc _ p q hpq⟩,
      fun i j p hij hp => hbot ![i, j, p]
        ⟨hsucc _ i j hij, ⟨hp.1, fun q hq => hp.2 (q 0) hq⟩⟩,
      fun i j p hij hp => htop ![i, j, p]
        ⟨hsucc _ i j hij, ⟨hp.1, fun q hq => hp.2 (q 0) hq⟩⟩,
      fun i p hi hp => hfin ![i, p] ⟨⟨hi.1, fun j hj => hi.2 (j 0) hj⟩, hp⟩,
      fun hno p hp => hemp (fun i => hno (i 0)) (fun _ => p) hp⟩
  · rintro ⟨⟨hrefl, htrans, hanti, htot⟩, hsel, hbase, hsum, hcarry, hbot, htop, hfin, hemp⟩
    have hsucc : ∀ (P : A → Prop) (x y : A),
        (P x ∧ (P y ∧ (BWLe x y ∧ (¬x = y ∧ ∀ r : Fin 1 → A,
          P (r 0) → BWLe x (r 0) → BWLe (r 0) y → r 0 = x ∨ r 0 = y)))) →
        SuccPos BWLe P x y :=
      fun P x y h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1,
        fun r hr h1 h2 => h.2.2.2.2 (fun _ => r) hr h1 h2⟩
    refine ⟨⟨fun i => hrefl (i 0), fun i hi => htrans (i 0) (i 1) (i 2) hi.1 hi.2,
      fun i hi => hanti (i 0) (i 1) hi.1 hi.2, fun i => htot (i 0) (i 1)⟩,
      fun i hi => hsel (i 0) hi,
      fun i hi => hbase (i 0) (i 1) ⟨hi.1.1, fun j hj => hi.1.2 (fun _ => j) hj⟩ hi.2,
      fun i hi => hsum (i 0) (i 1) (i 2) (hsucc _ _ _ hi.1) hi.2,
      fun i hi => hcarry (i 0) (i 1) (i 2) (i 3) (hsucc _ _ _ hi.1) (hsucc _ _ _ hi.2),
      fun i hi => hbot (i 0) (i 1) (i 2) (hsucc _ _ _ hi.1)
        ⟨hi.2.1, fun q hq => hi.2.2 (fun _ => q) hq⟩,
      fun i hi => htop (i 0) (i 1) (i 2) (hsucc _ _ _ hi.1)
        ⟨hi.2.1, fun q hq => hi.2.2 (fun _ => q) hq⟩,
      fun i hi => hfin (i 0) (i 1) ⟨hi.1.1, fun j hj => hi.1.2 (fun _ => j) hj⟩ hi.2,
      fun hno i hi => hemp (fun j => hno (fun _ => j)) (i 0) hi⟩


-- @@ L300-311 verbatim
/-- What the counting kernel says of an assignment of the block: the instance
is well formed, the chosen elements are items, the two binary relations are a
walk ending on the target, and they hold nowhere else. -/
def KnapsackCert (A : Type) [Language.binWeights.Structure A]
    (ρ : knapsackGuessBlock.Assignment A) : Prop :=
  IsLinOrd (BWLe (A := A)) ∧ (∀ i : A, ρ .sel ![i] → BWItem i) ∧
    IsChain BWLe BWItem BWLe BWPosn (fun i : A => ρ .sel ![i]) BWBit
      (fun i p => ρ .pS ![i, p]) (fun i p => ρ .carry ![i, p]) ∧
    (∀ i p : A, MaxPos BWLe BWItem i → BWPosn p → (ρ .pS ![i, p] ↔ BWTgt p)) ∧
    ((∀ i : A, ¬BWItem i) → ∀ p : A, BWPosn p → ¬BWTgt p) ∧
    (∀ i p : A, ρ .pS ![i, p] → BWItem i ∧ BWPosn p) ∧
    ∀ i p : A, ρ .carry ![i, p] → BWItem i ∧ BWPosn p ∧ ¬MinPos BWLe BWItem i


-- @@ L313-336 verbatim
private theorem realize_ksPinClauses :
    (@Sentence.Realize ksSOLang A
        (@sumStructure _ _ A _ (knapsackGuessBlock.structure ρ))
        (ksPinPSClause ⊓ ksPinCarryClause)) ↔
      (∀ i p : A, PSum ρ i p → BWItem i ∧ BWPosn p) ∧
        ∀ i p : A, Cy ρ i p → BWItem i ∧ BWPosn p ∧ ¬MinPos BWLe BWItem i := by
  let := knapsackGuessBlock.structure ρ
  have hsubP : ∀ w : Fin 2 → A,
      RelMap (L := ksSOLang) (M := A) ksPSSym w ↔ ρ .pS w := fun _ => Iff.rfl
  have hsubC : ∀ w : Fin 2 → A,
      RelMap (L := ksSOLang) (M := A) ksCarrySym w ↔ ρ .carry w := fun _ => Iff.rfl
  simp only [ksPinPSClause, ksPinCarryClause, kItemF, kPosnF, kLeF, kPSF, kCarryF, kMinItemF,
    Sentence.Realize, Formula.realize_inf, Formula.realize_imp, Formula.realize_not,
    Formula.realize_iAlls, Formula.realize_rel₁, Formula.realize_rel₂, Term.realize_var,
    Sum.elim_inr, Sum.elim_inl, Language.relMap_sumInl, hsubP, hsubC]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun i p h => h1 ![i, p] h, fun i p h => ?_⟩
    obtain ⟨⟨hi, hp⟩, hnmin⟩ := h2 ![i, p] h
    exact ⟨hi, hp, fun hmin => hnmin ⟨hmin.1, fun y hy => hmin.2 (y 0) hy⟩⟩
  · rintro ⟨h1, h2⟩
    refine ⟨fun i h => h1 (i 0) (i 1) h, fun i h => ?_⟩
    obtain ⟨hi, hp, hnmin⟩ := h2 (i 0) (i 1) h
    exact ⟨⟨hi, hp⟩, fun hmin => hnmin ⟨hmin.1, fun y hy => hmin.2 (fun _ => y) hy⟩⟩


-- @@ L338-358 verbatim
/-- **The counting kernel says exactly what it should.** -/
theorem realize_sharpKnapsackKernel :
    (@Sentence.Realize ksSOLang A
        (@sumStructure _ _ A _ (knapsackGuessBlock.structure ρ)) sharpKnapsackKernel) ↔
      KnapsackCert A ρ := by
  have h1 := realize_knapsackKernel ρ
  have h2 := realize_ksPinClauses ρ
  have hinf : (@Sentence.Realize ksSOLang A
        (@sumStructure _ _ A _ (knapsackGuessBlock.structure ρ)) sharpKnapsackKernel) ↔
      (@Sentence.Realize ksSOLang A
        (@sumStructure _ _ A _ (knapsackGuessBlock.structure ρ)) knapsackKernel) ∧
      (@Sentence.Realize ksSOLang A
        (@sumStructure _ _ A _ (knapsackGuessBlock.structure ρ))
        (ksPinPSClause ⊓ ksPinCarryClause)) := by
    let := knapsackGuessBlock.structure ρ
    exact Formula.realize_inf
  rw [hinf, h1, h2]
  exact ⟨fun ⟨⟨hlin, hsel, hb, hs, hc, hbo, ht, hfin, hemp⟩, hp1, hp2⟩ =>
      ⟨hlin, hsel, ⟨hb, hs, hc, hbo, ht⟩, hfin, hemp, hp1, hp2⟩,
    fun ⟨hlin, hsel, ⟨hb, hs, hc, hbo, ht⟩, hfin, hemp, hp1, hp2⟩ =>
      ⟨⟨hlin, hsel, hb, hs, hc, hbo, ht, hfin, hemp⟩, hp1, hp2⟩⟩


-- @@ L360-360 verbatim
end Realize


-- @@ L362-362 verbatim
/-! ### Membership -/


-- @@ L364-364 verbatim
section Walks


-- @@ L366-366 verbatim
variable {A : Type} [Language.binWeights.Structure A] [Finite A]


-- @@ L368-401 verbatim
/-- **A solution has a walk**: running totals and carries of a ripple-carry
addition of the chosen weights, ending on the target. -/
theorem exists_chain_of_subsetSum (hlin : IsLinOrd (BWLe (A := A))) {S : A → Prop}
    (hSitem : ∀ i, S i → BWItem i)
    (hsumeq : (∑ᶠ i ∈ {i | S i}, BWWeight i) = BWTarget A) :
    ∃ PS Cy : A → A → Prop, IsChain BWLe BWItem BWLe BWPosn S BWBit PS Cy ∧
      (∀ i p : A, MaxPos BWLe BWItem i → BWPosn p → (PS i p ↔ BWTgt p)) ∧
      ((∀ i : A, ¬BWItem i) → ∀ p : A, BWPosn p → ¬BWTgt p) := by
  have htot : (∑ᶠ j ∈ {j : A | S j}, binNum BWLe BWPosn (BWBit j)) <
      2 ^ ({p : A | BWPosn p} : Set A).ncard := by
    rw [show (∑ᶠ j ∈ {j : A | S j}, binNum BWLe BWPosn (BWBit j)) =
      ∑ᶠ j ∈ {j : A | S j}, BWWeight j from rfl, hsumeq, BWTarget]
    exact binNum_lt_two_pow hlin _ BWPosn rfl BWTgt
  obtain ⟨PS, Cy, hchain⟩ := exists_chain (wt := BWBit) hlin hlin hSitem htot
  refine ⟨PS, Cy, hchain, ?_, ?_⟩
  · -- at the last item the running total is the target
    intro i p hi hp
    refine binNum_inj_on hlin _ BWPosn rfl (PS i) BWTgt ?_ p hp
    rw [chain_sound hlin hlin hSitem hchain i hi.1, partSum_max hSitem hi]
    rw [show (∑ᶠ j ∈ {j : A | S j}, binNum BWLe BWPosn (BWBit j)) =
      ∑ᶠ j ∈ {j : A | S j}, BWWeight j from rfl, hsumeq, BWTarget]
  · -- with no items the target must vanish
    intro hno p hp
    have hSempty : {j : A | S j} = (∅ : Set A) := by
      ext j
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      exact fun hj => hno j (hSitem j hj)
    have hzero : binNum (BWLe (A := A)) BWPosn BWTgt = 0 := by
      have htarget : BWTarget A = 0 := by
        rw [← hsumeq, hSempty, finsum_mem_empty]
      exact htarget
    have := binNum_inj_on hlin _ BWPosn rfl BWTgt (fun _ => False)
      (by rw [hzero, binNum_bot]) p hp
    exact this.mp


-- @@ L403-427 verbatim
/-- **A walk ending on the target is a solution.** -/
theorem subsetSum_of_chain (hlin : IsLinOrd (BWLe (A := A))) {S : A → Prop}
    {PS Cy : A → A → Prop} (hsel : ∀ i, S i → BWItem i)
    (hchain : IsChain BWLe BWItem BWLe BWPosn S BWBit PS Cy)
    (hfinal : ∀ i p : A, MaxPos BWLe BWItem i → BWPosn p → (PS i p ↔ BWTgt p))
    (hempty : (∀ i : A, ¬BWItem i) → ∀ p : A, BWPosn p → ¬BWTgt p) :
    (∑ᶠ i ∈ {i | S i}, BWWeight i) = BWTarget A := by
  by_cases hitems : ∃ i : A, BWItem i
  · obtain ⟨imax, himax⟩ := exists_maxPos hlin hitems
    have h1 := chain_sound hlin hlin hsel hchain imax himax.1
    have h2 : binNum BWLe BWPosn (PS imax) = BWTarget A :=
      binNum_congr_on fun p hp => hfinal imax p himax hp
    rw [show (∑ᶠ j ∈ {j : A | S j}, BWWeight j) =
      ∑ᶠ j ∈ {j : A | S j}, binNum BWLe BWPosn (BWBit j) from rfl,
      ← partSum_max hsel himax, ← h1, h2]
  · have hno : ∀ i, ¬BWItem i := fun i hi => hitems ⟨i, hi⟩
    have hSempty : {i : A | S i} = (∅ : Set A) := by
      ext i
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      exact fun hi => hno i (hsel i hi)
    have htgt : {p : A | BWPosn p ∧ BWTgt p} = (∅ : Set A) := by
      ext p
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      exact fun h => hempty hno p h.1 h.2
    rw [hSempty, finsum_mem_empty, BWTarget, binNum, htgt, finsum_mem_empty]


-- @@ L429-429 verbatim
end Walks


-- @@ L431-454 verbatim
/-- **Knapsack is `Σ₁`-definable**: guess the chosen items, the running totals
and the carries, and check first-order that each step is a ripple-carry
addition whose last total is the target. Since NP is defined as
`Σ₁`-definability, this is the membership half of the NP-completeness of
Knapsack. -/
theorem knapsack_sigmaSODefinable : SigmaSODefinable 1 Knapsack := by
  refine ⟨[knapsackGuessBlock], rfl, knapsackKernel, ?_⟩
  intro A _ _ _
  constructor
  · -- a solution yields a certificate: the walk of `exists_chain`
    rintro ⟨hfin, hlin, S, hSitem, hsumeq⟩
    obtain ⟨PS, Cy, hchain, hfinal, hempty⟩ := exists_chain_of_subsetSum hlin hSitem hsumeq
    refine ⟨fun idx => match idx with
      | .sel => fun w : Fin 1 → A => S (w 0)
      | .pS => fun w : Fin 2 → A => PS (w 0) (w 1)
      | .carry => fun w : Fin 2 → A => Cy (w 0) (w 1), ?_⟩
    exact (realize_knapsackKernel _).mpr ⟨hlin, hSitem, hchain.1, hchain.2.1,
      hchain.2.2.1, hchain.2.2.2.1, hchain.2.2.2.2, hfinal, hempty⟩
  · -- a certificate yields a solution: the walk is sound
    rintro ⟨ρ, hρ⟩
    obtain ⟨hlin, hsel, hbase, hstepsum, hstepcarry, hstepbot, hsteptop, hfinal, hempty⟩ :=
      (realize_knapsackKernel ρ).mp hρ
    exact ⟨‹Finite A›, hlin, Sel ρ, hsel, subsetSum_of_chain hlin hsel
      ⟨hbase, hstepsum, hstepcarry, hstepbot, hsteptop⟩ hfinal hempty⟩


-- @@ L456-456 verbatim
end SigmaOne


-- @@ L458-458 verbatim
end DescriptiveComplexity
