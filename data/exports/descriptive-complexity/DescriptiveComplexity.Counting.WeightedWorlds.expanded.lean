/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Syntax
import DescriptiveComplexity.Counting.PossibleWorlds
import DescriptiveComplexity.Numbers.BinCount
import DescriptiveComplexity.Counting.Probability
import Mathlib.Algebra.BigOperators.Finprod


-- @@ L12-72 verbatim
/-!
# Counting weighted possible worlds

`DescriptiveComplexity.Counting.PossibleWorlds` counts the possible worlds of
an instance with certain and uncertain facts, each uncertain fact being
present with probability `1/2`. Here every uncertain fact carries its own
probability, as two natural **weights**: `a` for its being present and `c` for
its being absent, the probability being `a / (a + c)`. The quantity counted is
the **weighted number of worlds** in which a sentence `φ` of the schema holds,

`W(φ) = ∑ over the worlds satisfying φ of ∏ over the open facts of their weight`,

and the probability of `φ` is `W(φ) / W(⊤)`
(`DescriptiveComplexity.ProbAssignment.funcProb_ofWeights`).

## The instances

`DescriptiveComplexity.weightedLang L`: for each symbol of the schema `L`, of
arity `n`, the certain facts and the uncertain ones, and two relations of
arity `n + 1` holding the bits of the two weights of each fact; and one order
relation on the bit positions, which are all the elements. Weights are in
**binary**: the encoding in which a probability of a database is honestly
written, and the one for which membership is the stronger statement.

## Why this is in `#P`

A weight multiplies a count, and a count cannot be multiplied by a number of
the instance directly. The witness therefore carries, beside the world, one
number per open fact, *below the weight that fact takes in the world*: each
world is then counted once per unit of the product of its weights. “Below” is
first-order, by the highest position at which two binary numbers differ
(`DescriptiveComplexity.numLtFormula`, generic in the arity of the fact), and
the numbers below a weight are as many as the weight
(`DescriptiveComplexity.card_binNum_lt`).

* `DescriptiveComplexity.WeightedWorlds φ` is the witness count of that
  kernel, hence in `#P` for every first-order `φ`
  (`DescriptiveComplexity.weightedWorlds_mem_sharpP`).
* `DescriptiveComplexity.weightedWorlds_eq_weightSum`: on an instance whose
  order is linear, it is the weighted number of worlds. The proof sorts the
  witnesses by world (`DescriptiveComplexity.weightedWorlds_eq_sum`), then
  counts the numbers allowed at each fact
  (`DescriptiveComplexity.card_numCond`).
* On an instance whose order relation is not linear the count is zero
  (`DescriptiveComplexity.weightedWorlds_of_not_isLinOrd`): the kernel asks
  for linearity, such an instance carrying no number.

## The probability

The open facts of an instance are independent Boolean variables, and a world
is a valuation of them (`DescriptiveComplexity.worldOfVal`). So the count is a
weighted count in the sense of `DescriptiveComplexity.Counting.Probability`
(`DescriptiveComplexity.weightedWorlds_eq_weightedCount`), and

`Pr(φ) = WeightedWorlds φ / WeightedWorlds ⊤`

(`DescriptiveComplexity.funcProb_holdsEvent_eq_ratio`): **the probability of
any first-order query over a tuple-independent database is a ratio of two
`#P` numbers**.

-/


-- @@ L74-74 verbatim
namespace DescriptiveComplexity


-- @@ L76-76 verbatim
open FirstOrder


-- @@ L78-78 verbatim
open Language Structure


-- @@ L80-80 verbatim
/-! ### The vocabulary -/


-- @@ L82-97 verbatim
/-- The relation symbols of a weighted instance over the schema `L`: for each
symbol of the schema, the certain facts, the uncertain facts, and the bits of
the two weights of each fact; and one order, on the bit positions. -/
inductive WeightedRel (L : Language.{0, 0}) : ℕ → Type
  /-- The certain facts. -/
  | cert {n : ℕ} (R : L.Relations n) : WeightedRel L n
  /-- The uncertain facts. -/
  | unc {n : ℕ} (R : L.Relations n) : WeightedRel L n
  /-- `pres R (x̄, i)`: the bit of position `i` of the weight of the fact `R(x̄)`
  being present. -/
  | pres {n : ℕ} (R : L.Relations n) : WeightedRel L (n + 1)
  /-- `abs R (x̄, i)`: the bit of position `i` of the weight of the fact `R(x̄)`
  being absent. -/
  | abs {n : ℕ} (R : L.Relations n) : WeightedRel L (n + 1)
  /-- The order of the bit positions. -/
  | le : WeightedRel L 2


-- @@ L99-101 verbatim
/-- The vocabulary of weighted instances over the schema `L`. -/
def weightedLang (L : Language.{0, 0}) : Language.{0, 0} :=
  ⟨fun _ => Empty, WeightedRel L⟩


-- @@ L103-104 verbatim
instance (L : Language.{0, 0}) : (weightedLang L).IsRelational :=
  fun _ => inferInstanceAs (IsEmpty Empty)


-- @@ L106-106 verbatim
variable {L : Language.{0, 0}} [Finite (Σ n, L.Relations n)]


-- @@ L108-112 verbatim
/-- The block guessing a weighted world: a world, and for each fact a number,
as the set of its bits. -/
def weightBlock (L : Language.{0, 0}) [Finite (Σ n, L.Relations n)] : SOBlock where
  ι := (Σ n, L.Relations n) ⊕ (Σ n, L.Relations n)
  arity := Sum.elim (fun p => p.1) fun p => p.1 + 1


-- @@ L114-116 verbatim
/-- The vocabulary of the kernel. -/
abbrev weightKernelLang (L : Language.{0, 0}) [Finite (Σ n, L.Relations n)] : Language :=
  (weightedLang L).sum (weightBlock L).lang


-- @@ L118-118 verbatim
section Symbols


-- @@ L120-120 verbatim
variable (p : Σ n, L.Relations n)


-- @@ L122-123 verbatim
/-- The certain facts of a symbol, in the kernel vocabulary. -/
abbrev wkCert : (weightKernelLang L).Relations p.1 := Sum.inl (WeightedRel.cert p.2)


-- @@ L125-126 verbatim
/-- The uncertain facts of a symbol, in the kernel vocabulary. -/
abbrev wkUnc : (weightKernelLang L).Relations p.1 := Sum.inl (WeightedRel.unc p.2)


-- @@ L128-129 verbatim
/-- The bits of the weight of presence, in the kernel vocabulary. -/
abbrev wkPres : (weightKernelLang L).Relations (p.1 + 1) := Sum.inl (WeightedRel.pres p.2)


-- @@ L131-132 verbatim
/-- The bits of the weight of absence, in the kernel vocabulary. -/
abbrev wkAbs : (weightKernelLang L).Relations (p.1 + 1) := Sum.inl (WeightedRel.abs p.2)


-- @@ L134-135 verbatim
/-- The guessed world, in the kernel vocabulary. -/
abbrev wkWorld : (weightKernelLang L).Relations p.1 := Sum.inr ⟨Sum.inl p, rfl⟩


-- @@ L137-138 verbatim
/-- The guessed numbers, in the kernel vocabulary. -/
abbrev wkNum : (weightKernelLang L).Relations (p.1 + 1) := Sum.inr ⟨Sum.inr p, rfl⟩


-- @@ L140-140 verbatim
end Symbols


-- @@ L142-144 verbatim
/-- The order of the positions, in the kernel vocabulary. -/
abbrev wkLe (L : Language.{0, 0}) [Finite (Σ n, L.Relations n)] :
    (weightKernelLang L).Relations 2 := Sum.inl WeightedRel.le


-- @@ L146-146 verbatim
/-! ### Atoms about a fact and a position -/


-- @@ L148-148 verbatim
section Atoms


-- @@ L150-150 verbatim
variable {L' : Language.{0, 0}} {α : Type} {n : ℕ}


-- @@ L152-155 verbatim
/-- The atom `S(x̄)`, the tuple being read off the free variables through
`e`. -/
def factAtom (S : L'.Relations n) (e : Fin n → α) : L'.Formula α :=
  Relations.formula S fun m => Term.var (e m)


-- @@ L157-159 verbatim
/-- The atom `S(x̄, i)`: a fact and a position. -/
def bitAtom (S : L'.Relations (n + 1)) (e : Fin n → α) (i : α) : L'.Formula α :=
  Relations.formula S (Fin.snoc (α := fun _ => L'.Term α) (fun m => Term.var (e m)) (Term.var i))


-- @@ L161-161 verbatim
variable {M : Type} [L'.Structure M]


-- @@ L163-165 verbatim
theorem realize_factAtom (S : L'.Relations n) (e : Fin n → α) (v : α → M) :
    (factAtom S e).Realize v ↔ RelMap S fun m => v (e m) :=
  Formula.realize_rel


-- @@ L167-174 verbatim
theorem realize_bitAtom (S : L'.Relations (n + 1)) (e : Fin n → α) (i : α) (v : α → M) :
    (bitAtom S e i).Realize v ↔
      RelMap S (Fin.snoc (α := fun _ => M) (fun m => v (e m)) (v i)) := by
  rw [bitAtom, Formula.realize_rel]
  refine iff_of_eq (congrArg _ (funext fun k => ?_))
  refine Fin.lastCases ?_ (fun m => ?_) k
  · simp
  · simp


-- @@ L176-176 verbatim
end Atoms


-- @@ L178-178 verbatim
/-! ### Comparing two numbers attached to a fact -/


-- @@ L180-180 verbatim
section Compare


-- @@ L182-182 verbatim
variable {L' : Language.{0, 0}} {n : ℕ} (N W : L'.Relations (n + 1)) (Le : L'.Relations 2)


-- @@ L184-194 verbatim
/-- “The number `N(x̄, ·)` is below the number `W(x̄, ·)`”, by the highest
position at which they differ: some position carries `1` in `W` and `0` in
`N`, and the two agree strictly above it. -/
noncomputable def numLtFormula : L'.Formula (Fin n) :=
  Formula.iExs Unit
    (bitAtom W Sum.inl (Sum.inr ()) ⊓ (∼(bitAtom N Sum.inl (Sum.inr ())) ⊓
      Formula.iAlls Unit
        (((Relations.formula₂ Le (Term.var (Sum.inl (Sum.inr ()))) (Term.var (Sum.inr ()))) ⊓
            ∼(Term.equal (Term.var (Sum.inr ())) (Term.var (Sum.inl (Sum.inr ()))))).imp
          ((bitAtom N (fun m => Sum.inl (Sum.inl m)) (Sum.inr ())).iff
            (bitAtom W (fun m => Sum.inl (Sum.inl m)) (Sum.inr ()))))))


-- @@ L196-199 expanded
/-- “The relation `Le` is a linear order”, as a sentence. -/
noncomputable def linOrdSentence : L'.Sentence :=
  FirstOrder.Language.Formula.iAlls (Fin 1)
        (FirstOrder.Language.Relations.formula₂ Le (FirstOrder.Language.Term.var (Sum.inr 0))
          (FirstOrder.Language.Term.var (Sum.inr 0))) ⊓
      FirstOrder.Language.Formula.iAlls (Fin 3)
        ((FirstOrder.Language.Relations.formula₂ Le (FirstOrder.Language.Term.var (Sum.inr 0))
              (FirstOrder.Language.Term.var (Sum.inr 1))).imp
          ((FirstOrder.Language.Relations.formula₂ Le (FirstOrder.Language.Term.var (Sum.inr 1))
                (FirstOrder.Language.Term.var (Sum.inr 2))).imp
            (FirstOrder.Language.Relations.formula₂ Le (FirstOrder.Language.Term.var (Sum.inr 0))
              (FirstOrder.Language.Term.var (Sum.inr 2))))) ⊓
    (FirstOrder.Language.Formula.iAlls (Fin 2)
        ((FirstOrder.Language.Relations.formula₂ Le (FirstOrder.Language.Term.var (Sum.inr 0))
              (FirstOrder.Language.Term.var (Sum.inr 1))).imp
          ((FirstOrder.Language.Relations.formula₂ Le (FirstOrder.Language.Term.var (Sum.inr 1))
                (FirstOrder.Language.Term.var (Sum.inr 0))).imp
            (FirstOrder.Language.Term.equal (FirstOrder.Language.Term.var (Sum.inr 0))
              (FirstOrder.Language.Term.var (Sum.inr 1))))) ⊓
      FirstOrder.Language.Formula.iAlls (Fin 2)
        (FirstOrder.Language.Relations.formula₂ Le (FirstOrder.Language.Term.var (Sum.inr 0))
            (FirstOrder.Language.Term.var (Sum.inr 1)) ⊔
          FirstOrder.Language.Relations.formula₂ Le (FirstOrder.Language.Term.var (Sum.inr 1))
            (FirstOrder.Language.Term.var (Sum.inr 0))))


-- @@ L201-203 verbatim
/-- “The number `N(x̄, ·)` is zero”: it has no bit. -/
noncomputable def numZeroFormula : L'.Formula (Fin n) :=
  Formula.iAlls Unit (∼(bitAtom N Sum.inl (Sum.inr ())))


-- @@ L205-205 verbatim
variable {M : Type} [L'.Structure M]


-- @@ L207-222 verbatim
theorem realize_numLtFormula (x : Fin n → M) :
    (numLtFormula N W Le).Realize x ↔
      ∃ i : M, RelMap W (Fin.snoc (α := fun _ => M) x i) ∧
        ¬RelMap N (Fin.snoc (α := fun _ => M) x i) ∧
        ∀ j : M, RelMap Le ![i, j] → j ≠ i →
          (RelMap N (Fin.snoc (α := fun _ => M) x j) ↔
            RelMap W (Fin.snoc (α := fun _ => M) x j)) := by
  rw [numLtFormula, Formula.realize_iExs]
  simp only [Formula.realize_inf, Formula.realize_not, realize_bitAtom, Formula.realize_iAlls,
    Formula.realize_imp, Formula.realize_iff, Formula.realize_rel₂, Formula.realize_equal,
    Term.realize_var, Sum.elim_inl, Sum.elim_inr]
  constructor
  · rintro ⟨f, h1, h2, h3⟩
    exact ⟨f (), h1, h2, fun j hle hne => h3 (fun _ => j) ⟨hle, hne⟩⟩
  · rintro ⟨i, h1, h2, h3⟩
    exact ⟨fun _ => i, h1, h2, fun g hg => h3 (g ()) hg.1 hg.2⟩


-- @@ L224-233 verbatim
theorem realize_linOrdSentence :
    M ⊨ linOrdSentence Le ↔ IsLinOrd (fun a b : M => RelMap Le ![a, b]) := by
  rw [linOrdSentence, IsLinOrd, Sentence.Realize]
  simp only [Formula.realize_inf, Formula.realize_iAlls, Formula.realize_imp,
    Formula.realize_sup, Formula.realize_rel₂, Formula.realize_equal, Term.realize_var,
    Sum.elim_inr, and_assoc]
  refine and_congr ⟨fun h a => h fun _ => a, fun h i => h (i 0)⟩ (and_congr ?_ (and_congr ?_ ?_))
  · exact ⟨fun h a b c => h ![a, b, c], fun h i => h (i 0) (i 1) (i 2)⟩
  · exact ⟨fun h a b => h ![a, b], fun h i => h (i 0) (i 1)⟩
  · exact ⟨fun h a b => h ![a, b], fun h i => h (i 0) (i 1)⟩


-- @@ L235-239 verbatim
theorem realize_numZeroFormula (x : Fin n → M) :
    (numZeroFormula N).Realize x ↔ ∀ i : M, ¬RelMap N (Fin.snoc (α := fun _ => M) x i) := by
  rw [numZeroFormula, Formula.realize_iAlls]
  simp only [Formula.realize_not, realize_bitAtom, Sum.elim_inl, Sum.elim_inr]
  exact ⟨fun h i => h fun _ => i, fun h f => h (f ())⟩


-- @@ L241-241 verbatim
end Compare


-- @@ L243-243 verbatim
/-! ### The kernel -/


-- @@ L245-245 verbatim
section Kernel


-- @@ L247-247 verbatim
variable {A : Type} [(weightedLang L).Structure A]


-- @@ L249-251 verbatim
/-- The world of an assignment of the block. -/
def worldOf (σ : (weightBlock L).Assignment A) : (worldBlock L).Assignment A :=
  fun p x => σ (Sum.inl p) x


-- @@ L253-257 verbatim
/-- The number an assignment of the block attaches to a fact, as its set of
bits. -/
def numOf (σ : (weightBlock L).Assignment A) (p : Σ n, L.Relations n) (x : Fin p.1 → A) :
    A → Prop :=
  fun i => σ (Sum.inr p) (Fin.snoc (α := fun _ => A) x i)


-- @@ L259-262 verbatim
/-- The bits of a weight of a fact, read through a symbol of arity one more
than the fact's. -/
def bitsOf {n : ℕ} (S : WeightedRel L (n + 1)) (x : Fin n → A) : A → Prop :=
  fun i => RelMap (L := weightedLang L) S (Fin.snoc (α := fun _ => A) x i)


-- @@ L264-266 verbatim
/-- The order of the positions of a weighted instance. -/
def WLe (L : Language.{0, 0}) (A : Type) [(weightedLang L).Structure A] (a b : A) : Prop :=
  RelMap (L := weightedLang L) WeightedRel.le ![a, b]


-- @@ L268-271 verbatim
/-- One set of bits is below another, by the highest position at which they
differ. -/
def BitLt (Le : A → A → Prop) (b w : A → Prop) : Prop :=
  ∃ i, w i ∧ ¬b i ∧ ∀ j, Le i j → j ≠ i → (b j ↔ w j)


-- @@ L273-291 verbatim
/-- What the kernel asks of an assignment at one fact: the world keeps a
certain fact and contains only certain or uncertain ones; at an *open* fact –
uncertain and not certain – the number is below the weight of presence if the
world keeps the fact, and below the weight of absence if not; at any other
fact the number is zero. -/
def WeightCond (σ : (weightBlock L).Assignment A) (p : Σ n, L.Relations n)
    (x : Fin p.1 → A) : Prop :=
  ((RelMap (L := weightedLang L) (WeightedRel.cert p.2) x → worldOf σ p x) ∧
      (worldOf σ p x → RelMap (L := weightedLang L) (WeightedRel.cert p.2) x ∨
        RelMap (L := weightedLang L) (WeightedRel.unc p.2) x)) ∧
    ((RelMap (L := weightedLang L) (WeightedRel.unc p.2) x ∧
          ¬RelMap (L := weightedLang L) (WeightedRel.cert p.2) x →
        (worldOf σ p x →
            BitLt (WLe L A) (numOf σ p x) (bitsOf (WeightedRel.pres p.2) x)) ∧
          (¬worldOf σ p x →
            BitLt (WLe L A) (numOf σ p x) (bitsOf (WeightedRel.abs p.2) x))) ∧
      (¬(RelMap (L := weightedLang L) (WeightedRel.unc p.2) x ∧
          ¬RelMap (L := weightedLang L) (WeightedRel.cert p.2) x) →
        ∀ i, ¬numOf σ p x i))


-- @@ L293-302 verbatim
/-- The condition of the kernel at one fact, as a formula in the fact. -/
noncomputable def weightFormulaAt (p : Σ n, L.Relations n) :
    (weightKernelLang L).Formula (Fin p.1) :=
  (((factAtom (wkCert p) id).imp (factAtom (wkWorld p) id)) ⊓
      ((factAtom (wkWorld p) id).imp (factAtom (wkCert p) id ⊔ factAtom (wkUnc p) id))) ⊓
    ((((factAtom (wkUnc p) id) ⊓ ∼(factAtom (wkCert p) id)).imp
        (((factAtom (wkWorld p) id).imp (numLtFormula (wkNum p) (wkPres p) (wkLe L))) ⊓
          ((∼(factAtom (wkWorld p) id)).imp (numLtFormula (wkNum p) (wkAbs p) (wkLe L))))) ⊓
      ((∼((factAtom (wkUnc p) id) ⊓ ∼(factAtom (wkCert p) id))).imp
        (numZeroFormula (wkNum p))))


-- @@ L304-313 verbatim
theorem realize_weightFormulaAt (σ : (weightBlock L).Assignment A) (p : Σ n, L.Relations n)
    (x : Fin p.1 → A) :
    @Formula.Realize (weightKernelLang L) A
        (@sumStructure (weightedLang L) (weightBlock L).lang A _ ((weightBlock L).structure σ))
        _ (weightFormulaAt p) x ↔ WeightCond σ p x := by
  let := (weightBlock L).structure σ
  rw [weightFormulaAt]
  simp only [Formula.realize_inf, Formula.realize_imp, Formula.realize_not,
    Formula.realize_sup, realize_factAtom, realize_numLtFormula, realize_numZeroFormula]
  exact Iff.rfl


-- @@ L315-319 verbatim
/-- Realization of a finite conjunction of formulas. -/
private theorem realize_iInf' {L' : Language.{0, 0}} {M : Type} [L'.Structure M] {α β : Type}
    [Finite β] (f : β → L'.Formula α) (v : α → M) :
    (Formula.iInf f).Realize v ↔ ∀ b, (f b).Realize v :=
  BoundedFormula.realize_iInf


-- @@ L321-325 verbatim
/-- The sentence asking the condition of the kernel at every fact. -/
noncomputable def weightSentence (L : Language.{0, 0}) [Finite (Σ n, L.Relations n)] :
    (weightKernelLang L).Sentence :=
  Formula.iInf fun p : Σ n, L.Relations n =>
    Formula.iAlls (Fin p.1) ((weightFormulaAt p).relabel Sum.inr)


-- @@ L327-338 verbatim
theorem realize_weightSentence (σ : (weightBlock L).Assignment A) :
    @Sentence.Realize (weightKernelLang L) A
        (@sumStructure (weightedLang L) (weightBlock L).lang A _ ((weightBlock L).structure σ))
        (weightSentence L) ↔ ∀ (p : Σ n, L.Relations n) (x : Fin p.1 → A), WeightCond σ p x := by
  have h := realize_weightFormulaAt σ
  let := (weightBlock L).structure σ
  rw [weightSentence, Sentence.Realize, realize_iInf']
  refine forall_congr' fun p => ?_
  rw [Formula.realize_iAlls]
  refine forall_congr' fun x => ?_
  rw [Formula.realize_relabel]
  exact h p x


-- @@ L340-344 verbatim
/-- Reading a sentence of the schema in the guessed world. -/
def toWeightWorld (L : Language.{0, 0}) [Finite (Σ n, L.Relations n)] [L.IsRelational] :
    L →ᴸ weightKernelLang L where
  onFunction := fun {_} f => isEmptyElim f
  onRelation := fun {n} R => wkWorld ⟨n, R⟩


-- @@ L346-357 verbatim
theorem realize_toWeightWorld [L.IsRelational] (σ : (weightBlock L).Assignment A)
    (φ : L.Sentence) :
    @Sentence.Realize (weightKernelLang L) A
        (@sumStructure (weightedLang L) (weightBlock L).lang A _ ((weightBlock L).structure σ))
        ((toWeightWorld L).onSentence φ) ↔
      @Sentence.Realize L A (worldStructure (worldOf σ)) φ := by
  let s₁ : L.Structure A := worldStructure (worldOf σ)
  let s₂ : (weightKernelLang L).Structure A :=
    @sumStructure (weightedLang L) (weightBlock L).lang A _ ((weightBlock L).structure σ)
  have : @LHom.IsExpansionOn _ _ (toWeightWorld L) A s₁ s₂ :=
    @LHom.IsExpansionOn.mk _ _ _ _ s₁ s₂ (fun f _ => isEmptyElim f) (fun _ _ => rfl)
  exact @LHom.realize_onSentence _ _ A s₁ s₂ (toWeightWorld L) this φ


-- @@ L359-363 verbatim
/-- The kernel: the positions are linearly ordered, the condition holds at
every fact, and the sentence holds in the world. -/
noncomputable def weightKernel [L.IsRelational] (φ : L.Sentence) :
    (weightKernelLang L).Sentence :=
  linOrdSentence (wkLe L) ⊓ (weightSentence L ⊓ (toWeightWorld L).onSentence φ)


-- @@ L365-378 verbatim
theorem realize_weightKernel [L.IsRelational] (σ : (weightBlock L).Assignment A)
    (φ : L.Sentence) :
    @Sentence.Realize (weightKernelLang L) A
        (@sumStructure (weightedLang L) (weightBlock L).lang A _ ((weightBlock L).structure σ))
        (weightKernel φ) ↔
      IsLinOrd (WLe L A) ∧
        (∀ (p : Σ n, L.Relations n) (x : Fin p.1 → A), WeightCond σ p x) ∧
          @Sentence.Realize L A (worldStructure (worldOf σ)) φ := by
  have h1 := realize_weightSentence σ
  have h2 := realize_toWeightWorld σ φ
  let := (weightBlock L).structure σ
  have h0 : A ⊨ linOrdSentence (wkLe L) ↔ IsLinOrd (WLe L A) := realize_linOrdSentence (wkLe L)
  rw [weightKernel, Sentence.Realize, Formula.realize_inf, Formula.realize_inf]
  exact and_congr h0 (and_congr h1 h2)


-- @@ L380-380 verbatim
end Kernel


-- @@ L382-382 verbatim
/-! ### The counting problem -/


-- @@ L384-384 verbatim
section Problem


-- @@ L386-386 verbatim
variable [L.IsRelational]


-- @@ L388-394 verbatim
/-- **Counting weighted possible worlds**: the witnesses are the worlds in
which the sentence `φ` holds, each with one number per open fact below the
weight that fact takes in the world. On an instance whose positions are
linearly ordered this is the weighted count of the worlds satisfying `φ`, and
on any other instance it is zero. -/
noncomputable def WeightedWorlds (φ : L.Sentence) : CountingProblem (weightedLang L) :=
  CountingProblem.ofKernel (weightBlock L) (weightKernel φ)


-- @@ L396-402 verbatim
theorem weightedWorlds_apply (φ : L.Sentence) (A : Type) [(weightedLang L).Structure A] :
    WeightedWorlds φ A =
      Nat.card {σ : (weightBlock L).Assignment A //
        IsLinOrd (WLe L A) ∧
          (∀ (p : Σ n, L.Relations n) (x : Fin p.1 → A), WeightCond σ p x) ∧
            @Sentence.Realize L A (worldStructure (worldOf σ)) φ} :=
  Nat.card_congr (Equiv.subtypeEquivRight fun σ => realize_weightKernel σ φ)


-- @@ L404-413 verbatim
/-- On an instance whose positions are not linearly ordered, the count is
zero: such an instance carries no number. -/
theorem weightedWorlds_of_not_isLinOrd (φ : L.Sentence) (A : Type)
    [(weightedLang L).Structure A] (h : ¬IsLinOrd (WLe L A)) : WeightedWorlds φ A = 0 := by
  rw [weightedWorlds_apply]
  have : IsEmpty {σ : (weightBlock L).Assignment A //
      IsLinOrd (WLe L A) ∧
        (∀ (p : Σ n, L.Relations n) (x : Fin p.1 → A), WeightCond σ p x) ∧
          @Sentence.Realize L A (worldStructure (worldOf σ)) φ} := ⟨fun σ => h σ.2.1⟩
  exact Nat.card_of_isEmpty


-- @@ L415-418 verbatim
/-- **Counting the weighted worlds of a first-order sentence is in `#P`**,
whatever the sentence. -/
theorem weightedWorlds_mem_sharpP (φ : L.Sentence) : WeightedWorlds φ ∈ SharpP :=
  sharpPDefinable_ofKernel (weightBlock L) (weightKernel φ)


-- @@ L420-420 verbatim
end Problem


-- @@ L422-422 verbatim
/-! ### The count -/


-- @@ L424-424 verbatim
section Count


-- @@ L426-426 verbatim
variable [L.IsRelational] {A : Type} [(weightedLang L).Structure A]


-- @@ L428-429 verbatim
/-- The facts over a universe: a symbol of the schema and a tuple. -/
abbrev Fact (L : Language.{0, 0}) (A : Type) : Type := Σ p : Σ n, L.Relations n, Fin p.1 → A


-- @@ L431-434 verbatim
/-- The fact is open: uncertain and not certain. -/
def IsOpen (q : Fact L A) : Prop :=
  RelMap (L := weightedLang L) (WeightedRel.unc q.1.2) q.2 ∧
    ¬RelMap (L := weightedLang L) (WeightedRel.cert q.1.2) q.2


-- @@ L436-440 verbatim
/-- The family of relations is a possible world of the weighted instance. -/
def IsWeightedWorld (ρ : (worldBlock L).Assignment A) : Prop :=
  ∀ q : Fact L A, (RelMap (L := weightedLang L) (WeightedRel.cert q.1.2) q.2 → ρ q.1 q.2) ∧
    (ρ q.1 q.2 → RelMap (L := weightedLang L) (WeightedRel.cert q.1.2) q.2 ∨
      RelMap (L := weightedLang L) (WeightedRel.unc q.1.2) q.2)


-- @@ L442-447 verbatim
/-- What the kernel asks of the number attached to a fact, in a world. -/
def NumCond (ρ : (worldBlock L).Assignment A) (q : Fact L A) (b : A → Prop) : Prop :=
  (IsOpen q →
      (ρ q.1 q.2 → BitLt (WLe L A) b (bitsOf (WeightedRel.pres q.1.2) q.2)) ∧
        (¬ρ q.1 q.2 → BitLt (WLe L A) b (bitsOf (WeightedRel.abs q.1.2) q.2))) ∧
    (¬IsOpen q → ∀ i, ¬b i)


-- @@ L449-469 verbatim
/-- An assignment of the block is a world and a number per fact. -/
def weightAssignEquiv (L : Language.{0, 0}) [Finite (Σ n, L.Relations n)] (A : Type) :
    (weightBlock L).Assignment A ≃ (worldBlock L).Assignment A × (Fact L A → A → Prop) where
  toFun σ := (worldOf σ, fun q => numOf σ q.1 q.2)
  invFun r := fun i =>
    match i with
    | Sum.inl p => r.1 p
    | Sum.inr p => fun y => r.2 ⟨p, Fin.init y⟩ (y (Fin.last p.1))
  left_inv σ := by
    funext i
    cases i with
    | inl p => rfl
    | inr p =>
      funext y
      exact congrArg (σ (Sum.inr p)) (Fin.snoc_init_self y)
  right_inv r := by
    refine Prod.ext rfl (funext fun q => funext fun i => ?_)
    obtain ⟨p, x⟩ := q
    change r.2 ⟨p, Fin.init (Fin.snoc (α := fun _ => A) x i)⟩
      (Fin.snoc (α := fun _ => A) x i (Fin.last p.1)) = r.2 ⟨p, x⟩ i
    rw [Fin.init_snoc, Fin.snoc_last]


-- @@ L471-506 verbatim
/-- **The witnesses, sorted by world**: the count is the sum, over the worlds
satisfying the sentence, of the product over the facts of the number of
numbers the kernel allows there. -/
theorem weightedWorlds_eq_sum [Finite A] (hlin : IsLinOrd (WLe L A)) (φ : L.Sentence) :
    WeightedWorlds φ A =
      ∑ᶠ ρ : {ρ : (worldBlock L).Assignment A //
          IsWeightedWorld ρ ∧ @Sentence.Realize L A (worldStructure ρ) φ},
        ∏ᶠ q : Fact L A, Nat.card {b : A → Prop // NumCond ρ.1 q b} := by
  classical
  let := Fintype.ofFinite {ρ : (worldBlock L).Assignment A //
    IsWeightedWorld ρ ∧ @Sentence.Realize L A (worldStructure ρ) φ}
  let := Fintype.ofFinite (Fact L A)
  rw [weightedWorlds_apply, finsum_eq_sum_of_fintype]
  have e1 : {σ : (weightBlock L).Assignment A //
        IsLinOrd (WLe L A) ∧
          (∀ (p : Σ n, L.Relations n) (x : Fin p.1 → A), WeightCond σ p x) ∧
            @Sentence.Realize L A (worldStructure (worldOf σ)) φ} ≃
      {r : (worldBlock L).Assignment A × (Fact L A → A → Prop) //
        (IsWeightedWorld r.1 ∧ @Sentence.Realize L A (worldStructure r.1) φ) ∧
          ∀ q, NumCond r.1 q (r.2 q)} :=
    Equiv.subtypeEquiv (weightAssignEquiv L A) fun σ =>
      ⟨fun h => ⟨⟨fun q => (h.2.1 q.1 q.2).1, h.2.2⟩, fun q => (h.2.1 q.1 q.2).2⟩,
        fun h => ⟨hlin, fun p x => ⟨h.1.1 ⟨p, x⟩, h.2 ⟨p, x⟩⟩, h.1.2⟩⟩
  have e2 : {r : (worldBlock L).Assignment A × (Fact L A → A → Prop) //
        (IsWeightedWorld r.1 ∧ @Sentence.Realize L A (worldStructure r.1) φ) ∧
          ∀ q, NumCond r.1 q (r.2 q)} ≃
      Σ ρ : {ρ : (worldBlock L).Assignment A //
          IsWeightedWorld ρ ∧ @Sentence.Realize L A (worldStructure ρ) φ},
        ∀ q : Fact L A, {b : A → Prop // NumCond ρ.1 q b} :=
    { toFun := fun r => ⟨⟨r.1.1, r.2.1⟩, fun q => ⟨r.1.2 q, r.2.2 q⟩⟩
      invFun := fun s => ⟨(s.1.1, fun q => (s.2 q).1), s.1.2, fun q => (s.2 q).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr (e1.trans e2), Nat.card_sigma]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  rw [Nat.card_pi, finprod_eq_prod_of_fintype]


-- @@ L508-517 verbatim
open Classical in
/-- The weight of a fact in a world: the weight of presence of an open fact
the world keeps, the weight of absence of an open fact it drops, and `1` for a
fact that is not open. Weights are read in binary on the order of the
instance. -/
noncomputable def factWeight (ρ : (worldBlock L).Assignment A) (q : Fact L A) : ℕ :=
  if IsOpen q then
    if ρ q.1 q.2 then binNum (WLe L A) (fun _ => True) (bitsOf (WeightedRel.pres q.1.2) q.2)
    else binNum (WLe L A) (fun _ => True) (bitsOf (WeightedRel.abs q.1.2) q.2)
  else 1


-- @@ L519-532 verbatim
/-- Over a linear order, the first-order comparison of two sets of bits is
the comparison of the numbers they encode. -/
theorem bitLt_iff_binNum_lt [Finite A] {Le : A → A → Prop} (hlin : IsLinOrd Le)
    (b w : A → Prop) :
    BitLt Le b w ↔ binNum Le (fun _ => True) b < binNum Le (fun _ => True) w := by
  have hcard : ({p : A | True} : Set A).ncard = Nat.card A := by
    rw [← Nat.card_coe_set_eq]
    exact Nat.card_congr (Equiv.subtypeUnivEquiv fun _ => trivial)
  rw [binNum_lt_iff hlin (Nat.card A) (fun _ => True) hcard b w]
  constructor
  · rintro ⟨i, hw, hb, h⟩
    exact ⟨i, trivial, hb, hw, fun j _ hle hne => h j hle hne⟩
  · rintro ⟨i, -, hb, hw, h⟩
    exact ⟨i, hw, hb, fun j hle hne => h j trivial hle hne⟩


-- @@ L534-558 verbatim
omit [L.IsRelational] in
/-- **The numbers the kernel allows at a fact are as many as its weight.** -/
theorem card_numCond [Finite A] (hlin : IsLinOrd (WLe L A))
    (ρ : (worldBlock L).Assignment A) (q : Fact L A) :
    Nat.card {b : A → Prop // NumCond ρ q b} = factWeight ρ q := by
  by_cases ho : IsOpen q
  · by_cases hρ : ρ q.1 q.2
    · simp only [factWeight, ho, hρ, ↓reduceIte]
      rw [← card_binNum_lt hlin]
      exact Nat.card_congr (Equiv.subtypeEquivRight fun b =>
        Iff.trans ⟨fun h => (h.1 ho).1 hρ, fun h => ⟨fun _ => ⟨fun _ => h,
          fun h' => absurd hρ h'⟩, fun h' => absurd ho h'⟩⟩ (bitLt_iff_binNum_lt hlin b _))
    · simp only [factWeight, ho, hρ, ↓reduceIte]
      rw [← card_binNum_lt hlin]
      exact Nat.card_congr (Equiv.subtypeEquivRight fun b =>
        Iff.trans ⟨fun h => (h.1 ho).2 hρ, fun h => ⟨fun _ => ⟨fun h' => absurd h' hρ,
          fun _ => h⟩, fun h' => absurd ho h'⟩⟩ (bitLt_iff_binNum_lt hlin b _))
  · simp only [factWeight, ho, ↓reduceIte]
    have e : {b : A → Prop // NumCond ρ q b} ≃ Unit :=
      { toFun := fun _ => ()
        invFun := fun _ => ⟨fun _ => False, fun h => absurd h ho, fun _ _ h => h⟩
        left_inv := fun b => Subtype.ext (funext fun i =>
          propext ⟨False.elim, fun h => b.2.2 ho i h⟩)
        right_inv := fun _ => rfl }
    rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_unit]


-- @@ L560-569 verbatim
/-- **The count is the weighted number of worlds**: on an instance whose
positions are linearly ordered, the count is the sum, over the possible worlds
in which the sentence holds, of the product of the weights of the facts. -/
theorem weightedWorlds_eq_weightSum [Finite A] (hlin : IsLinOrd (WLe L A)) (φ : L.Sentence) :
    WeightedWorlds φ A =
      ∑ᶠ ρ : {ρ : (worldBlock L).Assignment A //
          IsWeightedWorld ρ ∧ @Sentence.Realize L A (worldStructure ρ) φ},
        ∏ᶠ q : Fact L A, factWeight ρ.1 q := by
  rw [weightedWorlds_eq_sum hlin]
  exact finsum_congr fun ρ => finprod_congr fun q => card_numCond hlin ρ.1 q


-- @@ L571-571 verbatim
/-! ### Worlds as valuations of the open facts -/


-- @@ L573-576 verbatim
/-- The open facts of a finite instance, as a finite type: the independent
Boolean variables of the instance. -/
noncomputable instance openFactFintype [Finite A] : Fintype {q : Fact L A // IsOpen q} :=
  Fintype.ofFinite _


-- @@ L578-580 verbatim
/-- The weight of presence of an open fact. -/
noncomputable def presWeight (x : {q : Fact L A // IsOpen q}) : ℕ :=
  binNum (WLe L A) (fun _ => True) (bitsOf (WeightedRel.pres x.1.1.2) x.1.2)


-- @@ L582-584 verbatim
/-- The weight of absence of an open fact. -/
noncomputable def absWeight (x : {q : Fact L A // IsOpen q}) : ℕ :=
  binNum (WLe L A) (fun _ => True) (bitsOf (WeightedRel.abs x.1.1.2) x.1.2)


-- @@ L586-590 verbatim
/-- The world of a valuation of the open facts: the certain facts, and the
open facts the valuation makes true. -/
def worldOfVal (v : {q : Fact L A // IsOpen q} → Bool) : (worldBlock L).Assignment A :=
  fun p x => RelMap (L := weightedLang L) (WeightedRel.cert p.2) x ∨
    ∃ h : IsOpen (⟨p, x⟩ : Fact L A), v ⟨⟨p, x⟩, h⟩ = true


-- @@ L592-596 verbatim
open Classical in
/-- The event “the sentence holds in the world”, as a Boolean function of the
valuation of the open facts. -/
noncomputable def holdsEvent (φ : L.Sentence) (v : {q : Fact L A // IsOpen q} → Bool) : Bool :=
  decide (@Sentence.Realize L A (worldStructure (worldOfVal v)) φ)


-- @@ L598-601 verbatim
omit [L.IsRelational] in
theorem isWeightedWorld_worldOfVal (v : {q : Fact L A // IsOpen q} → Bool) :
    IsWeightedWorld (worldOfVal v) :=
  fun _ => ⟨Or.inl, fun h => h.elim Or.inl fun ⟨ho, _⟩ => Or.inr ho.1⟩


-- @@ L603-615 verbatim
open Classical in
omit [L.IsRelational] in
/-- A world is the world of its valuation. -/
theorem worldOfVal_decide {ρ : (worldBlock L).Assignment A} (hρ : IsWeightedWorld ρ) :
    worldOfVal (fun x : {q : Fact L A // IsOpen q} => decide (ρ x.1.1 x.1.2)) = ρ := by
  funext p x
  refine propext ⟨fun h => ?_, fun h => ?_⟩
  · rcases h with h | ⟨_, h⟩
    · exact (hρ ⟨p, x⟩).1 h
    · exact of_decide_eq_true h
  · by_cases hc : RelMap (L := weightedLang L) (WeightedRel.cert p.2) x
    · exact Or.inl hc
    · exact Or.inr ⟨⟨((hρ ⟨p, x⟩).2 h).resolve_left hc, hc⟩, decide_eq_true h⟩


-- @@ L617-627 verbatim
open Classical in
omit [L.IsRelational] in
/-- A valuation is the valuation of its world. -/
theorem decide_worldOfVal (v : {q : Fact L A // IsOpen q} → Bool) :
    (fun x : {q : Fact L A // IsOpen q} => decide (worldOfVal v x.1.1 x.1.2)) = v := by
  funext x
  have h : worldOfVal v x.1.1 x.1.2 ↔ v x = true :=
    ⟨fun h => h.elim (fun hc => absurd hc x.2.2) fun ⟨_, hv⟩ => hv, fun hv => Or.inr ⟨x.2, hv⟩⟩
  cases hv : v x
  · exact decide_eq_false fun hw => by rw [h.mp hw] at hv; exact Bool.noConfusion hv
  · exact decide_eq_true (h.mpr hv)


-- @@ L629-647 verbatim
open Classical in
omit [L.IsRelational] in
/-- The product of the weights of the facts in a world is the weight of its
valuation: the facts that are not open contribute nothing. -/
theorem finprod_factWeight [Finite A] (ρ : (worldBlock L).Assignment A) :
    ∏ᶠ q : Fact L A, factWeight ρ q =
      valWeight presWeight absWeight
        fun x : {q : Fact L A // IsOpen q} => decide (ρ x.1.1 x.1.2) := by
  let := Fintype.ofFinite (Fact L A)
  rw [finprod_eq_prod_of_fintype, valWeight,
    ← Finset.prod_filter_of_ne (p := fun q : Fact L A => IsOpen q) fun q _ hq => by
      by_contra ho
      exact hq (by simp only [factWeight, ho, ↓reduceIte]),
    Finset.prod_subtype (p := fun q : Fact L A => IsOpen q)
      (Finset.univ.filter fun q : Fact L A => IsOpen q) (by simp)]
  refine Finset.prod_congr rfl fun x _ => ?_
  by_cases hρ : ρ x.1.1 x.1.2
  · simp only [factWeight, x.2, hρ, ↓reduceIte, decide_true, presWeight]
  · simp only [factWeight, x.2, hρ, ↓reduceIte, decide_false, Bool.false_eq_true, absWeight]


-- @@ L649-673 verbatim
open Classical in
/-- **The count is a weighted count of valuations**: on an instance whose
positions are linearly ordered, counting the weighted worlds of a sentence is
the weighted count, over the valuations of the open facts, of the event that
the sentence holds. -/
theorem weightedWorlds_eq_weightedCount [Finite A] (hlin : IsLinOrd (WLe L A))
    (φ : L.Sentence) :
    WeightedWorlds φ A = weightedCount presWeight absWeight (holdsEvent (A := A) φ) := by
  let := Fintype.ofFinite {ρ : (worldBlock L).Assignment A //
    IsWeightedWorld ρ ∧ @Sentence.Realize L A (worldStructure ρ) φ}
  let e : {ρ : (worldBlock L).Assignment A //
        IsWeightedWorld ρ ∧ @Sentence.Realize L A (worldStructure ρ) φ} ≃
      {v : {q : Fact L A // IsOpen q} → Bool // holdsEvent (A := A) φ v = true} :=
    { toFun := fun ρ => ⟨fun x => decide (ρ.1 x.1.1 x.1.2), by
        rw [holdsEvent, worldOfVal_decide ρ.2.1]
        exact decide_eq_true ρ.2.2⟩
      invFun := fun v => ⟨worldOfVal v.1, isWeightedWorld_worldOfVal v.1,
        of_decide_eq_true v.2⟩
      left_inv := fun ρ => Subtype.ext (worldOfVal_decide ρ.2.1)
      right_inv := fun v => Subtype.ext (decide_worldOfVal v.1) }
  rw [weightedWorlds_eq_weightSum hlin, finsum_eq_sum_of_fintype, weightedCount,
    ← Finset.sum_filter,
    Finset.sum_subtype (p := fun v => holdsEvent (A := A) φ v = true)
      (Finset.univ.filter fun v => holdsEvent (A := A) φ v = true) (by simp)]
  exact Fintype.sum_equiv e _ _ fun ρ => finprod_factWeight ρ.1


-- @@ L675-693 verbatim
open Classical in
/-- **The probability of a first-order sentence is a ratio of two `#P`
numbers.** Over a weighted instance whose positions are linearly ordered, let
each open fact be present independently, with probability its weight of
presence over the sum of its two weights. Then the probability that `φ` holds
is the count of the weighted worlds of `φ`, divided by the count of all the
weighted worlds; and both counting problems are in `#P`
(`DescriptiveComplexity.weightedWorlds_mem_sharpP`). -/
theorem funcProb_holdsEvent_eq_ratio [Finite A] (hlin : IsLinOrd (WLe L A))
    (hpos : ∀ x : {q : Fact L A // IsOpen q}, 0 < presWeight x + absWeight x)
    (φ : L.Sentence) :
    (ProbAssignment.ofWeights presWeight absWeight hpos).funcProb (holdsEvent φ) =
      (WeightedWorlds φ A : ℚ) / (WeightedWorlds (⊤ : L.Sentence) A : ℚ) := by
  have htop : holdsEvent (A := A) (⊤ : L.Sentence) = fun _ => true :=
    funext fun v => by
      let := worldStructure (worldOfVal v)
      exact decide_eq_true (Formula.realize_top.mpr trivial)
  rw [ProbAssignment.funcProb_ofWeights, weightedWorlds_eq_weightedCount hlin φ,
    weightedWorlds_eq_weightedCount hlin ⊤, htop]


-- @@ L695-702 verbatim
open Classical in
/-- **The probability of a sentence** over a weighted instance: each open fact
is present independently, with probability its weight of presence over the sum
of its two weights, and the probability is that of the event that the sentence
holds in the resulting world. -/
noncomputable def worldProb [Finite A] (φ : L.Sentence)
    (hpos : ∀ x : {q : Fact L A // IsOpen q}, 0 < presWeight x + absWeight x) : ℚ :=
  (ProbAssignment.ofWeights presWeight absWeight hpos).funcProb (holdsEvent φ)


-- @@ L704-710 verbatim
/-- The probability of a first-order sentence is a ratio of two `#P` numbers:
`DescriptiveComplexity.funcProb_holdsEvent_eq_ratio`, for the packaged
probability. -/
theorem worldProb_eq_ratio [Finite A] (hlin : IsLinOrd (WLe L A)) (φ : L.Sentence)
    (hpos : ∀ x : {q : Fact L A // IsOpen q}, 0 < presWeight x + absWeight x) :
    worldProb φ hpos = (WeightedWorlds φ A : ℚ) / (WeightedWorlds (⊤ : L.Sentence) A : ℚ) :=
  funcProb_holdsEvent_eq_ratio hlin hpos φ


-- @@ L712-712 verbatim
end Count


-- @@ L714-714 verbatim
end DescriptiveComplexity
