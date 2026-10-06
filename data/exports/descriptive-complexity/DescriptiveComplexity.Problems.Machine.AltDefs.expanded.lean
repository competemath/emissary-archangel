/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.MachinesAlt
import DescriptiveComplexity.Problems.Machine.Defs


-- @@ L9-54 verbatim
/-!
# Alternating machine acceptance as a decision problem

The vocabulary of the machine bridge for the polynomial hierarchy, and the
problem the bridge is about: an alternating Turing machine with `k` quantifier
blocks is *data in an instance*, and

> does this machine accept its input within as many steps as there are
> positions?

is `DescriptiveComplexity.ATMAccept k start`, an ordinary iso-invariant problem
of the catalog. The semantics it reads is
`DescriptiveComplexity.ATMData`, defined without a vocabulary in
`DescriptiveComplexity.MachinesAlt`.

## The vocabulary

`FirstOrder.Language.turingAlt k` is `FirstOrder.Language.turing` – every
symbol of which it carries verbatim, under the constructor `base` – together
with `k` unary marks `blk i` splitting the states into quantifier blocks,
exactly as `FirstOrder.Language.qbf k` extends the vocabulary of SAT by `k`
marks on the propositional variables. The two families of marks meet in the
hardness proof, which turns the block of a variable into the block of the state
guessing it.

Making the marks a *family* indexed by `Fin k`, rather than a fixed pair of
marks “existential”/“universal”, is what lets the alternation *bound* be
first-order: a transition may not decrease the block index, and may raise it by
at most one, so a run passes through the blocks in order and alternates at most
`k - 1` times. That promise – `DescriptiveComplexity.ATMData.BlocksWellFormed` –
is folded into the yes-instances alongside
`DescriptiveComplexity.TMData.WellFormed`, in the style of
`DescriptiveComplexity.IsLinOrd` for Knapsack.

## The two families

`ATMAccept k true` starts with an existential block and is the `Σₖᵖ` candidate;
`ATMAccept k false` starts with a universal one and is the `Πₖᵖ` candidate. The
two are the *same* problem up to the polarity parameter, so the `Πₖᵖ` half of
the bridge costs nothing beyond swapping the marks – the machine-side reading
of `DescriptiveComplexity.QBF` and `DescriptiveComplexity.QBFPi` sharing a
single reduction.
-/

/- The language of alternating machine instances lives in Mathlib's
`FirstOrder.Language` namespace, next to `Language.turing`. -/

-- @@ L55-55 verbatim
namespace FirstOrder


-- @@ L57-57 verbatim
namespace Language


-- @@ L59-65 verbatim
/-- Relation symbols of alternating machine instances: those of
`FirstOrder.Language.turing`, and one unary mark per quantifier block. -/
inductive turingAltRel (k : ℕ) : ℕ → Type
  /-- A symbol of the underlying machine vocabulary. -/
  | base {n : ℕ} : turingRel n → turingAltRel k n
  /-- `blk i q`: the state `q` belongs to the `i`-th quantifier block. -/
  | blk : Fin k → turingAltRel k 1


-- @@ L67-70 verbatim
/-- The relational vocabulary of alternating machine instances with `k`
quantifier blocks. -/
protected def turingAlt (k : ℕ) : Language :=
  ⟨fun _ => Empty, turingAltRel k⟩


-- @@ L72-73 verbatim
instance (k : ℕ) : IsRelational (Language.turingAlt k) :=
  fun _ => ⟨fun f => Empty.elim f⟩


-- @@ L75-75 verbatim
variable {k : ℕ}


-- @@ L77-78 verbatim
/-- The position symbol. -/
abbrev atmPosn : (Language.turingAlt k).Relations 1 := .base .posn


-- @@ L80-81 verbatim
/-- The transition symbol. -/
abbrev atmTr : (Language.turingAlt k).Relations 1 := .base .tr


-- @@ L83-84 verbatim
/-- The start-state symbol. -/
abbrev atmStart : (Language.turingAlt k).Relations 1 := .base .start


-- @@ L86-87 verbatim
/-- The accepting-state symbol. -/
abbrev atmAcc : (Language.turingAlt k).Relations 1 := .base .acc


-- @@ L89-90 verbatim
/-- The blank symbol. -/
abbrev atmBlank : (Language.turingAlt k).Relations 1 := .base .blank


-- @@ L92-93 verbatim
/-- The move-right symbol. -/
abbrev atmRight : (Language.turingAlt k).Relations 1 := .base .right


-- @@ L95-96 verbatim
/-- The order symbol. -/
abbrev atmLe : (Language.turingAlt k).Relations 2 := .base .le


-- @@ L98-99 verbatim
/-- The transition-source symbol. -/
abbrev atmSrc : (Language.turingAlt k).Relations 2 := .base .tsrc


-- @@ L101-102 verbatim
/-- The transition-read symbol. -/
abbrev atmRead : (Language.turingAlt k).Relations 2 := .base .tread


-- @@ L104-105 verbatim
/-- The transition-destination symbol. -/
abbrev atmDst : (Language.turingAlt k).Relations 2 := .base .tdst


-- @@ L107-108 verbatim
/-- The transition-write symbol. -/
abbrev atmWrite : (Language.turingAlt k).Relations 2 := .base .twrite


-- @@ L110-111 verbatim
/-- The input symbol. -/
abbrev atmInp : (Language.turingAlt k).Relations 2 := .base .inp


-- @@ L113-114 verbatim
/-- The mark of the `i`-th quantifier block. -/
abbrev atmBlk (i : Fin k) : (Language.turingAlt k).Relations 1 := .blk i


-- @@ L116-116 verbatim
end Language


-- @@ L118-118 verbatim
end FirstOrder


-- @@ L120-120 verbatim
namespace DescriptiveComplexity


-- @@ L122-122 verbatim
open FirstOrder


-- @@ L124-124 verbatim
open Language Structure


-- @@ L126-126 verbatim
/-! ### The shorthands of the vocabulary -/


-- @@ L128-128 verbatim
section Shorthands


-- @@ L130-130 verbatim
variable {k : ℕ} {A : Type} [(Language.turingAlt k).Structure A]


-- @@ L132-133 verbatim
/-- Being a position. -/
def ATMPosn (a : A) : Prop := RelMap (atmPosn (k := k)) ![a]


-- @@ L135-136 verbatim
/-- Being a transition. -/
def ATMTr (a : A) : Prop := RelMap (atmTr (k := k)) ![a]


-- @@ L138-139 verbatim
/-- Being a start state. -/
def ATMStart (a : A) : Prop := RelMap (atmStart (k := k)) ![a]


-- @@ L141-142 verbatim
/-- Being an accepting state. -/
def ATMAcc (a : A) : Prop := RelMap (atmAcc (k := k)) ![a]


-- @@ L144-145 verbatim
/-- Being the blank symbol. -/
def ATMBlank (a : A) : Prop := RelMap (atmBlank (k := k)) ![a]


-- @@ L147-148 verbatim
/-- Moving the head right. -/
def ATMRight (a : A) : Prop := RelMap (atmRight (k := k)) ![a]


-- @@ L150-151 verbatim
/-- The order on positions. -/
def ATMLe (a b : A) : Prop := RelMap (atmLe (k := k)) ![a, b]


-- @@ L153-154 verbatim
/-- The state a transition applies in. -/
def ATMSrc (a b : A) : Prop := RelMap (atmSrc (k := k)) ![a, b]


-- @@ L156-157 verbatim
/-- The symbol a transition reads. -/
def ATMRead (a b : A) : Prop := RelMap (atmRead (k := k)) ![a, b]


-- @@ L159-160 verbatim
/-- The state a transition moves to. -/
def ATMDst (a b : A) : Prop := RelMap (atmDst (k := k)) ![a, b]


-- @@ L162-163 verbatim
/-- The symbol a transition writes. -/
def ATMWrite (a b : A) : Prop := RelMap (atmWrite (k := k)) ![a, b]


-- @@ L165-166 verbatim
/-- The initial contents of a cell. -/
def ATMInp (a b : A) : Prop := RelMap (atmInp (k := k)) ![a, b]


-- @@ L168-172 verbatim
/-- The block of a state, read off the marks: the marks of the vocabulary are
indexed by `Fin k`, so a block index beyond `k` marks nothing. This is what
makes the “exactly one mark, below `k`” clause of
`DescriptiveComplexity.ATMData.BlocksWellFormed` a first-order statement. -/
def ATMBlk (j : ℕ) (a : A) : Prop := ∃ h : j < k, RelMap (atmBlk (⟨j, h⟩ : Fin k)) ![a]


-- @@ L174-188 verbatim
/-- The alternating machine an instance describes. -/
def atmData (k : ℕ) (A : Type) [(Language.turingAlt k).Structure A] : ATMData A where
  Posn := ATMPosn (k := k)
  Le := ATMLe (k := k)
  Tr := ATMTr (k := k)
  Start := ATMStart (k := k)
  Acc := ATMAcc (k := k)
  Blank := ATMBlank (k := k)
  Right := ATMRight (k := k)
  Src := ATMSrc (k := k)
  Read := ATMRead (k := k)
  Dst := ATMDst (k := k)
  Write := ATMWrite (k := k)
  Inp := ATMInp (k := k)
  Blk := ATMBlk (k := k)


-- @@ L190-190 verbatim
end Shorthands


-- @@ L192-192 verbatim
/-! ### The problem -/


-- @@ L194-194 verbatim
section Problem


-- @@ L196-197 verbatim
variable {k : ℕ} {A B : Type}
  [(Language.turingAlt k).Structure A] [(Language.turingAlt k).Structure B]


-- @@ L199-219 verbatim
/-- **An isomorphism makes the two machines agree.** Every symbol of the
vocabulary transports, which is all `DescriptiveComplexity.ATMData.AltAgree`
asks for. -/
theorem altAgree_of_equiv (e : A ≃[Language.turingAlt k] B) :
    (atmData k B).AltAgree e.symm.toEquiv (atmData k A) := by
  have h1 : ∀ (r : (Language.turingAlt k).Relations 1) (b : B),
      (RelMap r ![b] : Prop) ↔ RelMap r ![(e.symm b : A)] := fun r b => by
    have h := relMap_equiv₁ e r (e.symm b)
    rw [show (e (e.symm b) : B) = b from e.toEquiv.apply_symm_apply b] at h
    exact h.symm
  have h2 : ∀ (r : (Language.turingAlt k).Relations 2) (b b' : B),
      (RelMap r ![b, b'] : Prop) ↔ RelMap r ![(e.symm b : A), (e.symm b' : A)] := fun r b b' => by
    have h := relMap_equiv₂ e r (e.symm b) (e.symm b')
    rw [show (e (e.symm b) : B) = b from e.toEquiv.apply_symm_apply b,
      show (e (e.symm b') : B) = b' from e.toEquiv.apply_symm_apply b'] at h
    exact h.symm
  exact ⟨⟨fun b => h1 atmPosn b, fun b b' => h2 atmLe b b', fun b => h1 atmTr b,
      fun b => h1 atmStart b, fun b => h1 atmAcc b, fun b => h1 atmBlank b,
      fun b => h1 atmRight b, fun b b' => h2 atmSrc b b', fun b b' => h2 atmRead b b',
      fun b b' => h2 atmDst b b', fun b b' => h2 atmWrite b b', fun b b' => h2 atmInp b b'⟩,
    fun j b => exists_congr fun h => h1 (atmBlk ⟨j, h⟩) b⟩


-- @@ L221-236 verbatim
/-- **Alternating machine acceptance.** Does the alternating machine described
by the instance accept its input within as many steps as there are positions?
The prefix starts with an existential block when `start` is `true`.

Both promises are folded into the yes-instances, as
`DescriptiveComplexity.NTMAccept` folds in
`DescriptiveComplexity.TMData.WellFormed`: the machine is well formed, and its
`k` block marks partition the states into blocks entered in order. -/
def ATMAccept (k : ℕ) (start : Bool) : DecisionProblem (Language.turingAlt k) where
  Holds := fun A inst => @TMData.WellFormed A (atmData k A).toTMData ∧
    @ATMData.BlocksWellFormed A (atmData k A) k ∧
    @ATMData.AltAccepts A (atmData k A) start
  iso_invariant := fun {A B} _ _ e => by
    have h := altAgree_of_equiv e
    exact (and_congr h.base.wellFormed
      (and_congr (h.blocksWellFormed k) (h.altAccepts start))).symm


-- @@ L238-238 verbatim
end Problem


-- @@ L240-244 verbatim
/-! ### Reading the block marks

The marks of the vocabulary are indexed by `Fin k`, so
`DescriptiveComplexity.ATMBlk` is `False` beyond `k` by construction; the two
lemmas below are the only unfolding the rest of the development needs. -/


-- @@ L246-246 verbatim
section Marks


-- @@ L248-248 verbatim
variable {k : ℕ} {A : Type} [(Language.turingAlt k).Structure A]


-- @@ L250-252 verbatim
/-- A marked state has a block index below `k`. -/
theorem lt_of_atmBlk {j : ℕ} {a : A} (h : ATMBlk (k := k) j a) : j < k :=
  h.1


-- @@ L254-257 verbatim
/-- The mark of a block, with its index bound supplied. -/
theorem atmBlk_iff {j : ℕ} (h : j < k) (a : A) :
    ATMBlk (k := k) j a ↔ RelMap (atmBlk (⟨j, h⟩ : Fin k)) ![a] :=
  ⟨fun hb => hb.2, fun hb => ⟨h, hb⟩⟩


-- @@ L259-259 verbatim
end Marks


-- @@ L261-266 verbatim
/-! ### The one-block instances

At `k = 1` the vocabulary has a single mark, the only block is `0` and its
polarity is that of `start`; so for `start = true` no state is universal, and
the alternating model is the nondeterministic one
(`DescriptiveComplexity.ATMData.altAccepts_true_iff_accepts`). -/


-- @@ L268-268 verbatim
section OneBlock


-- @@ L270-270 verbatim
variable {A : Type} [(Language.turingAlt 1).Structure A]


-- @@ L272-277 verbatim
/-- **At one block nothing is universal**, when the prefix starts
existentially: the only block is `0`, whose polarity is `true`. -/
theorem not_isUniv_one (q : A) : ¬(atmData 1 A).IsUniv true q := by
  rintro ⟨j, hj, hpol⟩
  obtain rfl : j = 0 := by have := lt_of_atmBlk (k := 1) hj; omega
  exact Bool.noConfusion hpol


-- @@ L279-296 verbatim
/-- **At one block, well-formedness of the block structure is just that every
state is marked.** Uniqueness and monotonicity are automatic: there is only one
mark to carry. -/
theorem blocksWellFormed_one_iff :
    (atmData 1 A).BlocksWellFormed 1 ↔ ∀ q : A, ATMBlk (k := 1) 0 q := by
  constructor
  · intro h q
    obtain ⟨j, hjk, hj, -⟩ := h.1 q
    obtain rfl : j = 0 := by omega
    exact hj
  · intro h
    refine ⟨fun q => ⟨0, by omega, h q, fun j' hj' => ?_⟩,
      fun τ q q' j j' _ _ _ hj hj' => ?_, fun q _ => h q⟩
    · have := lt_of_atmBlk (k := 1) hj'
      omega
    · have h1 := lt_of_atmBlk (k := 1) hj
      have h2 := lt_of_atmBlk (k := 1) hj'
      omega


-- @@ L298-298 verbatim
end OneBlock


-- @@ L300-300 verbatim
end DescriptiveComplexity
