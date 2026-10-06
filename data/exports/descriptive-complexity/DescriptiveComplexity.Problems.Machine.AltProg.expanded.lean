/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Machine.AltTape
import DescriptiveComplexity.Problems.Qbf.Defs
import DescriptiveComplexity.MachinesAlt


-- @@ L10-58 verbatim
/-!
# The machine of a quantified Boolean formula

The program half of `QBF k ≤ᶠᵒ[≤] ATMAccept k`: the states, symbols and
transitions of the alternating machine `M_φ` built inside an ordered QBF
instance, on the tape laid out in
`DescriptiveComplexity.Problems.Machine.AltTape`.

## The program

```
  sweep i:  ⊢ →  at each cell (x, b): if block i marks x and b is false,
                 write true or leave it – the round's choice        → ⊣
            ⊣ ←  back over the cells, unchanged                     → ⊢
            at ⊢: hand over to sweep i + 1, or start the check
  check c:  sweep over the cells accumulating
              flag := flag ∨ (the literal of c at this cell is `good`)
            at the far marker: settle the clause, or die
  accept:   the check has settled every clause
```

Three things differ from the SAT machine of
`DescriptiveComplexity.Problems.Machine.Hardness`.

**The guess is spread over `k` sweeps, and it accumulates.** A cell holds one
truth value, initially `false`, and sweep `i` may turn it to `true` when block
`i` marks the variable – never back. After the `k` sweeps the cell holds
`DescriptiveComplexity.qbfVal`, which is a disjunction over the blocks marking
the variable. So there are two transitions available at a cell block `i` marks
and holds `false`, and one everywhere else: the choice a round makes is exactly
its block's truth assignment.

**Only the guess is nondeterministic**, as in the SAT machine – which is what
makes the check work at either polarity: a universal block whose configuration
has a single available move is an existential one.

**The check serves both matrix shapes.** For a conjunctive matrix the flag
records that some literal of the clause is *satisfied*, and a clause is settled
when the flag is set; for a disjunctive one it records that some literal is
*violated*, and a term is settled – by accepting – when the flag is *clear*.
The two are the same clause with the truth value flipped
(`DescriptiveComplexity.AltQbf.xorB`), which is why one table serves both.

## Semantics first

Everything here is a plain predicate on tagged tuples: the machine is assembled
as a `DescriptiveComplexity.ATMData` and reasoned about directly. Only once its
correctness is proved does the first-order transcription happen.
-/


-- @@ L60-60 verbatim
namespace DescriptiveComplexity


-- @@ L62-62 verbatim
namespace AltQbf


-- @@ L64-64 verbatim
open FirstOrder


-- @@ L66-66 verbatim
open Language Structure


-- @@ L68-68 verbatim
noncomputable section Machine


-- @@ L70-70 verbatim
variable {k : ℕ} {A : Type} [(Language.qbf k).Structure A] [LinearOrder A] [Finite A] [Nonempty A]


-- @@ L72-72 verbatim
/-! ### The instance, read -/


-- @@ L74-76 verbatim
variable (k) in
/-- Being a clause – a term, for a disjunctive matrix – of the instance. -/
def QbfCl (c : A) : Prop := RelMap (qbfIsClause (k := k)) ![c]


-- @@ L78-80 verbatim
variable (k) in
/-- The variable `x` occurs positively in the clause `c`. -/
def QbfPos (c x : A) : Prop := RelMap (qbfPosIn (k := k)) ![c, x]


-- @@ L82-84 verbatim
variable (k) in
/-- The variable `x` occurs negatively in the clause `c`. -/
def QbfNeg (c x : A) : Prop := RelMap (qbfNegIn (k := k)) ![c, x]


-- @@ L86-87 verbatim
/-- The variable `x` carries the mark of block `i`. -/
def QbfBlk (i : Fin k) (x : A) : Prop := RelMap (qbfBlock i) ![x]


-- @@ L89-91 verbatim
/-- The variable `x` carries the mark of the block of index `i`, where `i` is
allowed to be the sentinel `k`: at the sentinel, no mark. -/
def QbfBlkAt (i : Fin (k + 1)) (x : A) : Prop := ∃ j : Fin k, (j : ℕ) = (i : ℕ) ∧ QbfBlk j x


-- @@ L93-98 verbatim
variable (k) in
/-- **The literal test**: the cell `x`, holding the truth value `v`, satisfies
the clause `c`. This is the first-order test on the source structure that the
transition relation performs. -/
def QbfLit (c x : A) (v : Bool) : Prop :=
  (QbfPos k c x ∧ v = true) ∨ (QbfNeg k c x ∧ v = false)


-- @@ L100-103 verbatim
/-- The truth value the check phase tests: the value itself for a conjunctive
matrix, its negation for a disjunctive one, so that the flag records a
satisfied literal in the first case and a violated one in the second. -/
def xorB (cnf v : Bool) : Bool := if cnf then v else !v


-- @@ L105-107 verbatim
variable (k) in
/-- `c` is the lowest clause. -/
def QbfMinCl (c : A) : Prop := QbfCl k c ∧ ∀ e, QbfCl k e → c ≤ e


-- @@ L109-111 verbatim
variable (k) in
/-- `c` is the highest clause. -/
def QbfMaxCl (c : A) : Prop := QbfCl k c ∧ ∀ e, QbfCl k e → e ≤ c


-- @@ L113-116 verbatim
variable (k) in
/-- `c'` is the clause immediately above `c`. -/
def QbfNextCl (c c' : A) : Prop :=
  QbfCl k c ∧ QbfCl k c' ∧ c < c' ∧ ∀ e, QbfCl k e → c < e → c' ≤ e


-- @@ L118-118 verbatim
/-! ### The elements of the machine -/


-- @@ L120-122 verbatim
/-- The least element of the instance, to which every constant of the machine
is pinned. -/
def qbotA : A := (Finite.exists_min (id : A → A)).choose


-- @@ L124-125 verbatim
omit [(Language.qbf k).Structure A] in
theorem qbotA_le (a : A) : qbotA (A := A) ≤ a := (Finite.exists_min (id : A → A)).choose_spec a


-- @@ L127-128 verbatim
omit [(Language.qbf k).Structure A] in
theorem isMinTup2_qbot : IsMinTup2 (fun _ => qbotA (A := A)) := ⟨qbotA_le, qbotA_le⟩


-- @@ L130-132 verbatim
variable (k A) in
/-- The universe of the machine: tagged pairs. -/
abbrev AltV : Type := AltTag k × (Fin 2 → A)


-- @@ L134-135 verbatim
/-- A constant of the machine at the sweep index `i`. -/
def acstI (t : AltBase) (i : Fin (k + 1)) : AltV k A := ((t, i), fun _ => qbotA)


-- @@ L137-138 verbatim
/-- A tag carrying one element at the sweep index `i`. -/
def aoneI (t : AltBase) (i : Fin (k + 1)) (a : A) : AltV k A := ((t, i), ![a, qbotA])


-- @@ L140-141 verbatim
/-- A constant of the machine: a tag on the pair of least elements. -/
abbrev acst (t : AltBase) : AltV k A := acstI t 0


-- @@ L143-144 verbatim
/-- A tag carrying one element, pinned in the second coordinate. -/
abbrev aone (t : AltBase) (a : A) : AltV k A := aoneI t 0 a


-- @@ L146-146 verbatim
/-! #### Symbols -/


-- @@ L148-149 verbatim
/-- The left-marker symbol. -/
abbrev symStart : AltV k A := acst .sStart


-- @@ L151-152 verbatim
/-- The right-marker symbol. -/
abbrev symEnd : AltV k A := acst .sEnd


-- @@ L154-155 verbatim
/-- The blank symbol. -/
abbrev symBlank : AltV k A := acst .sBlank


-- @@ L157-158 verbatim
/-- The symbol of the cell of `x`, holding the truth value `v`. -/
abbrev symV (v : Bool) (x : A) : AltV k A := aone (.sVal v) x


-- @@ L160-160 verbatim
/-! #### Positions -/


-- @@ L162-163 verbatim
/-- The left-marker cell. -/
abbrev posStart : AltV k A := acst .pStart


-- @@ L165-166 verbatim
/-- The cell of the element `x`. -/
abbrev posCell (x : A) : AltV k A := aone .pCell x


-- @@ L168-169 verbatim
/-- The right-marker cell. -/
abbrev posEnd : AltV k A := acst .pEnd


-- @@ L171-171 verbatim
/-! #### States -/


-- @@ L173-175 verbatim
/-- Sweeping in direction `d` during the sweep of index `i`. The index runs
over `Fin (k + 1)`, but only the values below `k` are ever reached. -/
abbrev stG (i : Fin (k + 1)) (d : Bool) : AltV k A := acstI (.qG d) i


-- @@ L177-178 verbatim
/-- Checking the clause `c`, flag `f`, sweeping in direction `d`. -/
abbrev stChk (f d : Bool) (c : A) : AltV k A := aone (.qChk f d) c


-- @@ L180-181 verbatim
/-- The accepting state. -/
abbrev stAcc : AltV k A := acst .qAcc


-- @@ L183-183 verbatim
/-! ### The transition table -/


-- @@ L185-203 verbatim
/-- Which tagged tuples are transitions. The payload is pinned exactly as far
as the transition needs it, the sweep index is required to be a real sweep, and
the clause coordinates are required to be clauses, so that no junk element is
ever a transition. -/
def AltTr (cnf : Bool) (τ : AltV k A) : Prop :=
  match τ.1.1 with
  | .tGStart => IsMinTup2 τ.2 ∧ (τ.1.2 : ℕ) = 0 ∧ 0 < k
  | .tGKeep _ => (∀ a : A, τ.2 1 ≤ a) ∧ (τ.1.2 : ℕ) < k
  | .tGSet => (∀ a : A, τ.2 1 ≤ a) ∧ QbfBlkAt τ.1.2 (τ.2 0)
  | .tGTurn => IsMinTup2 τ.2 ∧ (τ.1.2 : ℕ) < k
  | .tGBack _ => (∀ a : A, τ.2 1 ≤ a) ∧ (τ.1.2 : ℕ) < k
  | .tGNext => IsMinTup2 τ.2 ∧ (τ.1.2 : ℕ) + 1 < k
  | .tGEndAcc => IsMinTup2 τ.2 ∧ (τ.1.2 : ℕ) + 1 = k ∧ cnf = true ∧ ∀ e : A, ¬QbfCl k e
  | .tGEndChk => (∀ a : A, τ.2 1 ≤ a) ∧ (τ.1.2 : ℕ) + 1 = k ∧ QbfMinCl k (τ.2 0)
  | .tChk _ _ _ => QbfCl k (τ.2 0) ∧ (τ.1.2 : ℕ) = 0
  | .tTurnNext _ => QbfNextCl k (τ.2 0) (τ.2 1) ∧ (τ.1.2 : ℕ) = 0
  | .tTurnAcc _ =>
      (∀ a : A, τ.2 1 ≤ a) ∧ (τ.1.2 : ℕ) = 0 ∧ QbfCl k (τ.2 0) ∧ (cnf = true → QbfMaxCl k (τ.2 0))
  | _ => False


-- @@ L205-222 verbatim
/-- The state a transition applies in. The accepting turn fires at the flag
`cnf`: set, for a conjunctive matrix, where it means the clause is satisfied;
clear, for a disjunctive one, where it means no literal of the term is
violated. -/
def AltSrc (cnf : Bool) (τ q : AltV k A) : Prop :=
  match τ.1.1 with
  | .tGStart => q = stG τ.1.2 true
  | .tGKeep _ => q = stG τ.1.2 true
  | .tGSet => q = stG τ.1.2 true
  | .tGTurn => q = stG τ.1.2 true
  | .tGBack _ => q = stG τ.1.2 false
  | .tGNext => q = stG τ.1.2 false
  | .tGEndAcc => q = stG τ.1.2 false
  | .tGEndChk => q = stG τ.1.2 false
  | .tChk _ f d => q = stChk f d (τ.2 0)
  | .tTurnNext d => q = stChk true d (τ.2 0)
  | .tTurnAcc d => q = stChk cnf d (τ.2 0)
  | _ => False


-- @@ L224-238 verbatim
/-- The symbol a transition reads. -/
def AltRead (τ a : AltV k A) : Prop :=
  match τ.1.1 with
  | .tGStart => a = symStart
  | .tGKeep b => a = symV b (τ.2 0)
  | .tGSet => a = symV false (τ.2 0)
  | .tGTurn => a = symEnd
  | .tGBack b => a = symV b (τ.2 0)
  | .tGNext => a = symStart
  | .tGEndAcc => a = symStart
  | .tGEndChk => a = symStart
  | .tChk v _ _ => a = symV v (τ.2 1)
  | .tTurnNext d => a = if d then symEnd else symStart
  | .tTurnAcc d => a = if d then symEnd else symStart
  | _ => False


-- @@ L240-258 verbatim
/-- The state a transition moves to. The only place the instance is consulted
is the check clause, where the new flag depends on
`DescriptiveComplexity.AltQbf.QbfLit`. -/
def AltDst (cnf : Bool) (τ q : AltV k A) : Prop :=
  match τ.1.1 with
  | .tGStart => q = stG τ.1.2 true
  | .tGKeep _ => q = stG τ.1.2 true
  | .tGSet => q = stG τ.1.2 true
  | .tGTurn => q = stG τ.1.2 false
  | .tGBack _ => q = stG τ.1.2 false
  | .tGNext => q = stG (τ.1.2 + 1) true
  | .tGEndAcc => q = stAcc
  | .tGEndChk => q = stChk false true (τ.2 0)
  | .tChk v f d =>
      (q = stChk true d (τ.2 0) ∧ (f = true ∨ QbfLit k (τ.2 0) (τ.2 1) (xorB cnf v))) ∨
        (q = stChk false d (τ.2 0) ∧ f = false ∧ ¬QbfLit k (τ.2 0) (τ.2 1) (xorB cnf v))
  | .tTurnNext d => q = stChk false (!d) (τ.2 1)
  | .tTurnAcc _ => q = stAcc
  | _ => False


-- @@ L260-275 verbatim
/-- The symbol a transition writes: only a guessing sweep ever changes the
tape, and only from `false` to `true`. -/
def AltWrite (τ a : AltV k A) : Prop :=
  match τ.1.1 with
  | .tGStart => a = symStart
  | .tGKeep b => a = symV b (τ.2 0)
  | .tGSet => a = symV true (τ.2 0)
  | .tGTurn => a = symEnd
  | .tGBack b => a = symV b (τ.2 0)
  | .tGNext => a = symStart
  | .tGEndAcc => a = symStart
  | .tGEndChk => a = symStart
  | .tChk v _ _ => a = symV v (τ.2 1)
  | .tTurnNext d => a = if d then symEnd else symStart
  | .tTurnAcc d => a = if d then symEnd else symStart
  | _ => False


-- @@ L277-292 verbatim
/-- Which transitions move the head right: a sweep goes in its own direction,
and every transition that fires at a marker moves away from it. -/
def AltRight (τ : AltV k A) : Prop :=
  match τ.1.1 with
  | .tGStart => True
  | .tGKeep _ => True
  | .tGSet => True
  | .tGTurn => False
  | .tGBack _ => False
  | .tGNext => True
  | .tGEndAcc => True
  | .tGEndChk => True
  | .tChk _ _ d => d = true
  | .tTurnNext d => d = false
  | .tTurnAcc d => d = false
  | _ => False


-- @@ L294-295 verbatim
/-- Accepting states: just `DescriptiveComplexity.stAcc`. -/
def AltAccSt (q : AltV k A) : Prop := q.1.1 = AltBase.qAcc


-- @@ L297-298 verbatim
/-- Start states: the rightward sweep of index `0`. -/
def AltStartSt (q : AltV k A) : Prop := q.1 = (AltBase.qG true, 0) ∧ IsMinTup2 q.2


-- @@ L300-309 verbatim
/-- The quantifier block an element belongs to: its sweep index for a sweeping
state, the last block for the check and the accepting state, and block `0` for
everything else – `DescriptiveComplexity.ATMData.BlocksWellFormed` asks *every*
element for a block, junk included. -/
def altBlockOf (q : AltV k A) : ℕ :=
  match q.1.1 with
  | .qG _ => if (q.1.2 : ℕ) < k then (q.1.2 : ℕ) else 0
  | .qChk _ _ => k - 1
  | .qAcc => k - 1
  | _ => 0


-- @@ L311-312 verbatim
/-- The block marks of the machine. -/
def AltBlkOf (j : ℕ) (q : AltV k A) : Prop := j = altBlockOf q


-- @@ L314-329 verbatim
variable (k A) in
/-- **The alternating machine of a quantified Boolean formula.** -/
def altMachine (cnf : Bool) : ATMData (AltV k A) where
  Posn := AltPosn
  Le := tagTupleLe
  Tr := AltTr cnf
  Start := AltStartSt
  Acc := AltAccSt
  Blank := AltBlank
  Right := AltRight
  Src := AltSrc cnf
  Read := AltRead
  Dst := AltDst cnf
  Write := AltWrite
  Inp := AltInp
  Blk := AltBlkOf


-- @@ L331-335 verbatim
/-! ### The instance obligations

Everything `DescriptiveComplexity.TMData.WellFormed` and
`DescriptiveComplexity.ATMData.BlocksWellFormed` ask, discharged before any run
is considered. -/


-- @@ L337-340 verbatim
theorem altMachine_wellFormed (cnf : Bool) :
    (altMachine k A cnf).toTMData.WellFormed :=
  ⟨isLinOrd_altTagTupleLe, exists_altPosn, fun _ _ _ ha hb => altInp_functional ha hb,
    exists_altBlank, fun _ _ ha hb => altBlank_unique ha hb⟩


-- @@ L342-351 verbatim
omit [(Language.qbf k).Structure A] [LinearOrder A] [Finite A] [Nonempty A] in
theorem altBlockOf_lt (hk : 0 < k) (q : AltV k A) : altBlockOf q < k := by
  unfold altBlockOf
  split
  · split
    · assumption
    · exact hk
  · omega
  · omega
  · exact hk


-- @@ L353-358 verbatim
omit [(Language.qbf k).Structure A] in
/-- A sweeping state's block is its sweep index. -/
theorem altBlockOf_stG {i : Fin (k + 1)} (hi : (i : ℕ) < k) (d : Bool) :
    altBlockOf (stG i d : AltV k A) = (i : ℕ) := by
  simp only [altBlockOf, acstI, stG]
  exact ite_eq_left hi


-- @@ L360-362 verbatim
omit [(Language.qbf k).Structure A] in
theorem altBlockOf_stChk (f d : Bool) (c : A) :
    altBlockOf (stChk f d c : AltV k A) = k - 1 := rfl


-- @@ L364-365 verbatim
omit [(Language.qbf k).Structure A] in
theorem altBlockOf_stAcc : altBlockOf (stAcc : AltV k A) = k - 1 := rfl


-- @@ L367-404 verbatim
/-- **The block structure is well formed**: every element has exactly one
block, a transition stays in its block or moves to the next one, and a start
state is in block `0`. -/
theorem altMachine_blocksWellFormed (cnf : Bool) (hk : 0 < k) :
    (altMachine k A cnf).BlocksWellFormed k := by
  refine ⟨fun q => ⟨altBlockOf q, altBlockOf_lt hk q, rfl, fun j' hj' => hj'⟩, ?_, ?_⟩
  · rintro τ q q' j j' hτ hsrc hdst rfl rfl
    revert hτ hsrc hdst
    change AltTr cnf τ → AltSrc cnf τ q → AltDst cnf τ q' →
      altBlockOf q ≤ altBlockOf q' ∧ altBlockOf q' ≤ altBlockOf q + 1
    unfold AltTr AltSrc AltDst
    cases hb : τ.1.1 <;> intro hτ hsrc hdst <;>
      first
        | exact hτ.elim
        | (subst hsrc; subst hdst; exact ⟨le_refl _, Nat.le_succ _⟩)
        | (subst hsrc
           rcases hdst with ⟨rfl, -⟩ | ⟨rfl, -, -⟩ <;> exact ⟨le_refl _, Nat.le_succ _⟩)
        | (subst hsrc; subst hdst
           have hne : τ.1.2 ≠ Fin.last k := by
             intro hcon
             rw [hcon] at hτ
             simp only [Fin.val_last] at hτ
             omega
           have hlt : ((τ.1.2 + 1 : Fin (k + 1)) : ℕ) = (τ.1.2 : ℕ) + 1 :=
             Fin.val_add_one_of_lt (Fin.lt_last_iff_ne_last.mpr hne)
           rw [altBlockOf_stG (show (τ.1.2 : ℕ) < k by omega) false,
             altBlockOf_stG (show ((τ.1.2 + 1 : Fin (k + 1)) : ℕ) < k by omega) true, hlt]
           omega)
        | (subst hsrc; subst hdst
           rw [altBlockOf_stG (show (τ.1.2 : ℕ) < k by omega) false, altBlockOf_stChk]
           omega)
        | (subst hsrc; subst hdst
           rw [altBlockOf_stG (show (τ.1.2 : ℕ) < k by omega) false, altBlockOf_stAcc]
           omega)
  · rintro q ⟨hq, -⟩
    change (0 : ℕ) = altBlockOf q
    simp only [altBlockOf, hq]
    exact (ite_eq_left hk).symm


-- @@ L406-406 verbatim
end Machine


-- @@ L408-408 verbatim
end AltQbf


-- @@ L410-410 verbatim
end DescriptiveComplexity
