/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.SecondOrderMerge


-- @@ L8-36 verbatim
/-!
# A quantifier prefix of `k` copies of one block

The shape every `Σₖ` definition in this library has: `k` alternating blocks
that are all *the same* block, one per round of whatever the definition
describes – one truth assignment per quantifier block for
`DescriptiveComplexity.QBF`, one run per round of the game for the machine
bridge of the polynomial hierarchy.

`DescriptiveComplexity.SecondOrderMerge` collapses a prefix into a single
block, at the cost of turning the alternation into
`DescriptiveComplexity.altAssign`, an alternating quantification over the
*pieces* of one merged assignment. That is awkward to use: the pieces are
indexed by the shape of the merge rather than by the round. This file removes
the awkwardness when all the blocks are equal:

* `DescriptiveComplexity.repBlockAssign` assembles a merged assignment out of a
  family `Fin k → B.Assignment A`, one per round (`DescriptiveComplexity.QBF`'s
  own `repAssign` is its monadic special case, and should be folded into it);
* `DescriptiveComplexity.repSym` names the relation variable of the `i`-th
  round, and `DescriptiveComplexity.relMap_repSym` reads it back;
* `DescriptiveComplexity.altBlockQuant` is the alternating quantification over
  such a family, and `DescriptiveComplexity.altAssign_repBlocks` identifies it
  with `altAssign`.

Nothing here is specific to a block: the symbol and the assignment are built by
the same recursion on `k`, so the reading lemma is `Iff.rfl` at the head and the
induction hypothesis at the tail.
-/


-- @@ L38-38 verbatim
namespace DescriptiveComplexity


-- @@ L40-40 verbatim
open FirstOrder


-- @@ L42-42 verbatim
open Language Structure


-- @@ L44-44 verbatim
/-! ### The prefix and its merge -/


-- @@ L46-47 verbatim
/-- A quantifier prefix of `k` copies of the block `B`. -/
abbrev repBlocks (B : SOBlock) (k : ℕ) : List SOBlock := List.replicate k B


-- @@ L49-51 verbatim
@[simp]
theorem repBlocks_length (B : SOBlock) (k : ℕ) : (repBlocks B k).length = k :=
  List.length_replicate ..


-- @@ L53-54 verbatim
/-- The single block merging a prefix of `k` copies of `B`. -/
abbrev repMerged (B : SOBlock) (k : ℕ) : SOBlock := mergeBlocks (repBlocks B k)


-- @@ L56-65 verbatim
/-- The relation variable of `B` used by the `i`-th round, as a symbol of the
merged block's vocabulary. The arity proof is carried along the recursion, so
that reading the symbol back needs no cast. -/
def repSym (B : SOBlock) {n : ℕ} (x : B.ι) (h : B.arity x = n) :
    ∀ (k : ℕ), Fin k → (repMerged B k).lang.Relations n
  | 0, i => i.elim0
  | _ + 1, ⟨0, _⟩ => ⟨Sum.inl x, h⟩
  | k + 1, ⟨j + 1, hj⟩ =>
      ⟨Sum.inr (repSym B x h k ⟨j, Nat.lt_of_succ_lt_succ hj⟩).1,
        (repSym B x h k ⟨j, Nat.lt_of_succ_lt_succ hj⟩).2⟩


-- @@ L67-71 verbatim
/-- The merged assignment determined by one assignment of `B` per round. -/
def repBlockAssign (B : SOBlock) (A : Type) : ∀ (k : ℕ), (Fin k → B.Assignment A) →
    (repMerged B k).Assignment A
  | 0, _ => nilAssign A
  | k + 1, ρs => consAssign (ρs 0) (repBlockAssign B A k fun i => ρs i.succ)


-- @@ L73-86 verbatim
/-- **Reading back the relation variable of a round.** -/
theorem relMap_repSym (B : SOBlock) {A : Type} {n : ℕ} (x : B.ι) (h : B.arity x = n) :
    ∀ (k : ℕ) (ρs : Fin k → B.Assignment A) (i : Fin k) (v : Fin n → A),
      @RelMap (repMerged B k).lang A ((repMerged B k).structure (repBlockAssign B A k ρs)) n
          (repSym B x h k i) v ↔ ρs i x fun j => v (Fin.cast h j) := by
  intro k
  induction k with
  | zero => intro _ i; exact i.elim0
  | succ k ih =>
    intro ρs i v
    obtain ⟨j, hj⟩ := i
    cases j with
    | zero => exact Iff.rfl
    | succ j => exact ih (fun i => ρs i.succ) ⟨j, Nat.lt_of_succ_lt_succ hj⟩ v


-- @@ L88-88 verbatim
/-! ### Alternating over the rounds -/


-- @@ L90-99 verbatim
/-- Alternating quantification over one assignment of `B` per round: the round
of index `0` is quantified outermost, existentially if `pol` is `true`, and the
polarities alternate inwards. -/
def altBlockQuant (A : Type) (B : SOBlock) :
    ∀ (k : ℕ), ((Fin k → B.Assignment A) → Prop) → Bool → Prop
  | 0, P, _ => P Fin.elim0
  | k + 1, P, true =>
      ∃ ρ : B.Assignment A, altBlockQuant A B k (fun ρs => P (Fin.cons ρ ρs)) false
  | k + 1, P, false =>
      ∀ ρ : B.Assignment A, altBlockQuant A B k (fun ρs => P (Fin.cons ρ ρs)) true


-- @@ L101-113 verbatim
/-- Alternating quantification over the rounds only depends on the quantified
predicate up to pointwise equivalence. -/
theorem altBlockQuant_congr {A : Type} {B : SOBlock} :
    ∀ (k : ℕ) (P Q : (Fin k → B.Assignment A) → Prop), (∀ ρs, P ρs ↔ Q ρs) →
      ∀ pol : Bool, altBlockQuant A B k P pol ↔ altBlockQuant A B k Q pol := by
  intro k
  induction k with
  | zero => intro P Q h pol; exact h _
  | succ k ih =>
    intro P Q h pol
    cases pol with
    | true => exact exists_congr fun ρ => ih _ _ (fun ρs => h _) false
    | false => exact forall_congr' fun ρ => ih _ _ (fun ρs => h _) true


-- @@ L115-141 verbatim
/-- **The prefix quantifies one assignment per round**: alternating over the
pieces of the merged assignment of `k` copies of `B` is alternating over `k`
assignments of `B`. -/
theorem altAssign_repBlocks (B : SOBlock) {A : Type} :
    ∀ (k : ℕ) (P : (repMerged B k).Assignment A → Prop) (pol : Bool),
      altAssign A (repBlocks B k) P pol ↔
        altBlockQuant A B k (fun ρs => P (repBlockAssign B A k ρs)) pol := by
  intro k
  induction k with
  | zero => intro P pol; exact Iff.rfl
  | succ k ih =>
    intro P pol
    have hrep : ∀ (ρ : B.Assignment A) (ρs : Fin k → B.Assignment A),
        repBlockAssign B A (k + 1) (Fin.cons ρ ρs) = consAssign ρ (repBlockAssign B A k ρs) := by
      intro ρ ρs
      simp only [repBlockAssign, Fin.cons_zero, Fin.cons_succ]
      rfl
    have key : ∀ ρ : B.Assignment A,
        altAssign A (repBlocks B k) (fun μ => P (consAssign ρ μ)) (!pol) ↔
          altBlockQuant A B k
            (fun ρs => P (repBlockAssign B A (k + 1) (Fin.cons ρ ρs))) (!pol) := by
      intro ρ
      refine (ih _ (!pol)).trans (altBlockQuant_congr k _ _ (fun ρs => ?_) (!pol))
      exact iff_of_eq (congrArg P (hrep ρ ρs).symm)
    cases pol with
    | true => exact exists_congr key
    | false => exact forall_congr' key


-- @@ L143-148 verbatim
/-! ### The definability statement

Put together: a sentence over the *single* merged block, transported into the
iterated expansion by `DescriptiveComplexity.unmergeHom`, is satisfied
alternately exactly when the `k` round assignments are quantified alternately.
This is the form a `Σₖ`-definability proof consumes. -/


-- @@ L150-157 verbatim
theorem sorealize_repBlocks (B : SOBlock) (L : Language.{0, 0}) (A : Type)
    (instL : L.Structure A) (k : ℕ) (ψ : (L.sum (repMerged B k).lang).Sentence) (pol : Bool) :
    @SORealize L A instL (repBlocks B k) ((unmergeHom (repBlocks B k) L).onSentence ψ) pol ↔
      altBlockQuant A B k (fun ρs =>
        @Sentence.Realize (L.sum (repMerged B k).lang) A
          (@sumStructure L (repMerged B k).lang A instL
            ((repMerged B k).structure (repBlockAssign B A k ρs))) ψ) pol :=
  (sorealize_unmerge (repBlocks B k) L A instL ψ pol).trans (altAssign_repBlocks B k _ pol)


-- @@ L159-159 verbatim
end DescriptiveComplexity
