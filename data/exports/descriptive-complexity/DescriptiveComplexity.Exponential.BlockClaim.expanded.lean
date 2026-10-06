/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Exponential.Copies
import DescriptiveComplexity.Composition


-- @@ L9-55 verbatim
/-!
# Claiming the block atoms of a quantifier-free matrix

The second of the two normal forms that let a *machine* evaluate a fixed
first-order sentence with a finite control.
`DescriptiveComplexity.Exponential.AltQuant` turned a sentence into an
alternating prefix over a quantifier-free matrix; the matrix still mentions the
block, whose atoms live on the machine's tape and are not available to a
transition. This file removes them:

> a quantifier-free matrix over two copies of a block is a **base formula**
> determined by the truth values of finitely many block atoms, whose addresses
> are read off the valuation.

`DescriptiveComplexity.exists_blockClaims` produces the finite list of
occurrences (`DescriptiveComplexity.BlockAtom`: a copy, a relation variable, and
where its arguments sit among the matrix's variables) and, for each vector of
*claimed* truth values, the base formula the matrix becomes.

## What a machine does with it

The claims are `Bool`s and the statement is conditional on their correctness,
which is exactly the shape of the standard alternating check: the existential
player claims the whole vector `b` in one move – there are finitely many, so
this is one nondeterministic transition – the universal player then either
challenges one claim, which the machine settles by a single tape lookup at the
address `(copy, var, args)` names, or lets the base formula be evaluated. The
base formula has no block atoms left, so it is a condition on the source
structure alone: a *guard of the transition relation*, written by the
interpretation that emits the machine, and never something the machine has to
compute.

Everything is stated for the two-copy structure
`DescriptiveComplexity.SOBlock.structure₂`, the shape of an
`DescriptiveComplexity.SOGameSpec.move`.

## The relation symbols are named

A relation symbol of the two-copy language is a nested `Sum`, and a goal
mentioning a raw `Sum.inl (Sum.inl r)` is ill-typed at `implicit`
transparency – `Language.sum` has to be unfolded for it to typecheck – so
`rw` and `simp` fail on it. The three shapes are therefore named
(`DescriptiveComplexity.twoBaseSym`, `DescriptiveComplexity.twoFstSym`,
`DescriptiveComplexity.twoSndSym`), the case analysis goes through
`DescriptiveComplexity.exists_symCase`, and every realization lemma is stated
at a named symbol.
-/


-- @@ L57-57 verbatim
namespace DescriptiveComplexity


-- @@ L59-59 verbatim
open FirstOrder


-- @@ L61-61 verbatim
open Language BoundedFormula


-- @@ L63-63 verbatim
/-! ### An occurrence of a block atom -/


-- @@ L65-77 verbatim
/-- **An occurrence of a block atom in a matrix**: which of the two copies of
the block it reads, which relation variable of the block, and where each of its
arguments sits among the matrix's variables.

This is an *address*: on a machine's tape the cell it names is
`(copy, var, args applied to the valuation)`. -/
structure BlockAtom (B : SOBlock) (n : ℕ) where
  /-- The copy of the block the occurrence reads: `false` is the first copy. -/
  copy : Bool
  /-- The relation variable of the block. -/
  var : B.ι
  /-- Where the arguments of the occurrence sit among the matrix's variables. -/
  args : Fin (B.arity var) → Fin n


-- @@ L79-79 verbatim
namespace BlockAtom


-- @@ L81-81 verbatim
variable {B : SOBlock} {n : ℕ} {A : Type}


-- @@ L83-85 verbatim
/-- The truth value of an occurrence, under two assignments and a valuation. -/
def Holds (a : BlockAtom B n) (ρ σ : B.Assignment A) (v : Fin n → A) : Prop :=
  cond a.copy σ ρ a.var fun j => v (a.args j)


-- @@ L87-87 verbatim
end BlockAtom


-- @@ L89-89 verbatim
/-! ### The relation symbols of the two-copy language -/


-- @@ L91-91 verbatim
section Symbols


-- @@ L93-93 verbatim
variable {K : Language.{0, 0}} {B : SOBlock} {l : ℕ}


-- @@ L95-97 verbatim
/-- A relation symbol of the base vocabulary, read in the two-copy language. -/
abbrev twoBaseSym (r : K.Relations l) : ((K.sum B.lang).sum B.lang).Relations l :=
  Sum.inl (Sum.inl r)


-- @@ L99-101 verbatim
/-- A relation variable of the *first* copy of the block. -/
abbrev twoFstSym (s : B.lang.Relations l) : ((K.sum B.lang).sum B.lang).Relations l :=
  Sum.inl (Sum.inr s)


-- @@ L103-105 verbatim
/-- A relation variable of the *second* copy of the block. -/
abbrev twoSndSym (s : B.lang.Relations l) : ((K.sum B.lang).sum B.lang).Relations l :=
  Sum.inr s


-- @@ L107-114 verbatim
/-- **The three shapes of a relation symbol of the two-copy language.** -/
theorem exists_symCase (R : ((K.sum B.lang).sum B.lang).Relations l) :
    (∃ r, R = twoBaseSym (B := B) r) ∨ (∃ s, R = twoFstSym (K := K) s) ∨
      (∃ s, R = twoSndSym (K := K) s) := by
  match R with
  | Sum.inl (Sum.inl r) => exact Or.inl ⟨r, rfl⟩
  | Sum.inl (Sum.inr s) => exact Or.inr (Or.inl ⟨s, rfl⟩)
  | Sum.inr s => exact Or.inr (Or.inr ⟨s, rfl⟩)


-- @@ L116-116 verbatim
end Symbols


-- @@ L118-118 verbatim
/-! ### Realization at the two-copy structure -/


-- @@ L120-120 verbatim
section TwoRealize


-- @@ L122-122 verbatim
variable {K : Language.{0, 0}} {B : SOBlock} {A : Type} [K.Structure A] {n : ℕ}


-- @@ L124-129 verbatim
/-- Realization of a formula over two stacked copies of a block, at the
assignments `ρ` (first copy) and `σ` (second). -/
def twoRealize (mat : ((K.sum B.lang).sum B.lang).BoundedFormula Empty n)
    (ρ σ : B.Assignment A) (v : Fin n → A) : Prop :=
  letI := B.structure₂ (L := K) ρ σ
  mat.Realize default v


-- @@ L131-131 verbatim
variable (ρ σ : B.Assignment A) (v : Fin n → A)


-- @@ L133-135 verbatim
theorem twoRealize_bot :
    ¬ twoRealize (⊥ : ((K.sum B.lang).sum B.lang).BoundedFormula Empty n) ρ σ v :=
  id


-- @@ L137-140 verbatim
theorem twoRealize_imp (φ₁ φ₂ : ((K.sum B.lang).sum B.lang).BoundedFormula Empty n) :
    twoRealize (φ₁.imp φ₂) ρ σ v ↔ (twoRealize φ₁ ρ σ v → twoRealize φ₂ ρ σ v) :=
  letI := B.structure₂ (L := K) ρ σ
  realize_imp


-- @@ L142-142 verbatim
end TwoRealize


-- @@ L144-144 verbatim
/-! ### Every quantifier-free matrix is a base formula plus claims -/


-- @@ L146-146 verbatim
section Claims


-- @@ L148-149 verbatim
variable {K : Language.{0, 0}} [K.IsRelational] {B : SOBlock} {n : ℕ} {A : Type}
  [K.Structure A] {ρ σ : B.Assignment A}


-- @@ L151-153 verbatim
/-- The bound variable a term of a relational language over `Empty ⊕ Fin n`
reads. -/
def bvarOf (x : Empty ⊕ Fin n) : Fin n := Sum.elim (fun e => e.elim) id x


-- @@ L155-159 verbatim
theorem elim_bvarOf (v : Fin n → A) (d : Empty → A) (x : Empty ⊕ Fin n) :
    Sum.elim d v x = v (bvarOf x) := by
  cases x with
  | inl e => exact e.elim
  | inr _ => rfl


-- @@ L161-161 verbatim
variable {v : Fin n → A}


-- @@ L163-168 verbatim
/-- An equality of the matrix is an equality of two of its variables. -/
theorem twoRealize_bdEqual (t₁ t₂ : ((K.sum B.lang).sum B.lang).Term (Empty ⊕ Fin n)) :
    twoRealize (t₁.bdEqual t₂) ρ σ v ↔ v (bvarOf t₁.varOf) = v (bvarOf t₂.varOf) := by
  let := B.structure₂ (L := K) ρ σ
  change (t₁.bdEqual t₂).Realize default v ↔ _
  rw [realize_bdEqual, Term.realize_varOf, Term.realize_varOf, elim_bvarOf, elim_bvarOf]


-- @@ L170-177 verbatim
/-- The arguments of an atom, realized: they are the variables they name. -/
private theorem args_eq {l : ℕ}
    (ts : Fin l → ((K.sum B.lang).sum B.lang).Term (Empty ⊕ Fin n)) :
    letI := B.structure₂ (L := K) ρ σ
    (fun q => Term.realize (Sum.elim (default : Empty → A) v) (ts q)) =
      fun q => v (bvarOf (ts q).varOf) := by
  let := B.structure₂ (L := K) ρ σ
  exact funext fun q => by rw [Term.realize_varOf, elim_bvarOf]


-- @@ L179-187 verbatim
/-- A base atom of the matrix is the same atom of the base structure. -/
theorem twoRealize_base {l : ℕ} (r : K.Relations l)
    (ts : Fin l → ((K.sum B.lang).sum B.lang).Term (Empty ⊕ Fin n)) :
    twoRealize (Relations.boundedFormula (twoBaseSym (B := B) r) ts) ρ σ v ↔
      Structure.RelMap r fun q => v (bvarOf (ts q).varOf) := by
  let := B.structure₂ (L := K) ρ σ
  change (Relations.boundedFormula (twoBaseSym (B := B) r) ts).Realize default v ↔ _
  rw [realize_rel, args_eq (ρ := ρ) (σ := σ) ts]
  exact Iff.rfl


-- @@ L189-198 verbatim
/-- An atom of the first copy is the first assignment, read at the addresses
its arguments name. -/
theorem twoRealize_fst {l : ℕ} (s : B.lang.Relations l)
    (ts : Fin l → ((K.sum B.lang).sum B.lang).Term (Empty ⊕ Fin n)) :
    twoRealize (Relations.boundedFormula (twoFstSym (K := K) s) ts) ρ σ v ↔
      ρ s.1 fun j => v (bvarOf (ts (Fin.cast s.2 j)).varOf) := by
  let := B.structure₂ (L := K) ρ σ
  change (Relations.boundedFormula (twoFstSym (K := K) s) ts).Realize default v ↔ _
  rw [realize_rel, args_eq (ρ := ρ) (σ := σ) ts]
  exact Iff.rfl


-- @@ L200-209 verbatim
/-- An atom of the second copy is the second assignment, read at the addresses
its arguments name. -/
theorem twoRealize_snd {l : ℕ} (s : B.lang.Relations l)
    (ts : Fin l → ((K.sum B.lang).sum B.lang).Term (Empty ⊕ Fin n)) :
    twoRealize (Relations.boundedFormula (twoSndSym (K := K) s) ts) ρ σ v ↔
      σ s.1 fun j => v (bvarOf (ts (Fin.cast s.2 j)).varOf) := by
  let := B.structure₂ (L := K) ρ σ
  change (Relations.boundedFormula (twoSndSym (K := K) s) ts).Realize default v ↔ _
  rw [realize_rel, args_eq (ρ := ρ) (σ := σ) ts]
  exact Iff.rfl


-- @@ L211-269 verbatim
/-- **A quantifier-free matrix over two copies of a block is a base formula
determined by the truth values of finitely many block atoms.**

The atoms are listed once and for all; the base formula depends on the vector
of *claimed* values, and the equivalence holds as soon as the claims are
correct. That conditional form is what a machine needs: it guesses `b`, has the
claims challenged one at a time by tape lookups, and evaluates the base formula
as a guard of its transition relation. -/
theorem exists_blockClaims :
    ∀ {mat : ((K.sum B.lang).sum B.lang).BoundedFormula Empty n}, mat.IsQF →
      ∃ (m : ℕ) (atoms : Fin m → BlockAtom B n)
        (sub : (Fin m → Bool) → K.BoundedFormula Empty n),
        ∀ (A : Type) [K.Structure A] (ρ σ : B.Assignment A) (v : Fin n → A) (b : Fin m → Bool),
          (∀ j, b j = true ↔ (atoms j).Holds ρ σ v) →
          (twoRealize mat ρ σ v ↔ (sub b).Realize default v) := by
  intro mat h
  induction h with
  | falsum =>
    exact ⟨0, Fin.elim0, fun _ => ⊥, fun A _ ρ σ v b _ =>
      ⟨fun hc => (twoRealize_bot ρ σ v hc).elim, fun hc => hc.elim⟩⟩
  | @of_isAtomic φ ha =>
    cases ha with
    | equal t₁ t₂ =>
      refine ⟨0, Fin.elim0, fun _ => (Term.var (Sum.inr (bvarOf t₁.varOf)) :
          K.Term (Empty ⊕ Fin n)).bdEqual (Term.var (Sum.inr (bvarOf t₂.varOf))),
        fun A _ ρ σ v b _ => ?_⟩
      rw [twoRealize_bdEqual t₁ t₂, realize_bdEqual]
      rfl
    | rel R ts =>
      rcases exists_symCase R with ⟨r, rfl⟩ | ⟨s, rfl⟩ | ⟨s, rfl⟩
      · refine ⟨0, Fin.elim0,
          fun _ => r.boundedFormula fun q => Term.var (Sum.inr (bvarOf (ts q).varOf)),
          fun A _ ρ σ v b _ => ?_⟩
        rw [twoRealize_base r ts, realize_rel]
        rfl
      · refine ⟨1, fun _ => ⟨false, s.1, fun j => bvarOf (ts (Fin.cast s.2 j)).varOf⟩,
          fun b => if b 0 = true then ⊤ else ⊥, fun A _ ρ σ v b hb => ?_⟩
        have hb0 : b 0 = true ↔ ρ s.1 fun j => v (bvarOf (ts (Fin.cast s.2 j)).varOf) := hb 0
        rw [twoRealize_fst s ts, ← hb0]
        cases hv : b 0 <;> simp [hv]
      · refine ⟨1, fun _ => ⟨true, s.1, fun j => bvarOf (ts (Fin.cast s.2 j)).varOf⟩,
          fun b => if b 0 = true then ⊤ else ⊥, fun A _ ρ σ v b hb => ?_⟩
        have hb0 : b 0 = true ↔ σ s.1 fun j => v (bvarOf (ts (Fin.cast s.2 j)).varOf) := hb 0
        rw [twoRealize_snd s ts, ← hb0]
        cases hv : b 0 <;> simp [hv]
  | @imp φ₁ φ₂ _ _ ih₁ ih₂ =>
    obtain ⟨m₁, atoms₁, sub₁, hsub₁⟩ := ih₁
    obtain ⟨m₂, atoms₂, sub₂, hsub₂⟩ := ih₂
    refine ⟨m₁ + m₂, Fin.addCases (motive := fun _ => BlockAtom B n) atoms₁ atoms₂,
      fun b => (sub₁ fun j => b (Fin.castAdd m₂ j)).imp (sub₂ fun j => b (Fin.natAdd m₁ j)),
      fun A _ ρ σ v b hb => ?_⟩
    have hb₁ : ∀ j, b (Fin.castAdd m₂ j) = true ↔ (atoms₁ j).Holds ρ σ v := by
      intro j
      rw [hb (Fin.castAdd m₂ j), Fin.addCases_left]
    have hb₂ : ∀ j, b (Fin.natAdd m₁ j) = true ↔ (atoms₂ j).Holds ρ σ v := by
      intro j
      rw [hb (Fin.natAdd m₁ j), Fin.addCases_right]
    rw [twoRealize_imp, realize_imp]
    exact imp_congr (hsub₁ A ρ σ v _ hb₁) (hsub₂ A ρ σ v _ hb₂)


-- @@ L271-271 verbatim
end Claims


-- @@ L273-273 verbatim
end DescriptiveComplexity
