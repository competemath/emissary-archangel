/-
Copyright (c) 2026 Tetsuya Ishiu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tetsuya Ishiu
-/
module

public import Mathlib.ModelTheory.Semantics


-- @@ L10-39 verbatim
/-!
# The Basics of First Order Language of ZFC set theory

## Main Definitions

- A `FirstOrder.Language.LZFC` defines the language of ZFC set theory.
  It consists only of the binary relation ∈'.
- A `FirstOrder.ZFC.fv'` defines the free variable with index k.
  The first argument is implicitly determined.
- A `FirstOrder.ZFC.bv'` defines the bounded variable with index (k : Fin n).
  The first argument is implicitly determined.
- A `FirstOrder.ZFC.bv''` defines the bounded variable with index (k : ℕ).
  The first argument is implicitly determined.
- A `FirsOrder.ZFC.ModelSets` is a class of models of set theory.

## Notations

- ∈' is the symbol to mean "is an element of".
- ∉' is the symbol to mean "is not an element of".
- ≠' is the symbol to mean "is not equal to".
  Recall that =' is defined as FirstOrder.Language.Term.bdEqual.
- ∈ is the actual relation to mean "is an element of".
- ∉ is the actual relation to mean "is not an element of".

## Implimentation notes

- Most of the relations have the theorems named "realize_*".
  They prove the relationship between the internal and external expressions.

-/


-- @@ L41-41 verbatim
@[expose] public section


-- @@ L43-43 verbatim
namespace FirstOrder

-- @@ L44-44 verbatim
open FirstOrder.Language

-- @@ L45-47 verbatim
open FirstOrder.Language.BoundedFormula

-- u for universe, v for free variable indexes

-- @@ L48-48 verbatim
universe u v


-- @@ L50-56 verbatim
/-- Relation symbols for LSet. -/
inductive LSetRel : ℕ → Type
| isEltOf : LSetRel 2
deriving DecidableEq

-- Instead of defining Relations n for each n,
-- define the entire Relations

-- @@ L57-57 verbatim
namespace Language


-- @@ L59-64 verbatim
/-- Language of Set Theory. -/
def LZFC : Language :=
{
  Functions := fun _ => Empty
  Relations := LSetRel
}


-- @@ L66-66 verbatim
end Language


-- @@ L68-68 verbatim
namespace ZFC


-- @@ L70-70 verbatim
variable {V : Type u} [Language.LZFC.Structure V]


-- @@ L72-75 verbatim
/-- The version of isEltOf with the type LSet.Relations 2. -/
def isEltOfTwo : Language.LZFC.Relations 2 := LSetRel.isEltOf

-- Language.BoundedFormula.falsum is the bot.

-- @@ L76-77 verbatim
/-- The formula ⊥ -/
def ϕbot : Language.LZFC.Formula  ℕ:= Language.BoundedFormula.falsum


-- @@ L79-83 verbatim
/-- Make an atomic formula t1 ∈ t2. -/
def ϕelt {n : ℕ} (t₁ t₂ : Language.LZFC.Term (ℕ ⊕ Fin n)) :=
  Language.Relations.boundedFormula₂ isEltOfTwo t₁ t₂

-- I added ' to distinguish the outside and inside ∈

-- @@ L84-84 verbatim
@[inherit_doc] scoped[FirstOrder] infixl : 120 " ∈' " => FirstOrder.ZFC.ϕelt


-- @@ L86-88 verbatim
/-- Make an atomic formula t1 ∉ t2. -/
def ϕnotElt {n : ℕ} (t₁ t₂ : Language.LZFC.Term (ℕ ⊕ Fin n)) :=
  ∼(Language.Relations.boundedFormula₂ isEltOfTwo t₁ t₂)


-- @@ L90-90 verbatim
@[inherit_doc] scoped[FirstOrder] infixl : 120 " ∉' " => FirstOrder.ZFC.ϕnotElt


-- @@ L92-94 verbatim
/-- The negation of the equality of two terms as a bounded formula. -/
def intNotEqual {n : ℕ} (t₁ t₂ : Language.LZFC.Term (ℕ ⊕ Fin n)) :=
    ∼(FirstOrder.Language.Term.bdEqual t₁ t₂)


-- @@ L96-96 verbatim
@[inherit_doc] scoped[FirstOrder] infixl: 88 " ≠' " => FirstOrder.ZFC.intNotEqual


-- @@ L98-99 verbatim
/-- Make a free variable in LSet. -/
def fv (n : ℕ) (k : ℕ) : Language.LZFC.Term (ℕ ⊕ Fin n) := Language.Term.var (Sum.inl k)


-- @@ L101-102 verbatim
/-- Make a to-be bounded variable indexed by k, in which free variables are indexed by ℕ. -/
def bv (n : ℕ) (k : Fin n) : Language.LZFC.Term (ℕ ⊕ Fin n) := Language.Term.var (Sum.inr k)


-- @@ L104-111 verbatim
/-- Model of set theory. -/
class ModelSets (V : Type u) extends LZFC.Structure V, Inhabited V where
  /-- The external membership relation interpreting the language's ∈ symbol. -/
  isEltOf : V → V → Prop
  /-- The external relation matches the language's `RelMap`. -/
  interpret_is_elt_of : ∀ {a b : V}, isEltOf a b ↔ RelMap isEltOfTwo ![a, b]
  /-- Extensionality: sets with the same elements are equal. -/
  extensionality : ∀ {a b : V}, (∀(z : V), (isEltOf z a) ↔ isEltOf z b) → a = b


-- @@ L113-113 verbatim
variable {V : Type u}


-- @@ L115-117 verbatim
/-- The negation of `ModelSets.isEltOf`. -/
def notIsEltOf [ModelSets V] (a b : V) : Prop :=
  ¬ (ModelSets.isEltOf a b)


-- @@ L119-119 verbatim
@[inherit_doc ModelSets.isEltOf] infix : 120 " ∈ " => ModelSets.isEltOf

-- @@ L120-120 verbatim
@[inherit_doc notIsEltOf] infix : 120 " ∉ " => notIsEltOf


-- @@ L122-126 verbatim
/-- Realize a free varaible. -/
@[simp]
theorem realize_fv [ModelSets V] {n : ℕ} {s : ℕ → V} {xs : Fin n → V} (k : ℕ) :
    Language.Term.realize (Sum.elim s xs) (fv n k) = s k := by
  exact rfl


-- @@ L128-132 verbatim
/-- Realize a bounded variable with the type ℕ. -/
@[simp]
theorem realize_bv [ModelSets V] {n : ℕ} (s : ℕ → V) (xs : Fin n → V) (k : Fin n) :
    Language.Term.realize (Sum.elim s xs) (bv n k) = xs k := by
  simp [bv]


-- @@ L134-140 expanded
@[simp]
theorem realize_in [ModelSets V] {n : ℕ} {s : ℕ → V} {xs : Fin n → V}
    {t₁ t₂ : LZFC.Term (ℕ ⊕ Fin n)} :
    (t₁ ∈' t₂).Realize s xs ↔ Term.realize (Sum.elim s xs) t₁ ∈ Term.realize (Sum.elim s xs) t₂ :=
  by
  rw [ModelSets.interpret_is_elt_of]
  apply realize_rel₂


-- @@ L142-147 expanded
@[simp]
theorem realize_nin [ModelSets V] {n : ℕ} {s : ℕ → V} {xs : Fin n → V}
    {t₁ t₂ : LZFC.Term (ℕ ⊕ Fin n)} :
    (t₁ ∉' t₂).Realize s xs ↔ Term.realize (Sum.elim s xs) t₁ ∉ Term.realize (Sum.elim s xs) t₂ :=
  by apply not_congr realize_in


-- @@ L149-154 verbatim
@[simp]
theorem realize_neq [ModelSets V] {n : ℕ} {s : ℕ → V} {xs : Fin n → V}
    {t₁ t₂ : LZFC.Term (ℕ ⊕ Fin n)} :
    (t₁≠'t₂).Realize s xs ↔
      Term.realize (Sum.elim s xs) t₁ ≠ Term.realize (Sum.elim s xs) t₂ := by
  simp [intNotEqual]


-- @@ L156-157 verbatim
/-- Make a free variable in LSet with n implicit. -/
def fv' {n : ℕ} (k : ℕ) : Language.LZFC.Term (ℕ ⊕ Fin n) := Language.Term.var (Sum.inl k)


-- @@ L159-161 verbatim
/-- Make a to-be bounded variable indexed by (k : Fin n),
  in which free variables are indexed by ℕ with n implicit. -/
def bv' {n : ℕ} (k : Fin n) : Language.LZFC.Term (ℕ ⊕ Fin n) := Language.Term.var (Sum.inr k)


-- @@ L163-166 verbatim
/-- Make a to-be bounded variable indexed by (k : ℕ),
  in which free variables are indexed by ℕ with n implicit. -/
def bv'' {n : ℕ} [NeZero n] (k : ℕ) : Language.LZFC.Term (ℕ ⊕ Fin n) :=
    Language.Term.var (Sum.inr (Fin.ofNat n k))


-- @@ L168-172 verbatim
/-- Realize a free varaible. -/
@[simp]
theorem realize_fv' [ModelSets V] {n : ℕ} {s : ℕ → V} {xs : Fin n → V} (k : ℕ) :
    Language.Term.realize (Sum.elim s xs) (fv' k) = s k := by
  exact rfl


-- @@ L174-178 verbatim
/-- Realize bv' with the type ℕ. -/
@[simp]
theorem realize_bv' [ModelSets V] {n : ℕ} (s : ℕ → V) (xs : Fin n → V) (k : Fin n) :
    Language.Term.realize (Sum.elim s xs) (bv' k) = xs k := by
  simp [bv']


-- @@ L180-184 verbatim
/-- Realize bv'' with the type ℕ. -/
@[simp]
theorem realize_bv'' [ModelSets V] {n : ℕ} [NeZero n] (s : ℕ → V) (xs : Fin n → V) (k : ℕ) :
    Language.Term.realize (Sum.elim s xs) (bv'' k) = xs (Fin.ofNat n k) := by
  simp [bv'']


-- @@ L186-186 verbatim
end ZFC

-- @@ L187-187 verbatim
end FirstOrder
