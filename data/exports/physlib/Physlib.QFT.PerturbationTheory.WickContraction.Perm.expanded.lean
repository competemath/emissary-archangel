/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.QFT.PerturbationTheory.WickAlgebra.WickTerm
public import Physlib.QFT.PerturbationTheory.WickContraction.IsFull
public import Physlib.Meta.Linters.Sorry

-- @@ L11-27 verbatim
/-!

# Permutations of Wick contractions

We define two Wick contractions to be permutations of each other
if the Wick term they produce is equal.

## TODO

The long term aim is to simplify this condition as much as possible,
so that it can eventually be made decidable.

It should become apparent that two Wick contractions are permutations of each other
if they correspond to the same Feynman diagram.
Please speak to JTS before working in this direction.

-/


-- @@ L29-29 verbatim
@[expose] public section


-- @@ L31-31 verbatim
open FieldSpecification

-- @@ L32-32 verbatim
variable {𝓕 : FieldSpecification}


-- @@ L34-34 verbatim
namespace WickContraction

-- @@ L35-35 verbatim
variable {n : ℕ} (c : WickContraction n)

-- @@ L36-36 verbatim
open Physlib.List

-- @@ L37-37 verbatim
open WickAlgebra

-- @@ L38-38 verbatim
open FieldStatistic

-- @@ L39-39 verbatim
noncomputable section


-- @@ L41-44 verbatim
/-- For a list `φs` of `𝓕.FieldOp`, and two Wick contractions `φsΛ₁` and `φsΛ₂` of `φs`,
  we say that `φsΛ₁` and `φsΛ₂` are permutations of each other if they have the same Wick term. -/
def Perm {φs : List 𝓕.FieldOp} (φsΛ₁ φsΛ₂ : WickContraction φs.length) : Prop :=
  φsΛ₁.wickTerm = φsΛ₂.wickTerm


-- @@ L46-46 verbatim
namespace Perm


-- @@ L48-48 verbatim
variable {φs : List 𝓕.FieldOp} {φsΛ φsΛ₁ φsΛ₂ φsΛ₃ : WickContraction φs.length}


-- @@ L50-53 verbatim
/-- The reflexivity of the `Perm` relation. -/
@[refl]
lemma refl : Perm φsΛ φsΛ := by
  rw [Perm]


-- @@ L55-59 verbatim
/-- The symmetry of the `Perm` relation. -/
@[symm]
lemma symm (h : Perm φsΛ₁ φsΛ₂) : Perm φsΛ₂ φsΛ₁ := by
  rw [Perm] at h ⊢
  exact h.symm


-- @@ L61-66 verbatim
/-- The transitivity of the `Perm` relation. -/
@[trans]
lemma trans (h12 : Perm φsΛ₁ φsΛ₂) (h23 : Perm φsΛ₂ φsΛ₃) :
    Perm φsΛ₁ φsΛ₃ := by
  rw [Perm] at h12 h23 ⊢
  exact h12.trans h23


-- @@ L68-74 verbatim
/-- If `Perm φsΛ₁ φsΛ₂` and both contractions are grading-compliant,
  then if `φsΛ₁` is a full Wick contraction, so is `φsΛ₂`. -/
@[sorryful]
lemma isFull_of_isFull (h : Perm φsΛ₁ φsΛ₂)
    (h₁ : GradingCompliant φs φsΛ₁) (h₂ : GradingCompliant φs φsΛ₂)
    (hf : IsFull φsΛ₁) : IsFull φsΛ₂ := by
  sorry


-- @@ L76-82 verbatim
/-- If `Perm φsΛ₁ φsΛ₂` and both contractions are grading-compliant,
  then their uncontracted lists are permutations of each other. -/
@[sorryful]
lemma perm_uncontractedList (h : Perm φsΛ₁ φsΛ₂)
    (h₁ : GradingCompliant φs φsΛ₁) (h₂ : GradingCompliant φs φsΛ₂) :
    [φsΛ₁]ᵘᶜ.Perm [φsΛ₂]ᵘᶜ := by
  sorry


-- @@ L84-84 verbatim
end Perm


-- @@ L86-86 verbatim
end

-- @@ L87-87 verbatim
end WickContraction
