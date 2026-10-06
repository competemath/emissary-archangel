/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Counting.Quantitative


-- @@ L8-24 verbatim
/-!
# Writing quantitative terms

Helpers for writing a term of quantitative first-order logic
(`DescriptiveComplexity.QTerm`) the way it is read, and for evaluating it.

A quantifier of `DescriptiveComplexity.QTerm` binds a block of variables,
named by position in a sum type. `DescriptiveComplexity.QTerm.sumOver` and
`DescriptiveComplexity.QTerm.prodOver` bind *one* variable and hand it to the
body by name: the body is a function of the bound variable, and of the way the
variables already in scope are read under the binder. So
`sumOver fun up x => f (up y) x` is `Σx. f(y, x)`, and its value is a sum over
the elements (`DescriptiveComplexity.QTerm.eval_sumOver`).

`DescriptiveComplexity.QTerm.cond` is the choice between two terms by a
formula.
-/


-- @@ L26-26 verbatim
namespace DescriptiveComplexity


-- @@ L28-28 verbatim
open FirstOrder


-- @@ L30-30 verbatim
open Language Structure


-- @@ L32-32 verbatim
namespace QTerm


-- @@ L34-34 verbatim
variable {L : Language.{0, 0}} {γ : Type}


-- @@ L36-39 verbatim
/-- `Σx. t`: the body is given the reading of the variables in scope, and the
bound variable. -/
def sumOver (f : ∀ {δ : Type}, (γ → δ) → δ → QTerm L δ) : QTerm L γ :=
  .sum 1 (f Sum.inl (Sum.inr 0))


-- @@ L41-44 verbatim
/-- `Πx. t`: the body is given the reading of the variables in scope, and the
bound variable. -/
def prodOver (f : ∀ {δ : Type}, (γ → δ) → δ → QTerm L δ) : QTerm L γ :=
  .prod 1 (f Sum.inl (Sum.inr 0))


-- @@ L46-49 verbatim
/-- The choice between two terms: `s` where the formula holds, `t` where it
does not. -/
def cond (φ : L.Formula γ) (s t : QTerm L γ) : QTerm L γ :=
  .add (.mul (.ind φ) s) (.mul (.ind ∼φ) t)


-- @@ L51-51 verbatim
variable {A : Type} [L.Structure A]


-- @@ L53-58 verbatim
theorem eval_sumOver (f : ∀ {δ : Type}, (γ → δ) → δ → QTerm L δ) (v : γ → A) :
    (sumOver f).eval v =
      ∑ᶠ a : A, (f (δ := γ ⊕ Fin 1) Sum.inl (Sum.inr 0)).eval (Sum.elim v fun _ => a) :=
  (finsum_comp_equiv (Equiv.funUnique (Fin 1) A).symm
    (f := fun w : Fin 1 → A =>
      (f (δ := γ ⊕ Fin 1) Sum.inl (Sum.inr 0)).eval (Sum.elim v w))).symm


-- @@ L60-65 verbatim
theorem eval_prodOver (f : ∀ {δ : Type}, (γ → δ) → δ → QTerm L δ) (v : γ → A) :
    (prodOver f).eval v =
      ∏ᶠ a : A, (f (δ := γ ⊕ Fin 1) Sum.inl (Sum.inr 0)).eval (Sum.elim v fun _ => a) :=
  (finprod_comp_equiv (Equiv.funUnique (Fin 1) A).symm
    (f := fun w : Fin 1 → A =>
      (f (δ := γ ⊕ Fin 1) Sum.inl (Sum.inr 0)).eval (Sum.elim v w))).symm


-- @@ L67-70 verbatim
open Classical in
theorem eval_cond (φ : L.Formula γ) (s t : QTerm L γ) (v : γ → A) :
    (cond φ s t).eval v = if φ.Realize v then s.eval v else t.eval v := by
  by_cases h : φ.Realize v <;> simp [cond, eval, h]


-- @@ L72-75 verbatim
open Classical in
theorem eval_ind (φ : L.Formula γ) (v : γ → A) :
    (ind φ : QTerm L γ).eval v = if φ.Realize v then 1 else 0 :=
  rfl


-- @@ L77-78 verbatim
theorem eval_mul (s t : QTerm L γ) (v : γ → A) : (mul s t).eval v = s.eval v * t.eval v :=
  rfl


-- @@ L80-81 verbatim
theorem eval_add (s t : QTerm L γ) (v : γ → A) : (add s t).eval v = s.eval v + t.eval v :=
  rfl


-- @@ L83-84 verbatim
theorem eval_const (n : ℕ) (v : γ → A) : (const n : QTerm L γ).eval v = n :=
  rfl


-- @@ L86-86 verbatim
end QTerm


-- @@ L88-88 verbatim
end DescriptiveComplexity
