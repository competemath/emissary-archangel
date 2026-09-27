/-
Copyright (c) 2026 Andrej Bauer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrej Bauer
-/
module

public import LeanPool.PartialCombinatoryAlgebras.Basic
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.Basic
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.SetLike
import Mathlib.Tactic.Widget.Calc


-- @@ L15-36 verbatim
/-!
# Partial combinatory algebras

A partial combinatory algebra is a set equipped with a partial binary operation,
which has the so-called combinators `K` and `S`. We formalize it in two stages.

We first define the class `PartialApplication` which equips a given set `A` with
a partial binary operation. One might expect such an operation to have type
`A → A → Part A`, but this leads to complications because it is not composable.
So instead we specify that a partial operation is a map of type `Part A → Part A → Part A`.
In other words, we *always* work with partial elements, and separately state that they are
total as necessary.

(It would be natural to require that the applications be strict, i.e., if the result is defined
so are its arguments. An early version did so, but the assumption of strictness was never used.)

We then define the class `PCA` (partial combinatory algebra) to be an extension of
`PartialApplication`. It prescribed combinators `K` and `S` satisfying the usual properties.
Following our strategy, `K` and `S` are again partial elements on the carrier set,
with a separate claim that they are total.

-/


-- @@ L38-38 verbatim
@[expose] public section


-- @@ L40-40 verbatim
namespace LeanPool.PartialCombinatoryAlgebras


-- @@ L42-61 expanded
/-- The partial combinatory structure on a set `A`. -/
class PCA (A : Type*) extends PartialApplication A where
  /-- The `K` combinator as a partial element. -/
  K : Part A
  /-- The `S` combinator as a partial element. -/
  S : Part A
  /-- The `K` combinator is total. -/
  df_K₀ : Part.Dom K
  /-- Applying `K` to a total argument is total. -/
  df_K₁ : ∀ {u : Part A}, Part.Dom u → Part.Dom (HasDot.dot K u)
  /-- The `S` combinator is total. -/
  df_S₀ : Part.Dom S
  /-- Applying `S` to one total argument is total. -/
  df_S₁ : ∀ {u : Part A}, Part.Dom u → Part.Dom (HasDot.dot S u)
  /-- Applying `S` to two total arguments is total. -/
  df_S₂ : ∀ {u v : Part A}, Part.Dom u → Part.Dom v → Part.Dom (HasDot.dot (HasDot.dot S u) v)
  /-- The defining equation of `K`. -/
  eq_K : ∀ (u v : Part A), Part.Dom u → Part.Dom v → (HasDot.dot (HasDot.dot K u) v) = u
  /-- The defining equation of `S`. -/
  eq_S :
    ∀ (u v w : Part A),
      Part.Dom u →
        Part.Dom v →
          Part.Dom w →
            HasDot.dot (HasDot.dot (HasDot.dot S u) v) w =
              HasDot.dot (HasDot.dot u w) (HasDot.dot v w)


-- @@ L63-63 verbatim
attribute [simp] PCA.df_K₀

-- @@ L64-64 verbatim
attribute [simp] PCA.df_K₁

-- @@ L65-65 verbatim
attribute [simp] PCA.df_S₀

-- @@ L66-66 verbatim
attribute [simp] PCA.df_S₁

-- @@ L67-67 verbatim
attribute [simp] PCA.df_S₂


-- @@ L69-69 verbatim
namespace PCA


-- @@ L71-73 verbatim
/-- Every PCA is inhabited. We pick K as its default element. -/
instance inhabited {A : Type*} [PCA A] : Inhabited A where
  default := PCA.K.get PCA.df_K₀


-- @@ L75-75 verbatim
end PCA


-- @@ L77-86 verbatim
/-! `Expr Γ A` is the type of expressions built inductively from
    constants `K` and `S`, variables in `Γ` (the variable context),
    the elements of a carrier set `A`, and formal binary application.

    The usual accounts of PCAs typically do not introduce `K` and `S`
    as separate constants, because a PCA `A` already contains such combinators.
    However, as we defined the combinators to be partial elements, it is more
    convenient to have separate primitive constants denoting them.
    Also, this way `A` need not be an applicative structure.
-/


-- @@ L88-88 verbatim
namespace PCA


-- @@ L90-101 verbatim
/-- Expressions with variables from context `Γ` and elements from `A`. -/
inductive Expr (Γ A : Type*) where
/-- Formal expression denoting the K combinator -/
| K : Expr Γ A
/-- Formal expression denoting the S combinator -/
| S : Expr Γ A
/-- An element as a formal expression -/
| elm : A → Expr Γ A
/-- A variable as a formal expression -/
| var : Γ → Expr Γ A
/-- Formal expression application -/
| app : Expr Γ A → Expr Γ A → Expr Γ A


-- @@ L103-103 verbatim
namespace Expr


-- @@ L105-107 verbatim
/-- Formal application as a binary operation `·` -/
instance hasDot {Γ A : Type*} : HasDot (Expr Γ A) where
  dot := Expr.app


-- @@ L109-109 verbatim
end Expr


-- @@ L111-111 verbatim
section


-- @@ L113-113 verbatim
universe u v

-- @@ L114-114 verbatim
variable {Γ : Type u} [DecidableEq Γ]

-- @@ L115-115 verbatim
variable {A : Type v} [PCA A]


-- @@ L117-121 verbatim
/-- A valuation `η : Γ → A` assigning elements to variables,
    with the value of `x` overridden to be `a`. -/
@[reducible]
def override (x : Γ) (a : A) (η : Γ → A) (y : Γ) : A :=
  if y = x then a else η y


-- @@ L123-129 expanded
/-- Evaluate an expression with respect to a given valuation `η`. -/
def eval (η : Γ → A) : Expr Γ A → Part A
  | .K => PCA.K
  | .S => PCA.S
  | .elm a => .some a
  | .var x => .some (η x)
  | .app e₁ e₂ => HasDot.dot (eval η e₁) (eval η e₂)


-- @@ L131-132 expanded
/-- An expression is said to be defined when it is defined at every valuation. -/
def defined (e : Expr Γ A) :=
  ∀ (η : Γ → A), Part.Dom (eval η e)


-- @@ L134-140 expanded
/-- The substitution of an element for the extra variable. -/
def subst (x : Γ) (a : A) : Expr Γ A → Expr Γ A
  | .K => .K
  | .S => .S
  | .elm b => .elm b
  | .var y => if y = x then .elm a else .var y
  | .app e₁ e₂ => HasDot.dot (subst x a e₁) (subst x a e₂)


-- @@ L142-151 expanded
/-- `abstr e` is an expression with one fewer variables than
    the expression `e`, which works similarly to function
    abastraction in the λ-calculus. It is at the heart of
    combinatory completeness. -/
def abstr (x : Γ) : Expr Γ A → Expr Γ A
  | .K => HasDot.dot .K .K
  | .S => HasDot.dot .K .S
  | .elm a => HasDot.dot .K (.elm a)
  | .var y => if y = x then HasDot.dot (HasDot.dot .S .K) .K else HasDot.dot .K (.var y)
  | .app e₁ e₂ => HasDot.dot (HasDot.dot .S (abstr x e₁)) (abstr x e₂)


-- @@ L153-178 verbatim
/-- An abstraction is defined. -/
@[simp]
lemma df_abstr (x : Γ) (e : Expr Γ A) : defined (abstr x e) := by
  intro η
  induction e
  case K =>
    dsimp [abstr, eval, HasDot.dot]
    exact PCA.df_K₁ PCA.df_K₀
  case S =>
    dsimp [abstr, eval, HasDot.dot]
    exact PCA.df_K₁ PCA.df_S₀
  case elm a =>
    dsimp [abstr, eval, HasDot.dot]
    exact PCA.df_K₁ (by simp)
  case var y =>
    by_cases h : y = x
    · subst h
      simp only [abstr, ite_true]
      dsimp [eval, HasDot.dot]
      exact PCA.df_S₂ (A := A) (u := (PCA.K : Part A)) (v := (PCA.K : Part A))
        PCA.df_K₀ PCA.df_K₀
    · simp only [abstr, h, ite_false, eval, HasDot.dot]
      exact PCA.df_K₁ (A := A) (u := Part.some (η y)) (Part.some_dom _)
  case app e₁ e₂ ih₁ ih₂ =>
    dsimp [abstr, eval, HasDot.dot]
    exact PCA.df_S₂ ih₁ ih₂


-- @@ L180-217 expanded
/-- `eval_abstr e` behaves like abstraction in the extra variable.
    This is known as *combinatory completeness*. -/
lemma eval_abstr (x : Γ) (e : Expr Γ A) (a : A) (η : Γ → A) :
    eval η (HasDot.dot (abstr x e) (.elm a)) = eval (override x a η) e :=
  by
  induction e
  case K =>
    dsimp [abstr, eval, HasDot.dot]
    exact PCA.eq_K (PCA.K : Part A) (Part.some a) PCA.df_K₀ (by simp)
  case S =>
    dsimp [abstr, eval, HasDot.dot]
    exact PCA.eq_K (PCA.S : Part A) (Part.some a) PCA.df_S₀ (by simp)
  case elm b =>
    dsimp [abstr, eval, HasDot.dot]
    exact PCA.eq_K (Part.some b) (Part.some a) (by simp) (by simp)
  case var y =>
    by_cases h : y = x
    · subst h
      simp only [abstr, ite_true]
      dsimp [eval, override, HasDot.dot]
      simp only [ite_true]
      change HasDot.dot (HasDot.dot (HasDot.dot PCA.S PCA.K) PCA.K) (Part.some a) = Part.some a
      rw [PCA.eq_S (PCA.K : Part A) (PCA.K : Part A) (Part.some a) PCA.df_K₀ PCA.df_K₀
          (Part.some_dom _)]
      exact
        PCA.eq_K (Part.some a) (HasDot.dot PCA.K (Part.some a)) (by simp)
          (PCA.df_K₁ (A := A) (u := Part.some a) (Part.some_dom _))
    · simp only [abstr, h, ite_false, eval, override, HasDot.dot]
      exact PCA.eq_K (Part.some (η y)) (Part.some a) (Part.some_dom _) (Part.some_dom _)
  case app e₁ e₂ ih₁ ih₂ =>
    dsimp [abstr, eval, HasDot.dot]
    change
      HasDot.dot (HasDot.dot (HasDot.dot PCA.S (eval η (abstr x e₁))) (eval η (abstr x e₂)))
          (Part.some a) =
        HasDot.dot (eval (override x a η) e₁) (eval (override x a η) e₂)
    rw [PCA.eq_S (eval η (abstr x e₁)) (eval η (abstr x e₂)) (Part.some a) (df_abstr x e₁ η)
        (df_abstr x e₂ η) (Part.some_dom _)]
    have ih₁' : HasDot.dot (eval η (abstr x e₁)) (Part.some a) = eval (override x a η) e₁ := by
      simpa [eval, HasDot.dot] using ih₁
    have ih₂' : HasDot.dot (eval η (abstr x e₂)) (Part.some a) = eval (override x a η) e₂ := by
      simpa [eval, HasDot.dot] using ih₂
    rw [ih₁', ih₂']


-- @@ L219-226 expanded
/-- Like `eval_abstr` but with the application on the outside of `eval`. -/
lemma eval_abstr_app (η : Γ → A) (x : Γ) (e : Expr Γ A) (u : Part A) (hu : Part.Dom u) :
    HasDot.dot (eval η (abstr x e)) u = eval (override x (u.get hu) η) e := by
  calc
    _ = eval η (HasDot.dot (abstr x e) (.elm (u.get hu))) :=
      by
      dsimp [eval, HasDot.dot]
      rw [Part.some_get hu]
    _ = eval (override x (u.get hu) η) e := by apply eval_abstr


-- @@ L228-241 verbatim
@[simp]
lemma eval_override (η : Γ → A) (x : Γ) (a : A) (e : Expr Γ A) :
    eval (override x a η) e = eval η (subst x a e) := by
  induction e
  case K => simp [eval, subst]
  case S => simp [eval, subst]
  case elm => simp [eval, subst]
  case var y =>
    cases (decEq y x)
    case isFalse p => simp [eval, subst, p]
    case isTrue p => simp [eval, subst, p]
  case app e₁ e₂ ih₁ ih₂ =>
    dsimp [eval, subst, HasDot.dot]
    rw [ih₁, ih₂]


-- @@ L243-247 verbatim
/-- Compile an expression to a partial element, substituting
    the default value for any variables occurring in e. -/
@[simp]
def compile (e : Expr Γ A) : Part A :=
  eval (fun _ => default) e


-- @@ L249-263 expanded
/-- Evaluate an expression under the assumption that it is closed.
    Return `inl x` if variable `x` is encountered, otherwise `inr u`
    where `u` is the partial element so obtained. -/
def evalClosed : Expr Γ A → Sum Γ (Part A)
  | .K => .inr K
  | .S => .inr S
  | .elm a => .inr (.some a)
  | .var x => .inl x
  | .app e₁ e₂ =>
    match evalClosed e₁ with
    | .inl x => .inl x
    | .inr a₁ =>
      match evalClosed e₂ with
      | .inl x => .inl x
      | .inr a₂ => .inr (HasDot.dot a₁ a₂)


-- @@ L265-266 verbatim
/-- Notation for combinatory abstraction in an expression. -/
syntax:20 "≪" term "≫" term:20 : term


-- @@ L268-269 expanded
macro_rules
  | `(LeanPool.PartialCombinatoryAlgebras.PCA.abstr $x:term $a:term) =>
    `(LeanPool.PartialCombinatoryAlgebras.PCA.abstr $x $a)


-- @@ L271-272 verbatim
/-- Notation for compiling a closed PCA expression to a partial element. -/
syntax "[pca: " term "]" : term


-- @@ L274-276 expanded
macro_rules
  | `(LeanPool.PartialCombinatoryAlgebras.PCA.compile (Γ := Lean.Name) $e:term) =>
    `(LeanPool.PartialCombinatoryAlgebras.PCA.compile (Γ := Lean.Name) $e)


-- @@ L278-278 verbatim
end


-- @@ L280-280 verbatim
end PCA


-- @@ L282-282 verbatim
end LeanPool.PartialCombinatoryAlgebras
