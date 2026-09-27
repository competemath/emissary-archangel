/-
Copyright (c) 2026 Andrej Bauer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrej Bauer
-/
module

public import LeanPool.PartialCombinatoryAlgebras.CombinatoryAlgebra
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.SetLike


-- @@ L12-12 verbatim
/-! # Free (total) combinatory algebra -/


-- @@ L14-14 verbatim
@[expose] public section


-- @@ L16-16 verbatim
namespace LeanPool.PartialCombinatoryAlgebras


-- @@ L18-18 verbatim
namespace FreeCA


-- @@ L20-24 verbatim
/-- The underlying expressions fo the free combinatory algebra -/
inductive Expr where
| K : Expr
| S : Expr
| app : Expr → Expr → Expr


-- @@ L26-26 verbatim
instance exprHasDot : HasDot Expr where dot := Expr.app


-- @@ L28-35 expanded
/-- The equational axioms of the free combinatory algebra.
    Symmetry and transitivity are commented out because
    so far we have not needed them. -/
inductive eq : Expr → Expr → Prop where
  | refl : ∀ {a}, eq a a
  | app : ∀ {a b c d}, eq a b → eq c d → eq (HasDot.dot a c) (HasDot.dot b d)
  | K : ∀ {a b}, eq (.app (.app .K a) b) a
  | S : ∀ {a b c}, eq (.app (.app (.app .S a) b) c) (.app (.app a c) (.app b c))


-- @@ L37-38 verbatim
@[inherit_doc]
infix:40 " ≈ " => eq


-- @@ L40-42 verbatim
/-- The carrier of the free total combinatory algebra -/
@[reducible]
def carrier := Quot eq


-- @@ L44-46 verbatim
/-- Convert an expression to a (defined) partial element of the carrier. -/
@[reducible]
def mk := Quot.mk eq


-- @@ L48-51 expanded
instance hasDot : HasDot carrier where
  dot :=
    Quot.lift₂ (fun (x y : Expr) => mk (HasDot.dot x y))
      (by intros a b c e'; exact Quot.sound (.app .refl ‹_›))
      (by intros a b c e'; exact Quot.sound (.app ‹_› .refl))


-- @@ L53-54 expanded
@[simp]
theorem eq_mk_app (a b : Expr) : HasDot.dot (mk a) (mk b) = mk (HasDot.dot a b) :=
  rfl


-- @@ L56-56 verbatim
end FreeCA


-- @@ L58-74 verbatim
/-- The free combinatory algebra -/
instance FreeCA : CA FreeCA.carrier where
  K := FreeCA.mk .K
  S := FreeCA.mk .S

  eq_K := by
    apply Quot.ind; intro a
    apply Quot.ind; intro b
    rw [FreeCA.eq_mk_app, FreeCA.eq_mk_app]
    exact Quot.sound FreeCA.eq.K

  eq_S := by
    apply Quot.ind; intro a
    apply Quot.ind; intro b
    apply Quot.ind; intro c
    rw [FreeCA.eq_mk_app, FreeCA.eq_mk_app, FreeCA.eq_mk_app]
    exact Quot.sound FreeCA.eq.S


-- @@ L76-76 verbatim
end LeanPool.PartialCombinatoryAlgebras
