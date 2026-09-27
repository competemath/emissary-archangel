/-
Copyright (c) 2026 Qiyuan Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qiyuan Zhao
-/
module

public import Lean.Meta.Basic
import LeanPool.Lentil.Basic


-- @@ L11-11 verbatim
@[expose] public section


-- @@ L13-13 verbatim
namespace TLA.Expr


-- @@ L15-15 verbatim
open Lean Meta


-- @@ L17-24 verbatim
/-- Split a TLA conjunction `Expr` into its list of conjuncts. -/
def splitAndIntoParts (p : Expr) : MetaM (List Expr) := do
  match p with
  | .app (.app (.app (.const ``TLA.tlaAnd _) _) a) b =>
    let as ← splitAndIntoParts a
    let bs ← splitAndIntoParts b
    pure (as ++ bs)
  | _ => pure [p]


-- @@ L26-35 verbatim
/-- Split a chain of TLA implications into its list of premises and conclusion,
    optionally further splitting each premise conjunction (`cutAnd?`). -/
def splitImplicationsIntoParts (p : Expr) (cutAnd? : Bool := true) :
    MetaM (List Expr × Expr) := do
  match p with
  | .app (.app (.app (.const ``TLA.tlaImplies _) _) hp) q =>
    let ps ← if cutAnd? then splitAndIntoParts hp else pure [hp]
    let (ps', q') ← splitImplicationsIntoParts q
    pure (ps ++ ps', q')
  | _ => pure ([], p)


-- @@ L37-45 verbatim
/-- Split a `predImplies`/`valid` statement into its premises and conclusion. -/
def splitPredImpliesIntoParts (p : Expr) : MetaM (List Expr × Expr) := do
  match_expr p with
  | TLA.predImplies _ p q =>
    let ps ← splitAndIntoParts p
    let (ps', q') ← splitImplicationsIntoParts q
    pure (ps ++ ps', q')
  | TLA.valid _ body => splitImplicationsIntoParts body
  | _ => throwError "not a |-tla- statement"


-- @@ L47-55 verbatim
/-- Given some TLA related expression and return the type of the state
    (i.e., the argument after `TLA.pred`).
    While this could be done via `inferType`, just peeking the expression
    should be much "cheaper". -/
def peekStateType (p : Expr) : Option Expr :=
  match_expr p with
  | TLA.predImplies σ _ _ => .some σ
  | TLA.valid σ _ => .some σ
  | _ => .none


-- @@ L57-57 verbatim
end TLA.Expr
