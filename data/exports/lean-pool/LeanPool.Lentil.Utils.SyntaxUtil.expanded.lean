/-
Copyright (c) 2026 Qiyuan Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qiyuan Zhao
-/
module

meta import Lean.Parser.Term
import Lean.Parser.Term


-- @@ L11-11 verbatim
@[expose] public section


-- @@ L13-13 verbatim
open Lean


-- @@ L15-15 verbatim
namespace LentilLib


-- @@ L17-22 verbatim
/-- Convert a `binderIdent` into a function binder. -/
def binderIdentToFunBinder (stx : TSyntax ``binderIdent) : MacroM (TSyntax ``Parser.Term.funBinder) :=
  match stx with
  | `(binderIdent| $x:ident) =>  `(Parser.Term.funBinder| $x:ident )
  | `(binderIdent| _ ) =>  `(Parser.Term.funBinder| _ )
  | _ => Macro.throwUnsupported


-- @@ L24-24 verbatim
end LentilLib
