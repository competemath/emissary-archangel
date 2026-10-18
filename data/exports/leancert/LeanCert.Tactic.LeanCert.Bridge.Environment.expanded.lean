/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Core.IntervalRat.Basic


-- @@ L8-8 verbatim
/-! # Environments shared by proof-carrying reification -/


-- @@ L10-10 verbatim
namespace LeanCert.Tactic.Bridge


-- @@ L12-18 verbatim
/-- Real environment used by proof-carrying reification. The unary case keeps
the historical constant-environment convention; higher arities use zero beyond
the supplied arguments. -/
def realEnvironment (values : List ℝ) (index : Nat) : ℝ :=
  match values with
  | [value] => value
  | _ => values.getD index 0


-- @@ L20-20 verbatim
end LeanCert.Tactic.Bridge
