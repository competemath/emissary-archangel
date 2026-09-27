/-
Copyright (c) 2026 Qiyuan Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qiyuan Zhao
-/
module

public import LeanPool.Lentil.ProofMode.Basic
import LeanPool.Lentil.Rules.Basic


-- @@ L11-11 verbatim
@[expose] public section


-- @@ L13-13 verbatim
namespace TLA.ProofMode


-- @@ L15-15 verbatim
open Lean Meta Elab Tactic


-- @@ L17-17 verbatim
section


-- @@ L19-21 verbatim
variable {σ : Type u} {hyps : List (NamedPred σ)} {a b : pred σ}

-- NOTE: Implemented in a way that is probably more boring than you'd have expected

-- @@ L22-23 verbatim
theorem Entails_or_left : Entails hyps a → Entails hyps (tlaOr a b) :=
  fun h => pred_implies_trans h TLA.or_inl


-- @@ L25-26 verbatim
theorem Entails_or_right : Entails hyps b → Entails hyps (tlaOr a b) :=
  fun h => pred_implies_trans h TLA.or_inr


-- @@ L28-28 verbatim
end


-- @@ L30-34 verbatim
/--
`tlaLeft` reduces a disjunctive proof-mode goal `p ∨ q` to its left disjunct
`p`.
-/
macro "tlaLeft" : tactic => `(tactic| refine $(mkIdent ``Entails_or_left) ?_)


-- @@ L36-40 verbatim
/--
`tlaRight` reduces a disjunctive proof-mode goal `p ∨ q` to its right
disjunct `q`.
-/
macro "tlaRight" : tactic => `(tactic| refine $(mkIdent ``Entails_or_right) ?_)


-- @@ L42-42 verbatim
end TLA.ProofMode
