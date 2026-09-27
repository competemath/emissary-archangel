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


-- @@ L17-19 verbatim
theorem Entails_exists {σ : Type u} {hyps : List (NamedPred σ)}
    {α : Sort v} {p : α → pred σ} (witness : α) :
    Entails hyps (p witness) → Entails hyps (TLA.tlaExists p) := exists_elim witness


-- @@ L21-32 verbatim
/--
`tlaExists w₁, w₂, ...` supplies witnesses for existential quantifiers in the
proof-mode goal.

For example, if the goal is `∃ n : Nat, P n`, then
```lean
tlaExists 0
```
changes the goal to `P 0`. Multiple witnesses are applied from left to right,
so `tlaExists n, m` handles a goal such as `∃ n, ∃ m, P n m`.
-/
syntax (name := tlaExistsTac) "tlaExists" (ppSpace colGt term),+ : tactic


-- @@ L34-38 verbatim
elab_rules : tactic
  | `(tactic| tlaExists $[$ts],*) => do
    for t in ts do
      evalTactic <| ← `(tactic|
        refine $(mkIdent ``Entails_exists) $t ?_)


-- @@ L40-40 verbatim
end TLA.ProofMode
