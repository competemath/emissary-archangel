/-
Copyright (c) 2026 Qiyuan Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qiyuan Zhao
-/
module

public import LeanPool.Lentil.ProofMode.Basic
import Batteries.Tactic.Init
import LeanPool.Lentil.Rules.Basic


-- @@ L12-12 verbatim
@[expose] public section


-- @@ L14-14 verbatim
namespace TLA.ProofMode


-- @@ L16-16 verbatim
open Lean Meta Elab Tactic


-- @@ L18-19 verbatim
theorem Entails_and_split {σ : Type u} {hyps : List (NamedPred σ)} {g1 g2 : pred σ} :
  Entails hyps (tlaAnd g1 g2) = (Entails hyps g1 ∧ Entails hyps g2) := and_pred_implies_split ..


-- @@ L21-30 verbatim
/--
`tlaSplitAnds` splits a conjunctive proof-mode goal into separate goals.

For example, if the proof-mode goal is `p ∧ q`, then
```lean
tlaSplitAnds
```
creates one goal for `p` and one goal for `q`.
-/
macro "tlaSplitAnds" : tactic => `(tactic| (simp only [$(mkIdent ``Entails_and_split):ident]; split_ands ))


-- @@ L32-32 verbatim
end TLA.ProofMode
