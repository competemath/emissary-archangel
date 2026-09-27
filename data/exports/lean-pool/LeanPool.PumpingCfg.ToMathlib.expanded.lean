/-
Copyright (c) 2026 Alexander Loitzl, Martin Dvorak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Loitzl, Martin Dvorak
-/
module

public import LeanPool.PumpingCfg.ChomskyNormalForm.Basic


-- @@ L10-15 verbatim
/-!
# Auxiliary grammar lemmas

Small facts about `ChomskyNormalFormRule.Rewrites` and `ChomskyNormalFormGrammar.Produces`
intended for upstreaming into Mathlib alongside the Chomsky-normal-form development.
-/


-- @@ L17-17 verbatim
@[expose] public section


-- @@ L19-19 verbatim
universe uT uN

-- @@ L20-20 verbatim
variable {T : Type uT}


-- @@ L22-30 verbatim
lemma ChomskyNormalFormRule.Rewrites.word {N : Type uN} {r : ChomskyNormalFormRule T N}
    {u : List T} {v : List (Symbol T N)}
    (hruv : r.Rewrites (u.map Symbol.terminal) v) :
    False := by
  induction u generalizing v with
  | nil => cases hruv
  | cons _ _ ih =>
    cases hruv with
    | cons _ _ hru => exact ih hru


-- @@ L32-36 verbatim
lemma ChomskyNormalFormGrammar.Produces.input_output
    {g : ChomskyNormalFormGrammar T} {r : ChomskyNormalFormRule T g.NT}
    (hrg : r ∈ g.rules) :
    g.Produces [.nonterminal r.input] r.output :=
  ⟨r, hrg, ChomskyNormalFormRule.Rewrites.input_output⟩
