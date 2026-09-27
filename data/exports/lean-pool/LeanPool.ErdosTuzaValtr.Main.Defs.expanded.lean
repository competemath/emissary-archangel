/-
Copyright (c) 2026 Jineon Baek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jineon Baek
-/
module

public import Mathlib.Data.Nat.Choose.Basic
public import LeanPool.ErdosTuzaValtr.Etv.Defs
public import Mathlib.Data.Finset.Card
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow


-- @@ L17-21 verbatim
/-!
# LeanPool.ErdosTuzaValtr.Main.Defs

Imported Lean Pool material for `LeanPool.ErdosTuzaValtr.Main.Defs`.
-/


-- @@ L23-23 verbatim
@[expose] public section


-- @@ L25-25 verbatim
noncomputable section


-- @@ L27-27 verbatim
variable {α : Type _} [LinearOrder α] (C : Config α)


-- @@ L29-34 verbatim
/-- The configuration-relative main goal at level `n`: any large cap-free, cup-free finset
contains an interweaved laced configuration. -/
def Config.MainGoal (n : ℕ) : Prop :=
  ∀ S : Finset α,
    Nat.choose (n + 2) 2 + 2 ≤ S.card →
      ¬C.HasNCap 4 S → ¬C.HasNCup (n + 3) S → ∃ p q r s, C.HasInterweavedLaced (n + 2) S p q r s


-- @@ L36-41 verbatim
/-- The main goal under the without-loss-of-generality assumption that a certain join is absent. -/
def Config.MainGoalWlog (n : ℕ) : Prop :=
  ∀ S : Finset α,
    ¬C.HasJoin (n + 2) (n + 1) S →
      Nat.choose (n + 2) 2 + 2 ≤ S.card →
        ¬C.HasNCap 4 S → ¬C.HasNCup (n + 3) S → ∃ p q r s, C.HasInterweavedLaced (n + 2) S p q r s
