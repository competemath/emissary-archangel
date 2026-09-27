/-
Copyright (c) 2026 Sven Manthe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sven Manthe
-/
module


public meta import Aesop.BuiltinRules
public import Aesop.BuiltinRules
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.Attr.Core
public meta import Mathlib.Tactic.Basic
public import Mathlib.Tactic.Push
public meta import Mathlib.Tactic.ToAdditive
public import Mathlib.Tactic.ToAdditive
public meta import Mathlib.Tactic.ToDual
public import Mathlib.Tactic.ToDual
public meta import Qq.Typ
import LeanPool.AFormalizationOfBorelDeterminacyInLean.Basic.General
import LeanPool.AFormalizationOfBorelDeterminacyInLean.Basic.Meta
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.ApplyFun
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow


-- @@ L29-33 verbatim
/-!
# LeanPool.AFormalizationOfBorelDeterminacyInLean.Game.Player

Auxiliary declarations for the Borel determinacy formalization.
-/


-- @@ L35-35 verbatim
@[expose] public section



-- @@ L38-38 verbatim
namespace GaleStewartGame


-- @@ L40-43 verbatim
/-- a player in a Gale-Stewart game -/
inductive Player
  | zero
  | one


-- @@ L45-45 verbatim
section «Section1»

-- @@ L46-46 verbatim
open Lean Meta Elab Tactic Term Qq

-- @@ L47-54 verbatim
/-- Tactic support used by the Borel determinacy formalization. -/
elab "casesPlayer" : tactic => withMainContext do
  for hyp in ← getLCtx do
    if ← isDefEq (← instantiateMVars hyp.type) q(Player) then
      let syn ← exprToSyntax hyp.toExpr
      evalTactic (← `(tactic | cases $syn:term))
      return
  throwError "no variable of type player"

-- @@ L55-56 verbatim
/-- Tactic support used by the Borel determinacy formalization. -/
macro "casesPlayers" : tactic => `(tactic | focus repeat all_goals casesPlayer)

-- @@ L57-63 verbatim
attribute [simp_isPosition]
  iff_true iff_false true_iff false_iff
  and_true true_and and_false false_and
  or_true true_or or_false false_or
  ite_eq_iff eq_ite_iff ite_prop_iff_or
  --apply_ite
  --maybe reduce priority to stop (apply_ite (Eq _))

-- @@ L64-65 verbatim
/-- Constructor equality reduction for the position simplifier. -/
simproc_decl playerReduceCtorEq (_ = _) := reduceCtorEq

-- @@ L66-66 verbatim
attribute [simp_isPosition] playerReduceCtorEq

-- @@ L67-76 unexpanded
/-- Tactic support used by the Borel determinacy formalization. -/
macro "synthIsPosition" : tactic =>
  `(tactic | first | done |
  (casesPlayers <;> (try apply_fun List.length at *) <;>
    simpAtStar (config := {failIfUnchanged := false}) only [simp_isPosition, simp_lengths] <;>
    /-(try split_ifs at * <;>
      --split_ifs at * fails in win_asap due to order issue
      --(manually reordering goals fixes the issue)
      simpAtStar (config := {failIfUnchanged := false}) only [simp_isPosition]) <;>-/
    omega))

-- @@ L77-77 verbatim
end «Section1»


-- @@ L79-79 verbatim
variable {A : Type*} (x : List A) (p q : Player)

-- @@ L80-80 verbatim
namespace Player

-- @@ L81-84 verbatim
/-- Auxiliary declaration for the Borel determinacy formalization. -/
def toNat : Player → ℕ
  | zero => 0
  | one => 1

-- @@ L85-88 verbatim
/-- Auxiliary declaration for the Borel determinacy formalization. -/
@[simp_isPosition] lemma apply_ite_toNat (P : Prop) [Decidable P] (a b : Player) :
    toNat (if P then a else b) = if P then toNat a else toNat b := by
  simpa using (apply_ite toNat P a b)

-- @@ L89-89 verbatim
@[simp, simp_isPosition] lemma zero_toNat : zero.toNat = 0 := rfl

-- @@ L90-90 verbatim
@[simp, simp_isPosition] lemma one_toNat : one.toNat = 1 := rfl

-- @@ L91-91 expanded
@[ext]
lemma ext (h : p.toNat = q.toNat) : p = q := by
  first
  | done
  |
    (focus repeat all_goals casesPlayer <;> (try apply_fun List.length at *) <;>
          simpAtStar (config := { failIfUnchanged := false }) only [simp_isPosition,
            simp_lengths] <;>
        omega)


-- @@ L93-96 verbatim
/-- Auxiliary declaration for the Borel determinacy formalization. -/
def swap : Player → Player
  | zero => one
  | one => zero

-- @@ L97-100 verbatim
/-- Auxiliary declaration for the Borel determinacy formalization. -/
@[simp_isPosition] lemma apply_ite_swap (P : Prop) [Decidable P] (a b : Player) :
    swap (if P then a else b) = if P then swap a else swap b := by
  simpa using (apply_ite swap P a b)

-- @@ L101-101 verbatim
@[simp, simp_isPosition] lemma swap_zero : zero.swap = one := rfl

-- @@ L102-102 verbatim
@[simp, simp_isPosition] lemma swap_one : one.swap = zero := rfl


-- @@ L104-105 verbatim
/-- if `p` moves in position `[]`, then `p.residual x` moves in position `x` -/
@[simp_isPosition] def residual := if x.length % 2 = 0 then p else p.swap

-- @@ L106-106 verbatim
end Player


-- @@ L108-109 verbatim
/-- is player `p` to move in position `x`? -/
@[simp_isPosition] def IsPosition (x : List A) (p : Player) : Prop := x.length % 2 = p.toNat




-- @@ L113-113 verbatim
namespace Player

-- @@ L114-115 expanded
@[simp]
lemma residual_swap : (p.residual x).swap = p.swap.residual x := by
  first
  | done
  |
    (focus repeat all_goals casesPlayer <;> (try apply_fun List.length at *) <;>
          simpAtStar (config := { failIfUnchanged := false }) only [simp_isPosition,
            simp_lengths] <;>
        omega)


-- @@ L116-117 expanded
@[simp]
lemma residual_residual {x y : List A} : (p.residual x).residual y = p.residual (x ++ y) := by
  first
  | done
  |
    (focus repeat all_goals casesPlayer <;> (try apply_fun List.length at *) <;>
          simpAtStar (config := { failIfUnchanged := false }) only [simp_isPosition,
            simp_lengths] <;>
        omega)


-- @@ L118-119 expanded
@[simp]
lemma residual_even (h : x.length % 2 = 0) : p.residual x = p := by
  first
  | done
  |
    (focus repeat all_goals casesPlayer <;> (try apply_fun List.length at *) <;>
          simpAtStar (config := { failIfUnchanged := false }) only [simp_isPosition,
            simp_lengths] <;>
        omega)


-- @@ L120-121 expanded
@[simp]
lemma residual_odd (h : x.length % 2 = 1) : p.residual x = p.swap := by
  first
  | done
  |
    (focus repeat all_goals casesPlayer <;> (try apply_fun List.length at *) <;>
          simpAtStar (config := { failIfUnchanged := false }) only [simp_isPosition,
            simp_lengths] <;>
        omega)


-- @@ L122-123 expanded
@[simp]
lemma residual_append_both {y} : (p.residual (x ++ (y ++ x))) = p.residual y := by
  first
  | done
  |
    (focus repeat all_goals casesPlayer <;> (try apply_fun List.length at *) <;>
          simpAtStar (config := { failIfUnchanged := false }) only [simp_isPosition,
            simp_lengths] <;>
        omega)


-- @@ L124-125 expanded
@[simp]
lemma residual_cons {a} : (p.residual (a :: x)) = (p.residual x).swap := by
  first
  | done
  |
    (focus repeat all_goals casesPlayer <;> (try apply_fun List.length at *) <;>
          simpAtStar (config := { failIfUnchanged := false }) only [simp_isPosition,
            simp_lengths] <;>
        omega)


-- @@ L126-127 expanded
@[simp]
lemma residual_append_cons {a} {y} : (p.residual (x ++ a :: y)) = (p.residual (x ++ y)).swap := by
  first
  | done
  |
    (focus repeat all_goals casesPlayer <;> (try apply_fun List.length at *) <;>
          simpAtStar (config := { failIfUnchanged := false }) only [simp_isPosition,
            simp_lengths] <;>
        omega)


-- @@ L128-129 expanded
lemma residual_concat {a} : (p.residual (x ++ [a])) = (p.residual x).swap := by
  first
  | done
  |
    (focus repeat all_goals casesPlayer <;> (try apply_fun List.length at *) <;>
          simpAtStar (config := { failIfUnchanged := false }) only [simp_isPosition,
            simp_lengths] <;>
        omega)


-- @@ L130-131 expanded
lemma residual_concat2 {a b} : (p.residual (x ++ [a, b])) = p.residual x := by
  first
  | done
  |
    (focus repeat all_goals casesPlayer <;> (try apply_fun List.length at *) <;>
          simpAtStar (config := { failIfUnchanged := false }) only [simp_isPosition,
            simp_lengths] <;>
        omega)


-- @@ L132-132 verbatim
end Player


-- @@ L134-134 verbatim
end GaleStewartGame
