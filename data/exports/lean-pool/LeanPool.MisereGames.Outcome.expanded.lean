/-
Copyright (c) 2025 Tomasz Maciosowski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomasz Maciosowski
-/
module

public import LeanPool.MisereGames.Player


-- @@ L10-12 verbatim
/-!
Misere combinatorial games.
-/


-- @@ L14-14 verbatim
namespace MisereGames


-- @@ L16-16 verbatim
public section


-- @@ L18-38 verbatim
/--
The four outcome classes of a short partizan game.
-/
inductive Outcome where
  /--
  Left always wins, regardless of who starts.
  -/
  | L
  /--
  The Next (first) player wins.
  -/
  | N
  /--
  The Previous (second) player wins.
  -/
  | P
  /--
  Right always wins, regardless of who starts.
  -/
  | R
deriving DecidableEq


-- @@ L40-40 verbatim
namespace Outcome


-- @@ L42-57 verbatim
/--
Game outcomes are partially ordered in favour of Left, as illustrated in the
following Hasse diagram:
```
  L
 / \
N   P
 \ /
  R
```
-/
instance : LT Outcome where
  lt lhs rhs :=
    (lhs ≠ Outcome.L ∧ rhs = Outcome.L) ∨
    (lhs = Outcome.R ∧ rhs = Outcome.N) ∨
    (lhs = Outcome.R ∧ rhs = Outcome.P)


-- @@ L59-61 verbatim
instance : DecidableLT Outcome := by
  simp only [DecidableLT, DecidableRel, LT.lt]
  infer_instance


-- @@ L63-64 verbatim
instance instLE : LE Outcome where
  le lhs rhs := (lhs = rhs) ∨ (lhs < rhs)


-- @@ L66-68 verbatim
instance : DecidableLE Outcome := by
  simp only [DecidableLE, DecidableRel, LE.le]
  infer_instance


-- @@ L70-80 verbatim
instance : Preorder Outcome where
  le_refl _ := Or.inl rfl
  le_trans a b c _ _ := by
    cases a
    all_goals cases b
    all_goals cases c
    all_goals simp [LE.le, LT.lt] at *
  lt_iff_le_not_ge a b := by
    cases a
    all_goals cases b
    all_goals simp [LE.le, LT.lt] at *


-- @@ L82-86 verbatim
instance : PartialOrder Outcome where
  le_antisymm a b _ _ := by
    cases a
    all_goals cases b
    all_goals simp [LE.le, LT.lt] at *


-- @@ L88-93 verbatim
@[simp]
theorem ge_R (o : Outcome) : o ≥ Outcome.R := by
  simp only [ge_iff_le]
  unfold LE.le
  cases o
  all_goals simp [instLE, LT.lt]


-- @@ L95-99 verbatim
@[simp]
theorem le_R_iff (o : Outcome) : o ≤ Outcome.R ↔ o = .R := by
  constructor <;> intro h1
  · exact le_antisymm h1 (ge_R o)
  · rw [h1]


-- @@ L101-106 verbatim
@[simp]
theorem L_ge (o : Outcome) : Outcome.L ≥ o := by
  simp only [ge_iff_le]
  unfold LE.le
  cases o
  all_goals simp [instLE, LT.lt]


-- @@ L108-111 verbatim
theorem ge_P_ge_N_eq_L {o : Outcome} (hp : o ≥ Outcome.P) (hn : o ≥ Outcome.N)
    : o = Outcome.L := by
  cases o
  all_goals simp [LE.le, LT.lt, LE.le] at *


-- @@ L113-117 verbatim
@[simp]
theorem le_N_eq_N_or_R {o : Outcome} (hp : o ≤ Outcome.N)
    : o = Outcome.N ∨ o = Outcome.R := by
  cases o
  all_goals simp [LE.le, LT.lt, LE.le] at *


-- @@ L119-125 verbatim
/-- Conjugate an outcome by swapping the players. -/
@[expose]
def Conjugate : Outcome → Outcome
  | .L => .R
  | .R => .L
  | .P => .P
  | .N => .N


-- @@ L127-128 verbatim
theorem conjugate_conjugate_eq_self {o : Outcome} : o.Conjugate.Conjugate = o := by
  cases o <;> rfl


-- @@ L130-140 verbatim
theorem outcome_ge_conjugate_le {x y : Outcome} (h1 : x ≥ y) :
    x.Conjugate ≤ y.Conjugate := by
  cases h2 : x
    <;> cases h3 : y
    <;> unfold Outcome.Conjugate
    <;> simp only [LE.le, LT.lt, and_false, and_self, and_true, ne_eq, not_false_eq_true,
                   not_true_eq_false, or_self, reduceCtorEq, or_false, or_true]
    <;> simp only [h2, h3, ge_iff_le] at h1
    <;> absurd h1
    <;> simp only [LE.le, LT.lt, and_false, and_self, and_true, ne_eq, not_false_eq_true,
                   not_true_eq_false, or_self, reduceCtorEq]


-- @@ L142-148 verbatim
/-- The outcome determined by the winners when Left and Right start. -/
@[expose]
def ofPlayers : Player → Player → Outcome
  | .left, .left => Outcome.L
  | .right, .right => Outcome.R
  | .right, .left => Outcome.P
  | .left, .right => Outcome.N


-- @@ L150-154 verbatim
/-- The outcome where the given player wins no matter who starts. -/
@[expose]
def ofPlayer : Player → Outcome
  | .left => Outcome.L
  | .right => Outcome.R


-- @@ L156-157 verbatim
@[simp]
theorem ofPlayer_left : ofPlayer .left = .L := by rfl


-- @@ L159-160 verbatim
@[simp]
theorem ofPlayer_right : ofPlayer .right = .R := by rfl


-- @@ L162-162 verbatim
end Outcome


-- @@ L164-164 verbatim
end


-- @@ L166-166 verbatim
end MisereGames
