/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alfie Davies, Tomasz Maciosowski, Violeta Hernández Palacios
-/
module

public import LeanPool.MisereGames.Form
public import LeanPool.MisereGames.Mathlib.NatOrdinal


-- @@ L11-13 verbatim
/-!
Misere combinatorial games.
-/


-- @@ L15-15 verbatim
namespace MisereGames


-- @@ L17-31 verbatim
/-!
# Birthdays of games

There are two related but distinct notions of a birthday within combinatorial
game theory. One is the birthday of an `GameForm`, which represents the "step"
at which it is constructed; the *day* on which it is *born*. This is sometimes
called the *formal birthday* of a game (see [Siegel, Definition 1.27 on p.
61][siegel:CombinatorialGameTheory:2013]).

It can be defined recursively as the least ordinal strictly larger than the
birthdays of its Left and Right options.

The birthday of an `GameForm` can also be understood as the depth of its game
tree.
-/


-- @@ L33-33 verbatim
open NatOrdinal Order Set


-- @@ L35-35 verbatim
universe u


-- @@ L37-37 verbatim
public section


-- @@ L39-39 verbatim
namespace Form


-- @@ L41-41 verbatim
open Form


-- @@ L43-43 verbatim
variable {G : Type (u + 1)} [g_form : Form G]


-- @@ L45-54 expanded
/-- The birthday of a form is inductively defined as the least ordinal strictly
larger than the birthdays of its options. It may be thought as the "step" in
which the given game is constructed.
-/
@[expose]
noncomputable def birthday (x : G) : NatOrdinal.{u + 1} :=
  ⨆ y : { y // IsOption y x }, Order.succ (birthday y)
termination_by x
decreasing_by
  all_goals
    solve_by_elim (maxDepth := 8) [Prod.Lex.left, Prod.Lex.right, PSigma.Lex.left, PSigma.Lex.right,
      Subposition.of_mem_moves, Subposition.trans, Subtype.prop]


-- @@ L56-59 verbatim
theorem lt_birthday_iff' {x : G} {o : NatOrdinal} : o < birthday x ↔
    ∃ y, IsOption y x ∧ o ≤ birthday y := by
  rw [birthday, NatOrdinal.lt_iSup_iff]
  simp only [succ_eq_add_one, lt_add_one_iff, Subtype.exists, exists_prop]


-- @@ L61-63 verbatim
theorem birthday_le_iff' {x : G} {o : NatOrdinal} : birthday x ≤ o ↔
    ∀ y, IsOption y x → birthday y < o := by
  simpa using lt_birthday_iff'.not


-- @@ L65-67 verbatim
theorem lt_birthday_iff {x : G} {o : NatOrdinal} : o < birthday x ↔
    (∃ y ∈ moves .left x, o ≤ birthday y) ∨ (∃ y ∈ moves .right x, o ≤ birthday y) := by
  simp [lt_birthday_iff', IsOption.iff_mem_union, or_and_right, exists_or]


-- @@ L69-71 verbatim
theorem birthday_le_iff {x : G} {o : NatOrdinal} : birthday x ≤ o ↔
    (∀ y ∈ moves .left x, birthday y < o) ∧ (∀ y ∈ moves .right x, birthday y < o) := by
  simpa using lt_birthday_iff.not


-- @@ L73-77 verbatim
theorem birthday_eq_max (x : G) : birthday x =
    max (⨆ y : moves .left x, succ (birthday y.1)) (⨆ y : moves .right x, succ (birthday y.1)) := by
  apply eq_of_forall_lt_iff
  simp only [lt_birthday_iff, succ_eq_add_one, lt_sup_iff, NatOrdinal.lt_iSup_iff, lt_add_one_iff,
             Subtype.exists, exists_prop, implies_true]


-- @@ L79-82 verbatim
@[aesop safe apply]
theorem birthday_lt_of_mem_moves {p : Player} {x y : G} (hy : y ∈ moves p x) :
    birthday y < birthday x :=
  lt_birthday_iff'.2 ⟨y, .of_mem_moves hy, le_rfl⟩


-- @@ L84-85 verbatim
theorem birthday_lt_of_isOption {x y : G} (hy : IsOption y x) : birthday y < birthday x :=
  lt_birthday_iff'.2 ⟨y, hy, le_rfl⟩


-- @@ L87-93 expanded
theorem birthday_lt_of_subposition {x y : G} (hy : Subposition y x) : birthday y < birthday x := by
  cases hy with
  | single h => exact birthday_lt_of_isOption h
  | tail IH h => exact (birthday_lt_of_subposition IH).trans (birthday_lt_of_isOption h)
termination_by x
decreasing_by
  all_goals
    solve_by_elim (maxDepth := 8) [Prod.Lex.left, Prod.Lex.right, PSigma.Lex.left, PSigma.Lex.right,
      Subposition.of_mem_moves, Subposition.trans, Subtype.prop]


-- @@ L95-106 expanded
@[simp]
theorem birthday_neg (x : G) : birthday (-x) = birthday x :=
  by
  refine eq_of_forall_lt_iff fun y ↦ ?_
  rw [lt_birthday_iff, lt_birthday_iff]
  rw [exists_moves_neg, exists_moves_neg, or_comm]
  congr! 3
  all_goals
    dsimp; rw [and_congr_right]
    intro h
    rw [birthday_neg]
termination_by x
decreasing_by
  all_goals
    solve_by_elim (maxDepth := 8) [Prod.Lex.left, Prod.Lex.right, PSigma.Lex.left, PSigma.Lex.right,
      Subposition.of_mem_moves, Subposition.trans, Subtype.prop]


-- @@ L108-125 expanded
@[simp]
theorem birthday_add (g h : G) : birthday (g + h) = birthday g + birthday h :=
  by
  refine eq_of_forall_lt_iff fun o ↦ ?_
  simp only [lt_birthday_iff, moves_add, mem_union, mem_image, or_and_right, exists_or,
    ↓existsAndEq, and_true, lt_add_iff, or_or_or_comm]
  congr! 2
  all_goals
    constructor
    · rintro ⟨z, hz, hz'⟩
      refine ⟨_, ⟨z, hz, le_rfl⟩, ?_⟩
      rwa [← birthday_add]
    · rintro ⟨a, ⟨⟨z, hz, hz'⟩, ha⟩⟩
      use z, hz
      rw [birthday_add]
      apply ha.trans
      first
      | exact add_le_add_left hz' _
      | exact add_le_add_right hz' _
termination_by (g, h)
decreasing_by
  all_goals
    solve_by_elim (maxDepth := 8) [Prod.Lex.left, Prod.Lex.right, PSigma.Lex.left, PSigma.Lex.right,
      Subposition.of_mem_moves, Subposition.trans, Subtype.prop]


-- @@ L127-129 verbatim
theorem birthday_add_lt_left {g' g h : G} (hlt : birthday g' < birthday g) :
    birthday g' + birthday h < birthday g + birthday h := by
  gcongr


-- @@ L131-133 verbatim
theorem birthday_add_lt_right {g h' h : G} (hlt : birthday h' < birthday h) :
    birthday g + birthday h' < birthday g + birthday h := by
  gcongr


-- @@ L135-140 expanded
@[simp]
theorem birthday_ofSets (s t : Set G) [Small.{u} s] [Small.{u} t] :
    birthday
        (OfSets.ofSets (Player.cases s t)
          (by
            first
            | done
            | trivial
            | assumption
            | aesop
            |
              fail "failed to prove sets are valid, try to use `!{st}'h` notation instead, \
                where `h` is a proof that sets are valid")) =
      max (sSup (succ ∘ birthday '' s)) (sSup (succ ∘ birthday '' t)) :=
  by
  rw [birthday_eq_max]
  rw [leftMoves_ofSets, rightMoves_ofSets]
  simp only [iSup, succ_eq_add_one, Function.comp_apply, image_eq_range]


-- @@ L142-146 expanded
@[simp]
theorem birthday_ofSets_const (s : Set G) [Small.{u} s] :
    birthday
        (OfSets.ofSets (fun _ ↦ s)
          (by
            first
            | done
            | trivial
            | assumption
            | aesop
            |
              fail "failed to prove sets are valid, try to use `!{st}'h` notation instead, \
                where `h` is a proof that sets are valid")) =
      sSup (succ ∘ birthday '' s) :=
  by
  rw [ofSets_eq_ofSets_cases, birthday_ofSets]
  exact max_eq_left le_rfl


-- @@ L148-151 verbatim
@[simp]
theorem birthday_zero : birthday (0 : G) = 0 := by
  unfold birthday
  simp [iSup_eq_zero_iff]


-- @@ L153-154 verbatim
@[simp]
theorem birthday_one : birthday (1 : G) = 1 := by simp [one_def]


-- @@ L156-160 verbatim
@[simp]
theorem birthday_natCast (n : ℕ) : birthday (n : G) = n := by
  induction n with
  | zero => simp only [Nat.cast_zero, birthday_zero]
  | succ k ih => simpa only [Nat.cast_add, Nat.cast_one, birthday_add, birthday_one, add_left_inj]


-- @@ L162-164 verbatim
@[simp]
theorem birthday_ofNat (n : ℕ) [n.AtLeastTwo] : birthday (ofNat(n) : G) = n := by
  simp only [OfNat.ofNat, birthday_natCast]


-- @@ L166-170 verbatim
@[simp]
theorem birthday_intCast (k : ℤ) : birthday (k : G) = k.natAbs := by
  match k with
  | Int.ofNat n => simp
  | Int.negSucc n => simpa using add_comm (G := NatOrdinal) 1 n


-- @@ L172-172 verbatim
open Lean Meta Elab Tactic


-- @@ L174-196 verbatim
/-- Add birthday inequalities from move hypotheses, then simplify birthday arithmetic. -/
elab (name := gameformBirthday) "gameform_birthday" : tactic => do
  Lean.Elab.Tactic.withMainContext do
    -- TODO: Also generate proofs from IsOption g' g and Subposition g' g
    -- From (g' ∈ moves p g) generate proofs for (birthday g' < birthday g)
    let lctx ← getLCtx
    for h in lctx do
      if h.isImplementationDetail then continue
      let type ← instantiateMVars h.type
      if type.isAppOfArity ``Membership.mem 5 then
        let args := type.getAppArgs
        let collection := args[3]!
        if collection.getAppFn.isConstOf `Moves.moves then
          let birthdayName ← mkFreshUserName `h
          let birthdayProof ← mkAppM `Form.birthday_lt_of_mem_moves #[h.toExpr]
          liftMetaTactic fun goalId => do
            let newGoalId ← goalId.assert birthdayName (← inferType birthdayProof) birthdayProof
            let (_, birthdayProofId) ← newGoalId.intro1P
            return [birthdayProofId]
  Lean.Elab.Tactic.withMainContext do
    evalTactic (← `(tactic| try simp only [Form.birthday_neg, Form.birthday_add] at *))
    evalTactic (← `(tactic| try simp))
    evalTactic (← `(tactic| try omega))


-- @@ L198-198 verbatim
end Form


-- @@ L200-200 verbatim
end


-- @@ L202-202 verbatim
end MisereGames
