/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.PFunctor.Dynamical.Game
public import PolyFun.PFunctor.Lens.Composite


-- @@ L11-22 verbatim
/-!
# Examples for responders, games, and two-phase games

Regression tests: the `game` / `closedGame` step equations and the
responder eta canaries hold by `rfl`, `stepWith` at `m := Id` is the closed
game's step, the query-conditioned `DynComputation` run law specializes to a
nontrivial responder with the answer/state pair in the intended order, a
concrete counting-responder game runs by `rfl`, the Moore win-bit game is the
`Bool y^ PUnit` instance of `game`, and a deterministic PrivK-shaped
`game₂` (challenger as a composite lens, adversary via `orderPair`) computes one
composite step by `rfl`.
-/


-- @@ L24-24 verbatim
@[expose] public section


-- @@ L26-26 verbatim
universe u v


-- @@ L28-28 verbatim
namespace PFunctor


-- @@ L30-30 verbatim
/-! ## Structural canaries -/


-- @@ L32-32 verbatim
section Canaries


-- @@ L34-34 verbatim
variable {S T : Type u} {q r : PFunctor.{u, u}}


-- @@ L36-39 verbatim
/-- The game's exposed position is the committed challenger lens applied to the
adversary's position. -/
example (chal : DynSystem S (q ⊸ r)) (adv : DynSystem T q) (s : S) (t : T) :
    (DynSystem.game chal adv).expose (s, t) = (chal.expose s).toFunA (adv.expose t) := rfl


-- @@ L41-47 verbatim
/-- The game's update: the challenger hears the adversary's query with the outer
direction; the adversary hears the committed lens's pulled-back answer. -/
example (chal : DynSystem S (q ⊸ r)) (adv : DynSystem T q) (s : S) (t : T)
    (d : r.B ((DynSystem.game chal adv).expose (s, t))) :
    (DynSystem.game chal adv).update (s, t) d
      = (chal.update s ⟨adv.expose t, d⟩,
          adv.update t ((chal.expose s).toFunB (adv.expose t) d)) := rfl


-- @@ L49-52 verbatim
/-- The closed game steps by "adversary queries, responder answers". -/
example (R : Responder S q) (adv : DynSystem T q) (s : S) (t : T) :
    (DynSystem.closedGame R adv).step (s, t)
      = (R.next s (adv.expose t), adv.update t (R.answer s (adv.expose t))) := rfl


-- @@ L54-58 verbatim
/-- The game former is the uncurried challenger (tensor–hom adjunction). -/
example (chal : DynSystem S (q ⊸ r)) (adv : DynSystem T q) :
    DynSystem.game chal adv
      = ((Lens.id (selfMonomial S) ⊗ₗ adv) ⨟ Lens.uncurry chal :
          Lens (selfMonomial S ⊗ selfMonomial T) r) := rfl


-- @@ L60-62 verbatim
/-- Eta canary: a responder's raw lens update reads only the query component. -/
example (R : Responder S q) (s : S) (d : (q ⊸ y).B (DynSystem.expose R s)) :
    DynSystem.update R s d = R.next s d.1 := rfl


-- @@ L64-65 verbatim
/-- Eta canaries: the Kleisli–Mealy round-trips are definitional. -/
example (R : Responder S q) : Responder.ofStateHandler R.toStateHandler = R := rfl


-- @@ L67-68 verbatim
example (h : Handler (StateT S Id) q) :
    Responder.toStateHandler (Responder.ofStateHandler h) = h := rfl


-- @@ L70-71 verbatim
example (R : Responder S q) :
    Responder.equivStateHandler.symm (Responder.equivStateHandler R) = R := rfl


-- @@ L73-77 verbatim
/-- `stepWith` against a responder's stateful handler, at `m := Id`, is the
closed game's step. -/
example (R : Responder T q) (A : DynSystem S q) (p : T × S) :
    DynSystem.stepWith (m := Id) R.toStateHandler A p
      = (DynSystem.closedGame R A).step p := rfl


-- @@ L79-79 verbatim
end Canaries


-- @@ L81-81 verbatim
/-! ## Returning computations against responders -/


-- @@ L83-93 verbatim
/-- One visible `true` query whose answer becomes the terminal result. -/
def responderQueryComputation : DynSystem.DynComputation (Bool y^ Nat) PUnit Nat where
  State := Option Nat
  toDynSystem :=
    (fun
      | none => Sum.inl true
      | some value => Sum.inr value) ⇆
    fun
      | none => fun answer => some answer
      | some _ => PEmpty.elim
  init := fun _ => none


-- @@ L95-99 verbatim
/-- On the exposed `true` query, answer with `state + 10` and advance the
responder state by one. The two components are deliberately distinguishable. -/
def answerAndAdvanceResponder : Responder Nat (Bool y^ Nat) :=
  Responder.mk' (fun state query => Bool.rec (state + 20) (state + 10) query)
    (fun state query => Bool.rec (state + 2) (state + 1) query)


-- @@ L101-102 verbatim
@[simp] theorem answerAndAdvanceResponder_answer_true (state : Nat) :
    answerAndAdvanceResponder.answer state true = state + 10 := rfl


-- @@ L104-105 verbatim
@[simp] theorem answerAndAdvanceResponder_next_true (state : Nat) :
    answerAndAdvanceResponder.next state true = state + 1 := rfl


-- @@ L107-108 verbatim
def answerAndAdvanceHandler : Handler (StateT Nat (Id.{0})) (Bool y^ Nat) :=
  answerAndAdvanceResponder.toStateHandler


-- @@ L110-111 verbatim
def responderQueryRun (fuel : Nat) (state : Option Nat) : StateT Nat (Id.{0}) (Option Nat) :=
  responderQueryComputation.{0}.runWith answerAndAdvanceHandler fuel state


-- @@ L113-124 verbatim
/-- The query-branch run law exposed through `Game` selects the computation's
answer-indexed continuation and threads the responder's next state. Writing the
right-hand side explicitly makes an answer/state swap fail this canary. -/
example (fuel responderState : Nat) :
    (responderQueryRun (fuel + 1) none).run responderState =
      (responderQueryRun fuel (some (responderState + 10))).run
        (responderState + 1) := by
  unfold responderQueryRun
  rw [responderQueryComputation.runWith_query_succ_stateT
    answerAndAdvanceHandler fuel none true
    (fun answer => some answer) rfl responderState]
  rfl


-- @@ L126-126 verbatim
/-! ## A concrete closed game: counting responder vs doubling adversary -/


-- @@ L128-131 verbatim
/-- The counting responder over `ℕ y^ ℕ`: answers every query with its running
count and increments it. -/
def countingResponder : Responder ℕ (ℕ y^ ℕ) :=
  Responder.mk' (fun s _ => s) (fun s _ => s + 1)


-- @@ L133-136 verbatim
/-- The doubling adversary over `ℕ y^ ℕ`: queries its state, stores double the
answer it hears. -/
def doublingAdversary : DynSystem ℕ (ℕ y^ ℕ) :=
  id ⇆ fun _ (a : ℕ) => 2 * a


-- @@ L138-141 verbatim
/-- Three closed-game steps, computed by `rfl`:
`(0, 5) ↦ (1, 0) ↦ (2, 2) ↦ (3, 4)`. -/
example : (DynSystem.closedGame countingResponder doublingAdversary).iterate (0, 5) 3
    = (3, 4) := rfl


-- @@ L143-143 verbatim
/-! ## The Moore win-bit game: `game` at `r := Bool y^ PUnit` -/


-- @@ L145-148 verbatim
/-- A challenger with a Moore win bit: the adversary wins when its query matches
the secret; every answer leaks the secret, and the secret never changes. -/
def secretMatchChallenger : DynSystem ℕ (ℕ y^ ℕ ⊸ Bool y^ PUnit) :=
  (fun s => (fun (qy : ℕ) => qy == s) ⇆ fun _ _ => s) ⇆ fun s _ => s


-- @@ L150-153 verbatim
/-- The win-bit game *is* a Moore machine: `game` at `r := Bool y^ PUnit`
lands in `MooreMachine (S × T) Bool PUnit`, no scored-game structure needed. -/
def secretMatchGame : MooreMachine (ℕ × ℕ) Bool PUnit :=
  DynSystem.game secretMatchChallenger doublingAdversary


-- @@ L155-155 verbatim
example : secretMatchGame.output (3, 3) = true := rfl


-- @@ L157-157 verbatim
example : secretMatchGame.output (3, 4) = false := rfl


-- @@ L159-162 verbatim
/-- Close the Moore game with trivial feedback and step it: the challenger keeps
its secret, the adversary stores double the leaked secret. -/
example : (MooreMachine.feedback (fun _ => PUnit.unit) secretMatchGame).step (3, 3)
    = (3, 6) := rfl


-- @@ L164-171 verbatim
/-! ## A deterministic PrivK-shaped two-phase game

Commit phase `(Bool × Bool) y^ Bool`: the adversary submits a message-bit pair
and hears the "ciphertext" `m_b`. Guess phase `Bool y^ PUnit`: the adversary
submits a guess and the outer interface `Bool y^ PUnit` exposes the win bit.
The challenger is written directly as the corresponding composite lens, and
the two single-phase adversaries are ordered by `orderPair` — so the guesser
cannot see the ciphertext within the composite step, as documented there. -/


-- @@ L173-180 verbatim
/-- The PrivK challenger, from its destructor triple: state is the secret bit
`b`; commit phase answers `m_b`; guess phase exposes `guess == b`. -/
def privKChallenger : DynSystem Bool (((Bool × Bool) y^ Bool ⊸ y.{0, 0})
    ◃ (Bool y^ PUnit ⊸ Bool y^ PUnit)) :=
  (fun b =>
    ⟨sectionLens (fun mm => cond b mm.2 mm.1),
      fun _ => (fun (guess : Bool) => guess == b) ⇆ (fun _ _ => PUnit.unit)⟩) ⇆
    fun b _ => b


-- @@ L182-184 verbatim
/-- The commit-phase adversary: submits the fixed message pair `(false, true)`. -/
def commitAdversary : DynSystem PUnit ((Bool × Bool) y^ Bool) :=
  Lens.fromY (false, true)


-- @@ L186-188 verbatim
/-- The guess-phase adversary: guesses its own (fixed) state bit. -/
def guessAdversary : DynSystem Bool (Bool y^ PUnit) :=
  id ⇆ fun t _ => t


-- @@ L190-192 verbatim
/-- The full PrivK-shaped game: challenger against the ordered adversary pair. -/
def privKGame : DynSystem (Bool × (PUnit × Bool)) (y.{0, 0} ◃ Bool y^ PUnit) :=
  DynSystem.game₂ privKChallenger (DynSystem.orderPair commitAdversary guessAdversary)


-- @@ L194-196 verbatim
/-- With secret `true` and message pair `(false, true)`, guessing `true` wins:
the composite position's continuation carries the win bit. -/
example : (privKGame.expose (true, (PUnit.unit, true))).2 PUnit.unit = true := rfl


-- @@ L198-199 verbatim
/-- Guessing `false` against secret `true` loses. -/
example : (privKGame.expose (true, (PUnit.unit, false))).2 PUnit.unit = false := rfl


-- @@ L201-204 verbatim
/-- One composite step of the game, by `rfl`: every participant here is
stationary, so the state is unchanged. -/
example : privKGame.update (true, (PUnit.unit, true)) ⟨PUnit.unit, PUnit.unit⟩
    = (true, (PUnit.unit, true)) := rfl


-- @@ L206-206 verbatim
end PFunctor
