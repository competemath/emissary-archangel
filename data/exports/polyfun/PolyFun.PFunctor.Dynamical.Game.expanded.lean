/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.PFunctor.Dynamical.Responder
public import PolyFun.PFunctor.Dynamical.DynComputation.Bounded
public import PolyFun.PFunctor.Dynamical.Combinators
public import PolyFun.PFunctor.Lens.Duoidal


-- @@ L13-48 verbatim
/-!
# Games: challengers wired against adversaries along evaluation

A **game** pairs a challenger, whose interface is an internal hom `q ⊸ r`
(Spivak–Niu Ex 4.78), with an adversary playing `q`. Wiring the two along the
evaluation lens `Lens.eval : (q ⊸ r) ⊗ q ⟹ r` (`DynSystem.game`) yields a single
system over the outer interface `r`; equivalently — definitionally — it is the
uncurried challenger applied to the adversary (`game_eq_uncurry`), the
tensor–hom adjunction in dynamical clothing. When the challenger is a
`Responder` (`r = y`) the game is closed and runs autonomously
(`DynSystem.closedGame`), the deterministic shadow of VCVio's `wireKStep`
wiring. There is no separate scored-game structure: a win readout is a state (or
Moore) readout on the closed run, and the win-bit form is the
`r := Bool y^ PUnit` instance of `game`.

Monadic runs against handlers are provided in two strengths: `kleisliStep` /
`kleisliIterate` drive a system with a stateless handler in a monad `m` (VCVio's
`wireKStep` / `wireKIterate` are the `m := SPMF` instances), and `stepWith` /
`iterWith` drive it with a *stateful* handler in `StateT σ m`, the handler state
first in the pair. The two agree along `StateT.lift` (`stepWith_lift`), and at
`m := Id` a responder's handler recovers the closed game
(`stepWith_toStateHandler`). The load-bearing export is
`DynComputation.runWith_query_succ_stateT`: under an explicit visible-query
view, it unrolls one unit of fuel through the stateful handler and threads the
answer and handler state into the residual computation. The query hypothesis
is essential because a returned computation state has no query transition.

Two-phase (commit-then-guess) games arrive by substitution: `Lens.eval₂` runs
two evaluations in sequence after reshuffling along the duoidal interchange
`Lens.duoidalLens` (Spivak–Niu Eq 6.86), `DynSystem.orderPair` orders two
single-phase adversaries into a `q₁ ◃ q₂` player along `Lens.orderingLens`
(Ex 6.85), and `DynSystem.game₂` wires a two-phase challenger against a
two-phase adversary. `Lens.compOuter`, `Lens.compInner`, and `Lens.compPullback`
(Ex 6.40) are the
intro/elim rules for the two-phase challenger interface.
-/


-- @@ L50-50 verbatim
@[expose] public section


-- @@ L52-52 verbatim
universe u v uA uB uA₁ uB₁ uA₂ uB₂


-- @@ L54-54 verbatim
namespace PFunctor


-- @@ L56-56 verbatim
namespace DynSystem


-- @@ L58-58 verbatim
/-! ## The game former -/


-- @@ L60-60 verbatim
section Game


-- @@ L62-62 verbatim
variable {S : Type u} {T : Type v} {q r : PFunctor.{uA, uB}}


-- @@ L64-71 verbatim
/-- Wire a challenger over the internal hom `q ⊸ r` against an adversary playing
`q`, along the evaluation lens (Spivak–Niu Ex 4.78): at each step the challenger
commits to a lens `q ⟹ r`, the adversary picks a `q`-position, and the composite
exposes the resulting `r`-position; the incoming `r`-direction is answered back
through the committed lens. VCVio's `Challenger`-vs-adversary wiring is the
Kleisli consumer of this former. -/
def game (chal : DynSystem S (q ⊸ r)) (adv : DynSystem T q) : DynSystem (S × T) r :=
  wire₂ (Lens.eval q r) chal adv


-- @@ L73-75 verbatim
@[simp] theorem game_expose (chal : DynSystem S (q ⊸ r)) (adv : DynSystem T q)
    (s : S) (t : T) :
    (game chal adv).expose (s, t) = (chal.expose s).toFunA (adv.expose t) := rfl


-- @@ L77-81 verbatim
@[simp] theorem game_update (chal : DynSystem S (q ⊸ r)) (adv : DynSystem T q)
    (s : S) (t : T) (d : r.B ((game chal adv).expose (s, t))) :
    (game chal adv).update (s, t) d
      = (chal.update s ⟨adv.expose t, d⟩,
          adv.update t ((chal.expose s).toFunB (adv.expose t) d)) := rfl


-- @@ L83-84 verbatim
theorem game_eq_wire₂ (chal : DynSystem S (q ⊸ r)) (adv : DynSystem T q) :
    game chal adv = wire₂ (Lens.eval q r) chal adv := rfl


-- @@ L86-86 verbatim
end Game


-- @@ L88-95 verbatim
/-- The game former is evaluation of the uncurried challenger: wiring along
`Lens.eval` is the tensor–hom adjunction in dynamical clothing. Stated with the
challenger's state universe identified with the interface universes, as
`Lens.uncurry` requires. -/
theorem game_eq_uncurry {S : Type u} {T : Type v} {q r : PFunctor.{u, u}}
    (chal : DynSystem S (q ⊸ r)) (adv : DynSystem T q) :
    game chal adv = ((Lens.id (selfMonomial S) ⊗ₗ adv) ⨟ Lens.uncurry chal :
      Lens (selfMonomial S ⊗ selfMonomial T) r) := rfl


-- @@ L97-97 verbatim
/-! ## Closed games -/


-- @@ L99-99 verbatim
section Game


-- @@ L101-101 verbatim
variable {S : Type u} {T : Type v} {q : PFunctor.{uA, uB}}


-- @@ L103-109 verbatim
/-- Close a responder against an adversary: the `r = y` instance of `game` runs
autonomously, so the pair steps by "adversary queries, responder answers". This
is the deterministic shadow of VCVio's `wireKStep`; a win condition is a state
readout on the closed run (for a Moore win bit, instantiate `game` at
`r := Bool y^ PUnit` instead). -/
def closedGame (R : Responder S q) (adv : DynSystem T q) : Closed (S × T) :=
  game R adv


-- @@ L111-113 verbatim
@[simp] theorem closedGame_step (R : Responder S q) (adv : DynSystem T q) (s : S) (t : T) :
    (closedGame R adv).step (s, t)
      = (R.next s (adv.expose t), adv.update t (R.answer s (adv.expose t))) := rfl


-- @@ L115-115 verbatim
end Game


-- @@ L117-117 verbatim
/-! ## Kleisli runs against monadic handlers -/


-- @@ L119-119 verbatim
section Kleisli


-- @@ L121-121 verbatim
variable {q : PFunctor.{uA, u}} {S σ : Type u} {m : Type u → Type v} [Monad m]


-- @@ L123-127 verbatim
/-- One step of a system driven by a stateless monadic handler: resolve the
exposed position in `m` and update. VCVio's `wireKStep` is the `m := SPMF`
instance. -/
def kleisliStep (h : Handler m q) (A : DynSystem S q) (s : S) : m S :=
  (fun d => A.update s d) <$> h (A.expose s)


-- @@ L129-133 verbatim
/-- `n` monadic steps of a system against a stateless handler. VCVio's
`wireKIterate` is the `m := SPMF` instance. -/
def kleisliIterate (h : Handler m q) (A : DynSystem S q) : ℕ → S → m S
  | 0, s => pure s
  | n + 1, s => kleisliStep h A s >>= kleisliIterate h A n


-- @@ L135-136 verbatim
@[simp] theorem kleisliIterate_zero (h : Handler m q) (A : DynSystem S q) (s : S) :
    kleisliIterate h A 0 s = pure s := rfl


-- @@ L138-139 verbatim
theorem kleisliIterate_succ (h : Handler m q) (A : DynSystem S q) (n : ℕ) (s : S) :
    kleisliIterate h A (n + 1) s = kleisliStep h A s >>= kleisliIterate h A n := rfl


-- @@ L141-145 verbatim
/-- One step of a system driven by a *stateful* handler: the handler threads its
own state `σ` alongside the system's, handler state first in the pair. -/
def stepWith (h : Handler.Stateful m σ q) (A : DynSystem S q)
    (p : σ × S) : m (σ × S) :=
  (fun dt => (dt.2, A.update p.2 dt.1)) <$> h (A.expose p.2) p.1


-- @@ L147-152 verbatim
/-- `n` steps of a system against a stateful handler, threading the handler
state. -/
def iterWith (h : Handler.Stateful m σ q) (A : DynSystem S q) :
    ℕ → σ × S → m (σ × S)
  | 0, p => pure p
  | n + 1, p => stepWith h A p >>= iterWith h A n


-- @@ L154-155 verbatim
@[simp] theorem iterWith_zero (h : Handler (StateT σ m) q) (A : DynSystem S q) (p : σ × S) :
    iterWith h A 0 p = pure p := rfl


-- @@ L157-158 verbatim
theorem iterWith_succ (h : Handler (StateT σ m) q) (A : DynSystem S q) (n : ℕ) (p : σ × S) :
    iterWith h A (n + 1) p = stepWith h A p >>= iterWith h A n := rfl


-- @@ L160-165 verbatim
/-- A stateless handler lifted into the state monad steps the system as
`kleisliStep` does and carries the handler state unchanged. -/
theorem stepWith_lift [LawfulMonad m] (h₀ : Handler m q) (A : DynSystem S q) (p : σ × S) :
    stepWith (fun a => StateT.lift (h₀ a)) A p
      = (fun s' => (p.1, s')) <$> kleisliStep h₀ A p.2 := by
  simp [stepWith, kleisliStep, StateT.lift]


-- @@ L167-178 verbatim
/-- A lifted stateless handler runs as `kleisliIterate` does, carrying the
handler state unchanged. -/
theorem iterWith_lift [LawfulMonad m] (h₀ : Handler m q) (A : DynSystem S q) (n : ℕ)
    (p : σ × S) :
    iterWith (fun a => StateT.lift (h₀ a)) A n p
      = (fun s' => (p.1, s')) <$> kleisliIterate h₀ A n p.2 := by
  induction n generalizing p with
  | zero => simp
  | succ n ih =>
    rw [iterWith_succ, kleisliIterate_succ, stepWith_lift]
    simp only [bind_map_left, map_bind]
    exact bind_congr fun s' => ih (p.1, s')


-- @@ L180-183 verbatim
/-- Running a system against a responder's stateful handler is stepping the
closed game: `stepWith` at `m := Id` is `closedGame`'s step. -/
theorem stepWith_toStateHandler (R : Responder σ q) (A : DynSystem S q) (p : σ × S) :
    stepWith (m := Id) R.toStateHandler A p = (closedGame R A).step p := rfl


-- @@ L185-194 verbatim
/-- The `Id` run against a responder's stateful handler computes the closed
game's trajectory. -/
theorem iterWith_toStateHandler (R : Responder σ q) (A : DynSystem S q) (n : ℕ) (p : σ × S) :
    iterWith (m := Id) R.toStateHandler A n p = pure ((closedGame R A).iterate p n) := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih =>
    change iterWith (m := Id) R.toStateHandler A n (stepWith (m := Id) R.toStateHandler A p) = _
    rw [stepWith_toStateHandler, ih]
    rfl


-- @@ L196-196 verbatim
end Kleisli


-- @@ L198-198 verbatim
end DynSystem


-- @@ L200-205 verbatim
/-! ## Two-phase games

Commit-then-guess games by substitution: the challenger plays
`(q₁ ⊸ r₁) ◃ (q₂ ⊸ r₂)` — a phase-one responder lens whose continuation, fed the
phase-one transcript, is a phase-two responder lens — and the adversary plays
`q₁ ◃ q₂`. -/


-- @@ L207-207 verbatim
namespace Lens


-- @@ L209-215 verbatim
/-- The **two-phase evaluation wiring**: reshuffle a two-phase challenger against
a two-phase adversary along the duoidal interchange `duoidalLens` (Spivak–Niu
Eq 6.86), so the phase-one pair and phase-two pair each meet in an evaluation
lens (Ex 4.78), run in sequence. -/
def eval₂ (q₁ r₁ q₂ r₂ : PFunctor.{uA, uB}) :
    Lens (((q₁ ⊸ r₁) ◃ (q₂ ⊸ r₂)) ⊗ (q₁ ◃ q₂)) (r₁ ◃ r₂) :=
  duoidalLens (q₁ ⊸ r₁) (q₂ ⊸ r₂) q₁ q₂ ⨟ (eval q₁ r₁ ◃ₗ eval q₂ r₂)


-- @@ L217-217 verbatim
end Lens


-- @@ L219-219 verbatim
namespace DynSystem


-- @@ L221-221 verbatim
section OrderPair


-- @@ L223-223 verbatim
variable {T₁ : Type u} {T₂ : Type v} {q₁ : PFunctor.{uA₁, uB₁}} {q₂ : PFunctor.{uA₂, uB₂}}


-- @@ L225-234 verbatim
/-- Order two systems into a single two-phase system along `Lens.orderingLens`
(Spivak–Niu Ex 6.85): the pair plays `q₁ ◃ q₂`, phase one first. **The second
phase cannot see the first phase's answer within one composite step**: before
ordering, the two phases were simultaneous (`tensor`), and the ordering lens
makes the phase-two position constant in the phase-one direction. A
same-step-adaptive second phase (e.g. a guesser reading the commit phase's
answer) must instead be built directly as a system over `q₁ ◃ q₂`. -/
def orderPair (A₁ : DynSystem T₁ q₁) (A₂ : DynSystem T₂ q₂) :
    DynSystem (T₁ × T₂) (q₁ ◃ q₂) :=
  wrap (Lens.orderingLens q₁ q₂) (A₁.tensor A₂)


-- @@ L236-238 verbatim
@[simp] theorem orderPair_expose (A₁ : DynSystem T₁ q₁) (A₂ : DynSystem T₂ q₂)
    (st : T₁ × T₂) :
    (orderPair A₁ A₂).expose st = ⟨A₁.expose st.1, fun _ => A₂.expose st.2⟩ := rfl


-- @@ L240-242 verbatim
@[simp] theorem orderPair_update (A₁ : DynSystem T₁ q₁) (A₂ : DynSystem T₂ q₂)
    (st : T₁ × T₂) (d : (q₁ ◃ q₂).B ((orderPair A₁ A₂).expose st)) :
    (orderPair A₁ A₂).update st d = (A₁.update st.1 d.1, A₂.update st.2 d.2) := rfl


-- @@ L244-244 verbatim
end OrderPair


-- @@ L246-246 verbatim
section Game₂


-- @@ L248-248 verbatim
variable {S : Type u} {T : Type v} {q₁ r₁ q₂ r₂ : PFunctor.{uA, uB}}


-- @@ L250-258 verbatim
/-- Wire a two-phase challenger against a two-phase adversary along
`Lens.eval₂`: commit phase, then guess phase, exposed on the outer interface
`r₁ ◃ r₂`. The challenger's interface has the direct composite-lens accessors
`compOuter`, `compInner`, and `compPullback` (Spivak–Niu Ex 6.40) as its
elimination rules; VCVio's
`Challenger₂` is the Kleisli consumer of this former. -/
def game₂ (chal : DynSystem S ((q₁ ⊸ r₁) ◃ (q₂ ⊸ r₂))) (adv : DynSystem T (q₁ ◃ q₂)) :
    DynSystem (S × T) (r₁ ◃ r₂) :=
  wire₂ (Lens.eval₂ q₁ r₁ q₂ r₂) chal adv


-- @@ L260-260 verbatim
end Game₂


-- @@ L262-262 verbatim
end DynSystem


-- @@ L264-264 verbatim
end PFunctor
