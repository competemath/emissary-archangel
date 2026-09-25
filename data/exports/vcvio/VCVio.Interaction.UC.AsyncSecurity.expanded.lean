/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import PolyFun.Interaction.Concurrent.Fairness
public import VCVio.Interaction.UC.AsyncRuntime
public import VCVio.Interaction.UC.Computational


-- @@ L13-77 verbatim
/-!
# Fair PPT security for asynchronous env-open processes

This file lifts the synchronous `Concurrent.Fairness` ticket
machinery to the asynchronous runtime in `AsyncRuntime.lean`, and
packages a fair-PPT computational security definition
`secureAgainstFair` that quantifies over scheduler pairs
satisfying user-specified PPT and fairness predicates.

## Main definitions

* `AsyncRun process envAction` — an infinite execution of the async
  runtime, structured as in `Concurrent.ProcessOver.Run` but
  threading the runtime alphabet `RuntimeEvent Event`.
* `Ticketed Party Δ Event State` — an `EnvOpenProcess` paired with
  a stable ticket map for its underlying process steps. Lifts
  `Concurrent.ProcessOver.Ticketed` to the env-open setting.
* `Ticketed.enabledAt` / `Ticketed.firedAt` — process-side ticket
  predicates evaluated on `AsyncRun`.
* `Ticketed.WeakFairOn` / `StrongFairOn` / `WeakFair` /
  `StrongFair` — process-side fairness predicates lifted from
  `Concurrent.Fairness`.
* `SchedulerPair Party m State Event` — the joint adversary type
  for the async runtime: a process scheduler plus a sibling env
  scheduler.
* `secureAgainstFair mkSem real ideal ε isPPT isFair` — fair-PPT
  computational emulation: every scheduler pair that is both PPT
  and fair distinguishes real from ideal with advantage at most
  `ε`.
* `asympSecureAgainstFair` — security-parameter-indexed,
  negligible variant.

## Design notes

The pair `(isPPT, isFair)` is intentionally orthogonal: PPT does
not imply fair delivery (an efficient adversary may starve a
process), and fair delivery does not imply PPT execution (a fair
scheduler may take unbounded internal computation between
firings).

Three different "fairness" notions in the literature are *not*
collapsed here. *Scheduler fairness* (TLA+ WF/SF, this file) is
the only one captured by `isFair` arguments below. *UC resource
fairness* is a property of the protocol design, and *cryptographic
fair exchange* is a security goal for specific protocols; both
compose orthogonally with `secureAgainstFair`.

Process tickets are the only ticket category lifted in this file.
Env tickets reduce to `Event` itself, but their fairness story is
governed entirely by the env scheduler (i.e. by the `isFair`
predicate the user supplies). Lifting a unified ticket type
carrying both process and env tickets is a deliberate non-goal at
this stage: the two sides have different enable conditions and
different adversary-control attributions and are easier to reason
about separately.

## Universe constraints

The lifted security layer pins move types, env state, env event
alphabets, and the underlying open-process universes to `0`. This
matches the universe constraints already imposed by
`AsyncRuntime.lean` (which threads `ProbComp : Type → Type`
through the runtime), and is required for `(openTheory.{u, 0, 0}
Party).Closed` to be well-formed.
-/


-- @@ L79-79 verbatim
@[expose] public section


-- @@ L81-81 verbatim
universe u


-- @@ L83-83 verbatim
open OracleComp ProbComp ENNReal


-- @@ L85-85 verbatim
namespace Interaction

-- @@ L86-86 verbatim
namespace UC


-- @@ L88-88 verbatim
/-! ## Async runs -/


-- @@ L90-136 verbatim
/--
`AsyncRun process envAction` is an infinite execution of the
asynchronous runtime threading the `RuntimeEvent Event` alphabet.

It mirrors `Concurrent.ProcessOver.Run` shape-for-shape, with three
extensions that match `runStepsAsync`:

* `state n` is the *joint* runtime state at step `n`, i.e. the
  residual process state plus the env-action bookkeeping state.
* `event n` records which side fired at step `n`: a `processTick`
  consumes the `procPath`, while an `envTick e` consumes the
  `envSample`.
* `next_state n` enforces the coherence law of one async step: at
  process ticks the proc field advances by the chosen path;
  at env ticks the env state advances to the sampled new state.

This is a freer object than the runtime's randomized executions
(it does not commit to a particular scheduler); fairness
predicates are phrased over `AsyncRun` rather than over the
runtime distribution, exactly as
`Concurrent.ProcessOver.Ticketed.WeakFair` is phrased over
`ProcessOver.Run`.
-/
structure AsyncRun
    {Γ : TypeTree.Node.Context} {m : Type → Type} [Pure m] {State Event P : Type}
    (process : Concurrent.ProcessOver P Γ)
    (envAction : EnvAction m Event State) where
  /-- The joint runtime state at each step. -/
  state : ℕ → AsyncRuntimeState process.Proc State
  /-- The runtime event chosen at each step. -/
  event : ℕ → RuntimeEvent Event
  /-- The process-side path chosen at each step. Only constrained
  to be coherent when `event n = .processTick`; left unconstrained
  in the env-tick branch. -/
  procPath : (n : ℕ) → (process.step (state n).proc).tree.Path
  /-- The env-state result sampled at each step. Only constrained to be
  coherent when `event n = .envTick e`. -/
  envSample : ℕ → State
  /-- One-step coherence: at process ticks the proc field advances by
  the chosen path, at env ticks the env state advances to the
  sampled new state. -/
  next_state : ∀ n, state (n + 1) =
    match event n with
    | .processTick =>
        { state n with
          proc := (process.step (state n).proc).next (procPath n) }
    | .envTick _ => { state n with envState := envSample n }


-- @@ L138-138 verbatim
namespace AsyncRun


-- @@ L140-140 verbatim
variable {Γ : TypeTree.Node.Context}

-- @@ L141-141 verbatim
variable {m : Type → Type} [Pure m]

-- @@ L142-142 verbatim
variable {State Event P : Type}

-- @@ L143-143 verbatim
variable {process : Concurrent.ProcessOver P Γ}

-- @@ L144-144 verbatim
variable {envAction : EnvAction m Event State}


-- @@ L146-149 verbatim
/-- The initial joint runtime state of an async run. -/
def initial (run : AsyncRun process envAction) :
    AsyncRuntimeState process.Proc State :=
  run.state 0


-- @@ L151-153 verbatim
/-- The first runtime event of an async run. -/
def head (run : AsyncRun process envAction) : RuntimeEvent Event :=
  run.event 0


-- @@ L155-155 verbatim
end AsyncRun


-- @@ L157-157 verbatim
/-! ## Ticketed env-open processes -/


-- @@ L159-180 verbatim
/--
`Ticketed Party Δ Event State` packages an `EnvOpenProcess` with a
stable ticket map for its underlying open process.

This lifts `Concurrent.ProcessOver.Ticketed` to the env-open
setting. The env channel is *not* assigned tickets here: env
events are scheduled by the environment and are represented in
the runtime trace by their alphabet symbol directly. Process
tickets are the obligations whose firing fairness predicates
constrain.

The bundle pins all relevant universes to `0` to match the
runtime layer in `AsyncRuntime.lean`.
-/
structure Ticketed
    (Party : Type) (m : Type → Type) [Pure m] (Δ : PortBoundary) (Event : Type) (State : Type) where
  /-- The underlying env-open process. -/
  toEnvProcess : EnvOpenProcess.{0, 0, 0, 0, 0} m Party Δ Event State
  /-- The stable obligation type. -/
  Ticket : Type
  /-- The stable ticket assigned to each complete process-step path. -/
  ticket : toEnvProcess.process.toProcess.Tickets Ticket


-- @@ L182-182 verbatim
namespace Ticketed


-- @@ L184-185 verbatim
variable {Party : Type} {m : Type → Type} [Pure m] {Δ : PortBoundary}
  {Event State : Type}


-- @@ L187-191 verbatim
/-- The underlying open process of a ticketed env-open process. -/
@[reducible]
def process (ticketed : Ticketed Party m Δ Event State) :
    OpenProcess.{0, 0, 0, 0} m Party Δ :=
  ticketed.toEnvProcess.process


-- @@ L193-197 verbatim
/-- The env-action channel of a ticketed env-open process. -/
@[reducible]
def envAction (ticketed : Ticketed Party m Δ Event State) :
    EnvAction m Event State :=
  ticketed.toEnvProcess.envAction


-- @@ L199-214 verbatim
/--
A process ticket is *enabled* at step `n` of an async run when
some path through the current process type tree carries that
ticket.

Equivalent to the synchronous
`Concurrent.ProcessOver.Ticketed.enabledAt` evaluated at the
process state `(run.state n).proc`. The env state is irrelevant
because tickets only label process-step obligations.
-/
def enabledAt
    (ticketed : Ticketed Party m Δ Event State)
    (run : AsyncRun ticketed.process.toProcess ticketed.envAction)
    (ticket : ticketed.Ticket) (n : ℕ) : Prop :=
  ∃ tr : (ticketed.process.step (run.state n).proc).tree.Path,
    ticketed.ticket (run.state n).proc tr = ticket


-- @@ L216-233 verbatim
/--
A process ticket *fires* at step `n` of an async run when:

1. the runtime fired a `processTick` at step `n`, and
2. the chosen path carries that ticket.

Note the asymmetry with the synchronous `firedAt`: an `envTick`
at step `n` cannot fire a process ticket, even though the
recorded `procPath n` is still well-formed. This matches
the operational reading that env ticks do not advance the
process side.
-/
def firedAt
    (ticketed : Ticketed Party m Δ Event State)
    (run : AsyncRun ticketed.process.toProcess ticketed.envAction)
    (ticket : ticketed.Ticket) (n : ℕ) : Prop :=
  run.event n = .processTick ∧
    ticketed.ticket (run.state n).proc (run.procPath n) = ticket


-- @@ L235-251 verbatim
/--
*Weak fairness* for a single process ticket: continuously enabled
implies fired infinitely often.

Lifts `Concurrent.ProcessOver.Ticketed.WeakFairOn` to async runs,
with the additional `processTick` precondition baked into
`firedAt` (so the env scheduler cannot vacuously satisfy weak
fairness by firing nothing but env ticks).
-/
def WeakFairOn
    (ticketed : Ticketed Party m Δ Event State)
    (run : AsyncRun ticketed.process.toProcess ticketed.envAction)
    (ticket : ticketed.Ticket) : Prop :=
  Concurrent.ProcessOver.Run.EventuallyAlways
      (enabledAt ticketed run ticket) →
    Concurrent.ProcessOver.Run.InfinitelyOften
      (firedAt ticketed run ticket)


-- @@ L253-267 verbatim
/--
*Strong fairness* for a single process ticket: enabled infinitely
often implies fired infinitely often.

Lifts `Concurrent.ProcessOver.Ticketed.StrongFairOn` to async
runs, with the same `processTick` precondition as `WeakFairOn`.
-/
def StrongFairOn
    (ticketed : Ticketed Party m Δ Event State)
    (run : AsyncRun ticketed.process.toProcess ticketed.envAction)
    (ticket : ticketed.Ticket) : Prop :=
  Concurrent.ProcessOver.Run.InfinitelyOften
      (enabledAt ticketed run ticket) →
    Concurrent.ProcessOver.Run.InfinitelyOften
      (firedAt ticketed run ticket)


-- @@ L269-273 verbatim
/-- An async run is *weakly fair* when every process ticket is. -/
def WeakFair
    (ticketed : Ticketed Party m Δ Event State)
    (run : AsyncRun ticketed.process.toProcess ticketed.envAction) : Prop :=
  ∀ ticket, WeakFairOn ticketed run ticket


-- @@ L275-279 verbatim
/-- An async run is *strongly fair* when every process ticket is. -/
def StrongFair
    (ticketed : Ticketed Party m Δ Event State)
    (run : AsyncRun ticketed.process.toProcess ticketed.envAction) : Prop :=
  ∀ ticket, StrongFairOn ticketed run ticket


-- @@ L281-287 verbatim
/-- A process ticket fired at step `n` is enabled at step `n`. -/
theorem fired_implies_enabled
    (ticketed : Ticketed Party m Δ Event State)
    (run : AsyncRun ticketed.process.toProcess ticketed.envAction)
    (ticket : ticketed.Ticket) (n : ℕ) :
    firedAt ticketed run ticket n → enabledAt ticketed run ticket n :=
  fun ⟨_, hticket⟩ => ⟨run.procPath n, hticket⟩


-- @@ L289-298 verbatim
/-- Strong fairness implies weak fairness on the same ticket. -/
theorem weakFairOn_of_strongFairOn
    (ticketed : Ticketed Party m Δ Event State)
    (run : AsyncRun ticketed.process.toProcess ticketed.envAction)
    (ticket : ticketed.Ticket) :
    StrongFairOn ticketed run ticket → WeakFairOn ticketed run ticket :=
  fun hSF hEA => by
    obtain ⟨N, hN⟩ := Concurrent.ProcessOver.Run.eventuallyAlways_iff.mp hEA
    exact hSF <| Concurrent.ProcessOver.Run.infinitelyOften_iff.mpr fun N' =>
      ⟨max N N', le_max_right _ _, hN _ (le_max_left _ _)⟩


-- @@ L300-305 verbatim
/-- Strong fairness implies weak fairness for the whole run. -/
theorem weakFair_of_strongFair
    (ticketed : Ticketed Party m Δ Event State)
    (run : AsyncRun ticketed.process.toProcess ticketed.envAction) :
    StrongFair ticketed run → WeakFair ticketed run :=
  fun hSF ticket => weakFairOn_of_strongFairOn ticketed run ticket (hSF ticket)


-- @@ L307-307 verbatim
end Ticketed


-- @@ L309-309 verbatim
/-! ## Scheduler pairs -/


-- @@ L311-328 verbatim
/--
`SchedulerPair Party m State Event` bundles the two sibling
samplers driving the async runtime: a process scheduler and an
env scheduler, each indexed by the closed open-theory process
they will run against.

This is the natural "joint adversary" type for the async runtime:
fair-PPT security definitions quantify over scheduler pairs.
-/
structure SchedulerPair
    (Party : Type u) (m : Type → Type) (schedulerSampler : m (ULift Bool))
    (State Event : Type) where
  /-- The process-side sampler, indexed by closed processes. -/
  proc : ∀ p : (openTheory.{u, 0, 0, 0} Party m schedulerSampler).Closed,
    ProcessScheduler m p.Proc State (fun st => (p.step st.proc).tree)
  /-- The env-side sampler, indexed by closed processes. -/
  env : ∀ p : (openTheory.{u, 0, 0, 0} Party m schedulerSampler).Closed,
    EnvScheduler m p.Proc State Event


-- @@ L330-330 verbatim
/-! ## Fair PPT security -/


-- @@ L332-369 verbatim
/--
Fair-PPT computational emulation up to advantage `ε`.

`mkSem` is a *scheduler-parametric* `Semantics` constructor: given
a scheduler pair, it produces a `Semantics` for the open-process
theory `openTheory.{u, 0, 0} Party`. The canonical instantiation is

```
fun s => processSemanticsAsync Party close envAction
  initState init s.proc s.env fuel observe
```

`isPPT` is the user's PPT class on scheduler pairs (typically
specialized to `PolyQueries`-style query bounds plus polynomial
runtime). `isFair` is the user's fairness class (typically
expressed in terms of `Ticketed.WeakFair` / `StrongFair`
evaluated on every run the scheduler pair could induce).

The two predicates are intentionally orthogonal. PPT does *not*
imply fair delivery, and fair delivery does *not* imply PPT
execution. Conflating them would lose the standard
safety/liveness vs. complexity split familiar from TLA+ and from
the PIOA literature.
-/
def secureAgainstFair
    {Party : Type u} {m : Type → Type} {schedulerSampler : m (ULift Bool)}
    {State Event : Type}
    (mkSem : SchedulerPair Party m schedulerSampler State Event →
      Semantics (openTheory.{u, 0, 0, 0} Party m schedulerSampler))
    {Δ : PortBoundary}
    (real ideal : (openTheory.{u, 0, 0, 0} Party m schedulerSampler).Obj Δ)
    (ε : ℝ)
    (isPPT : SchedulerPair Party m schedulerSampler State Event → Prop)
    (isFair : SchedulerPair Party m schedulerSampler State Event → Prop) :
    Prop :=
  ∀ scheds : SchedulerPair Party m schedulerSampler State Event,
    isPPT scheds → isFair scheds →
      ObservedCompEmulates (mkSem scheds) ε real ideal


-- @@ L371-371 verbatim
namespace secureAgainstFair


-- @@ L373-374 verbatim
variable {Party : Type u} {m : Type → Type}
  {schedulerSampler : m (ULift Bool)} {State Event : Type}

-- @@ L375-376 verbatim
variable {mkSem : SchedulerPair Party m schedulerSampler State Event →
  Semantics (openTheory.{u, 0, 0, 0} Party m schedulerSampler)}

-- @@ L377-377 verbatim
variable {Δ : PortBoundary}

-- @@ L378-379 verbatim
variable {real ideal :
  (openTheory.{u, 0, 0, 0} Party m schedulerSampler).Obj Δ}

-- @@ L380-380 verbatim
variable {ε : ℝ}


-- @@ L382-389 verbatim
/-- Uniform `ObservedCompEmulates` against every scheduler pair implies
fair-PPT security against any choice of `isPPT` and `isFair`. -/
theorem of_observedCompEmulates
    {isPPT : SchedulerPair Party m schedulerSampler State Event → Prop}
    {isFair : SchedulerPair Party m schedulerSampler State Event → Prop}
    (h : ∀ scheds, ObservedCompEmulates (mkSem scheds) ε real ideal) :
    secureAgainstFair mkSem real ideal ε isPPT isFair :=
  fun scheds _ _ => h scheds


-- @@ L391-398 verbatim
/-- Self-emulation: every scheduler pair's induced semantics
distinguishes a system from itself with advantage zero. -/
theorem refl
    (isPPT : SchedulerPair Party m schedulerSampler State Event → Prop)
    (isFair : SchedulerPair Party m schedulerSampler State Event → Prop)
    (W : (openTheory.{u, 0, 0, 0} Party m schedulerSampler).Obj Δ) :
    secureAgainstFair mkSem W W 0 isPPT isFair :=
  fun _ _ _ => ObservedCompEmulates.refl _ W


-- @@ L400-406 verbatim
/-- Weakening on the advantage bound. -/
theorem mono {ε₁ ε₂ : ℝ} (hε : ε₁ ≤ ε₂)
    {isPPT : SchedulerPair Party m schedulerSampler State Event → Prop}
    {isFair : SchedulerPair Party m schedulerSampler State Event → Prop}
    (h : secureAgainstFair mkSem real ideal ε₁ isPPT isFair) :
    secureAgainstFair mkSem real ideal ε₂ isPPT isFair :=
  fun scheds hppt hfair => ObservedCompEmulates.mono hε (h scheds hppt hfair)


-- @@ L408-417 verbatim
/-- Weakening on the PPT class: a smaller PPT class quantifies over
fewer schedulers, so security against the larger class implies
security against the smaller class. -/
theorem mono_isPPT
    {isPPT₁ isPPT₂ : SchedulerPair Party m schedulerSampler State Event → Prop}
    (hPPT : ∀ scheds, isPPT₁ scheds → isPPT₂ scheds)
    {isFair : SchedulerPair Party m schedulerSampler State Event → Prop}
    (h : secureAgainstFair mkSem real ideal ε isPPT₂ isFair) :
    secureAgainstFair mkSem real ideal ε isPPT₁ isFair :=
  fun scheds hppt hfair => h scheds (hPPT scheds hppt) hfair


-- @@ L419-428 verbatim
/-- Weakening on the fairness class: a smaller fairness class
quantifies over fewer schedulers, so security against the larger
class implies security against the smaller class. -/
theorem mono_isFair
    {isPPT : SchedulerPair Party m schedulerSampler State Event → Prop}
    {isFair₁ isFair₂ : SchedulerPair Party m schedulerSampler State Event → Prop}
    (hFair : ∀ scheds, isFair₁ scheds → isFair₂ scheds)
    (h : secureAgainstFair mkSem real ideal ε isPPT isFair₂) :
    secureAgainstFair mkSem real ideal ε isPPT isFair₁ :=
  fun scheds hppt hfair => h scheds hppt (hFair scheds hfair)


-- @@ L430-430 verbatim
end secureAgainstFair


-- @@ L432-460 verbatim
/--
Asymptotic version of `secureAgainstFair`: a security-parameter
indexed family of `mkSem` constructors and `(real, ideal)` pairs
is *fair-secure* when every PPT, fair adversary has negligible
distinguishing advantage in the security parameter.

The shape mirrors `AsympObservedCompEmulates` from `Computational.lean`:
the adversary type `Adv` is opaque, equipped with PPT and
fairness predicates, plus an `extract` function producing the
scheduler pair and the closing plug at each security parameter.
-/
def asympSecureAgainstFair
    {Party : Type u} {m : Type → Type} {schedulerSampler : m (ULift Bool)}
    {State Event : Type} {Δ : PortBoundary}
    (mkSem : ℕ → SchedulerPair Party m schedulerSampler State Event →
      Semantics (openTheory.{u, 0, 0, 0} Party m schedulerSampler))
    (real ideal : ℕ →
      (openTheory.{u, 0, 0, 0} Party m schedulerSampler).Obj Δ)
    (Adv : Type*) (isPPT : Adv → Prop) (isFair : Adv → Prop)
    (extract : Adv → ∀ _n : ℕ,
      SchedulerPair Party m schedulerSampler State Event ×
      (openTheory.{u, 0, 0, 0} Party m schedulerSampler).Plug Δ) : Prop :=
  ∀ A, isPPT A → isFair A → negligible fun n =>
    ENNReal.ofReal <|
      (mkSem n (extract A n).1).distAdvantage
        ((openTheory.{u, 0, 0, 0} Party m schedulerSampler).close
          (real n) (extract A n).2)
        ((openTheory.{u, 0, 0, 0} Party m schedulerSampler).close
          (ideal n) (extract A n).2)


-- @@ L462-462 verbatim
namespace asympSecureAgainstFair


-- @@ L464-465 verbatim
variable {Party : Type u} {m : Type → Type}
  {schedulerSampler : m (ULift Bool)} {State Event : Type}

-- @@ L466-466 verbatim
variable {Δ : PortBoundary}

-- @@ L467-468 verbatim
variable {mkSem : ℕ → SchedulerPair Party m schedulerSampler State Event →
  Semantics (openTheory.{u, 0, 0, 0} Party m schedulerSampler)}

-- @@ L469-470 verbatim
variable {real ideal : ℕ →
  (openTheory.{u, 0, 0, 0} Party m schedulerSampler).Obj Δ}

-- @@ L471-471 verbatim
variable {Adv : Type*}

-- @@ L472-472 verbatim
variable {isPPT : Adv → Prop} {isFair : Adv → Prop}

-- @@ L473-475 verbatim
variable {extract : Adv → ∀ _n : ℕ,
  SchedulerPair Party m schedulerSampler State Event ×
  (openTheory.{u, 0, 0, 0} Party m schedulerSampler).Plug Δ}


-- @@ L477-488 verbatim
/-- A pointwise bound on the distinguishing advantage by a
negligible function implies asymptotic fair-PPT security. -/
theorem of_pointwise_bound
    (f : ℕ → ℝ≥0∞) (hf : negligible f)
    (hbound : ∀ (_A : Adv) (n : ℕ),
      ENNReal.ofReal ((mkSem n (extract _A n).1).distAdvantage
        ((openTheory.{u, 0, 0, 0} Party m schedulerSampler).close
          (real n) (extract _A n).2)
        ((openTheory.{u, 0, 0, 0} Party m schedulerSampler).close
          (ideal n) (extract _A n).2)) ≤ f n) :
    asympSecureAgainstFair mkSem real ideal Adv isPPT isFair extract :=
  fun A _ _ => negligible_of_le (hbound A) hf


-- @@ L490-500 verbatim
/-- A family of `secureAgainstFair` bounds with negligible advantage
sequence implies asymptotic fair-PPT security. -/
theorem of_secureAgainstFair
    (ε : ℕ → ℝ) (hε : negligible (fun n => ENNReal.ofReal (ε n)))
    (h : ∀ n, secureAgainstFair (mkSem n) (real n) (ideal n) (ε n)
      (fun s => ∃ A, isPPT A ∧ (extract A n).1 = s)
      (fun s => ∃ A, isFair A ∧ (extract A n).1 = s)) :
    asympSecureAgainstFair mkSem real ideal Adv isPPT isFair extract :=
  fun A hppt hfair => negligible_of_le
    (fun n => ENNReal.ofReal_le_ofReal
      (h n (extract A n).1 ⟨A, hppt, rfl⟩ ⟨A, hfair, rfl⟩ (extract A n).2)) hε


-- @@ L502-502 verbatim
end asympSecureAgainstFair


-- @@ L504-504 verbatim
end UC

-- @@ L505-505 verbatim
end Interaction
