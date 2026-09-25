/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio.OracleComp.Coinductive.DynSystem
public import PolyFun.PFunctor.Dynamical.DynComputation.Bounded
public import PolyFun.PFunctor.Dynamical.Simulation


-- @@ L12-54 verbatim
/-!
# Oracle machines: `DynComputation` presentations of `OracleComp` programs

An **oracle machine** is an operational presentation of an `OracleComp spec` program: a hidden
state type, an initialization from the input, and a one-step transition that either returns a
result or issues a typed oracle query. This is exactly PolyFun's
`PFunctor.DynSystem.DynComputation` at the interface `spec.toPFunctor`, so this file defines

* `OracleMachine spec α β := DynComputation spec.toPFunctor α β`

and otherwise *inherits* the whole upstream theory by dot notation rather than re-deriving it:
`M.Implements program` (unbounded), `M.ImplementsWithin program k` (fuelled),
`M.runWith`/`M.runWithInput` (monad-parametric execution through any handler),
`DynSystem.IsSimulation` with `implementsWithin_of_isSimulation` (the practical proof method),
`ImplementsWithin.seqComp` (sequential composition), and `DynComputation.wrap` (interface
transport along a lens).

What this file adds is the `OracleSpec`-side reading of that theory:

* `OracleComp.toMachine` — the canonical residual-program machine implementing any program
  family, via `DynComputation.ofFreeM`.
* `implements_iff_behavior_eq` — `Implements` **is** behavior equality: the machine's behavior
  tree (its cofree/`Resumption` denotation) coincides with the program's query tree. Machines
  are the intensional, state-carrying presentation; behaviors are the extensional carrier; the
  implementation relation is a fact about behaviors.
* `runWith_eq_simulateQ` and the `ImplementsWithin` readings through `simulateQ` — execution
  through a `QueryImpl spec m` is definitionally `simulateQ` of the fuelled unrolling, so an
  implementing machine reproduces the program's semantics under every lawful query
  implementation, in particular its distribution semantics under a probabilistic one.

## Main definitions

* `OracleMachine spec α β` — machines with interface `spec`, inputs `α`, results `β`.
* `OracleComp.toMachine` — programs as (state = residual program) machines.

## Main results

* `OracleMachine.implements_iff_behavior_eq` — implementation = behavior equality.
* `DynComputation.ImplementsWithin.simulateQ_run_eq` — implementing machines compute the
  program under any lawful `QueryImpl`.
* `DynComputation.ImplementsWithin.probOutput_none_runWithInput` — no probability mass on
  fuel exhaustion under a probabilistic handler.
-/


-- @@ L56-56 verbatim
@[expose] public section


-- @@ L58-58 verbatim
universe u v w


-- @@ L60-60 verbatim
open OracleSpec PFunctor PFunctor.DynSystem


-- @@ L62-62 verbatim
namespace OracleComp


-- @@ L64-64 verbatim
variable {ι : Type u} {spec : OracleSpec.{u, u} ι}


-- @@ L66-71 verbatim
/-- An **oracle machine** with oracle interface `spec`, inputs `α`, and results `β`: a hidden
state, an initialization, and a step map that either returns a `β` or issues a `spec`-query.
This is PolyFun's `DynComputation` at the polynomial `spec.toPFunctor`; every generic notion
(`Implements`, `ImplementsWithin`, `runWith`, `seqComp`, `wrap`, simulations) applies directly. -/
abbrev OracleMachine (spec : OracleSpec.{u, u} ι) (α : Type u) (β : Type u) : Type _ :=
  DynComputation spec.toPFunctor α β


-- @@ L73-73 verbatim
namespace OracleMachine


-- @@ L75-75 verbatim
variable {α β : Type u} {m : Type u → Type v} [Monad m]


-- @@ L77-79 verbatim
/-- `QueryImpl spec m` is definitionally PolyFun's monadic handler type, so machines run
directly through query implementations. Regression guard for the definitional bridge. -/
example : QueryImpl spec m = PFunctor.Handler m spec.toPFunctor := rfl


-- @@ L81-85 verbatim
/-- Executing a machine through a `QueryImpl` is definitionally `simulateQ` of the fuelled
unrolling: the machine layer plugs into the existing simulation semantics with no glue. -/
theorem runWith_eq_simulateQ (M : OracleMachine spec α β) (impl : QueryImpl spec m)
    (k : ℕ) (s : M.State) :
    M.runWith impl k s = simulateQ impl (ofFreeM (M.unroll k s)) := rfl


-- @@ L87-90 verbatim
/-- Input form of `runWith_eq_simulateQ`. -/
theorem runWithInput_eq_simulateQ (M : OracleMachine spec α β) (impl : QueryImpl spec m)
    (k : ℕ) (x : α) :
    M.runWithInput impl k x = simulateQ impl (ofFreeM (M.unroll k (M.init x))) := rfl


-- @@ L92-100 verbatim
/-- The implementation relation **is** behavior equality: `M.Implements program` says the
machine's behavior tree at each input — its extensional, state-free denotation in the cofree
carrier `Resumption` — equals the program's query tree. The machine is an intensional
presentation; the relation it witnesses is a fact about behaviors. -/
theorem implements_iff_behavior_eq (M : OracleMachine spec α β)
    (program : α → OracleComp spec β) :
    M.Implements program ↔
      ∀ x, M.toDynSystem.behavior (M.init x) = FreeM.toResumption (program x) :=
  Iff.rfl


-- @@ L102-102 verbatim
end OracleMachine


-- @@ L104-109 verbatim
/-- The canonical machine implementing a program family: the state is the residual program,
initialization is the program itself, and each step peels one query. This is PolyFun's
`DynComputation.ofFreeM` read at `OracleComp`. -/
abbrev toMachine {α β : Type u} (program : α → OracleComp spec β) :
    OracleMachine spec α β :=
  DynComputation.ofFreeM program


-- @@ L111-114 verbatim
/-- Every program family is implemented by its residual-program machine. -/
theorem toMachine_implements {α β : Type u} (program : α → OracleComp spec β) :
    (toMachine program).Implements program :=
  DynComputation.implements_ofFreeM program


-- @@ L116-116 verbatim
end OracleComp


-- @@ L118-121 verbatim
namespace PFunctor.DynSystem.DynComputation.ImplementsWithin

/- The `OracleSpec`/`simulateQ` readings of the fuelled implementation relation live in the
upstream namespace so that dot notation on `h : M.ImplementsWithin program k` finds them. -/


-- @@ L123-123 verbatim
open OracleComp OracleSpec


-- @@ L125-126 verbatim
variable {ι : Type u} {spec : OracleSpec.{u, u} ι} {α β : Type u}
  {m : Type u → Type v} [Monad m]


-- @@ L128-134 verbatim
/-- An implementing machine computes the program through every lawful query implementation:
the `simulateQ` reading of `DynComputation.ImplementsWithin.runWithInput_eq`. -/
theorem simulateQ_run_eq [LawfulMonad m] {M : OracleMachine spec α β}
    {program : α → OracleComp spec β} {k : ℕ}
    (h : M.ImplementsWithin program k) (impl : QueryImpl spec m) (x : α) :
    M.runWithInput impl k x = some <$> simulateQ impl (program x) :=
  h.runWithInput_eq impl x


-- @@ L136-143 verbatim
/-- Deterministic reading: through a deterministic handler, an implementing machine returns
exactly the handler-computed value of the program. -/
theorem runWithInput_ofFn_eq {M : OracleMachine spec α β}
    {program : α → OracleComp spec β} {k : ℕ}
    (h : M.ImplementsWithin program k) (hf : OracleHandler spec) (x : α) :
    M.runWithInput (QueryImpl.ofFn hf) k x =
      some (evalWithAnswerFn (QueryImpl.ofFn hf) (program x)) :=
  h.runWithInput_eq (QueryImpl.ofFn hf) x


-- @@ L145-152 expanded
/-- Probabilistic reading: an implementing machine puts no probability mass on fuel
exhaustion — the `none` branch of the fuelled run through a probabilistic handler is null. -/
theorem probOutput_none_runWithInput {M : OracleMachine spec α β} {program : α → OracleComp spec β}
    {k : ℕ} (h : M.ImplementsWithin program k) (impl : ProbHandler spec) (x : α) :
    probOutput (M.runWithInput impl k x) none = 0 :=
  by
  rw [h.simulateQ_run_eq impl x]
  exact probOutput_some_map_none _


-- @@ L154-154 verbatim
end PFunctor.DynSystem.DynComputation.ImplementsWithin
