/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.OracleComp.ProbComp
public import VCVio.EvalDist.Defs.Semantics
public import PolyFun.Control.Monad.Hom
import VCVio.EvalDist.Monad.Map


-- @@ L13-27 verbatim
/-!
# Bundled Lifts from `ProbComp`

This file packages the "public randomness" capability separately from denotational semantics.

Many crypto constructions need two orthogonal pieces of structure on their ambient monad `m`:

1. a way to *observe* computations probabilistically (`SPMFSemantics` / `PMFSemantics`)
2. a way to *inject* plain probabilistic sampling into `m`

This file packages the second capability as a bundled monad homomorphism `ProbComp →ᵐ m`, so it
can be carried independently of whatever denotational semantics the construction uses. It also
defines `ProbCompRuntime`, the common crypto-facing bundle that pairs public-randomness lifting
with bundled `SPMF` semantics for an ambient monad.
-/


-- @@ L29-29 verbatim
@[expose] public section


-- @@ L31-31 verbatim
universe v w


-- @@ L33-39 verbatim
/-- Bundled way to lift plain probabilistic computations into an ambient monad `m`.

Intuitively, this is the capability "sample fresh public randomness inside `m`". We package it as
a monad homomorphism so it composes lawfully with `pure` and `bind`. -/
structure ProbCompLift (m : Type → Type v) [Monad m] where
  /-- Inject a plain `ProbComp` computation into `m`. -/
  liftProbComp : ProbComp →ᵐ m


-- @@ L41-41 verbatim
namespace ProbCompLift


-- @@ L43-46 verbatim
/-- Build a bundled `ProbCompLift` from an existing lawful `MonadLiftT ProbComp m` instance. -/
def ofMonadLift (m : Type → Type v) [Monad m]
    [MonadLiftT ProbComp m] [LawfulMonadLiftT ProbComp m] : ProbCompLift m where
  liftProbComp := MonadHom.ofLift ProbComp m


-- @@ L48-50 verbatim
/-- The identity lift on `ProbComp` itself. -/
def id : ProbCompLift ProbComp where
  liftProbComp := MonadHom.id ProbComp


-- @@ L52-52 verbatim
end ProbCompLift


-- @@ L54-67 verbatim
/-- Common runtime bundle for crypto games in an ambient monad `m`.

This packages the two capabilities that security experiments usually need together:

1. `SPMFSemantics m` to observe the experiment as a Boolean subdistribution.
2. `ProbCompLift m` to sample fresh public randomness inside `m`.

The bundle is kept separate from the core scheme definitions so that executable scheme data does
not become noncomputable merely by carrying denotational semantics. -/
structure ProbCompRuntime (m : Type → Type v) [Monad m] where
  /-- Bundled subprobabilistic semantics for the ambient monad. -/
  toSPMFSemantics : SPMFSemantics.{0, v, w} m
  /-- Bundled injection of plain probabilistic sampling into the ambient monad. -/
  toProbCompLift : ProbCompLift m


-- @@ L69-69 verbatim
namespace ProbCompRuntime


-- @@ L71-71 verbatim
variable {m : Type → Type v} [Monad m] {α : Type}


-- @@ L73-75 verbatim
/-- Observe an ambient computation as an `SPMF` using the runtime's bundled semantics. -/
def evalSPMF (runtime : ProbCompRuntime m) (mx : m α) : SPMF α :=
  runtime.toSPMFSemantics.evalSPMF mx


-- @@ L77-79 verbatim
/-- Failure probability of an ambient computation under the runtime's bundled semantics. -/
def probFailure (runtime : ProbCompRuntime m) (mx : m α) : ENNReal :=
  runtime.toSPMFSemantics.probFailure mx


-- @@ L81-84 verbatim
/-- Lift a plain `ProbComp` computation into the ambient monad using the runtime's public
randomness capability. -/
def liftProbComp (runtime : ProbCompRuntime m) : ProbComp →ᵐ m :=
  runtime.toProbCompLift.liftProbComp


-- @@ L86-89 verbatim
/-- Canonical runtime for `ProbComp` itself. -/
noncomputable def probComp : ProbCompRuntime ProbComp where
  toSPMFSemantics := SPMFSemantics.ofMonadLift ProbComp
  toProbCompLift := ProbCompLift.id


-- @@ L91-100 verbatim
/-- The canonical `ProbComp` runtime satisfies the pure-return factoring law: `evalSPMF`
commutes with binding a pure function. Security decompositions that couple several
experiments through one joint execution (e.g. the exact SUF-CMA partition in
`VCVio.CryptoFoundations.SignatureAlg`) take exactly this equation as their pull-through
hypothesis, so consumers instantiating them at `ProbCompRuntime.probComp` can use this
lemma directly. -/
lemma probComp_evalSPMF_bind_pure {α β : Type} (f : α → β) (mx : ProbComp α) :
    probComp.evalSPMF (mx >>= fun x => pure (f x)) = f <$> probComp.evalSPMF mx := by
  change _root_.evalSPMF (mx >>= fun x => pure (f x)) = f <$> _root_.evalSPMF mx
  rw [bind_pure_comp, evalSPMF_map]


-- @@ L102-102 verbatim
end ProbCompRuntime
