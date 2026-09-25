/-
Copyright (c) 2026 Oleksandr Vovkotrub. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oleksandr Vovkotrub
-/

module

public import VCVio.CryptoFoundations.SigmaProtocol
public import VCVio.CryptoFoundations.SignatureAlg
public import VCVio.CryptoFoundations.HardnessAssumptions.HardRelation
public import VCVio.OracleComp.SimSemantics.QueryImpl.Basic
public import VCVio.OracleComp.QueryTracking.RandomOracle.Basic
public import VCVio.OracleComp.QueryTracking.RandomOracle.Simulation
public import VCVio.OracleComp.QueryTracking.LoggingOracle
public import VCVio.OracleComp.QueryTracking.QueryCost
public import VCVio.OracleComp.Coercions.Add
public import VCVio.OracleComp.SimSemantics.StateT.BundledSemantics
public import Mathlib.Data.FinEnum
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.Data.Sym.Card
public import Mathlib.Algebra.Order.Antidiag.Pi


-- @@ L25-64 verbatim
/-!
# Fischlin Transform: Core Definitions

This file defines the Fischlin transform (CRYPTO 2005), which converts a Σ-protocol
into a signature scheme (non-interactive proof of knowledge) in the random oracle model
with *online (straight-line) extraction*.

Unlike the Fiat-Shamir transform, which requires a rewinding extractor (via the forking lemma),
the Fischlin transform enables extraction by simply observing the prover's hash queries.
This comes at the cost of a more complex prover that performs a "proof-of-work" search
over the challenge space, and a slight completeness error.

This module holds the core definitions: the random-oracle input type `FischlinROInput`, the
oracle signature `fischlinROSpec`, the proof type `FischlinProof`, the prover's inner search
`fischlinSearchAux`, the transform `Fischlin` itself, and the bundled random-oracle `runtime`
used to denote the signature scheme as a probabilistic computation.

## Parameters

* `ρ` — number of parallel repetitions
* `b` — hash output bit-length (random oracle range is `Fin (2^b)`)
* `S` — maximum allowed sum of hash values in a valid proof (paper notation)

## Module layout

The development is split across the sibling modules under `Fischlin/`:

* `Fischlin.Defs` — the definitions in this file.
* `Fischlin.CostAccounting` — random-oracle query-cost and expected-query bounds for
  `sign` and `verify`.
* `Fischlin.Completeness` — the completeness bound `almostComplete` via the pure-probability
  model game.
* `Fischlin.KnowledgeSoundness` — online extraction and the `knowledgeSoundness` bound via a
  supermartingale potential argument.

## References

* Marc Fischlin, "Communication-Efficient Non-Interactive Proofs of Knowledge
  with Online Extractors", CRYPTO 2005.
-/


-- @@ L66-66 verbatim
@[expose] public section


-- @@ L68-68 verbatim
universe u v


-- @@ L70-70 verbatim
open OracleComp OracleSpec


-- @@ L72-72 verbatim
/-! ## Type Definitions -/


-- @@ L74-83 verbatim
/-- Input to the Fischlin random oracle. Defined as a structure rather than a nested product
to give fast `DecidableEq` synthesis (avoiding deep product-type unfolding). -/
structure FischlinROInput (Stmt Commit Chal Resp : Type) (ρ : ℕ) (M : Type) where
  stmt : Stmt
  msg : M
  comList : List Commit
  rep : Fin ρ
  chal : Chal
  resp : Resp
  deriving DecidableEq


-- @@ L85-89 expanded
/-- The random oracle specification for the Fischlin transform.
Domain: `FischlinROInput` (statement, message, commitment list, index, challenge, response).
Range: `Fin (2^b)` (b-bit hash values). -/
abbrev fischlinROSpec (Stmt Commit Chal Resp : Type) (ρ b : ℕ) (M : Type) :=
  OracleSpec.ofFn (ι := FischlinROInput Stmt Commit Chal Resp ρ M) (fun _ => Fin (2 ^ b))


-- @@ L91-93 verbatim
/-- A Fischlin proof consists of one `(commitment, challenge, response)` triple
per parallel repetition. -/
abbrev FischlinProof (Commit Chal Resp : Type) (ρ : ℕ) := Fin ρ → Commit × Chal × Resp


-- @@ L95-95 verbatim
/-! ## Prover Search -/


-- @@ L97-123 verbatim
/-- Recursive search over a list of challenges for one Fischlin repetition.

For each challenge `ω`, computes the sigma protocol response and queries the hash oracle.
Exits early if a hash value of `0` is found (the ideal "proof of work" result).
Otherwise, tracks the `(challenge, response)` pair with the minimal hash value.

This models the sequential search in Construction 1 of the Fischlin paper:
the prover queries `H` on each input and keeps the best. -/
def fischlinSearchAux {Stmt Wit Commit PrvState Chal Resp M : Type}
    {rel : Stmt → Wit → Bool} {ρ b : ℕ}
    {m : Type → Type v} [Monad m]
    (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel)
    [MonadLiftT ProbComp m] [HasQuery (fischlinROSpec Stmt Commit Chal Resp ρ b M) m]
    (pk : Stmt) (sk : Wit) (sc : PrvState) (msg : M) (comList : List Commit) (i : Fin ρ) :
    List Chal → Option (Chal × Resp × Fin (2 ^ b)) → m (Option (Chal × Resp))
  | [], best => return best.map fun (ω, resp, _) => (ω, resp)
  | ω :: rest, best => do
    let resp ← σ.respond pk sk sc ω
    let h ← HasQuery.query (spec := (fischlinROSpec Stmt Commit Chal Resp ρ b M))
      ⟨pk, msg, comList, i, ω, resp⟩
    if h.val = 0 then return some (ω, resp)
    else
      let newBest := match best with
        | none => some (ω, resp, h)
        | some (ω', resp', h') =>
          if h.val < h'.val then some (ω, resp, h) else some (ω', resp', h')
      fischlinSearchAux σ pk sk sc msg comList i rest newBest


-- @@ L125-125 verbatim
/-! ## Main Definition -/


-- @@ L127-128 verbatim
variable {Stmt Wit Commit PrvState Chal Resp : Type}
    {rel : Stmt → Wit → Bool}


-- @@ L130-130 verbatim
section mainDefinition


-- @@ L132-133 verbatim
variable [DecidableEq Stmt] [DecidableEq Commit] [DecidableEq Chal] [DecidableEq Resp]
  [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal]


-- @@ L135-178 verbatim
/-- The Fischlin transform applied to a Σ-protocol and a generable relation produces
a signature scheme in the random oracle model.

**Signing**: generates `ρ` independent commitments, then for each repetition searches
through all challenges `ω ∈ Ω` (via `FinEnum.toList`) to find the `(ω, response)` pair
whose hash value is minimal, exiting early at hash `0`.

**Verification**: re-hashes each `(commitment, challenge, response)` triple, checks
sigma-protocol verification for each repetition, and verifies that the sum of hash
values is at most `S`. -/
def Fischlin
    {m : Type → Type v} [Monad m]
    (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel)
    (hr : GenerableRelation Stmt Wit rel) (ρ b S : ℕ) (M : Type)
    [DecidableEq M] [MonadLiftT ProbComp m]
    [HasQuery (fischlinROSpec Stmt Commit Chal Resp ρ b M) m] :
    SignatureAlg m
      (M := M) (PK := Stmt) (SK := Wit) (S := FischlinProof Commit Chal Resp ρ) where
  keygen := liftM hr.gen
  sign := fun pk sk msg => do
    let commits : Fin ρ → Commit × PrvState ←
      Fin.mOfFn ρ fun _ => σ.commit pk sk
    let comVec : Fin ρ → Commit := fun i => (commits i).1
    let comList := List.ofFn comVec
    Fin.mOfFn ρ fun i => do
      let sc_i := (commits i).2
      let result ←
        fischlinSearchAux
          σ pk sk sc_i msg comList i (FinEnum.toList Chal)
          (none : Option (Chal × Resp × Fin (2 ^ b)))
      match result with
      | some (ω, resp) => return (comVec i, ω, resp)
      | none => return (comVec i, default, default)
  verify := fun pk msg π => do
    let comVec : Fin ρ → Commit := fun i => (π i).1
    let comList := List.ofFn comVec
    let results ← Fin.mOfFn ρ fun i => do
      let (_, ω_i, resp_i) := π i
      let h_i ← HasQuery.query (spec := (fischlinROSpec Stmt Commit Chal Resp ρ b M))
        ⟨pk, msg, comList, i, ω_i, resp_i⟩
      pure (σ.verify pk (comVec i) ω_i resp_i, h_i.val)
    let allVerified := (List.finRange ρ).all fun i => (results i).1
    let hashSum := (List.finRange ρ).foldl (fun acc i => acc + (results i).2) 0
    pure (allVerified && decide (hashSum ≤ S))


-- @@ L180-180 verbatim
end mainDefinition


-- @@ L182-182 verbatim
namespace Fischlin


-- @@ L184-184 verbatim
variable {Stmt Wit Commit PrvState Chal Resp : Type} {rel : Stmt → Wit → Bool}


-- @@ L186-186 verbatim
open ENNReal


-- @@ L188-188 verbatim
section runtime


-- @@ L190-191 verbatim
variable [DecidableEq Stmt] [DecidableEq Commit] [DecidableEq Chal] [DecidableEq Resp]
  [SampleableType Chal]


-- @@ L193-202 verbatim
/-- Runtime bundle for the Fischlin random-oracle world. -/
noncomputable def runtime
    (ρ b : ℕ) (M : Type) [DecidableEq M] :
    ProbCompRuntime (OracleComp (unifSpec + fischlinROSpec Stmt Commit Chal Resp ρ b M)) where
  toSPMFSemantics := SPMFSemantics.withStateOracle
    (hashImpl := (randomOracle :
      QueryImpl (fischlinROSpec Stmt Commit Chal Resp ρ b M)
        (StateT (fischlinROSpec Stmt Commit Chal Resp ρ b M).QueryCache ProbComp)))
    ∅
  toProbCompLift := ProbCompLift.ofMonadLift _


-- @@ L204-204 verbatim
end runtime


-- @@ L206-206 verbatim
end Fischlin
