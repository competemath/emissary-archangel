/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.OracleComp.Coercions.SubSpec
public import VCVio.OracleComp.EvalDist
public import VCVio.OracleComp.ProbComp
public import VCVio.OracleComp.QueryTracking.RandomOracle.Basic
public import VCVio.OracleComp.SimSemantics.Append


-- @@ L15-31 verbatim
/-!
# Pseudorandom Functions (PRFs)

This file defines pseudorandom functions and their security game.

A PRF adversary gets oracle access to uniform sampling plus a function `D → R` and tries to
distinguish the real function `PRF.eval k` (for a random key `k`) from a truly random function
(modeled as a lazy random oracle with consistent responses).

## Main Definitions

- `PRFScheme K D R` — a PRF with key space `K`, domain `D`, and range `R`.
- `PRFAdversary D R` — a distinguisher with oracle access to `D →ₒ R`.
- `prfRealExp` — the real experiment (adversary queries `PRF.eval k`).
- `prfIdealExp` — the ideal experiment (adversary queries a random oracle).
- `prfAdvantage` — distinguishing advantage.
-/


-- @@ L33-33 verbatim
@[expose] public section


-- @@ L35-35 verbatim
open OracleComp OracleSpec ENNReal


-- @@ L37-41 verbatim
/-- A pseudorandom function with key space `K`, domain `D`, and range `R`.
Key generation is probabilistic; evaluation is deterministic given a key. -/
structure PRFScheme (K D R : Type) where
  keygen : ProbComp K
  eval : K → D → R


-- @@ L43-43 verbatim
namespace PRFScheme


-- @@ L45-45 verbatim
variable {K D R : Type}


-- @@ L47-49 expanded
/-- Oracle interface for PRF distinguishers: unrestricted access to uniform sampling plus
oracle access to the candidate function. -/
@[reducible]
def PRFOracleSpec (_D R : Type) :=
  unifSpec + (OracleSpec.ofFn (ι := _D) (fun _ => R))


-- @@ L51-53 verbatim
/-- A PRF adversary gets oracle access to uniform sampling and a function `D → R`,
and outputs a boolean guess (`true` = "real PRF", `false` = "random function"). -/
abbrev PRFAdversary (D R : Type) := OracleComp (PRFOracleSpec D R) Bool


-- @@ L55-58 verbatim
/-- Query the candidate function through the PRF distinguisher interface. Keeping the
dependent sum index behind this concrete-result wrapper gives clients a stable query API. -/
def functionQuery (d : D) : OracleComp (PRFOracleSpec D R) R :=
  (PRFOracleSpec D R).query (Sum.inr d)


-- @@ L60-62 expanded
/-- A PRF has uniform key generation when its keygen algorithm is exactly uniform sampling. -/
def UniformKey [SampleableType K] (prf : PRFScheme K D R) : Prop :=
  prf.keygen = (uniformSample K)


-- @@ L64-69 expanded
/-- Query implementation for the real PRF experiment. Uniform-sampling queries are handled
by the ambient `unifSpec`; function queries are answered by `prf.eval k`. -/
def prfRealQueryImpl (prf : PRFScheme K D R) (k : K) : QueryImpl (PRFOracleSpec D R) ProbComp :=
  let so : QueryImpl (OracleSpec.ofFn (ι := D) (fun _ => R)) ProbComp := fun d =>
    pure (prf.eval k d)
  (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)) + so


-- @@ L71-77 expanded
/-- Query implementation for the ideal PRF experiment. Uniform-sampling queries are handled
by the ambient `unifSpec`; function queries are answered by a lazy random oracle. -/
def prfIdealQueryImpl [DecidableEq D] [SampleableType R] :
    QueryImpl (PRFOracleSpec D R)
      (StateT ((OracleSpec.ofFn (ι := D) (fun _ => R)).QueryCache) ProbComp) :=
  (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget
      (StateT ((OracleSpec.ofFn (ι := D) (fun _ => R)).QueryCache) ProbComp) +
    (OracleSpec.ofFn (ι := D) (fun _ => R)).randomOracle


-- @@ L79-83 verbatim
/-- The real PRF handler answers a function query by evaluating the keyed function. -/
@[simp]
lemma prfRealQueryImpl_apply_inr (prf : PRFScheme K D R) (k : K) (d : D) :
    prf.prfRealQueryImpl k (Sum.inr d) = pure (prf.eval k d) := by
  rw [prfRealQueryImpl, QueryImpl.add_apply_inr]


-- @@ L85-89 expanded
/-- The ideal PRF handler routes a function query to the lazy random oracle. -/
@[simp]
lemma prfIdealQueryImpl_apply_inr [DecidableEq D] [SampleableType R] (d : D) :
    prfIdealQueryImpl (D := D) (R := R) (Sum.inr d) =
      (OracleSpec.ofFn (ι := D) (fun _ => R)).randomOracle d :=
  by rw [prfIdealQueryImpl, QueryImpl.add_apply_inr]


-- @@ L91-95 verbatim
/-- Real PRF experiment: sample a key, let the adversary query `prf.eval k`. -/
def prfRealExp (prf : PRFScheme K D R) (adversary : PRFAdversary D R) :
    ProbComp Bool := do
  let k ← prf.keygen
  simulateQ (prfRealQueryImpl prf k) adversary


-- @@ L97-102 verbatim
/-- Ideal PRF experiment: let the adversary query a lazy random oracle
(consistent random function). The oracle caches responses so that
the same input always yields the same output. -/
def prfIdealExp [DecidableEq D] [SampleableType R]
    (adversary : PRFAdversary D R) : ProbComp Bool :=
  (simulateQ (prfIdealQueryImpl (D := D) (R := R)) adversary).run' ∅


-- @@ L104-109 expanded
/-- PRF advantage: how well the adversary distinguishes the real PRF from
a random function. -/
noncomputable def prfAdvantage [DecidableEq D] [SampleableType R] (prf : PRFScheme K D R)
    (adversary : PRFAdversary D R) : ℝ :=
  |(probOutput (prf.prfRealExp adversary) true).toReal -
      (probOutput (prfIdealExp adversary) true).toReal|


-- @@ L111-117 verbatim
/-! ## Forwarding lemmas for the PRF query implementations

How `prfRealQueryImpl`/`prfIdealQueryImpl` act on a computation lifted in from the ambient
`unifSpec` (their identity-handled left summand) and on a function (`Sum.inr`) query. These are the
facts a PRF distinguisher reduction needs when it forwards its own uniform sampling / oracle access
through the PRF experiment: the `unifSpec` side is transparent, and an `inr` query is exactly the
candidate function (real: `prf.eval k`; ideal: the lazy random oracle). -/


-- @@ L119-124 verbatim
/-- The real PRF handler is transparent on a computation lifted in from `unifSpec`: its
`unifSpec` side is the identity handler and the function oracle is never consulted. -/
lemma simulateQ_prfRealQueryImpl_liftComp (prf : PRFScheme K D R) (k : K)
    {β : Type} (ob : OracleComp unifSpec β) :
    simulateQ (prf.prfRealQueryImpl k) (OracleComp.liftComp ob (PRFOracleSpec D R)) = ob := by
  simp [prfRealQueryImpl, QueryImpl.simulateQ_add_liftM_left, QueryImpl.simulateQ_toQueryImpl]


-- @@ L126-132 expanded
/-- The ideal (lazy random oracle) PRF handler is transparent on a computation lifted in from
`unifSpec`, threading the cache: the result is just `ob` lifted into the cache state monad. -/
lemma simulateQ_prfIdealQueryImpl_liftComp [DecidableEq D] [SampleableType R] {β : Type}
    (ob : OracleComp unifSpec β) :
    simulateQ (prfIdealQueryImpl (D := D) (R := R)) (OracleComp.liftComp ob (PRFOracleSpec D R)) =
      (liftM ob : StateT ((OracleSpec.ofFn (ι := D) (fun _ => R)).QueryCache) ProbComp β) :=
  by simp [prfIdealQueryImpl, QueryImpl.simulateQ_add_liftM_left, QueryImpl.simulateQ_toQueryImpl]


-- @@ L134-139 verbatim
/-- A function query (`Sum.inr`) under the real PRF handler evaluates the PRF. -/
lemma simulateQ_prfRealQueryImpl_inr (prf : PRFScheme K D R) (k : K) (d : D) :
    simulateQ (prf.prfRealQueryImpl k)
        (liftM (OracleSpec.query (Sum.inr d) : OracleQuery (PRFOracleSpec D R) R))
      = pure (prf.eval k d) := by
  rw [simulateQ_spec_query, prfRealQueryImpl_apply_inr]


-- @@ L141-147 expanded
/-- A function query (`Sum.inr`) under the ideal PRF handler is the lazy random oracle at that
point. -/
lemma simulateQ_prfIdealQueryImpl_inr [DecidableEq D] [SampleableType R] (q : D) :
    simulateQ (prfIdealQueryImpl (D := D) (R := R))
        (liftM (OracleSpec.query (Sum.inr q) : OracleQuery (PRFOracleSpec D R) R)) =
      (OracleSpec.ofFn (ι := D) (fun _ => R)).randomOracle q :=
  by rw [simulateQ_spec_query, prfIdealQueryImpl_apply_inr]


-- @@ L149-152 verbatim
@[simp] lemma simulateQ_prfRealQueryImpl_functionQuery
    (prf : PRFScheme K D R) (k : K) (d : D) :
    simulateQ (prf.prfRealQueryImpl k) (functionQuery d) = pure (prf.eval k d) :=
  simulateQ_prfRealQueryImpl_inr prf k d


-- @@ L154-158 expanded
@[simp]
lemma simulateQ_prfIdealQueryImpl_functionQuery [DecidableEq D] [SampleableType R] (d : D) :
    simulateQ (prfIdealQueryImpl (D := D) (R := R)) (functionQuery d) =
      (OracleSpec.ofFn (ι := D) (fun _ => R)).randomOracle d :=
  simulateQ_prfIdealQueryImpl_inr d


-- @@ L160-160 verbatim
end PRFScheme
