/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.HardnessAssumptions.CollisionResistance


-- @@ L10-30 verbatim
/-!
# Interleaved target subset resilience

Interleaved target subset resilience (ITSR) is the exact keyed-hash property used for the
SPHINCS+/SLH-DSA message-compression hop.  The adversary may interleave its own computation with
target queries. A target query on `x` independently samples a key `k`, records `(k, x)`, and
returns `k`.
The adversary wins with a fresh pair `(k⋆, x⋆)` when every semantic index selected by its hash
output already occurs among the indices selected by the recorded targets.

Freshness is pair freshness: reusing an input with a newly supplied key or reusing a key with a new
input is not automatically excluded.  This matches the source game and is important for the
SLH-DSA reduction, where the sampled key is the per-message randomizer produced by the idealized
`PRF_msg`.

## References

* Barbosa, Dupressoir, Hülsing, Meijers, and Strub, “A Tight Security Proof for SPHINCS+,
  Formally Verified”, `KeyedHashFunctions.eca`, ITSR.
* Hülsing and Kudinov, “Recovering the Tight Security Proof of SPHINCS+”.
-/


-- @@ L32-32 verbatim
@[expose] public section


-- @@ L34-34 verbatim
open OracleComp OracleSpec ENNReal

-- @@ L35-35 verbatim
open CollisionResistance


-- @@ L37-37 verbatim
namespace KeyedHash


-- @@ L39-39 verbatim
variable {K X Y Index : Type}


-- @@ L41-44 verbatim
/-- A keyed hash family together with the semantic-index map used by the subset relation. -/
structure ITSRProblem (K X Y Index : Type) where
  khf : KeyedHashFamily K X Y
  indices : Y → List Index


-- @@ L46-47 expanded
/-- Target oracle: an input is answered with an independently sampled key. -/
abbrev ITSRTargetSpec (X K : Type) : OracleSpec X :=
  OracleSpec.ofFn (ι := X) (fun _ => K)


-- @@ L49-50 verbatim
/-- Target transcript in issue order. -/
abbrev ITSRTranscript (K X : Type) := List (K × X)


-- @@ L52-55 verbatim
/-- An ITSR adversary interleaves private uniform randomness and target queries before returning
its candidate pair. -/
structure ITSRAdversary (prob : ITSRProblem K X Y Index) where
  main : OracleComp (unifSpec + ITSRTargetSpec X K) (K × X)


-- @@ L57-59 verbatim
/-- The semantic indices selected by one keyed-hash input. -/
def ITSRProblem.indexSet (prob : ITSRProblem K X Y Index) (kx : K × X) : List Index :=
  prob.indices (prob.khf.hash kx.1 kx.2)


-- @@ L61-64 verbatim
/-- The combined semantic indices selected by all recorded targets. -/
def ITSRProblem.targetIndexSet (prob : ITSRProblem K X Y Index)
    (targets : ITSRTranscript K X) : List Index :=
  targets.flatMap prob.indexSet


-- @@ L66-70 verbatim
/-- Source-game winning relation: the candidate pair is fresh and its selected indices form a
subset of the indices selected by the target transcript. -/
def ITSRProblem.Wins [DecidableEq K] [DecidableEq X] [DecidableEq Index]
    (prob : ITSRProblem K X Y Index) (targets : ITSRTranscript K X) (candidate : K × X) : Prop :=
  candidate ∉ targets ∧ ∀ i ∈ prob.indexSet candidate, i ∈ prob.targetIndexSet targets


-- @@ L72-76 verbatim
instance [DecidableEq K] [DecidableEq X] [DecidableEq Index]
    (prob : ITSRProblem K X Y Index) (targets : ITSRTranscript K X) (candidate : K × X) :
    Decidable (prob.Wins targets candidate) := by
  unfold ITSRProblem.Wins ITSRProblem.indexSet ITSRProblem.targetIndexSet
  infer_instance


-- @@ L78-85 verbatim
/-- Target-oracle implementation. Every query samples and records a key; targets are not
deduplicated, since the final relation—not the oracle—determines success. -/
def ITSRTargetOracle (prob : ITSRProblem K X Y Index) :
    QueryImpl (ITSRTargetSpec X K) (StateT (ITSRTranscript K X) ProbComp) :=
  fun x => do
    let k ← (monadLift prob.khf.keygen : StateT (ITSRTranscript K X) ProbComp K)
    modify fun targets => targets ++ [(k, x)]
    return k


-- @@ L87-91 verbatim
/-- Combined private-randomness and target handler. -/
def ITSROracles (prob : ITSRProblem K X Y Index) :
    QueryImpl (unifSpec + ITSRTargetSpec X K) (StateT (ITSRTranscript K X) ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (ITSRTranscript K X) ProbComp) +
    ITSRTargetOracle prob


-- @@ L93-97 verbatim
/-- ITSR experiment. -/
noncomputable def ITSRExperiment [DecidableEq K] [DecidableEq X] [DecidableEq Index]
    {prob : ITSRProblem K X Y Index} (adv : ITSRAdversary prob) : ProbComp Bool := do
  let (candidate, targets) ← (simulateQ (ITSROracles prob) adv.main).run []
  return decide (prob.Wins targets candidate)


-- @@ L99-102 expanded
/-- ITSR success probability. -/
noncomputable def ITSRAdvantage [DecidableEq K] [DecidableEq X] [DecidableEq Index]
    {prob : ITSRProblem K X Y Index} (adv : ITSRAdversary prob) : ℝ≥0∞ :=
  probOutput (ITSRExperiment adv) true


-- @@ L104-108 verbatim
@[simp] theorem ITSRTargetOracle_run (prob : ITSRProblem K X Y Index)
    (x : X) (targets : ITSRTranscript K X) :
    (ITSRTargetOracle prob x).run targets =
      prob.khf.keygen >>= fun k => pure (k, targets ++ [(k, x)]) := by
  simp [ITSRTargetOracle]


-- @@ L110-110 verbatim
end KeyedHash
