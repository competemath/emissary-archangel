/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.CryptoFoundations.SecExp
public import VCVio.OracleComp.SimSemantics.QueryImpl.Basic
public import VCVio.OracleComp.ProbComp
public import VCVio.OracleComp.Constructions.SampleableType
public import VCVio.OracleComp.QueryTracking.RandomOracle.Basic
public import VCVio.OracleComp.SimSemantics.Append
public import VCVio.OracleComp.Coercions.Add
public import Mathlib.LinearAlgebra.Matrix.DotProduct


-- @@ L18-47 verbatim
/-!
# Short Integer Solution (SIS) and SelfTargetMSIS

This file defines the Short Integer Solution (SIS) problem and its variant SelfTargetMSIS
(Self-Target Module-SIS), which is used in the security proof of ML-DSA (CRYSTALS-Dilithium).

## SIS

The (Module-)SIS problem: given a uniformly random matrix `A`, find a short nonzero vector `x`
such that `Ax = 0`. The generic interface covers both ordinary SIS over `ZMod p` and module-SIS
over a finite coefficient ring.

## SelfTargetMSIS

The SelfTargetMSIS problem (introduced in the Dilithium security proof): given a random matrix
`A` and access to a random oracle `H`, find a hash preimage `(μ, w)` and a short response `z`
such that `c = H(μ, w)` and `Az = c*t + w'` where the recomputed commitment `w'` matches `w`.
The "self-target" is this binding of the solution to its own hash preimage: `isValid` receives
the preimage alongside the RO output `c`, and an instantiation must require the commitment it
recomputes from the response to equal the commitment component `w` of the hashed preimage. The
experiment enforces the RO side of the binding by looking the preimage up in the oracle's
query cache.

## References

- NIST FIPS 204 (ML-DSA security analysis)
- EasyCrypt `SelfTargetMSIS.eca` (formosa-crypto/dilithium)
- Fixing and Mechanizing the Security Proof of Fiat-Shamir with Aborts and Dilithium
  (CRYPTO 2023, ePrint 2023/246)
-/


-- @@ L49-49 verbatim
@[expose] public section



-- @@ L52-52 verbatim
open OracleComp OracleSpec ENNReal Matrix


-- @@ L54-54 verbatim
namespace SIS


-- @@ L56-56 verbatim
section Generic


-- @@ L58-58 verbatim
variable {Sample Solution : Type}


-- @@ L60-66 verbatim
/-- A generic SIS-style problem instance.
`Sample` is the public challenge data (e.g. a matrix), and `Solution` is the type of
short vectors the adversary must find. The predicate `isValid` checks whether a solution
is valid (short and satisfying the linear constraint). -/
structure Problem (Sample Solution : Type) where
  sampleChallenge : ProbComp Sample
  isValid : Sample → Solution → Bool


-- @@ L68-70 verbatim
/-- A search adversary for a SIS-style problem. -/
abbrev Adversary (_problem : Problem Sample Solution) :=
  Sample → ProbComp Solution


-- @@ L72-77 verbatim
/-- The SIS experiment: sample a random challenge, run the adversary, check validity. -/
def experiment (problem : Problem Sample Solution)
    (adv : Adversary problem) : ProbComp Bool := do
  let challenge ← problem.sampleChallenge
  let solution ← adv challenge
  return problem.isValid challenge solution


-- @@ L79-82 expanded
/-- Search advantage for the SIS experiment. -/
noncomputable def advantage (problem : Problem Sample Solution) (adv : Adversary problem) : ℝ≥0∞ :=
  probOutput (experiment problem adv) true


-- @@ L84-84 verbatim
end Generic


-- @@ L86-86 verbatim
section MatrixSIS


-- @@ L88-88 verbatim
variable {α : Type}


-- @@ L90-98 expanded
/-- The standard matrix-based SIS constructor.

Given matrix `A ∈ α^{n×m}`, find nonzero `x ∈ α^m` with `Ax = 0` and `‖x‖ ≤ β`.
The norm bound is encoded in `isShort`. -/
def matrixProblem (n m : ℕ) [Semiring α] [DecidableEq α] [SampleableType α]
    (isShort : (Fin m → α) → Bool) : Problem (Matrix (Fin n) (Fin m) α) (Fin m → α)
    where
  sampleChallenge := uniformSample (Matrix (Fin n) (Fin m) α)
  isValid A x := decide (x ≠ 0) && isShort x && decide (mulVec A x = 0)


-- @@ L100-100 verbatim
end MatrixSIS


-- @@ L102-102 verbatim
end SIS


-- @@ L104-104 verbatim
namespace SelfTargetMSIS


-- @@ L106-126 verbatim
/-- The SelfTargetMSIS problem for lattice-based signatures.

The adversary receives a matrix `A` and a target vector `t`, and has access to a random
oracle `H`. The adversary must produce `(hashInput, response)` such that:
1. `c = H(hashInput)` (RO consistency: the adversary must have queried the RO on `hashInput`)
2. `isValid(challenge, target, hashInput, c, response)` holds (shortness bound + verification
   equation binding the recomputed commitment to `hashInput`'s commitment component)

The experiment enforces RO consistency by looking up `hashInput` in the RO's query cache.
If the adversary never queried `H(hashInput)`, the check fails automatically.

This captures the core hardness assumption in the ML-DSA/Dilithium security proof. -/
structure Problem (Challenge Response Target HashInput HashOutput : Type) where
  /-- Sample the public parameters (matrix + target). -/
  sampleParams : ProbComp (Challenge × Target)
  /-- Check whether a purported solution is valid, given the hash preimage the adversary
  queried and the hash output the RO cached for it. Receiving the preimage is what makes the
  problem *self-targeting*: an instantiation must require the commitment recomputed from the
  response to equal the commitment component of the hashed preimage, binding the solution to
  the very input hashed to produce the challenge. -/
  isValid : Challenge → Target → HashInput → HashOutput → Response → Bool


-- @@ L128-128 verbatim
section Experiment


-- @@ L130-130 verbatim
variable {Challenge Response Target HashInput HashOutput : Type}


-- @@ L132-139 expanded
/-- A SelfTargetMSIS adversary has access to a random oracle `HashInput →ₒ HashOutput`
(modeling the hash function `H`) and uniform randomness. The adversary returns a hash
preimage and a response; the experiment checks RO consistency by looking up the preimage
in the oracle's cache. -/
structure Adversary (problem : Problem Challenge Response Target HashInput HashOutput) where
  run (params : Challenge × Target) :
    OracleComp (unifSpec + (OracleSpec.ofFn (ι := HashInput) (fun _ => HashOutput)))
      (HashInput × Response)


-- @@ L141-141 verbatim
variable [DecidableEq HashInput] [SampleableType HashOutput]


-- @@ L143-160 expanded
/-- The SelfTargetMSIS experiment in the ROM: sample parameters, run the adversary with
uniform randomness and a lazy random oracle for `H`, then enforce:
1. The adversary actually queried `H(hashInput)` (RO consistency check via the query cache)
2. The solution passes `isValid` with the queried preimage and the RO's cached output -/
noncomputable def experiment {problem : Problem Challenge Response Target HashInput HashOutput}
    (adv : Adversary problem) : ProbComp Bool := do
  let params ← problem.sampleParams
  let ro :
    QueryImpl (OracleSpec.ofFn (ι := HashInput) (fun _ => HashOutput))
      (StateT ((OracleSpec.ofFn (ι := HashInput) (fun _ => HashOutput)).QueryCache) ProbComp) :=
    randomOracle
  let idImpl :=
    (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget
      (StateT ((OracleSpec.ofFn (ι := HashInput) (fun _ => HashOutput)).QueryCache) ProbComp)
  let ((hashInput, response), cache) ← StateT.run (simulateQ (idImpl + ro) (adv.run params)) ∅
  match cache hashInput with
  | some hashOutput =>
    return problem.isValid params.1 params.2 hashInput hashOutput response
  | none =>
    return false


-- @@ L162-167 expanded
/-- Advantage of a SelfTargetMSIS adversary. -/
noncomputable def advantage {problem : Problem Challenge Response Target HashInput HashOutput}
    (adv : Adversary problem) : ℝ≥0∞ :=
  probOutput (experiment adv) true


-- @@ L169-169 verbatim
end Experiment


-- @@ L171-171 verbatim
end SelfTargetMSIS
