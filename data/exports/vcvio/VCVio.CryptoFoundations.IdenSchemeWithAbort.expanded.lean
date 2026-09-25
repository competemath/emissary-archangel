/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.EvalDist.TVDist
public import VCVio.OracleComp.Constructions.SampleableType


-- @@ L11-45 verbatim
/-!
# Identification Scheme with Aborts

This file defines a structure for identification schemes with aborts, as used in ML-DSA
(CRYSTALS-Dilithium). Unlike a standard Σ-protocol (`SigmaProtocol`), the prover's response
may fail (abort), in which case the protocol is retried. This abort mechanism is essential for
the security of lattice-based schemes where masking must hide the secret.

The structure follows the EasyCrypt formalization in `IDSabort.ec` (formosa-crypto/dilithium).

## Type Parameters

- `Stmt`: statement (public key)
- `Wit`: witness (secret key)
- `Commit`: public commitment (sent to the verifier)
- `PrvState`: private prover state (retained between commit and respond)
- `Chal`: verifier challenge
- `Resp`: prover response
- `rel`: the relation proven by the protocol

## Main Definitions

- `IdenSchemeWithAbort`: identification scheme where `respond` returns `Option Resp`
- `IdenSchemeWithAbort.Complete`: honest prover convinces verifier (conditioned on non-abort)
- `IdenSchemeWithAbort.HVZK`: transcript distribution is within a stated TV-distance
  of a simulator
- `IdenSchemeWithAbort.PerfectHVZK`: exact transcript distribution matching with a simulator
- `IdenSchemeWithAbort.CommitmentRecoverable`: ability to recover commitment from the transcript

## References

- Fixing and Mechanizing the Security Proof of Fiat-Shamir with Aborts and Dilithium
  (CRYPTO 2023, ePrint 2023/246)
- EasyCrypt `IDSabort.ec`
-/


-- @@ L47-47 verbatim
@[expose] public section


-- @@ L49-49 verbatim
open OracleSpec OracleComp


-- @@ L51-69 verbatim
/-- An identification scheme with aborts for statements in `Stmt` and witnesses in `Wit`, where
`rel : Stmt → Wit → Bool` is the proven relation. The prover's commitment is split into a public
part `Commit` (sent to the verifier) and a private state `PrvState`. The verifier's challenge is
in `Chal`, and the prover's response (which may abort) is in `Resp`.

Unlike `SigmaProtocol`, the `respond` function returns `Option Resp` — `none` indicates an abort
and the protocol must be retried. This is the key mechanism used in Dilithium/ML-DSA to ensure
that the response distribution is independent of the secret. -/
structure IdenSchemeWithAbort
    (Stmt Wit Commit PrvState Chal Resp : Type) (rel : Stmt → Wit → Bool) where
  /-- Generate a commitment: returns a public commitment and private prover state. -/
  commit (stmt : Stmt) (wit : Wit) : ProbComp (Commit × PrvState)
  /-- Respond to a challenge. Returns `none` if the response would leak information about
  the secret (abort), in which case the protocol is retried from scratch. -/
  respond (stmt : Stmt) (wit : Wit) (prvState : PrvState) (chal : Chal) :
    ProbComp (Option Resp)
  /-- Deterministic verification: check that the response is valid for the given
  statement, commitment, and challenge. -/
  verify (stmt : Stmt) (commit : Commit) (chal : Chal) (resp : Resp) : Bool


-- @@ L71-71 verbatim
namespace IdenSchemeWithAbort


-- @@ L73-73 verbatim
variable {Stmt Wit Commit PrvState Chal Resp : Type} {rel : Stmt → Wit → Bool}


-- @@ L75-75 verbatim
section HonestExecution


-- @@ L77-77 verbatim
variable [SampleableType Chal] [IsUniformSpec unifSpec]


-- @@ L79-87 expanded
/-- A single honest execution producing an optional transcript `(Commit, Chal, Resp)`.
Returns `none` if the prover aborts. -/
def honestExecution (ids : IdenSchemeWithAbort Stmt Wit Commit PrvState Chal Resp rel) (s : Stmt)
    (w : Wit) : ProbComp (Option (Commit × Chal × Resp)) := do
  let (cm, st) ← ids.commit s w
  let c ← uniformSample Chal
  let oz ← ids.respond s w st c
  return oz.map fun z => (cm, c, z)


-- @@ L89-89 verbatim
end HonestExecution


-- @@ L91-91 verbatim
section Completeness


-- @@ L93-93 verbatim
variable [SampleableType Chal] [IsUniformSpec unifSpec]


-- @@ L95-104 expanded
/-- An identification scheme with aborts is complete if: whenever the prover does not abort,
the verifier always accepts. -/
def Complete (ids : IdenSchemeWithAbort Stmt Wit Commit PrvState Chal Resp rel) : Prop :=
  ∀ s w,
    rel s w = true →
      probOutput
          (do
            let t? ← ids.honestExecution s w
            return
              match t? with
              | some (cm, c, z) => ids.verify s cm c z
              | none => true)
          true =
        1


-- @@ L106-114 verbatim
/-- Support-level consequence of completeness: any non-aborting honest transcript in the
support has an accepting verification. -/
lemma verify_of_complete (ids : IdenSchemeWithAbort Stmt Wit Commit PrvState Chal Resp rel)
    (hc : ids.Complete) {s : Stmt} {w : Wit} (hrel : rel s w = true)
    {cm : Commit} {c : Chal} {z : Resp}
    (h_mem : some (cm, c, z) ∈ support (ids.honestExecution s w)) :
    ids.verify s cm c z = true :=
  ((probOutput_eq_one_iff_forall _ _).1 (hc s w hrel)).2 _
    ((mem_support_bind_iff _ _ _).2 ⟨_, h_mem, by simp⟩)


-- @@ L116-116 verbatim
end Completeness


-- @@ L118-118 verbatim
section HVZK


-- @@ L120-120 verbatim
variable [SampleableType Chal] [IsUniformSpec unifSpec]


-- @@ L122-131 verbatim
/-- Approximate honest-verifier zero-knowledge for an identification scheme with aborts:
the transcript distribution produced by the honest prover is within total variation
distance `ζ_zk` of the distribution produced by the simulator.

Both distributions are over `Option (Commit × Chal × Resp)`, where `none` represents an abort.
The parameter `ζ_zk` captures both transcript mismatch and abort-probability mismatch. -/
def HVZK (ids : IdenSchemeWithAbort Stmt Wit Commit PrvState Chal Resp rel)
    (sim : Stmt → ProbComp (Option (Commit × Chal × Resp))) (ζ_zk : ℝ) : Prop :=
  ∀ s w, rel s w = true →
    tvDist (ids.honestExecution s w) (sim s) ≤ ζ_zk


-- @@ L133-139 expanded
/-- Exact honest-verifier zero-knowledge for an identification scheme with aborts:
the transcript distribution produced by the honest prover exactly matches the
distribution produced by the simulator. -/
def PerfectHVZK (ids : IdenSchemeWithAbort Stmt Wit Commit PrvState Chal Resp rel)
    (sim : Stmt → ProbComp (Option (Commit × Chal × Resp))) : Prop :=
  ∀ s w, rel s w = true → evalSPMF (ids.honestExecution s w) = evalSPMF (sim s)


-- @@ L141-147 verbatim
/-- The perfect HVZK property is equivalent to the approximate HVZK property with `ζ_zk = 0`. -/
@[grind =]
lemma perfectHVZK_iff_hvzk_zero
    (ids : IdenSchemeWithAbort Stmt Wit Commit PrvState Chal Resp rel)
    (sim : Stmt → ProbComp (Option (Commit × Chal × Resp))) :
    ids.PerfectHVZK sim ↔ ids.HVZK sim 0 := by
  simp [PerfectHVZK, HVZK, ← tvDist_eq_zero_iff, le_antisymm_iff, tvDist_nonneg]


-- @@ L149-149 verbatim
end HVZK


-- @@ L151-151 verbatim
section CommitmentRecoverability


-- @@ L153-162 verbatim
/-- Commitment recoverability: any accepting transcript determines the public commitment
from the statement, challenge, and response alone. This property is required for the
CMA-to-NMA reduction in the Fiat-Shamir with aborts security proof.

In Dilithium/ML-DSA, the commitment `w1` can be recomputed as `highBits(Az - c*t)`. -/
def CommitmentRecoverable (ids : IdenSchemeWithAbort Stmt Wit Commit PrvState Chal Resp rel)
    (recover : Stmt → Chal → Resp → Commit) : Prop :=
  ∀ s cm c z,
    ids.verify s cm c z = true →
    recover s c z = cm


-- @@ L164-164 verbatim
end CommitmentRecoverability


-- @@ L166-166 verbatim
section Impersonation


-- @@ L168-174 verbatim
/-- An adversary for the impersonation game against an identification scheme with aborts.
The adversary sees the public key (statement), produces a commitment together with an
internal state, and then responds to a challenge using that state. -/
structure ImpAdv (ids : IdenSchemeWithAbort Stmt Wit Commit PrvState Chal Resp rel)
    (AdvSt : Type) where
  commit (s : Stmt) : ProbComp (Commit × AdvSt)
  respond (s : Stmt) (c : Chal) (st : AdvSt) : ProbComp Resp


-- @@ L176-176 verbatim
variable [SampleableType Chal] [IsUniformSpec unifSpec]


-- @@ L178-185 expanded
/-- The impersonation experiment: the adversary tries to produce a valid transcript
without knowing the witness, against a fixed statement `s`. -/
def impExp {ids : IdenSchemeWithAbort Stmt Wit Commit PrvState Chal Resp rel} {AdvSt : Type}
    (adv : ImpAdv ids AdvSt) (s : Stmt) : ProbComp Bool := do
  let (cm, st) ← adv.commit s
  let c ← uniformSample Chal
  let z ← adv.respond s c st
  return ids.verify s cm c z


-- @@ L187-187 verbatim
end Impersonation


-- @@ L189-189 verbatim
end IdenSchemeWithAbort
