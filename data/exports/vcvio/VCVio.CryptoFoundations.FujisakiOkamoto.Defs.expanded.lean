/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.CryptoFoundations.AsymmEncAlg.Defs
public import VCVio.OracleComp.Coercions.Add
public import VCVio.OracleComp.Coercions.SubSpec
public import VCVio.OracleComp.SimSemantics.Append
public import VCVio.OracleComp.SimSemantics.QueryImpl.Basic
public import VCVio.OracleComp.SimSemantics.StateT.Basic


-- @@ L16-25 verbatim
/-!
# Fujisaki-Okamoto Shared Definitions

This file defines the shared objects used by the Fujisaki-Okamoto transform:

- explicit-coins PKEs as a specialization of `AsymmEncAlg`
- the induced randomized `AsymmEncAlg`
- spread notions and OW-CPA games for the `ProbComp` specialization
- OW-PCVA games for the general monadic interface
-/


-- @@ L27-27 verbatim
@[expose] public section


-- @@ L29-29 verbatim
open OracleComp OracleSpec ENNReal


-- @@ L31-31 verbatim
universe u v


-- @@ L33-33 verbatim
namespace AsymmEncAlg.ExplicitCoins


-- @@ L35-36 verbatim
variable {M PK SK R C : Type}
  (pke : AsymmEncAlg.ExplicitCoins ProbComp M PK SK R C)


-- @@ L38-38 verbatim
section Correct


-- @@ L40-40 verbatim
variable [DecidableEq M] [SampleableType R]


-- @@ L42-50 expanded
/-- `delta`-correctness: failure in the canonical `AsymmEncAlg.CorrectExp` experiment occurs with
probability at most `delta`. -/
def deltaCorrect (delta : ℝ≥0∞) : Prop :=
  ∀ msg : M,
    probOutput
        (do
          let (pk, sk) ← pke.keygen
          let r ← (uniformSample R)
          let c := pke.encrypt pk msg r
          let msg' := pke.decrypt sk c
          pure (decide (msg' = some msg)))
        false ≤
      delta


-- @@ L52-52 verbatim
end Correct


-- @@ L54-59 expanded
/-- `gamma`-spread: no ciphertext occurs with probability more than `gamma` for any fixed public
key and plaintext. -/
def gammaSpread [SampleableType R] [DecidableEq C] (gamma : ℝ≥0∞) : Prop :=
  ∀ pk msg c,
    probOutput
        (do
          let r ← (uniformSample R)
          pure (pke.encrypt pk msg r))
        c ≤
      gamma


-- @@ L61-61 verbatim
section OW_CPA


-- @@ L63-63 verbatim
variable [SampleableType M] [SampleableType R] [DecidableEq M]


-- @@ L65-72 expanded
/-- Oracle interface for the one-way under chosen-plaintext attack (OW-CPA) game.

The sum `unifSpec + (M →ₒ C)` gives the adversary two capabilities:
- unrestricted uniform sampling from any sampleable type
- an encryption oracle on chosen plaintexts `M → C`
-/
def OW_CPA_oracleSpec (_pke : AsymmEncAlg.ExplicitCoins ProbComp M PK SK R C) :=
  unifSpec + (OracleSpec.ofFn (ι := M) (fun _ => C))


-- @@ L74-76 verbatim
/-- An OW-CPA adversary gets `pk`, a challenge ciphertext, and oracle access to chosen-plaintext
encryptions. -/
abbrev OW_CPA_Adversary := PK → C → OracleComp pke.OW_CPA_oracleSpec M


-- @@ L78-84 expanded
/-- Implementation of the OW-CPA encryption oracle. -/
def OW_CPA_queryImpl (pk : PK) : QueryImpl pke.OW_CPA_oracleSpec ProbComp :=
  QueryImpl.add (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp))
    (fun msg => do
      let r ← (uniformSample R)
      pure (pke.encrypt pk msg r))


-- @@ L86-98 expanded
/-- Main one-way under chosen-plaintext attack (OW-CPA) experiment.

The game samples a fresh keypair and a uniform challenge message, forms the honest challenge
ciphertext via the induced randomized `AsymmEncAlg`, runs the adversary with oracle access
described by `OW_CPA_oracleSpec`, and returns `true` exactly when the adversary recovers the
challenge message. -/
def OW_CPA_Game (adversary : pke.OW_CPA_Adversary) : ProbComp Bool := do
  let (pk, _sk) ← pke.keygen
  let msg ← uniformSample M
  let r ← (uniformSample R)
  let c := pke.encrypt pk msg r
  let msg' ← simulateQ (pke.OW_CPA_queryImpl pk) (adversary pk c)
  return decide (msg' = msg)


-- @@ L100-102 expanded
/-- OW-CPA advantage is the probability of recovering the sampled challenge plaintext. -/
noncomputable def OW_CPA_Advantage (adversary : pke.OW_CPA_Adversary) : ℝ≥0∞ :=
  probOutput (pke.OW_CPA_Game adversary) true


-- @@ L104-104 verbatim
end OW_CPA


-- @@ L106-106 verbatim
end AsymmEncAlg.ExplicitCoins


-- @@ L108-108 verbatim
section OW_PCVA


-- @@ L110-110 verbatim
variable {ι : Type u} {spec : OracleSpec ι} {M PK SK C : Type}


-- @@ L112-121 expanded
/-- Oracle interface for the one-way under plaintext-checking and validity attacks
(OW-PCVA) game.

The sum `spec + (((C × M) →ₒ Bool) + (C →ₒ Bool))` has three components:
- the ambient oracle interface `spec`
- a plaintext-checking oracle sending `(c, msg)` to whether `c` decrypts to `msg`
- a validity oracle sending `c` to whether `c` decrypts to some plaintext at all
-/
def OW_PCVA_oracleSpec (_encAlg : AsymmEncAlg (OracleComp spec) M PK SK C) :=
  spec +
    ((OracleSpec.ofFn (ι := (C × M)) (fun _ => Bool)) + (OracleSpec.ofFn (ι := C) (fun _ => Bool)))


-- @@ L123-126 verbatim
/-- An OW-PCVA adversary gets the public key and challenge ciphertext, and outputs a plaintext
guess after querying the plaintext-checking and validity oracles. -/
abbrev OW_PCVA_Adversary (encAlg : AsymmEncAlg (OracleComp spec) M PK SK C) :=
  PK → C → OracleComp (OW_PCVA_oracleSpec encAlg) M


-- @@ L128-137 expanded
/-- Oracle implementation for OW-PCVA. -/
def OW_PCVA_queryImpl (encAlg : AsymmEncAlg (OracleComp spec) M PK SK C) [DecidableEq M] (sk : SK) :
    QueryImpl (OW_PCVA_oracleSpec encAlg) (OracleComp spec) :=
  let checkImpl : QueryImpl (OracleSpec.ofFn (ι := (C × M)) (fun _ => Bool)) (OracleComp spec) :=
    fun (c, msg) => do
    let msg' ← encAlg.decrypt sk c
    return decide (msg' = some msg)
  let validImpl : QueryImpl (OracleSpec.ofFn (ι := C) (fun _ => Bool)) (OracleComp spec) := fun c =>
    do
    let msg' ← encAlg.decrypt sk c
    return msg'.isSome
  (HasQuery.toQueryImpl (spec := spec) (m := OracleComp spec)) + (checkImpl + validImpl)


-- @@ L139-154 expanded
/-- Main one-way under plaintext-checking and validity attacks (OW-PCVA) experiment.

The game generates a keypair, samples a uniform challenge message, encrypts it honestly, and
then runs the adversary on the public key and challenge ciphertext. The adversary may query the
ambient oracle interface `spec`, the plaintext-checking oracle, and the validity oracle, and the
game returns `true` exactly when the final guess equals the hidden challenge message. -/
def OW_PCVA_Game {encAlg : AsymmEncAlg (OracleComp spec) M PK SK C} [SampleableType M]
    [DecidableEq M] (runtime : ProbCompRuntime (OracleComp spec))
    (adversary : OW_PCVA_Adversary encAlg) : SPMF Bool :=
  runtime.evalSPMF
    (do
      let (pk, sk) ← encAlg.keygen
      let msg ← runtime.liftProbComp (uniformSample M)
      let cStar ← encAlg.encrypt pk msg
      let msg' ← simulateQ (OW_PCVA_queryImpl encAlg sk) (adversary pk cStar)
      return decide (msg' = msg))


-- @@ L156-161 expanded
/-- OW-PCVA advantage is the message-recovery probability in the above game. -/
noncomputable def OW_PCVA_Advantage {encAlg : AsymmEncAlg (OracleComp spec) M PK SK C}
    [SampleableType M] [DecidableEq M] (runtime : ProbCompRuntime (OracleComp spec))
    (adversary : OW_PCVA_Adversary encAlg) : ℝ≥0∞ :=
  probOutput (OW_PCVA_Game runtime adversary) true


-- @@ L163-163 verbatim
end OW_PCVA
