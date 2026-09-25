/-
Copyright (c) 2025 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

module

public import VCVio.CryptoFoundations.SecExp
public import VCVio.OracleComp.SimSemantics.QueryImpl.Basic
public import VCVio.OracleComp.ProbCompLift
public import VCVio.OracleComp.ProbComp
public import VCVio.OracleComp.Coercions.Add
public import VCVio.OracleComp.Coercions.SubSpec
public import VCVio.OracleComp.SimSemantics.Append


-- @@ L17-22 verbatim
/-!
# Key Encapsulation Mechanisms

This file defines a type to represent protocols for key encapsulation mechanisms.
We also define basic correctness and security properties for these protocols.
-/


-- @@ L24-24 verbatim
@[expose] public section


-- @@ L26-26 verbatim
open OracleSpec OracleComp ENNReal


-- @@ L28-28 verbatim
universe u v


-- @@ L30-35 verbatim
/-- A key encapsulation mechanism with shared-key space `K`, public/secret key spaces `PK` and
`SK`, and ciphertext space `C`. -/
structure KEMScheme (m : Type → Type u) [Monad m] (K PK SK C : Type) where
  keygen : m (PK × SK)
  encaps : PK → m (C × K)
  decaps : SK → C → m (Option K)


-- @@ L37-37 verbatim
namespace KEMScheme

-- @@ L38-39 verbatim
variable {m : Type → Type v} [Monad m] {K PK SK C : Type}
  (kem : KEMScheme m K PK SK C)


-- @@ L41-41 verbatim
section Correct


-- @@ L43-43 verbatim
variable [DecidableEq K]


-- @@ L45-52 verbatim
/-- Correctness experiment: decapsulation of an honestly generated encapsulation should recover the
shared key. -/
def CorrectExp : m Bool :=
  do
    let (pk, sk) ← kem.keygen
    let (c, k) ← kem.encaps pk
    let k' ← kem.decaps sk c
    return decide (k' = some k)


-- @@ L54-56 expanded
/-- Perfect correctness of a KEM. -/
def PerfectlyCorrect (runtime : ProbCompRuntime m) : Prop :=
  probOutput (runtime.evalSPMF kem.CorrectExp) true = 1


-- @@ L58-58 verbatim
end Correct


-- @@ L60-60 verbatim
section IND_CPA


-- @@ L62-62 verbatim
variable {ι : Type} {spec : OracleSpec ι} [SampleableType K]


-- @@ L64-69 verbatim
/-- Two-phase IND-CPA adversary for a KEM. The adversary only gets access to the base oracle
set `spec`, with no decapsulation oracle. -/
structure IND_CPA_Adversary (_kem : KEMScheme (OracleComp spec) K PK SK C) where
  State : Type
  preChallenge : PK → OracleComp spec State
  postChallenge : State → C → K → OracleComp spec Bool


-- @@ L71-81 expanded
/-- Fixed-branch IND-CPA experiment for a KEM, matching the source proof-ladders formulation
`Exp.run(b)`. -/
def IND_CPA_Exp {kem : KEMScheme (OracleComp spec) K PK SK C}
    (runtime : ProbCompRuntime (OracleComp spec)) (adversary : kem.IND_CPA_Adversary) (b : Bool) :
    SPMF Bool :=
  runtime.evalSPMF do
    let (pk, _sk) ← kem.keygen
    let st ← adversary.preChallenge pk
    let (cStar, kReal) ← kem.encaps pk
    let kRand ← runtime.liftProbComp (uniformSample K)
    adversary.postChallenge st cStar (if b then kReal else kRand)


-- @@ L83-95 expanded
/-- Single-game IND-CPA experiment obtained by sampling the challenge bit uniformly and checking
whether the adversary guessed it correctly. -/
def IND_CPA_Game {kem : KEMScheme (OracleComp spec) K PK SK C}
    (runtime : ProbCompRuntime (OracleComp spec)) (adversary : kem.IND_CPA_Adversary) : SPMF Bool :=
  runtime.evalSPMF
    (do
      let (pk, _sk) ← kem.keygen
      let st ← adversary.preChallenge pk
      let b ← runtime.liftProbComp (uniformSample Bool)
      let (cStar, kReal) ← kem.encaps pk
      let kRand ← runtime.liftProbComp (uniformSample K)
      let b' ← adversary.postChallenge st cStar (if b then kReal else kRand)
      return (b == b'))


-- @@ L97-102 verbatim
/-- IND-CPA distinguishing advantage for a KEM, defined canonically as the bias of the single
game. -/
noncomputable def IND_CPA_Advantage {kem : KEMScheme (OracleComp spec) K PK SK C}
    (runtime : ProbCompRuntime (OracleComp spec))
    (adversary : kem.IND_CPA_Adversary) : ℝ :=
  (IND_CPA_Game runtime adversary).boolBiasAdvantage


-- @@ L104-109 verbatim
/-- The canonical IND-CPA advantage is definitionally the bias of the single game. -/
theorem IND_CPA_Advantage_eq_game_bias {kem : KEMScheme (OracleComp spec) K PK SK C}
    (runtime : ProbCompRuntime (OracleComp spec))
    (adversary : kem.IND_CPA_Adversary) :
    kem.IND_CPA_Advantage runtime adversary =
      (kem.IND_CPA_Game runtime adversary).boolBiasAdvantage := rfl


-- @@ L111-111 verbatim
end IND_CPA


-- @@ L113-113 verbatim
section IND_CCA


-- @@ L115-115 verbatim
variable {ι : Type} {spec : OracleSpec ι} [DecidableEq C] [SampleableType K]


-- @@ L117-119 expanded
/-- IND-CCA adversaries get access to the base oracle set `spec` plus a decapsulation oracle. -/
def IND_CCA_oracleSpec (_kem : KEMScheme (OracleComp spec) K PK SK C) :=
  spec + (OracleSpec.ofFn (ι := C) (fun _ => Option K))


-- @@ L121-125 verbatim
/-- Two-phase IND-CCA adversary for a KEM. -/
structure IND_CCA_Adversary (kem : KEMScheme (OracleComp spec) K PK SK C) where
  State : Type
  preChallenge : PK → OracleComp kem.IND_CCA_oracleSpec State
  postChallenge : State → C → K → OracleComp kem.IND_CCA_oracleSpec Bool


-- @@ L127-131 verbatim
/-- Pre-challenge decapsulation oracle. -/
def IND_CCA_preChallengeImpl (kem : KEMScheme (OracleComp spec) K PK SK C)
    (sk : SK) : QueryImpl (IND_CCA_oracleSpec kem) (OracleComp spec) :=
  QueryImpl.add (HasQuery.toQueryImpl (spec := spec) (m := OracleComp spec))
    fun c => kem.decaps sk c


-- @@ L133-137 verbatim
/-- Post-challenge decapsulation oracle: the challenge ciphertext itself maps to `none`. -/
def IND_CCA_postChallengeImpl (kem : KEMScheme (OracleComp spec) K PK SK C)
    (sk : SK) (cStar : C) : QueryImpl (IND_CCA_oracleSpec kem) (OracleComp spec) :=
  QueryImpl.add (HasQuery.toQueryImpl (spec := spec) (m := OracleComp spec)) fun c =>
    if c = cStar then return none else kem.decaps sk c


-- @@ L139-151 expanded
/-- IND-CCA real-or-random experiment for a KEM. -/
def IND_CCA_Game {kem : KEMScheme (OracleComp spec) K PK SK C}
    (runtime : ProbCompRuntime (OracleComp spec)) (adversary : kem.IND_CCA_Adversary) : SPMF Bool :=
  runtime.evalSPMF
    (do
      let (pk, sk) ← kem.keygen
      let st ← simulateQ (kem.IND_CCA_preChallengeImpl sk) (adversary.preChallenge pk)
      let b ← runtime.liftProbComp (uniformSample Bool)
      let (cStar, kReal) ← kem.encaps pk
      let kRand ← runtime.liftProbComp (uniformSample K)
      let b' ←
        simulateQ (kem.IND_CCA_postChallengeImpl sk cStar)
            (adversary.postChallenge st cStar (if b then kReal else kRand))
      return (b == b'))


-- @@ L153-157 verbatim
/-- IND-CCA distinguishing advantage for a KEM. -/
noncomputable def IND_CCA_Advantage {kem : KEMScheme (OracleComp spec) K PK SK C}
    (runtime : ProbCompRuntime (OracleComp spec))
    (adversary : kem.IND_CCA_Adversary) : ℝ :=
  (IND_CCA_Game runtime adversary).boolBiasAdvantage


-- @@ L159-170 expanded
/-- Any IND-CPA adversary can be viewed as an IND-CCA adversary that simply ignores the
decapsulation oracle while preserving its ordinary pre-challenge interaction with the base
oracle set `spec`. -/
def IND_CPA_Adversary.toIND_CCA {kem : KEMScheme (OracleComp spec) K PK SK C}
    (adversary : kem.IND_CPA_Adversary) : kem.IND_CCA_Adversary
    where
  State := adversary.State
  preChallenge
    pk :=
    simulateQ
      (HasQuery.toQueryImpl (spec := spec) (m :=
        OracleComp (spec + (OracleSpec.ofFn (ι := C) (fun _ => Option K)))))
      (adversary.preChallenge pk)
  postChallenge st cStar
    kStar :=
    simulateQ
      (HasQuery.toQueryImpl (spec := spec) (m :=
        OracleComp (spec + (OracleSpec.ofFn (ι := C) (fun _ => Option K)))))
      (adversary.postChallenge st cStar kStar)


-- @@ L172-198 expanded
/-- The one-stage IND-CPA game is exactly the IND-CCA game instantiated with the trivial
CPA-to-CCA embedding (`toIND_CCA`) that never uses the decryption oracle. -/
theorem IND_CPA_Game_eq_IND_CCA_Game_toIND_CCA {kem : KEMScheme (OracleComp spec) K PK SK C}
    (runtime : ProbCompRuntime (OracleComp spec)) (adversary : kem.IND_CPA_Adversary) :
    kem.IND_CPA_Game runtime adversary = kem.IND_CCA_Game runtime adversary.toIND_CCA :=
  by
  have h :
    ∀ (impl₂ : QueryImpl (OracleSpec.ofFn (ι := C) (fun _ => Option K)) (OracleComp spec))
      {α : Type} (oa : OracleComp spec α),
      simulateQ (QueryImpl.add (HasQuery.toQueryImpl (spec := spec) (m := OracleComp spec)) impl₂)
          (simulateQ
            (HasQuery.toQueryImpl (spec := spec) (m :=
              OracleComp (spec + (OracleSpec.ofFn (ι := C) (fun _ => Option K)))))
            oa) =
        oa :=
    by
    intro impl₂ α oa
    rw [← QueryImpl.simulateQ_compose]
    have :
      QueryImpl.compose
          (QueryImpl.add (HasQuery.toQueryImpl (spec := spec) (m := OracleComp spec)) impl₂)
          (HasQuery.toQueryImpl (spec := spec) (m :=
            OracleComp (spec + (OracleSpec.ofFn (ι := C) (fun _ => Option K))))) =
        QueryImpl.id' spec :=
      by
      rw [QueryImpl.add_eq_hAdd]
      ext t
      simp [QueryImpl.compose, HasQuery.toQueryImpl_eq_id']
      simpa using (QueryImpl.simulateQ_add_liftM_query_left (QueryImpl.id' spec) impl₂ t)
    rw [this, simulateQ_id']
  simp only [IND_CPA_Game, IND_CCA_Game, IND_CPA_Adversary.toIND_CCA, IND_CCA_preChallengeImpl,
    IND_CCA_postChallengeImpl, IND_CCA_oracleSpec, h]


-- @@ L200-200 verbatim
end IND_CCA


-- @@ L202-202 verbatim
end KEMScheme
