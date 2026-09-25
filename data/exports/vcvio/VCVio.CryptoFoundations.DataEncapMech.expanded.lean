/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.SecExp
public import VCVio.OracleComp.ProbComp
public import VCVio.OracleComp.ProbCompLift


-- @@ L12-17 verbatim
/-!
# Data Encapsulation Mechanisms

This file defines data encapsulation mechanisms (DEMs), their correctness notion, and the
one-time IND-CPA game used by the KEM+DEM composition theorem.
-/


-- @@ L19-19 verbatim
@[expose] public section


-- @@ L21-21 verbatim
universe u v


-- @@ L23-23 verbatim
open OracleSpec OracleComp ENNReal


-- @@ L25-29 verbatim
/-- A data encapsulation mechanism with key space `K`, message space `M`, and ciphertext space
`C`. The key is supplied externally, matching the proof-ladders DEM model. -/
structure DEMScheme (m : Type → Type u) [Monad m] (K M C : Type) where
  encrypt : K → M → m C
  decrypt : K → C → m M


-- @@ L31-31 verbatim
namespace DEMScheme

-- @@ L32-33 verbatim
variable {m : Type → Type v} [Monad m] {K M C : Type}
  (dem : DEMScheme m K M C)


-- @@ L35-35 verbatim
section Correct


-- @@ L37-37 verbatim
variable [DecidableEq M]


-- @@ L39-44 verbatim
/-- Correctness experiment for a DEM under an externally supplied key. -/
def CorrectExp (k : K) (msg : M) : m Bool :=
  do
    let c ← dem.encrypt k msg
    let msg' ← dem.decrypt k c
    return decide (msg' = msg)


-- @@ L46-49 expanded
/-- Perfect correctness for a DEM: every externally supplied key decrypts honest ciphertexts
correctly with probability `1`. -/
def PerfectlyCorrect (runtime : ProbCompRuntime m) : Prop :=
  ∀ k : K, ∀ msg : M, probOutput (runtime.evalSPMF (dem.CorrectExp k msg)) true = 1


-- @@ L51-51 verbatim
end Correct


-- @@ L53-53 verbatim
section IND_CPA


-- @@ L55-55 verbatim
variable {ι : Type} {spec : OracleSpec ι} [SampleableType K]


-- @@ L57-62 verbatim
/-- Two-phase one-time IND-CPA adversary for a DEM. The key is hidden, so the message-selection
phase receives no public input. -/
structure IND_CPA_Adversary (_dem : DEMScheme (OracleComp spec) K M C) where
  State : Type
  chooseMessages : OracleComp spec (M × M × State)
  distinguish : State → C → OracleComp spec Bool


-- @@ L64-73 expanded
/-- Fixed-branch one-time IND-CPA experiment for a DEM, matching the source proof-ladders
`DEM_1CPA_Exp.run(b)` presentation. -/
def IND_CPA_Exp {dem : DEMScheme (OracleComp spec) K M C}
    (runtime : ProbCompRuntime (OracleComp spec)) (adversary : dem.IND_CPA_Adversary) (b : Bool) :
    SPMF Bool :=
  runtime.evalSPMF do
    let k ← runtime.liftProbComp (uniformSample K)
    let (m₀, m₁, st) ← adversary.chooseMessages
    let c ← dem.encrypt k (if b then m₁ else m₀)
    adversary.distinguish st c


-- @@ L75-85 expanded
/-- Game-form one-time IND-CPA experiment for a DEM. -/
def IND_CPA_Game {dem : DEMScheme (OracleComp spec) K M C}
    (runtime : ProbCompRuntime (OracleComp spec)) (adversary : dem.IND_CPA_Adversary) : SPMF Bool :=
  runtime.evalSPMF
    (do
      let b ← runtime.liftProbComp (uniformSample Bool)
      let k ← runtime.liftProbComp (uniformSample K)
      let (m₀, m₁, st) ← adversary.chooseMessages
      let c ← dem.encrypt k (if b then m₁ else m₀)
      let b' ← adversary.distinguish st c
      return (b == b'))


-- @@ L87-91 verbatim
/-- One-time IND-CPA advantage for a DEM, defined canonically as the bias of the single game. -/
noncomputable def IND_CPA_Advantage {dem : DEMScheme (OracleComp spec) K M C}
    (runtime : ProbCompRuntime (OracleComp spec))
    (adversary : dem.IND_CPA_Adversary) : ℝ :=
  (IND_CPA_Game runtime adversary).boolBiasAdvantage


-- @@ L93-98 verbatim
/-- The canonical one-time IND-CPA advantage is definitionally the bias of the single game. -/
theorem IND_CPA_Advantage_eq_game_bias {dem : DEMScheme (OracleComp spec) K M C}
    (runtime : ProbCompRuntime (OracleComp spec))
    (adversary : dem.IND_CPA_Adversary) :
    dem.IND_CPA_Advantage runtime adversary =
      (dem.IND_CPA_Game runtime adversary).boolBiasAdvantage := rfl


-- @@ L100-100 verbatim
end IND_CPA


-- @@ L102-102 verbatim
end DEMScheme
