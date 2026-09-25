/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

module
public import VCVio.CryptoFoundations.AsymmEncAlg.Defs
public import VCVio.CryptoFoundations.SecExp


-- @@ L11-16 verbatim
/-!
# Asymmetric Encryption Schemes: One-Time IND-CPA

This file contains the standard two-phase one-time IND-CPA game together with the `ProbComp`
specialization used by the generic many-query lift.
-/


-- @@ L18-18 verbatim
@[expose] public section


-- @@ L20-20 verbatim
open OracleSpec OracleComp


-- @@ L22-22 verbatim
universe v


-- @@ L24-24 verbatim
namespace AsymmEncAlg


-- @@ L26-26 verbatim
variable {m : Type → Type v} [Monad m] {M PK SK C : Type}


-- @@ L28-28 verbatim
section IND_CPA_TwoPhase


-- @@ L30-30 verbatim
variable {ι : Type} {spec : OracleSpec ι}


-- @@ L32-36 verbatim
/-- Two-phase adversary for IND-CPA security. -/
structure IND_CPA_Adv (encAlg : AsymmEncAlg m M PK SK C) where
  State : Type
  chooseMessages : PK → m (M × M × State)
  distinguish : State → C → m Bool


-- @@ L38-39 verbatim
variable {encAlg : AsymmEncAlg (OracleComp spec) M PK SK C}
  (adv : IND_CPA_Adv encAlg)


-- @@ L41-52 expanded
/-- One-time IND-CPA experiment for an asymmetric encryption algorithm:
sample keys, let the adversary choose challenge messages, encrypt one branch, and return whether
the adversary guessed the hidden bit. -/
def IND_CPA_OneTime_Game (runtime : ProbCompRuntime (OracleComp spec)) : SPMF Bool :=
  runtime.evalSPMF
    (do
      let b : Bool ← runtime.liftProbComp (uniformSample Bool)
      let (pk, _) ← encAlg.keygen
      let (m₁, m₂, state) ← adv.chooseMessages pk
      let msg := if b then m₁ else m₂
      let c ← encAlg.encrypt pk msg
      let b' ← adv.distinguish state c
      return (b == b'))


-- @@ L54-59 verbatim
/-- Absolute one-time IND-CPA bias advantage for the general two-phase game. -/
noncomputable def IND_CPA_OneTime_biasAdvantage
    (encAlg : AsymmEncAlg (OracleComp spec) M PK SK C)
    (runtime : ProbCompRuntime (OracleComp spec))
    (adv : IND_CPA_Adv encAlg) : ℝ :=
  (IND_CPA_OneTime_Game (encAlg := encAlg) adv runtime).boolBiasAdvantage


-- @@ L61-61 verbatim
end IND_CPA_TwoPhase


-- @@ L63-63 verbatim
section ProbCompSpecialization


-- @@ L65-65 verbatim
variable {encAlg : AsymmEncAlg ProbComp M PK SK C}


-- @@ L67-74 expanded
/-- `ProbComp` specialization of the one-time IND-CPA game. -/
abbrev IND_CPA_OneTime_Game_ProbComp (adv : IND_CPA_Adv encAlg) : ProbComp Bool := do
  let b ← (uniformSample Bool)
  let (pk, _sk) ← encAlg.keygen
  let (m₁, m₂, state) ← adv.chooseMessages pk
  let c ← encAlg.encrypt pk (if b then m₁ else m₂)
  let b' ← adv.distinguish state c
  pure (b == b')


-- @@ L76-80 expanded
/-- Real-valued signed one-time IND-CPA advantage. -/
noncomputable def IND_CPA_OneTime_signedAdvantageReal (encAlg : AsymmEncAlg ProbComp M PK SK C)
    (adv : IND_CPA_Adv encAlg) : ℝ :=
  (probOutput (IND_CPA_OneTime_Game_ProbComp (encAlg := encAlg) adv) true).toReal - 1 / 2


-- @@ L82-82 verbatim
end ProbCompSpecialization


-- @@ L84-84 verbatim
end AsymmEncAlg
