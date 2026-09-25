/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.EvalDist.Defs.Instances
public import VCVio.OracleComp.ProbComp
public import VCVio.OracleComp.ProbCompLift
public import VCVio.OracleComp.QueryTracking.LoggingOracle
public import VCVio.OracleComp.SimSemantics.Append
public import VCVio.OracleComp.SimSemantics.QueryImpl.Basic


-- @@ L16-21 verbatim
/-!
# Message Authentication Codes

This file defines keyed message-authentication-code algorithms together with their standard
UF-CMA security game.
-/


-- @@ L23-23 verbatim
@[expose] public section


-- @@ L25-25 verbatim
universe u v


-- @@ L27-27 verbatim
open OracleSpec OracleComp ENNReal


-- @@ L29-34 verbatim
/-- MAC algorithm with computations in the monad `m`, where `M` is the message space, `K` the key
space, and `T` the tag space. -/
structure MacAlg (m : Type → Type v) [Monad m] (M K T : Type) where
  keygen : m K
  tag : K → M → m T
  verify : K → M → T → m Bool


-- @@ L36-36 verbatim
namespace MacAlg

-- @@ L37-37 verbatim
section taggingOracle


-- @@ L39-39 verbatim
variable {m : Type → Type v} [Monad m] {M K T : Type}


-- @@ L41-44 expanded
/-- Oracle exposing chosen-message tagging queries while logging every queried message. -/
def taggingOracle (macAlg : MacAlg m M K T) (k : K) :
    QueryImpl (OracleSpec.ofFn (ι := M) (fun _ => T))
      (WriterT (QueryLog (OracleSpec.ofFn (ι := M) (fun _ => T))) m) :=
  QueryImpl.withLogging (fun msg => macAlg.tag k msg)


-- @@ L46-46 verbatim
end taggingOracle


-- @@ L48-48 verbatim
section sound


-- @@ L50-50 verbatim
variable {m : Type → Type v} [Monad m] {M K T : Type}


-- @@ L52-57 expanded
/-- Perfect completeness for a MAC: honestly generated tags always verify. -/
def PerfectlyComplete (macAlg : MacAlg m M K T) (runtime : ProbCompRuntime m) : Prop :=
  ∀ msg : M,
    probOutput
        (runtime.evalSPMF do
          let k ← macAlg.keygen
          let τ ← macAlg.tag k msg
          macAlg.verify k msg τ)
        true =
      1


-- @@ L59-59 verbatim
end sound


-- @@ L61-61 verbatim
section UF_CMA


-- @@ L63-64 verbatim
variable {ι : Type u} {spec : OracleSpec ι} {M K T : Type}
  [DecidableEq M] [DecidableEq T]


-- @@ L66-69 expanded
/-- UF-CMA adversary for a MAC: it receives oracle access to the tagging oracle and outputs a
candidate forgery `(msg, tag)`. -/
structure UF_CMA_Adversary (_macAlg : MacAlg (OracleComp spec) M K T) where
  main : OracleComp (spec + (OracleSpec.ofFn (ι := M) (fun _ => T))) (M × T)


-- @@ L71-87 expanded
/-- UF-CMA experiment for a MAC: the adversary succeeds iff it outputs a valid tag for a fresh
message under the challenge key. -/
def UF_CMA_Exp {macAlg : MacAlg (OracleComp spec) M K T}
    (runtime : ProbCompRuntime (OracleComp spec)) (adversary : macAlg.UF_CMA_Adversary) :
    SPMF Bool :=
  runtime.evalSPMF
    (do
      let k ← macAlg.keygen
      let impl :
        QueryImpl (spec + (OracleSpec.ofFn (ι := M) (fun _ => T)))
          (WriterT (QueryLog (OracleSpec.ofFn (ι := M) (fun _ => T))) (OracleComp spec)) :=
        (HasQuery.toQueryImpl (spec := spec) (m := OracleComp spec)).liftTarget
            (WriterT (QueryLog (OracleSpec.ofFn (ι := M) (fun _ => T))) (OracleComp spec)) +
          macAlg.taggingOracle k
      let sim_adv :
        WriterT (QueryLog (OracleSpec.ofFn (ι := M) (fun _ => T))) (OracleComp spec) (M × T) :=
        simulateQ impl adversary.main
      let ((msg, τ), log) ← sim_adv.run
      let verified ← macAlg.verify k msg τ
      return !log.wasQueried msg && verified)


-- @@ L89-95 expanded
/-- UF-CMA advantage for a MAC, represented as the probability of producing a valid forgery on a
fresh message. -/
noncomputable def UF_CMA_Advantage {macAlg : MacAlg (OracleComp spec) M K T}
    (runtime : ProbCompRuntime (OracleComp spec)) (adversary : macAlg.UF_CMA_Adversary) : ℝ≥0∞ :=
  probOutput (UF_CMA_Exp runtime adversary) true


-- @@ L97-97 verbatim
end UF_CMA


-- @@ L99-99 verbatim
end MacAlg
