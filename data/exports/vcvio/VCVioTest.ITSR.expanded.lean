/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.HardnessAssumptions.KeyedHash.ITSR


-- @@ L10-10 verbatim
/-! # ITSR source-game canaries -/


-- @@ L12-12 verbatim
public section


-- @@ L14-14 verbatim
open OracleComp KeyedHash


-- @@ L16-16 verbatim
namespace ITSRTest


-- @@ L18-20 expanded
def parityProblem : ITSRProblem Bool Nat Bool Nat
    where
  khf := { keygen := uniformSample Bool, hash := fun k x => k == decide (x % 2 = 0) }
  indices := fun y => if y then [0] else [1]


-- @@ L22-24 expanded
def constantIndexProblem : ITSRProblem Bool Nat Unit Nat
    where
  khf := { keygen := uniformSample Bool, hash := fun _ _ => () }
  indices := fun _ => [0]


-- @@ L26-28 verbatim
def deterministicCoveredProblem : ITSRProblem Unit Nat Unit Nat where
  khf := { keygen := pure (), hash := fun _ _ => () }
  indices := fun _ => [0]


-- @@ L30-32 verbatim
def deterministicIndexedProblem : ITSRProblem Unit Nat Nat Nat where
  khf := { keygen := pure (), hash := fun _ x => x }
  indices := fun y => [y]


-- @@ L34-35 verbatim
def targetUnit (x : Nat) : OracleComp (unifSpec + ITSRTargetSpec Nat Unit) Unit :=
  liftM ((unifSpec + ITSRTargetSpec Nat Unit).query (.inr x))


-- @@ L37-38 verbatim
def coveredFresh : ITSRAdversary deterministicCoveredProblem where
  main := targetUnit 1 *> pure ((), 2)


-- @@ L40-41 verbatim
def repeatedPair : ITSRAdversary deterministicCoveredProblem where
  main := targetUnit 1 *> pure ((), 1)


-- @@ L43-44 verbatim
def uncoveredIndex : ITSRAdversary deterministicIndexedProblem where
  main := targetUnit 1 *> pure ((), 2)


-- @@ L46-49 verbatim
/-- The candidate pair must be fresh even when its semantic index is covered. -/
theorem repeated_pair_relation_canary :
    ¬parityProblem.Wins [(true, 2)] (true, 2) := by
  decide


-- @@ L51-54 verbatim
/-- Pair freshness permits reusing a target key at a fresh input. -/
theorem reused_key_relation_canary :
    constantIndexProblem.Wins [(true, 1)] (true, 2) := by
  decide


-- @@ L56-59 verbatim
/-- Pair freshness also permits reusing a target input under a fresh key. -/
theorem reused_input_relation_canary :
    constantIndexProblem.Wins [(true, 1)] (false, 1) := by
  decide


-- @@ L61-64 verbatim
/-- A fresh pair loses when its selected index is not covered by the transcript. -/
theorem uncovered_index_relation_canary :
    ¬parityProblem.Wins [(true, 2)] (true, 3) := by
  decide


-- @@ L66-74 verbatim
/-- The exact experiment distinguishes covered fresh pairs from the two near misses: repeating the
recorded pair and selecting an uncovered semantic index. -/
theorem exact_experiment_canary :
    ITSRExperiment coveredFresh = pure true ∧
      ITSRExperiment repeatedPair = pure false ∧
      ITSRExperiment uncoveredIndex = pure false := by
  simp [ITSRExperiment, coveredFresh, repeatedPair, uncoveredIndex, targetUnit,
    ITSROracles, ITSRTargetOracle, ITSRProblem.Wins, ITSRProblem.indexSet,
    ITSRProblem.targetIndexSet, deterministicCoveredProblem, deterministicIndexedProblem]


-- @@ L76-80 verbatim
/-- The target oracle's state theorem pins append-in-issue-order semantics. -/
theorem target_history_canary (x : Nat) (targets : ITSRTranscript Bool Nat) :
    (ITSRTargetOracle constantIndexProblem x).run targets =
      constantIndexProblem.khf.keygen >>= fun k => pure (k, targets ++ [(k, x)]) :=
  ITSRTargetOracle_run constantIndexProblem x targets


-- @@ L82-82 verbatim
end ITSRTest
