/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.SMDTDSPRFinalValidity


-- @@ L11-17 verbatim
/-!
# SM-DT-DSPR mutation canaries

These small executable games pin the security-critical parts of the definition: the hidden-seed
phase split, always-answering final-validity semantics, cap and cross-oracle poisoning, and the
`SPprob` subtraction in the exported advantage.
-/


-- @@ L19-19 verbatim
@[expose] public section


-- @@ L21-21 verbatim
open OracleComp OracleSpec TweakableHash


-- @@ L23-23 verbatim
namespace SMDTDSPRFinalValidityTest


-- @@ L25-26 verbatim
inductive Seed
  | only


-- @@ L28-31 verbatim
instance : SampleableType Seed where
  selectElem := pure .only
  mem_support_selectElem := by simp
  probOutput_selectElem_eq x y := by cases x; cases y; rfl


-- @@ L33-33 expanded
@[simp]
lemma uniformSample_seed : (uniformSample Seed : ProbComp Seed) = pure .only :=
  rfl


-- @@ L35-38 expanded
/-- Every Boolean target has a second preimage. -/
def collidingHash : TweakableHash Seed Bool Bool Bool
    where
  seedGen := uniformSample Seed
  eval _ _ _ := false


-- @@ L40-43 expanded
/-- No Boolean target has a second preimage. -/
def injectiveHash : TweakableHash Seed Bool Bool Bool
    where
  seedGen := uniformSample Seed
  eval _ _ m := m


-- @@ L45-47 verbatim
def collection : TweakableHashCollection Unit Seed Bool Bool where
  Msg _ := Bool
  eval _ _ _ m := m


-- @@ L49-52 verbatim
def collidingProblem : SM_DT_DSPR_SourceFinalValidity.Problem Unit Seed Bool Bool Bool where
  th := collidingHash
  thColl := collection
  numTargets := 1


-- @@ L54-57 verbatim
def injectiveProblem : SM_DT_DSPR_SourceFinalValidity.Problem Unit Seed Bool Bool Bool where
  th := injectiveHash
  thColl := collection
  numTargets := 1


-- @@ L59-59 verbatim
@[simp] lemma collidingProblem_seedGen : collidingProblem.th.seedGen = pure .only := rfl


-- @@ L61-61 verbatim
@[simp] lemma injectiveProblem_seedGen : injectiveProblem.th.seedGen = pure .only := rfl


-- @@ L63-65 verbatim
abbrev Specs (prob : SM_DT_DSPR_SourceFinalValidity.Problem Unit Seed Bool Bool Bool) :=
  unifSpec + (SM_DT_DSPR_SourceFinalValidity.challengeSpec Bool Bool Bool +
    SourceFinalValidity.collectionSpec prob.thColl)


-- @@ L67-69 verbatim
def challenge (prob : SM_DT_DSPR_SourceFinalValidity.Problem Unit Seed Bool Bool Bool)
    (t m : Bool) : OracleComp (Specs prob) Bool :=
  liftM ((Specs prob).query (.inr (.inl (t, m))))


-- @@ L71-73 verbatim
def collectionQuery (prob : SM_DT_DSPR_SourceFinalValidity.Problem Unit Seed Bool Bool Bool)
    (t : Bool) (m : prob.thColl.Msg ()) : OracleComp (Specs prob) Bool :=
  liftM ((Specs prob).query (.inr (.inr ⟨(), t, m⟩)))


-- @@ L75-79 verbatim
/-- This adversary predicts the collision that always exists for `collidingHash`. -/
def predictCollision : SM_DT_DSPR_SourceFinalValidity.Adversary collidingProblem where
  State := Unit
  choose := challenge collidingProblem false false *> pure ()
  guess _ _ := pure (0, true)


-- @@ L81-85 verbatim
/-- This adversary correctly predicts that the injective target has no second preimage. -/
def predictNoCollision : SM_DT_DSPR_SourceFinalValidity.Adversary injectiveProblem where
  State := Unit
  choose := challenge injectiveProblem false false *> pure ()
  guess _ _ := pure (0, false)


-- @@ L87-93 verbatim
/-- A second target query exceeds the cap but is still answered and recorded. -/
def exceedCap : SM_DT_DSPR_SourceFinalValidity.Adversary collidingProblem where
  State := Bool
  choose := do
    let _ ← challenge collidingProblem false false
    challenge collidingProblem true false
  guess answer _ := pure (if answer then 1 else 0, true)


-- @@ L95-102 verbatim
/-- A challenge/collection tweak clash is answered by both oracles but poisons the game. -/
def clashCollection : SM_DT_DSPR_SourceFinalValidity.Adversary collidingProblem where
  State := Bool × Bool
  choose := do
    let y₁ ← challenge collidingProblem false false
    let y₂ ← collectionQuery collidingProblem false true
    return (y₁, y₂)
  guess _ _ := pure (0, true)


-- @@ L104-108 verbatim
private lemma run_predictCollision :
    (simulateQ (SM_DT_DSPR_SourceFinalValidity.oracles collidingProblem .only)
      predictCollision.choose).run .initial =
      pure ((), ⟨[(false, false)], [], true⟩) := by
  rfl


-- @@ L110-114 verbatim
private lemma run_predictNoCollision :
    (simulateQ (SM_DT_DSPR_SourceFinalValidity.oracles injectiveProblem .only)
      predictNoCollision.choose).run .initial =
      pure ((), ⟨[(false, false)], [], true⟩) := by
  rfl


-- @@ L116-120 verbatim
private lemma run_exceedCap :
    (simulateQ (SM_DT_DSPR_SourceFinalValidity.oracles collidingProblem .only)
      exceedCap.choose).run .initial =
      pure (false, ⟨[(false, false), (true, false)], [], false⟩) := by
  rfl


-- @@ L122-126 verbatim
private lemma run_clashCollection :
    (simulateQ (SM_DT_DSPR_SourceFinalValidity.oracles collidingProblem .only)
      clashCollection.choose).run .initial =
      pure ((false, true), ⟨[(false, false)], [false], false⟩) := by
  rfl


-- @@ L128-132 verbatim
private lemma experiment_predictCollision :
    SM_DT_DSPR_SourceFinalValidity.Experiment predictCollision = pure true := by
  simp only [SM_DT_DSPR_SourceFinalValidity.Experiment, collidingProblem_seedGen, pure_bind]
  rw [run_predictCollision]
  rfl


-- @@ L134-138 verbatim
private lemma baseline_predictCollision :
    SM_DT_DSPR_SourceFinalValidity.SPExperiment predictCollision = pure true := by
  simp only [SM_DT_DSPR_SourceFinalValidity.SPExperiment, collidingProblem_seedGen, pure_bind]
  rw [run_predictCollision]
  rfl


-- @@ L140-144 verbatim
private lemma experiment_predictNoCollision :
    SM_DT_DSPR_SourceFinalValidity.Experiment predictNoCollision = pure true := by
  simp only [SM_DT_DSPR_SourceFinalValidity.Experiment, injectiveProblem_seedGen, pure_bind]
  rw [run_predictNoCollision]
  rfl


-- @@ L146-150 verbatim
private lemma baseline_predictNoCollision :
    SM_DT_DSPR_SourceFinalValidity.SPExperiment predictNoCollision = pure false := by
  simp only [SM_DT_DSPR_SourceFinalValidity.SPExperiment, injectiveProblem_seedGen, pure_bind]
  rw [run_predictNoCollision]
  rfl


-- @@ L152-156 verbatim
private lemma experiment_exceedCap :
    SM_DT_DSPR_SourceFinalValidity.Experiment exceedCap = pure false := by
  simp only [SM_DT_DSPR_SourceFinalValidity.Experiment, collidingProblem_seedGen, pure_bind]
  rw [run_exceedCap]
  rfl


-- @@ L158-162 verbatim
private lemma baseline_exceedCap :
    SM_DT_DSPR_SourceFinalValidity.SPExperiment exceedCap = pure false := by
  simp only [SM_DT_DSPR_SourceFinalValidity.SPExperiment, collidingProblem_seedGen, pure_bind]
  rw [run_exceedCap]
  rfl


-- @@ L164-168 verbatim
private lemma experiment_clashCollection :
    SM_DT_DSPR_SourceFinalValidity.Experiment clashCollection = pure false := by
  simp only [SM_DT_DSPR_SourceFinalValidity.Experiment, collidingProblem_seedGen, pure_bind]
  rw [run_clashCollection]
  rfl


-- @@ L170-174 verbatim
private lemma baseline_clashCollection :
    SM_DT_DSPR_SourceFinalValidity.SPExperiment clashCollection = pure false := by
  simp only [SM_DT_DSPR_SourceFinalValidity.SPExperiment, collidingProblem_seedGen, pure_bind]
  rw [run_clashCollection]
  rfl


-- @@ L176-188 verbatim
/-- Prediction success and `SPprob` differ on the no-second-preimage instance, while both equal one
on the collision instance. This pins the baseline subtraction: the corresponding advantages are
respectively one and zero. -/
theorem baseline_subtraction_canary :
    SM_DT_DSPR_SourceFinalValidity.Experiment predictCollision = pure true ∧
      SM_DT_DSPR_SourceFinalValidity.SPExperiment predictCollision = pure true ∧
      SM_DT_DSPR_SourceFinalValidity.Advantage predictCollision = 0 ∧
      SM_DT_DSPR_SourceFinalValidity.Experiment predictNoCollision = pure true ∧
      SM_DT_DSPR_SourceFinalValidity.SPExperiment predictNoCollision = pure false ∧
      SM_DT_DSPR_SourceFinalValidity.Advantage predictNoCollision = 1 := by
  simp [experiment_predictCollision, baseline_predictCollision, experiment_predictNoCollision,
    baseline_predictNoCollision, SM_DT_DSPR_SourceFinalValidity.Advantage,
    SM_DT_DSPR_SourceFinalValidity.Success, SM_DT_DSPR_SourceFinalValidity.SPProbability]


-- @@ L190-198 verbatim
/-- Invalid queries are not rejected: their concrete answers are visible in the private state, all
queries are recorded, and only the sticky final-validity bit makes both experiments lose. -/
theorem poison_not_rejection_canary :
    SM_DT_DSPR_SourceFinalValidity.Experiment exceedCap = pure false ∧
      SM_DT_DSPR_SourceFinalValidity.SPExperiment exceedCap = pure false ∧
      SM_DT_DSPR_SourceFinalValidity.Experiment clashCollection = pure false ∧
      SM_DT_DSPR_SourceFinalValidity.SPExperiment clashCollection = pure false := by
  exact ⟨experiment_exceedCap, baseline_exceedCap, experiment_clashCollection,
    baseline_clashCollection⟩


-- @@ L200-203 verbatim
/-- The phase types themselves pin seed/oracle access: `choose` gets the oracle bundle but no seed,
whereas `guess` gets the seed but has type `ProbComp` and therefore no challenge oracle. -/
example : OracleComp (Specs collidingProblem) predictCollision.State :=
  predictCollision.choose


-- @@ L205-205 verbatim
example : predictCollision.State → Seed → ProbComp (ℕ × Bool) := predictCollision.guess


-- @@ L207-207 verbatim
end SMDTDSPRFinalValidityTest
