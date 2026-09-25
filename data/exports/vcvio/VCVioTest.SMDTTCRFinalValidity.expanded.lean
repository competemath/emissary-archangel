/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.SMDTTCRFinalValidity


-- @@ L10-17 verbatim
/-!
# Source-final-validity SM-DT-TCR canaries

These concrete games pin the source-final-predicate branch behavior. Both query orders across the
challenge/collection boundary are answered and recorded but poison the final result. Repeated
collection-only tweaks remain legal, while a repeated target tweak is invalid even though its
second digest is returned.
-/


-- @@ L19-19 verbatim
@[expose] public section


-- @@ L21-21 verbatim
open OracleComp OracleSpec


-- @@ L23-23 verbatim
namespace SMDTTCRFinalValidityTest


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


-- @@ L35-37 expanded
def hash : TweakableHash Seed Bool Bool Bool
    where
  seedGen := uniformSample Seed
  eval _ _ _ := false


-- @@ L39-41 verbatim
def collection : TweakableHashCollection Unit Seed Bool Bool where
  Msg _ := Bool
  eval _ _ _ m := m


-- @@ L43-46 verbatim
def problem : TweakableHash.SM_DT_TCR_SourceFinalValidity.Problem Unit Seed Bool Bool Bool where
  th := hash
  thColl := collection
  numTargets := 2


-- @@ L48-48 verbatim
@[simp] lemma problem_seedGen : problem.th.seedGen = pure .only := rfl


-- @@ L50-52 verbatim
abbrev Specs := unifSpec +
  (TweakableHash.SM_DT_TCR_SourceFinalValidity.challengeSpec Bool Bool Bool +
    TweakableHash.SourceFinalValidity.collectionSpec problem.thColl)


-- @@ L54-55 verbatim
def challenge (t m : Bool) : OracleComp Specs Bool :=
  liftM (Specs.query (.inr (.inl (t, m))))


-- @@ L57-58 verbatim
def collectionQuery (t : Bool) (m : problem.thColl.Msg ()) : OracleComp Specs Bool :=
  liftM (Specs.query (.inr (.inr ⟨(), t, m⟩)))


-- @@ L60-63 verbatim
def challengeOnly : TweakableHash.SM_DT_TCR_SourceFinalValidity.Adversary problem where
  State := Unit
  choose := challenge false false *> pure ()
  forge _ _ := pure (0, true)


-- @@ L65-71 verbatim
def challengeThenCollection : TweakableHash.SM_DT_TCR_SourceFinalValidity.Adversary problem where
  State := Bool × Bool
  choose := do
    let y₁ ← challenge false false
    let y₂ ← collectionQuery false true
    return (y₁, y₂)
  forge _ _ := pure (0, true)


-- @@ L73-79 verbatim
def collectionThenChallenge : TweakableHash.SM_DT_TCR_SourceFinalValidity.Adversary problem where
  State := Bool × Bool
  choose := do
    let y₁ ← collectionQuery false true
    let y₂ ← challenge false false
    return (y₁, y₂)
  forge _ _ := pure (0, true)


-- @@ L81-89 verbatim
/-- Repeating a collection tweak is permitted; the subsequent fresh challenge remains valid. -/
def repeatedCollection : TweakableHash.SM_DT_TCR_SourceFinalValidity.Adversary problem where
  State := Bool × Bool
  choose := do
    let y₁ ← collectionQuery false false
    let y₂ ← collectionQuery false true
    let _ ← challenge true false
    return (y₁, y₂)
  forge _ _ := pure (0, true)


-- @@ L91-98 verbatim
/-- A repeated target tweak is answered and recorded, then final validity rejects the forgery. -/
def repeatedTarget : TweakableHash.SM_DT_TCR_SourceFinalValidity.Adversary problem where
  State := Bool × Bool
  choose := do
    let y₁ ← challenge false false
    let y₂ ← challenge false true
    return (y₁, y₂)
  forge _ _ := pure (0, true)


-- @@ L100-108 verbatim
/-- A collection query after target duplication still returns its digest and is appended. -/
def poisonThenCollection : TweakableHash.SM_DT_TCR_SourceFinalValidity.Adversary problem where
  State := Bool × Bool × Bool
  choose := do
    let y₁ ← challenge false false
    let y₂ ← challenge false true
    let y₃ ← collectionQuery true true
    return (y₁, y₂, y₃)
  forge _ _ := pure (0, true)


-- @@ L110-114 verbatim
private lemma run_challengeOnly :
    (simulateQ (TweakableHash.SM_DT_TCR_SourceFinalValidity.oracles problem .only)
      challengeOnly.choose).run .initial =
      pure ((), ⟨[(false, false)], [], true⟩) := by
  rfl


-- @@ L116-120 verbatim
private lemma run_challengeThenCollection :
    (simulateQ (TweakableHash.SM_DT_TCR_SourceFinalValidity.oracles problem .only)
      challengeThenCollection.choose).run .initial =
      pure ((false, true), ⟨[(false, false)], [false], false⟩) := by
  rfl


-- @@ L122-126 verbatim
private lemma run_collectionThenChallenge :
    (simulateQ (TweakableHash.SM_DT_TCR_SourceFinalValidity.oracles problem .only)
      collectionThenChallenge.choose).run .initial =
      pure ((true, false), ⟨[(false, false)], [false], false⟩) := by
  rfl


-- @@ L128-132 verbatim
private lemma run_repeatedCollection :
    (simulateQ (TweakableHash.SM_DT_TCR_SourceFinalValidity.oracles problem .only)
      repeatedCollection.choose).run .initial =
      pure ((false, true), ⟨[(true, false)], [false, false], true⟩) := by
  rfl


-- @@ L134-138 verbatim
private lemma run_repeatedTarget :
    (simulateQ (TweakableHash.SM_DT_TCR_SourceFinalValidity.oracles problem .only)
      repeatedTarget.choose).run .initial =
      pure ((false, false), ⟨[(false, false), (false, true)], [], false⟩) := by
  rfl


-- @@ L140-147 verbatim
/-- Once poisoned, the monitor remains always-answering: the later collection digest and its tweak
are both observable, while validity remains false. -/
theorem poison_then_collection_history_canary :
    (simulateQ (TweakableHash.SM_DT_TCR_SourceFinalValidity.oracles problem .only)
      poisonThenCollection.choose).run .initial =
      pure ((false, false, true),
        ⟨[(false, false), (false, true)], [true], false⟩) := by
  rfl


-- @@ L149-153 verbatim
private lemma experiment_challengeOnly :
    TweakableHash.SM_DT_TCR_SourceFinalValidity.Experiment challengeOnly = pure true := by
  simp only [TweakableHash.SM_DT_TCR_SourceFinalValidity.Experiment, problem_seedGen, pure_bind]
  rw [run_challengeOnly]
  rfl


-- @@ L155-160 verbatim
private lemma experiment_challengeThenCollection :
    TweakableHash.SM_DT_TCR_SourceFinalValidity.Experiment challengeThenCollection =
      pure false := by
  simp only [TweakableHash.SM_DT_TCR_SourceFinalValidity.Experiment, problem_seedGen, pure_bind]
  rw [run_challengeThenCollection]
  rfl


-- @@ L162-167 verbatim
private lemma experiment_collectionThenChallenge :
    TweakableHash.SM_DT_TCR_SourceFinalValidity.Experiment collectionThenChallenge =
      pure false := by
  simp only [TweakableHash.SM_DT_TCR_SourceFinalValidity.Experiment, problem_seedGen, pure_bind]
  rw [run_collectionThenChallenge]
  rfl


-- @@ L169-173 verbatim
private lemma experiment_repeatedCollection :
    TweakableHash.SM_DT_TCR_SourceFinalValidity.Experiment repeatedCollection = pure true := by
  simp only [TweakableHash.SM_DT_TCR_SourceFinalValidity.Experiment, problem_seedGen, pure_bind]
  rw [run_repeatedCollection]
  rfl


-- @@ L175-179 verbatim
private lemma experiment_repeatedTarget :
    TweakableHash.SM_DT_TCR_SourceFinalValidity.Experiment repeatedTarget = pure false := by
  simp only [TweakableHash.SM_DT_TCR_SourceFinalValidity.Experiment, problem_seedGen, pure_bind]
  rw [run_repeatedTarget]
  rfl


-- @@ L181-192 verbatim
/-- Both clash orders and a repeated target lose through final validity, while the legal control
cases win. The run equalities also pin that invalid queries still return their real answers. -/
theorem final_validity_branch_canary :
    TweakableHash.SM_DT_TCR_SourceFinalValidity.Experiment challengeOnly = pure true ∧
      TweakableHash.SM_DT_TCR_SourceFinalValidity.Experiment challengeThenCollection =
        pure false ∧
      TweakableHash.SM_DT_TCR_SourceFinalValidity.Experiment collectionThenChallenge =
        pure false ∧
      TweakableHash.SM_DT_TCR_SourceFinalValidity.Experiment repeatedCollection = pure true ∧
      TweakableHash.SM_DT_TCR_SourceFinalValidity.Experiment repeatedTarget = pure false :=
  ⟨experiment_challengeOnly, experiment_challengeThenCollection,
    experiment_collectionThenChallenge, experiment_repeatedCollection, experiment_repeatedTarget⟩


-- @@ L194-194 verbatim
end SMDTTCRFinalValidityTest
