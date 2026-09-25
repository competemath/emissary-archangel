/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Matthias Meijers
-/

module

public import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.SMDTTCR


-- @@ L11-34 verbatim
/-!
# End-to-end canaries for SM-DT-TCR and the collection oracle

The pins in `HardnessAssumptions/TweakableHash/` stop at an oracle's `run`; these run the whole
game, winning condition included, on a collapsing tweakable hash where every pair of messages
collides. What is being measured is therefore the bookkeeping, not the hash: which queries the
oracles accept, in what order the challenge history records them, and which index the winning
condition then reads.

`oracle_separation_canary` checks both directions of the security-critical tweak-separation rule. A
collection query at an existing challenge tweak must return `none`; the adversary branches on that
rejection, so forgetting the check turns its toy collision into a loss. In the other order, a
challenge query at a tweak already spent on the collection oracle is rejected and leaves no target
to forge against.

The remaining canaries are chosen so that each one is the sole canary whose verdict changes under
one specific weakening of the oracles: prepending rather than appending an accepted target, dropping
the target cap, dropping the challenge-history tweak check, and reading an index the challenge
history does not have. A canary that merely restates an oracle pin would not separate those.

`win_coin` pins that the target-selection phase can sample. A reduction that simulates a signer
needs coins before the seed is revealed, so `SM_DT_TCR_Adversary.choose` runs against a `unifSpec`
summand; this canary stops elaborating if that summand goes away.
-/


-- @@ L36-36 verbatim
@[expose] public section


-- @@ L38-38 verbatim
open OracleComp OracleSpec TweakableHash


-- @@ L40-40 verbatim
namespace SMDTTCRTest


-- @@ L42-45 verbatim
/-! ## A collapsing tweakable hash

A one-element seed type keeps `seedGen` deterministic, and a constant `eval` makes every message a
collision, so a canary that loses can only be losing on the tweak discipline or the index lookup. -/


-- @@ L47-48 verbatim
inductive Seed
  | only


-- @@ L50-53 verbatim
instance : SampleableType Seed where
  selectElem := pure .only
  mem_support_selectElem := by simp
  probOutput_selectElem_eq x y := by cases x; cases y; rfl


-- @@ L55-55 expanded
@[simp]
lemma uniformSample_seed : (uniformSample Seed : ProbComp Seed) = pure .only :=
  rfl


-- @@ L57-59 expanded
def hash : TweakableHash Seed Bool Bool Bool
    where
  seedGen := uniformSample Seed
  eval _ _ _ := false


-- @@ L61-63 verbatim
def collection : TweakableHashCollection Unit Seed Bool Bool where
  Msg _ := Bool
  eval _ _ _ _ := false


-- @@ L65-68 verbatim
def problem : SM_DT_TCR_Problem Unit Seed Bool Bool Bool where
  th := hash
  thColl := collection
  numTargets := 1


-- @@ L70-72 verbatim
/-- The same problem at a cap of two, for the canaries that need a second accepted target. -/
def problemTwo : SM_DT_TCR_Problem Unit Seed Bool Bool Bool :=
  { problem with numTargets := 2 }


-- @@ L74-74 verbatim
@[simp] lemma problem_seedGen : problem.th.seedGen = pure .only := rfl


-- @@ L76-77 verbatim
@[simp] lemma problem_eval (pk : Seed) (tweak message : Bool) :
    problem.th.eval pk tweak message = false := rfl


-- @@ L79-79 verbatim
@[simp] lemma problemTwo_th : problemTwo.th = problem.th := rfl


-- @@ L81-84 verbatim
/-! ## Queries

The two caps share one collection, so a single spec abbreviation serves adversaries against either
problem. -/


-- @@ L86-86 verbatim
abbrev Specs := unifSpec + (SM_DT_TCR_challengeSpec Bool Bool Bool + collectionSpec problem.thColl)


-- @@ L88-90 verbatim
/-- Query the challenge oracle on `(tweak, message)`. -/
def challenge (tweak message : Bool) : OracleComp Specs (Option Bool) :=
  liftM (Specs.query (.inr (.inl (tweak, message))))


-- @@ L92-95 verbatim
/-- Query the collection oracle on its sole member at `(tweak, message)`. -/
def collectionQuery (tweak : Bool) (message : problem.thColl.Msg ()) :
    OracleComp Specs (Option Bool) :=
  liftM (Specs.query (.inr (.inr ⟨(), tweak, message⟩)))


-- @@ L97-98 verbatim
/-- Draw a private coin, without the public seed. -/
def coin : OracleComp Specs (Fin 2) := liftM (Specs.query (.inl 1))


-- @@ L100-100 verbatim
/-! ## Adversaries -/


-- @@ L102-108 verbatim
/-- Place one target, then collide with it. -/
def challengeOnly : SM_DT_TCR_Adversary problem where
  State := Unit
  choose := do
    let _ ← challenge false false
    return ()
  forge _ _ := pure (0, true)


-- @@ L110-120 verbatim
/-- Challenge first, then touch the same tweak through the collection oracle, carrying that
oracle's answer into the second phase. Forging `true` collides and `false` does not, so the game's
verdict reports whether the collection query was rejected. -/
def challengeThenCollection : SM_DT_TCR_Adversary problem where
  State := Option Bool
  choose := do
    let _ ← challenge false false
    collectionQuery false false
  forge answer _ := match answer with
    | none => pure (0, true)
    | some _ => pure (0, false)


-- @@ L122-129 verbatim
/-- Spend the tweak on the collection oracle before challenging at it. -/
def collectionThenChallenge : SM_DT_TCR_Adversary problem where
  State := Unit
  choose := do
    let _ ← collectionQuery false false
    let _ ← challenge false false
    return ()
  forge _ _ := pure (0, true)


-- @@ L131-138 verbatim
/-- Two challenge queries at distinct tweaks against a cap of one, forging at the second. -/
def overCap : SM_DT_TCR_Adversary problem where
  State := Unit
  choose := do
    let _ ← challenge true false
    let _ ← challenge false false
    return ()
  forge _ _ := pure (1, true)


-- @@ L140-148 verbatim
/-- Two challenge queries at the *same* tweak with different messages, below the cap, forging
against the second. -/
def reusedTweak : SM_DT_TCR_Adversary problemTwo where
  State := Unit
  choose := do
    let _ ← challenge true false
    let _ ← challenge true true
    return ()
  forge _ _ := pure (1, false)


-- @@ L150-159 verbatim
/-- Two targets whose messages differ, forging the second one's own message at index `1`. Colliding
with a message requires differing from it, so this loses exactly when index `1` holds the *second*
target. -/
def order : SM_DT_TCR_Adversary problemTwo where
  State := Unit
  choose := do
    let _ ← challenge true false
    let _ ← challenge false true
    return ()
  forge _ _ := pure (1, true)


-- @@ L161-167 verbatim
/-- Place one target and forge against an index the challenge history does not have. -/
def outOfRange : SM_DT_TCR_Adversary problem where
  State := Unit
  choose := do
    let _ ← challenge true false
    return ()
  forge _ _ := pure (5, true)


-- @@ L169-176 verbatim
/-- Flip a coin during target selection, carry it into the second phase, and collide. -/
def coinFlip : SM_DT_TCR_Adversary problem where
  State := Fin 2
  choose := do
    let b ← coin
    let _ ← challenge true false
    return b
  forge _ _ := pure (0, true)


-- @@ L178-180 verbatim
/-! ## Transcripts

One equation per adversary, fixing both the answers it receives and the histories it leaves. -/


-- @@ L182-185 verbatim
private lemma run_challengeOnly :
    (simulateQ (SM_DT_TCR_oracles problem .only) challengeOnly.choose).run ([], []) =
      pure ((), ([(false, false)], [])) := by
  rfl


-- @@ L187-190 verbatim
private lemma run_challengeThenCollection :
    (simulateQ (SM_DT_TCR_oracles problem .only) challengeThenCollection.choose).run ([], []) =
      pure (none, ([(false, false)], [])) := by
  rfl


-- @@ L192-195 verbatim
private lemma run_collectionThenChallenge :
    (simulateQ (SM_DT_TCR_oracles problem .only) collectionThenChallenge.choose).run ([], []) =
      pure ((), ([], [false])) := by
  rfl


-- @@ L197-200 verbatim
private lemma run_overCap :
    (simulateQ (SM_DT_TCR_oracles problem .only) overCap.choose).run ([], []) =
      pure ((), ([(true, false)], [])) := by
  rfl


-- @@ L202-205 verbatim
private lemma run_reusedTweak :
    (simulateQ (SM_DT_TCR_oracles problemTwo .only) reusedTweak.choose).run ([], []) =
      pure ((), ([(true, false)], [])) := by
  rfl


-- @@ L207-210 verbatim
private lemma run_order :
    (simulateQ (SM_DT_TCR_oracles problemTwo .only) order.choose).run ([], []) =
      pure ((), ([(true, false), (false, true)], [])) := by
  rfl


-- @@ L212-215 verbatim
private lemma run_outOfRange :
    (simulateQ (SM_DT_TCR_oracles problem .only) outOfRange.choose).run ([], []) =
      pure ((), ([(true, false)], [])) := by
  rfl


-- @@ L217-221 verbatim
private lemma run_coinFlip :
    (simulateQ (SM_DT_TCR_oracles problem .only) coinFlip.choose).run ([], []) =
      (do let b ← (liftM (unifSpec.query 1) : ProbComp (Fin 2));
          pure (b, ([(true, false)], []))) := by
  rfl


-- @@ L223-223 verbatim
/-! ## Verdicts -/


-- @@ L225-239 verbatim
/-- Both query orders enforce challenge/collection tweak separation. -/
theorem oracle_separation_canary :
    SM_DT_TCR_Experiment challengeOnly = pure true ∧
      SM_DT_TCR_Experiment challengeThenCollection = pure true ∧
      SM_DT_TCR_Experiment collectionThenChallenge = pure false := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [SM_DT_TCR_Experiment, problem_seedGen, pure_bind]
    rw [run_challengeOnly]
    simp [challengeOnly, problem_eval]
  · simp only [SM_DT_TCR_Experiment, problem_seedGen, pure_bind]
    rw [run_challengeThenCollection]
    simp [challengeThenCollection, problem_eval]
  · simp only [SM_DT_TCR_Experiment, problem_seedGen, pure_bind]
    rw [run_collectionThenChallenge]
    rfl


-- @@ L241-245 verbatim
/-- A challenge query past the target cap is rejected, so the second target never exists. -/
theorem lose_overCap : SM_DT_TCR_Experiment overCap = pure false := by
  simp only [SM_DT_TCR_Experiment, problem_seedGen, pure_bind]
  rw [run_overCap]
  simp [overCap, problem_eval]


-- @@ L247-252 verbatim
/-- A second challenge query at a tweak already in the challenge history is rejected even below the
cap, so no second target exists to forge against. -/
theorem lose_reusedTweak : SM_DT_TCR_Experiment reusedTweak = pure false := by
  simp only [SM_DT_TCR_Experiment, problemTwo_th, problem_seedGen, pure_bind]
  rw [run_reusedTweak]
  simp [reusedTweak, problem_eval]


-- @@ L254-259 verbatim
/-- Accepted targets are appended, so index `1` holds the second one and forging its own message
fails to differ from it. -/
theorem lose_order : SM_DT_TCR_Experiment order = pure false := by
  simp only [SM_DT_TCR_Experiment, problemTwo_th, problem_seedGen, pure_bind]
  rw [run_order]
  simp [order, problem_eval]


-- @@ L261-265 verbatim
/-- An index outside the challenge history loses. -/
theorem lose_outOfRange : SM_DT_TCR_Experiment outOfRange = pure false := by
  simp only [SM_DT_TCR_Experiment, problem_seedGen, pure_bind]
  rw [run_outOfRange]
  simp [outOfRange, problem_eval]


-- @@ L267-274 verbatim
/-- The coin drawn during target selection is threaded through to the result, and the collision
wins on either draw. -/
theorem win_coin :
    SM_DT_TCR_Experiment coinFlip =
      (liftM (unifSpec.query 1) : ProbComp (Fin 2)) >>= fun _ => pure true := by
  simp only [SM_DT_TCR_Experiment, problem_seedGen, pure_bind]
  rw [run_coinFlip]
  simp [coinFlip, problem_eval]


-- @@ L276-276 verbatim
end SMDTTCRTest
