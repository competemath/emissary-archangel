/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module

public import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.SMDTPRE


-- @@ L11-26 verbatim
/-!
# End-to-end canaries for SM-DT-PRE

The pins in `HardnessAssumptions/TweakableHash/SMDTPRE.lean` stop at the challenge oracle's `run`;
these run the whole game, winning condition included. Between them they exercise the three parts of
`SM_DT_PRE_Experiment` no oracle pin reaches: that an accepted query's sampled message is recorded
where the winning condition looks for it, that the index lookup resolves against the challenge
history, and that a rejected query leaves nothing to invert.

The challenge oracle draws its own message, so the subspace is a one-element type whose
`SampleableType` instance is written out rather than inferred. That makes the draw reduce, and the
transcripts below are then equations between `pure`s rather than statements about `support`.

Because the target cap is one, append order is unobservable here; `SMDTTCR.lean` carries the order
canaries for the SM-TCR side, whose challenge history is built by the same `TweakFresh` discipline.
-/


-- @@ L28-28 verbatim
@[expose] public section


-- @@ L30-30 verbatim
open OracleComp OracleSpec TweakableHash


-- @@ L32-32 verbatim
namespace SMDTPRETest


-- @@ L34-34 verbatim
/-! ## A collapsing tweakable hash on a one-element subspace -/


-- @@ L36-37 verbatim
inductive Seed
  | only


-- @@ L39-41 verbatim
inductive Digest
  | zero
  deriving DecidableEq


-- @@ L43-46 verbatim
instance : SampleableType Seed where
  selectElem := pure .only
  mem_support_selectElem := by simp
  probOutput_selectElem_eq x y := by cases x; cases y; rfl


-- @@ L48-51 verbatim
instance : SampleableType Digest where
  selectElem := pure .zero
  mem_support_selectElem := by simp
  probOutput_selectElem_eq x y := by cases x; cases y; rfl


-- @@ L53-53 expanded
@[simp]
lemma uniformSample_seed : (uniformSample Seed : ProbComp Seed) = pure .only :=
  rfl


-- @@ L55-55 expanded
@[simp]
lemma uniformSample_digest : (uniformSample Digest : ProbComp Digest) = pure .zero :=
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


-- @@ L65-70 verbatim
def problem : SM_DT_PRE_Problem Unit Seed Bool Bool Digest Bool where
  th := hash
  emb _ := false
  emb_injective := fun a b _ => by cases a; cases b; rfl
  thColl := collection
  numTargets := 1


-- @@ L72-72 verbatim
@[simp] lemma problem_seedGen : problem.th.seedGen = pure .only := rfl


-- @@ L74-74 verbatim
/-! ## Queries -/


-- @@ L76-76 verbatim
abbrev Specs := unifSpec + (SM_DT_PRE_challengeSpec Bool Bool + collectionSpec problem.thColl)


-- @@ L78-80 verbatim
/-- Query the challenge oracle at `tweak`; the oracle picks the message. -/
def challenge (tweak : Bool) : OracleComp Specs (Option Bool) :=
  liftM (Specs.query (.inr (.inl tweak)))


-- @@ L82-85 verbatim
/-- Query the collection oracle on its sole member at `(tweak, message)`. -/
def collectionQuery (tweak : Bool) (message : problem.thColl.Msg ()) :
    OracleComp Specs (Option Bool) :=
  liftM (Specs.query (.inr (.inr ⟨(), tweak, message⟩)))


-- @@ L87-87 verbatim
/-! ## Adversaries -/


-- @@ L89-95 verbatim
/-- Place one target, then invert it. -/
def challengeOnly : SM_DT_PRE_Adversary problem where
  State := Unit
  choose := do
    let _ ← challenge true
    return ()
  invert _ _ := pure (0, .zero)


-- @@ L97-104 verbatim
/-- Spend the tweak on the collection oracle before challenging at it. -/
def collectionThenChallenge : SM_DT_PRE_Adversary problem where
  State := Unit
  choose := do
    let _ ← collectionQuery true false
    let _ ← challenge true
    return ()
  invert _ _ := pure (0, .zero)


-- @@ L106-106 verbatim
/-! ## Transcripts -/


-- @@ L108-111 verbatim
private lemma run_challengeOnly :
    (simulateQ (SM_DT_PRE_oracles problem .only) challengeOnly.choose).run ([], []) =
      pure ((), ([(true, Digest.zero)], [])) := by
  rfl


-- @@ L113-116 verbatim
private lemma run_collectionThenChallenge :
    (simulateQ (SM_DT_PRE_oracles problem .only) collectionThenChallenge.choose).run ([], []) =
      pure ((), ([], [true])) := by
  rfl


-- @@ L118-118 verbatim
/-! ## Verdicts -/


-- @@ L120-124 verbatim
/-- A target placed through the challenge oracle and inverted at its own index wins. -/
theorem win_challengeOnly : SM_DT_PRE_Experiment challengeOnly = pure true := by
  simp only [SM_DT_PRE_Experiment, problem_seedGen, pure_bind]
  rw [run_challengeOnly]
  simp [challengeOnly]


-- @@ L126-132 verbatim
/-- Reaching a tweak through the collection oracle first makes the later challenge query at that
tweak be rejected, so nothing is drawn and index `0` is out of range. -/
theorem lose_collectionThenChallenge :
    SM_DT_PRE_Experiment collectionThenChallenge = pure false := by
  simp only [SM_DT_PRE_Experiment, problem_seedGen, pure_bind]
  rw [run_collectionThenChallenge]
  simp [collectionThenChallenge]


-- @@ L134-134 verbatim
end SMDTPRETest
