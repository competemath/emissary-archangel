/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.Collection


-- @@ L10-23 verbatim
/-!
# Source-final-validity monitoring for multi-target tweakable-hash games

The source-final-validity games answer and record every target and collection query, then require
at the end that the target cap, distinct-target-tweak condition, and target/collection disjointness
all hold. This file packages an equivalent sticky poison-bit monitor: every query remains answered
and recorded, while the first validity violation changes `State.valid` permanently to `false`.

The monitor is intentionally separate from `TweakableHash.collectionOracle`, whose
rejection-on-arrival semantics define a different adaptive experiment.
`TweakableHash.ToFinalValidity` relates the two, one conversion per game: each sends a
rejection-on-arrival adversary to an adversary for the corresponding monitor game at exactly the
same advantage, so a bound proved against either presentation is usable against the other.
-/


-- @@ L25-25 verbatim
@[expose] public section


-- @@ L27-27 verbatim
namespace TweakableHash.SourceFinalValidity


-- @@ L29-29 verbatim
open OracleComp OracleSpec


-- @@ L31-31 verbatim
variable {ι PkSeed Tweak Y Q : Type}


-- @@ L33-40 verbatim
/-- Histories and sticky validity bit shared by a target oracle and a collection oracle. -/
structure State (Q Tweak : Type) where
  /-- Every target query, including queries issued after the game became invalid. -/
  challenges : List Q
  /-- Every collection tweak, including queries issued after the game became invalid. -/
  collectionTweaks : List Tweak
  /-- Sticky validity bit for the target cap and tweak-separation conditions. -/
  valid : Bool


-- @@ L42-43 verbatim
/-- The initially valid empty source-final-validity state. -/
def State.initial : State Q Tweak := ⟨[], [], true⟩


-- @@ L45-50 verbatim
/-- The final predicate: no more than `numTargets` targets, pairwise-distinct target tweaks, and no
target tweak used by the collection oracle. -/
def Valid (numTargets : ℕ) (tweakOf : Q → Tweak) (st : State Q Tweak) : Prop :=
  st.challenges.length ≤ numTargets ∧
    (st.challenges.map tweakOf).Nodup ∧
    (st.challenges.map tweakOf).Disjoint st.collectionTweaks


-- @@ L52-58 verbatim
instance [DecidableEq Tweak] (numTargets : ℕ) (tweakOf : Q → Tweak) (st : State Q Tweak) :
    Decidable (Valid numTargets tweakOf st) :=
  decidable_of_iff
    (st.challenges.length ≤ numTargets ∧
      (st.challenges.map tweakOf).Nodup ∧
      ∀ a ∈ st.challenges.map tweakOf, ∀ b ∈ st.collectionTweaks, a ≠ b)
    (and_congr Iff.rfl (and_congr Iff.rfl List.disjoint_iff_ne.symm))


-- @@ L60-66 verbatim
/-- Executable form of `Valid`. The disjointness conjunct is expanded elementwise so the decision
procedure is explicit. -/
def validBool [DecidableEq Tweak] (numTargets : ℕ) (tweakOf : Q → Tweak)
    (st : State Q Tweak) : Bool :=
  decide (st.challenges.length ≤ numTargets) &&
    decide (st.challenges.map tweakOf).Nodup &&
    decide (∀ a ∈ st.challenges.map tweakOf, ∀ b ∈ st.collectionTweaks, a ≠ b)


-- @@ L68-72 verbatim
/-- The monitor invariant: the sticky bit is exactly the decision procedure for the final
predicate, rather than merely a one-way soundness flag. -/
def Invariant [DecidableEq Tweak] (numTargets : ℕ) (tweakOf : Q → Tweak)
    (st : State Q Tweak) : Prop :=
  st.valid = validBool numTargets tweakOf st


-- @@ L74-81 verbatim
/-- Record a target query and poison the state if the target cap or tweak discipline is violated.
The query is always recorded; hashing and returning its answer is the caller's responsibility. -/
def State.recordTarget [DecidableEq Tweak] (numTargets : ℕ) (tweakOf : Q → Tweak)
    (st : State Q Tweak) (q : Q) : State Q Tweak where
  challenges := st.challenges ++ [q]
  collectionTweaks := st.collectionTweaks
  valid := st.valid && st.challenges.length < numTargets &&
    decide (TweakFresh tweakOf st.challenges st.collectionTweaks (tweakOf q))


-- @@ L83-89 verbatim
/-- Record a collection tweak and poison the state if it was already reserved by a target query.
Repeated collection tweaks are valid and remain recorded. -/
def State.recordCollection [DecidableEq Tweak] (tweakOf : Q → Tweak)
    (st : State Q Tweak) (t : Tweak) : State Q Tweak where
  challenges := st.challenges
  collectionTweaks := st.collectionTweaks ++ [t]
  valid := st.valid && decide (¬TweakReserved tweakOf st.challenges t)


-- @@ L91-91 verbatim
/-! ## Correspondence to the final predicate -/


-- @@ L93-93 verbatim
section Correspondence


-- @@ L95-95 verbatim
variable [DecidableEq Tweak]


-- @@ L97-101 verbatim
/-- The executable check recognizes exactly the final predicate. -/
theorem validBool_eq_true_iff (numTargets : ℕ) (tweakOf : Q → Tweak) (st : State Q Tweak) :
    validBool numTargets tweakOf st = true ↔ Valid numTargets tweakOf st := by
  simp [validBool, Valid, List.disjoint_iff_ne]
  tauto


-- @@ L103-109 verbatim
/-- The invariant has the literal `decide (Valid …)` form. -/
theorem Invariant.eq_decide (numTargets : ℕ) (tweakOf : Q → Tweak) (st : State Q Tweak)
    (hinv : Invariant numTargets tweakOf st) :
    st.valid = decide (Valid numTargets tweakOf st) := by
  rw [hinv]
  apply Bool.eq_iff_iff.mpr
  simp [validBool_eq_true_iff]


-- @@ L111-114 verbatim
/-- The initial monitor satisfies the exact final predicate. -/
theorem invariant_initial (numTargets : ℕ) (tweakOf : Q → Tweak) :
    Invariant numTargets tweakOf (.initial : State Q Tweak) := by
  simp [Invariant, State.initial, validBool]


-- @@ L116-149 verbatim
/-- Recording a target query preserves exact correspondence between the poison bit and the final
predicate. -/
theorem Invariant.recordTarget (numTargets : ℕ) (tweakOf : Q → Tweak) (st : State Q Tweak)
    (q : Q) (hinv : Invariant numTargets tweakOf st) :
    Invariant numTargets tweakOf (st.recordTarget numTargets tweakOf q) := by
  rcases st with ⟨challenges, collectionTweaks, valid⟩
  simp only [Invariant, State.recordTarget] at hinv ⊢
  rw [hinv]
  apply Bool.eq_iff_iff.mpr
  have hcore :
      ((((challenges.length ≤ numTargets ∧ (challenges.map tweakOf).Nodup) ∧
          ∀ a ∈ challenges, ∀ b ∈ collectionTweaks, tweakOf a ≠ b) ∧
          challenges.length < numTargets) ∧
        (∀ x ∈ challenges, tweakOf x ≠ tweakOf q) ∧
          tweakOf q ∉ collectionTweaks) ↔
        ((challenges.length < numTargets ∧ (challenges.map tweakOf).Nodup ∧
            ∀ x ∈ challenges, tweakOf x ≠ tweakOf q) ∧
          ∀ a : Tweak, (∃ x ∈ challenges, tweakOf x = a) ∨ a = tweakOf q →
            ∀ b ∈ collectionTweaks, a ≠ b) := by
    constructor
    · rintro ⟨⟨⟨⟨hlen, hnodup⟩, hdisjoint⟩, hlt⟩, hfresh, hnotColl⟩
      refine ⟨⟨hlt, hnodup, hfresh⟩, ?_⟩
      intro a ha b hb
      rcases ha with ⟨x, hx, rfl⟩ | rfl
      · exact hdisjoint x hx b hb
      · intro heq
        exact hnotColl (heq ▸ hb)
    · rintro ⟨⟨hlt, hnodup, hfresh⟩, hdisjoint⟩
      refine ⟨⟨⟨⟨Nat.le_of_lt hlt, hnodup⟩, ?_⟩, hlt⟩, hfresh, ?_⟩
      · intro x hx b hb
        exact hdisjoint (tweakOf x) (Or.inl ⟨x, hx, rfl⟩) b hb
      · intro hmem
        exact hdisjoint (tweakOf q) (Or.inr rfl) (tweakOf q) hmem rfl
  simpa [validBool, TweakFresh, TweakReserved, List.nodup_append] using hcore


-- @@ L151-180 verbatim
/-- Recording a collection query preserves exact correspondence between the poison bit and the
final predicate. -/
theorem Invariant.recordCollection (numTargets : ℕ) (tweakOf : Q → Tweak) (st : State Q Tweak)
    (t : Tweak) (hinv : Invariant numTargets tweakOf st) :
    Invariant numTargets tweakOf (st.recordCollection tweakOf t) := by
  rcases st with ⟨challenges, collectionTweaks, valid⟩
  simp only [Invariant, State.recordCollection] at hinv ⊢
  rw [hinv]
  apply Bool.eq_iff_iff.mpr
  have hcore :
      (((challenges.length ≤ numTargets ∧ (challenges.map tweakOf).Nodup) ∧
          ∀ a ∈ challenges, ∀ b ∈ collectionTweaks, tweakOf a ≠ b) ∧
        ∀ x ∈ challenges, tweakOf x ≠ t) ↔
        ((challenges.length ≤ numTargets ∧ (challenges.map tweakOf).Nodup) ∧
          ∀ a ∈ challenges, ∀ b : Tweak, (b ∈ collectionTweaks ∨ b = t) →
            tweakOf a ≠ b) := by
    constructor
    · rintro ⟨⟨⟨hlen, hnodup⟩, hdisjoint⟩, hunreserved⟩
      refine ⟨⟨hlen, hnodup⟩, ?_⟩
      intro x hx b hb
      rcases hb with hb | rfl
      · exact hdisjoint x hx b hb
      · exact hunreserved x hx
    · rintro ⟨⟨hlen, hnodup⟩, hdisjoint⟩
      refine ⟨⟨⟨hlen, hnodup⟩, ?_⟩, ?_⟩
      · intro x hx b hb
        exact hdisjoint x hx b (Or.inl hb)
      · intro x hx
        exact hdisjoint x hx t (Or.inr rfl)
  simpa [validBool, TweakReserved] using hcore


-- @@ L182-182 verbatim
end Correspondence


-- @@ L184-188 expanded
/-- Source-final-validity collection queries return a digest directly: invalid queries poison the
monitor but are never rejected. -/
abbrev collectionSpec (thColl : TweakableHashCollection ι PkSeed Tweak Y) :
    OracleSpec ((i : ι) × Tweak × thColl.Msg i) :=
  OracleSpec.ofFn (ι := _) (fun _ => Y)


-- @@ L190-197 verbatim
/-- The always-answering collection oracle for source-final-validity games. -/
def collectionOracle [DecidableEq Tweak] (tweakOf : Q → Tweak)
    (thColl : TweakableHashCollection ι PkSeed Tweak Y) (pk : PkSeed) :
    QueryImpl (collectionSpec thColl) (StateT (State Q Tweak) ProbComp) :=
  fun q => do
    let st ← get
    set (st.recordCollection tweakOf q.2.1)
    return thColl.eval q.1 pk q.2.1 q.2.2


-- @@ L199-206 verbatim
/-- Every collection query returns its real digest and is appended to the history, even when the
incoming state is already poisoned. -/
theorem collectionOracle_run [DecidableEq Tweak] (tweakOf : Q → Tweak)
    (thColl : TweakableHashCollection ι PkSeed Tweak Y) (pk : PkSeed)
    (q : (i : ι) × Tweak × thColl.Msg i) (st : State Q Tweak) :
    (collectionOracle tweakOf thColl pk q).run st =
      pure (thColl.eval q.1 pk q.2.1 q.2.2, st.recordCollection tweakOf q.2.1) := by
  simp [collectionOracle]


-- @@ L208-208 verbatim
/-! ## Semantic pins -/


-- @@ L210-211 verbatim
variable [DecidableEq Tweak] (tweakOf : Q → Tweak)
  {st : State Q Tweak} {q : Q} {t : Tweak}


-- @@ L213-217 verbatim
/-- Target queries are still recorded after violating the cap; the validity bit is poisoned. -/
theorem recordTarget_at_cap :
    (st.recordTarget 0 tweakOf q).challenges = st.challenges ++ [q] ∧
      (st.recordTarget 0 tweakOf q).valid = false := by
  simp [State.recordTarget]


-- @@ L219-224 verbatim
/-- Repeating a collection tweak does not poison an otherwise valid state when no target reserved
it. This fails if collection tweaks are incorrectly required to be distinct. -/
theorem recordCollection_repeated_of_unreserved (hvalid : st.valid = true)
    (hunreserved : ¬TweakReserved tweakOf st.challenges t) :
    ((st.recordCollection tweakOf t).recordCollection tweakOf t).valid = true := by
  simp [State.recordCollection, hvalid, hunreserved]


-- @@ L226-226 verbatim
end TweakableHash.SourceFinalValidity
