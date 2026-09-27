/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
module

public import LeanPool.FormalLearningTheory.Data
public import LeanPool.FormalLearningTheory.Learner.Core


-- @@ L11-21 verbatim
/-!
# Gold-Style Success Criteria (Identification in the Limit)

Seven success criteria for Gold-style learning: EX, BC, Finite,
Vacillatory, Anomalous, Monotonic, TrialAndError.

All share the quantifier pattern:
  ∃ L, ∀ c ∈ C, ∀ T (text/informant for c), ∃ t₀, ∀ t ≥ t₀, ...

The variation is in what "..." requires.
-/


-- @@ L23-23 verbatim
@[expose] public section


-- @@ L25-25 verbatim
universe u v


-- @@ L27-29 verbatim
/-- Helper: the data seen up to time t from a data stream. -/
def dataUpTo {X : Type u} {Y : Type v} (T : DataStream X Y) (t : ℕ) : List (X × Y) :=
  (List.range (t + 1)).map T.observe


-- @@ L31-39 verbatim
/-- EX-learning (explanatory learning, identification in the limit):
    The learner eventually converges to a hypothesis extensionally equal to c.
    Gold's original definition (1967). -/
def EXLearnable (X : Type u) (C : ConceptClass X Bool) : Prop :=
  ∃ (L : GoldLearner X Bool),
    ∀ (c : Concept X Bool), c ∈ C →
      ∀ (T : TextPresentation X c),
        ∃ (t₀ : ℕ), ∀ (t : ℕ), t ≥ t₀ →
          L.conjecture (dataUpTo T.toDataStream t) = c


-- @@ L41-48 verbatim
/-- BC-learning (behaviorally correct): the learner need only output a hypothesis
    EXTENSIONALLY equal to c (not syntactically). May oscillate between representations. -/
def BCLearnable (X : Type u) (C : ConceptClass X Bool) : Prop :=
  ∃ (L : GoldLearner X Bool),
    ∀ (c : Concept X Bool), c ∈ C →
      ∀ (T : TextPresentation X c),
        ∃ (t₀ : ℕ), ∀ (t : ℕ), t ≥ t₀ →
          ∀ (x : X), (L.conjecture (dataUpTo T.toDataStream t)) x = c x


-- @@ L50-60 verbatim
/-- Finite learning: EX-learning where the learner makes at most finitely many
    mind changes and eventually outputs a CORRECT hypothesis. Stronger than EX. -/
def FiniteLearnable (X : Type u) (C : ConceptClass X Bool) : Prop :=
  ∃ (L : GoldLearner X Bool),
    ∀ (c : Concept X Bool), c ∈ C →
      ∀ (T : TextPresentation X c),
        ∃ (t₀ : ℕ), ∀ (t : ℕ), t ≥ t₀ →
          L.conjecture (dataUpTo T.toDataStream t) = c
          ∧ ∀ (t' : ℕ), t' ≥ t₀ →
              L.conjecture (dataUpTo T.toDataStream t') =
              L.conjecture (dataUpTo T.toDataStream t₀)


-- @@ L62-71 verbatim
/-- Vacillatory learning: BC-learning where the learner may oscillate between
    finitely many correct hypotheses. -/
def VacillatoryLearnable (X : Type u) (C : ConceptClass X Bool) : Prop :=
  ∃ (L : GoldLearner X Bool),
    ∀ (c : Concept X Bool), c ∈ C →
      ∀ (T : TextPresentation X c),
        ∃ (S : Finset (Concept X Bool)),
          (∀ h ∈ S, ∀ x, h x = c x) ∧
          ∃ (t₀ : ℕ), ∀ (t : ℕ), t ≥ t₀ →
            L.conjecture (dataUpTo T.toDataStream t) ∈ S


-- @@ L73-82 verbatim
/-- Anomalous learning: EX-learning where the final hypothesis may have
    finitely many errors (anomalies). -/
def AnomalousLearnable (X : Type u) [Fintype X] (C : ConceptClass X Bool) (a : ℕ) : Prop :=
  ∃ (L : GoldLearner X Bool),
    ∀ (c : Concept X Bool), c ∈ C →
      ∀ (T : TextPresentation X c),
        ∃ (t₀ : ℕ), ∀ (t : ℕ), t ≥ t₀ →
          Finset.card (Finset.filter
            (fun x => (L.conjecture (dataUpTo T.toDataStream t)) x ≠ c x)
            Finset.univ) ≤ a


-- @@ L84-93 verbatim
/-- Monotonic learning: a Gold learner that never RETRACTS a positive claim. -/
def MonotonicLearnable (X : Type u) (C : ConceptClass X Bool) : Prop :=
  ∃ (L : GoldLearner X Bool),
    (∀ (c : Concept X Bool), c ∈ C →
      ∀ (T : TextPresentation X c),
        ∃ (t₀ : ℕ), ∀ (t : ℕ), t ≥ t₀ →
          L.conjecture (dataUpTo T.toDataStream t) = c) ∧
    (∀ (data : List (X × Bool)) (xy : X × Bool),
      ∀ (x : X), (L.conjecture data) x = true →
        (L.conjecture (data ++ [xy])) x = true)


-- @@ L95-101 verbatim
/-- Trial and error learning: point-wise convergence. Characterizes limiting recursion. -/
def TrialAndErrorLearnable (X : Type u) (C : ConceptClass X Bool) : Prop :=
  ∃ (L : GoldLearner X Bool),
    ∀ (c : Concept X Bool), c ∈ C →
      ∀ (T : TextPresentation X c),
        ∀ (x : X), ∃ (t₀ : ℕ), ∀ (t : ℕ), t ≥ t₀ →
          (L.conjecture (dataUpTo T.toDataStream t)) x = c x
