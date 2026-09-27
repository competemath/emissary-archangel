/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Instances
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Inv
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded


-- @@ L15-25 verbatim
/-!
# Basic Types for Formal Learning Theory

Foundational vocabulary: domains, labels, concepts, concept classes, hypothesis
spaces, inductive bias, version spaces, and loss functions. These are the base
types that all learners, criteria, and complexity measures are defined in terms of.

Alternative definitions for ConceptClass and InductiveBias are provided as
commented-out variants for different proof contexts (decidable, RE, measurable,
multiclass, Bayesian).
-/


-- @@ L27-27 verbatim
@[expose] public section


-- @@ L29-29 verbatim
universe u v


-- @@ L31-39 verbatim
/-!
## Atomic Types
-/


-- Domain (X : Type u) and Label (Y : Type v) are universe-polymorphic type parameters.
-- They are not defined as defs; they appear as parameters to every subsequent type.
-- Domain: the instance space (ℝⁿ, {0,1}ⁿ, or any type)
-- Label: the output space (Bool for binary, Fin k for multiclass, ℝ for regression)


-- @@ L41-43 verbatim
/-- A concept is a function from domain to label. This is the atomic unit that
    concept classes collect and learners try to approximate. -/
abbrev Concept (X : Type u) (Y : Type v) := X → Y


-- @@ L45-68 verbatim
/-- A concept class is a set of concepts. Used by every paradigm, complexity
    measure, and criterion.

    Primary definition: Set of functions. Used for PAC/agnostic PAC where
    concept classes are sets over which VC dimension, Rademacher complexity,
    covering numbers, etc. are measured. Alternative definitions below for
    contexts requiring decidability, enumerability, or measurability. -/
abbrev ConceptClass (X : Type u) (Y : Type v) := Set (Concept X Y)

/- Alternative: decidable membership (for online game tree construction):
-- def ConceptClassDecidable (X : Type u) (Y : Type v) [DecidableEq X] [DecidableEq Y] :=
--   { H : Set (X → Y) // ∀ h, Decidable (h ∈ H) } -/

/- Alternative: recursively enumerable (for Gold-style identification proofs):
-- def ConceptClassRE (X : Type u) (Y : Type v) [Encodable X] [Encodable Y] :=
--   { H : Set (X → Y) // ∃ e : ℕ → Option (X → Y), Set.range (fun n => (e n).get!) = H } -/

/- Alternative: measurable hypotheses (for Rademacher/PAC-Bayes proofs):
-- def ConceptClassMeas (X : Type u) (Y : Type v) [MeasurableSpace X] [MeasurableSpace Y] :=
--   { H : Set (X → Y) // ∀ h ∈ H, Measurable h } -/

/- Alternative: multiclass with Fintype label (for Natarajan/DS dimension):
-- def ConceptClassMulti (X : Type u) (Y : Type v) [Fintype Y] :=
--   { H : Set (X → Y) // Fintype.card Y ≥ 2 } -/


-- @@ L70-74 verbatim
/-- Every concept in C is a measurable function.
    Krapp-Wirth precondition: Γ(h) ∈ Σ_Z for all h ∈ H. -/
class MeasurableHypotheses (X : Type u) [MeasurableSpace X]
    (C : ConceptClass X Bool) : Prop where
  mem_measurable : ∀ h ∈ C, Measurable h


-- @@ L76-82 verbatim
/-- A hypothesis space is a set of candidate concepts that the learner searches over.
    When H = C (the realizable case), every concept in the target class is available.
    When H ⊂ C or H ⊃ C, we are in the improper/agnostic regime.

    Structurally identical to ConceptClass but semantically distinct: ConceptClass is
    the ground truth collection; HypothesisSpace is what the learner has access to. -/
abbrev HypothesisSpace (X : Type u) (Y : Type v) := Set (Concept X Y)


-- @@ L84-87 verbatim
/-- A single hypothesis - an element of the hypothesis space.
    Just a Concept by another name, but the semantic distinction matters:
    a hypothesis is a learner's GUESS, a concept is a ground truth. -/
abbrev Hypothesis (X : Type u) (Y : Type v) := Concept X Y


-- @@ L89-91 verbatim
/-- The target concept is the specific concept the learner is trying to identify/approximate.
    It's an element of the concept class. -/
def TargetConcept (X : Type u) (Y : Type v) (C : ConceptClass X Y) := { c : Concept X Y // c ∈ C }


-- @@ L93-97 verbatim
/-- The proper learning flag: whether the learner's hypothesis space equals the concept class.
    Proper: H = C. Improper: H ⊃ C (learner can output hypotheses outside C).
    This distinction matters for computational hardness results (proper_improper_separation). -/
def IsProper (X : Type u) (Y : Type v) (C : ConceptClass X Y) (H : HypothesisSpace X Y) : Prop :=
  (H : Set (Concept X Y)) = (C : Set (Concept X Y))


-- @@ L99-101 verbatim
/-!
## Structured Types
-/


-- @@ L103-123 verbatim
/-- Inductive bias: a preference ordering or scoring over hypotheses.
    This is NOT just a set; it bundles a hypothesis space with a way to RANK hypotheses.
    In Bayesian learning: the prior distribution.
    In SRM: the complexity hierarchy.
    In NFL theorem: the object whose absence makes learning impossible. -/
structure InductiveBias (X : Type u) (Y : Type v) where
  /-- The hypothesis space the bias operates over -/
  hypotheses : HypothesisSpace X Y
  /-- Preference score: lower is more preferred. Could be complexity, prior probability, etc. -/
  preference : Concept X Y → ℝ
  /-- Hypotheses outside the space are not preferred over those inside:
      everything outside H is penalized at least as much as anything inside H.
      This works for both MDL (description length) and Bayesian (-log prior) readings. -/
  not_preferred : ∀ h, h ∉ hypotheses → ∀ h' ∈ hypotheses, preference h' ≤ preference h

/- Alternative: measure-theoretic prior (for Bayesian posterior consistency proofs):
-- structure InductiveBiasBayes (X : Type u) (Y : Type v)
--     [MeasurableSpace (Concept X Y)] where
--   hypotheses : HypothesisSpace X Y
--   prior : MeasureTheory.ProbabilityMeasure (Concept X Y)
--   supported : prior.toMeasure (hypotheses)ᶜ = 0 -/


-- @@ L125-139 verbatim
/-- Version space: the set of hypotheses consistent with all data seen so far.
    Central to Gold-style learning; the learner narrows the version space as
    data arrives, and convergence = version space shrinks to the target.

    Defined using HypothesisSpace and a consistency predicate over data. -/
structure VersionSpace (X : Type u) (Y : Type v) where
  /-- The full hypothesis space -/
  hypotheses : HypothesisSpace X Y
  /-- Data seen so far: list of (input, label) pairs -/
  data : List (X × Y)
  /-- The consistent subset - hypotheses that agree with all data -/
  consistent : Set (Concept X Y)
  /-- Consistency condition: every consistent hypothesis is in H and agrees with data -/
  consistent_sub : consistent ⊆ hypotheses
  consistent_agrees : ∀ h ∈ consistent, ∀ p ∈ data, h p.1 = p.2


-- @@ L141-143 verbatim
/-!
## Realizability Flags
-/


-- @@ L145-148 verbatim
/-- Realizability assumption: the target concept is in the hypothesis space.
    This is a Prop because it's a condition on the learning setup, not a type. -/
def Realizable (X : Type u) (Y : Type v) (C : ConceptClass X Y) (H : HypothesisSpace X Y) : Prop :=
  C ⊆ H


-- @@ L150-154 verbatim
/-- Agnostic setting: no assumption that target ∈ H. The learner competes against
    the best hypothesis in H. -/
def Agnostic (X : Type u) (Y : Type v) (C : ConceptClass X Y) (H : HypothesisSpace X Y) : Prop :=
  C = C ∧ H = H -- The agnostic setting is the ABSENCE of a realizability assumption.
  -- It's captured by NOT requiring Realizable as a hypothesis in theorem statements.


-- @@ L156-161 verbatim
/-!
## Loss Functions

Loss functions bridge the domain/label types to ℝ for measuring error.
They are universal across paradigms (PAC uses expected loss, online uses cumulative loss).
-/


-- @@ L163-164 verbatim
/-- A loss function measures the discrepancy between a prediction and true label. -/
def LossFunction (Y : Type v) := Y → Y → ℝ


-- @@ L166-168 verbatim
/-- The 0-1 loss for classification. -/
noncomputable def zeroOneLoss (Y : Type v) [DecidableEq Y] : LossFunction Y :=
  fun y₁ y₂ => if y₁ = y₂ then 0 else 1


-- @@ L170-172 verbatim
/-- Squared loss for regression (Y = ℝ). -/
noncomputable def squaredLoss : LossFunction ℝ :=
  fun y₁ y₂ => (y₁ - y₂) ^ 2
