/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
module

public import LeanPool.FormalLearningTheory.Learner.Core
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Inv
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded


-- @@ L14-20 verbatim
/-!
# Learner Properties

Properties that learners may satisfy: iterative, set-driven, consistent,
conservative, passive. These are `Prop` predicates, not separate types.
Also includes probabilistic and team learner variants.
-/


-- @@ L22-22 verbatim
@[expose] public section


-- @@ L24-24 verbatim
universe u v


-- @@ L26-28 verbatim
/-!
## Learner Properties
-/


-- @@ L30-34 verbatim
/-- An iterative learner depends only on its previous hypothesis and the new data point. -/
def IsIterative {X : Type u} {Y : Type v} (L : GoldLearner X Y) : Prop :=
  ∃ step : Concept X Y → (X × Y) → Concept X Y,
    ∀ (data : List (X × Y)) (xy : X × Y),
      L.conjecture (data ++ [xy]) = step (L.conjecture data) xy


-- @@ L36-40 verbatim
/-- A set-driven learner's output depends only on the SET of data, not the order. -/
def IsSetDriven {X : Type u} {Y : Type v} [DecidableEq X] [DecidableEq Y]
    (L : GoldLearner X Y) : Prop :=
  ∀ (data₁ data₂ : List (X × Y)),
    data₁.toFinset = data₂.toFinset → L.conjecture data₁ = L.conjecture data₂


-- @@ L42-45 verbatim
/-- A consistent learner always outputs a hypothesis consistent with all data seen. -/
def IsConsistent {X : Type u} {Y : Type v} (L : GoldLearner X Y) : Prop :=
  ∀ (data : List (X × Y)),
    ∀ p ∈ data, (L.conjecture data) p.1 = p.2


-- @@ L47-51 verbatim
/-- A conservative learner only changes its hypothesis when forced by inconsistency. -/
def IsConservative {X : Type u} {Y : Type v} (L : GoldLearner X Y) : Prop :=
  ∀ (data : List (X × Y)) (xy : X × Y),
    (L.conjecture data) xy.1 = xy.2 →
      L.conjecture (data ++ [xy]) = L.conjecture data


-- @@ L53-58 verbatim
/-- A probabilistic learner uses randomness. -/
structure ProbabilisticLearner (X : Type u) (Y : Type v) where
  /-- The hypothesis space -/
  hypotheses : HypothesisSpace X Y
  /-- Randomized learning: seed → sample → hypothesis -/
  learn : {m : ℕ} → ℕ → (Fin m → X × Y) → Concept X Y


-- @@ L60-63 verbatim
/-- A team learner: multiple learners, at least one of which identifies the target. -/
structure TeamLearner (X : Type u) (Y : Type v) (n : ℕ) where
  /-- The team members -/
  team : Fin n → GoldLearner X Y


-- @@ L65-65 verbatim
/-! ## MeasurableBatchLearner API -/


-- @@ L67-75 verbatim
/-- Fixed-sample measurability: for fixed training data S,
    L.learn S is a measurable function X → Bool.
    This is the most commonly used consequence of MeasurableBatchLearner. -/
theorem MeasurableBatchLearner.learn_measurable
    {X : Type u} [MeasurableSpace X]
    (L : BatchLearner X Bool) [h : MeasurableBatchLearner X L]
    {m : ℕ} (S : Fin m → X × Bool) :
    Measurable (L.learn S) :=
  (h.eval_measurable m).comp (Measurable.prodMk measurable_const measurable_id)
