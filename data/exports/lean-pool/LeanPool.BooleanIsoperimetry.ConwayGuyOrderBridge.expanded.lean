/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import LeanPool.BooleanIsoperimetry.Cube
public import LeanPool.BooleanIsoperimetry.ConwayGuyCoherentGap
import LeanPool.BooleanIsoperimetry.ConwayGuyRigidity
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow


-- @@ L18-29 verbatim
/-!
# From unit relations to consecutive subset-sum gaps

This file supplies the elementary order-theoretic bridge between the
Conway--Guy unit-relation certificates and consecutive gaps in the coherent
Boolean term order induced by the Conway--Guy weights.

Tom Bohman's 1996 theorem that the Conway--Guy rows have distinct subset sums
is still an external input if one wants the induced comparison to be a total
order.  The bridge itself only uses integrality: two subset sums differing by
one have no integer subset sum strictly between them.
-/


-- @@ L31-31 verbatim
@[expose] public section


-- @@ L33-33 verbatim
open scoped BigOperators


-- @@ L35-35 verbatim
namespace BooleanIsoperimetry.CoherentGap


-- @@ L37-39 verbatim
/-- The integer weight of a Boolean-cube vertex. -/
def integerSubsetWeight {n : ℕ} (weights : Relation n) (vertex : Cube n) : ℤ :=
  ∑ coordinate ∈ vertex, weights coordinate


-- @@ L41-43 verbatim
/-- The real weight of a Boolean-cube vertex. -/
def realSubsetWeight {n : ℕ} (weights : Fin n → ℝ) (vertex : Cube n) : ℝ :=
  ∑ coordinate ∈ vertex, weights coordinate


-- @@ L45-47 verbatim
/-- Coordinates with coefficient one in a signed relation. -/
def positiveSupport {n : ℕ} (relation : Relation n) : Cube n :=
  Finset.univ.filter fun coordinate => relation coordinate = 1


-- @@ L49-51 verbatim
/-- Coordinates with coefficient minus one in a signed relation. -/
def negativeSupport {n : ℕ} (relation : Relation n) : Cube n :=
  Finset.univ.filter fun coordinate => relation coordinate = -1


-- @@ L53-61 verbatim
/-- No subset sum lies strictly between the weights of `lower` and `upper`. -/
def IsConsecutiveSubsetGap {n : ℕ} (weights : Relation n)
    (lower upper : Cube n) : Prop :=
  integerSubsetWeight weights lower < integerSubsetWeight weights upper ∧
    ∀ middle,
      ¬(integerSubsetWeight weights lower <
          integerSubsetWeight weights middle ∧
        integerSubsetWeight weights middle <
          integerSubsetWeight weights upper)


-- @@ L63-70 verbatim
/-- Every consecutive gap of a reference integer row has size at least one
when measured by the candidate real row. -/
def SatisfiesNormalizedConsecutiveGaps {n : ℕ} (reference : Relation n)
    (candidate : Fin n → ℝ) : Prop :=
  ∀ lower upper,
    IsConsecutiveSubsetGap reference lower upper →
      1 ≤ realSubsetWeight candidate upper -
        realSubsetWeight candidate lower


-- @@ L72-103 verbatim
lemma dot_eq_support_difference {n : ℕ} (weights relation : Relation n)
    (hvalues : ∀ coordinate,
      relation coordinate = -1 ∨
        relation coordinate = 0 ∨ relation coordinate = 1) :
    dot relation weights =
      integerSubsetWeight weights (positiveSupport relation) -
        integerSubsetWeight weights (negativeSupport relation) := by
  classical
  unfold dot integerSubsetWeight positiveSupport negativeSupport
  calc
    (∑ coordinate, relation coordinate * weights coordinate) =
        ∑ coordinate,
          ((if relation coordinate = 1 then weights coordinate else 0) -
            if relation coordinate = -1 then weights coordinate else 0) := by
      apply Finset.sum_congr rfl
      intro coordinate _
      rcases hvalues coordinate with hnegative | hzero | hpositive
      · simp [hnegative]
      · simp [hzero]
      · simp [hpositive]
    _ =
        (∑ coordinate,
          if relation coordinate = 1 then weights coordinate else 0) -
          ∑ coordinate,
            if relation coordinate = -1 then weights coordinate else 0 := by
      rw [Finset.sum_sub_distrib]
    _ =
        (∑ coordinate ∈ Finset.univ.filter
          (fun coordinate => relation coordinate = 1), weights coordinate) -
          ∑ coordinate ∈ Finset.univ.filter
            (fun coordinate => relation coordinate = -1), weights coordinate := by
      simp only [Finset.sum_filter]


-- @@ L105-137 verbatim
lemma realDot_eq_support_difference {n : ℕ} (candidate : Fin n → ℝ)
    (relation : Relation n)
    (hvalues : ∀ coordinate,
      relation coordinate = -1 ∨
        relation coordinate = 0 ∨ relation coordinate = 1) :
    realDot relation candidate =
      realSubsetWeight candidate (positiveSupport relation) -
        realSubsetWeight candidate (negativeSupport relation) := by
  classical
  unfold realDot realSubsetWeight positiveSupport negativeSupport
  calc
    (∑ coordinate, (relation coordinate : ℝ) * candidate coordinate) =
        ∑ coordinate,
          ((if relation coordinate = 1 then candidate coordinate else 0) -
            if relation coordinate = -1 then candidate coordinate else 0) := by
      apply Finset.sum_congr rfl
      intro coordinate _
      rcases hvalues coordinate with hnegative | hzero | hpositive
      · simp [hnegative]
      · simp [hzero]
      · simp [hpositive]
    _ =
        (∑ coordinate,
          if relation coordinate = 1 then candidate coordinate else 0) -
          ∑ coordinate,
            if relation coordinate = -1 then candidate coordinate else 0 := by
      rw [Finset.sum_sub_distrib]
    _ =
        (∑ coordinate ∈ Finset.univ.filter
          (fun coordinate => relation coordinate = 1), candidate coordinate) -
          ∑ coordinate ∈ Finset.univ.filter
            (fun coordinate => relation coordinate = -1), candidate coordinate := by
      simp only [Finset.sum_filter]


-- @@ L139-147 verbatim
/-- A unit relation is realized by two subsets whose integer weights differ
by exactly one. -/
lemma unitRelation_support_gap {n : ℕ} {weights relation : Relation n}
    (hrelation : IsLiftableUnit weights relation) :
    integerSubsetWeight weights (positiveSupport relation) =
      integerSubsetWeight weights (negativeSupport relation) + 1 := by
  have hdot := hrelation.2.1
  rw [dot_eq_support_difference weights relation hrelation.1] at hdot
  omega


-- @@ L149-158 verbatim
/-- Integrality alone makes every realized gap of size one consecutive. -/
lemma consecutive_of_integer_gap_one {n : ℕ} {weights : Relation n}
    {lower upper : Cube n}
    (hgap : integerSubsetWeight weights upper =
      integerSubsetWeight weights lower + 1) :
    IsConsecutiveSubsetGap weights lower upper := by
  constructor
  · omega
  · intro middle hbetween
    omega


-- @@ L160-166 verbatim
/-- Every liftable unit relation is a consecutive subset-sum gap. -/
theorem unitRelation_isConsecutiveSubsetGap {n : ℕ}
    {weights relation : Relation n}
    (hrelation : IsLiftableUnit weights relation) :
    IsConsecutiveSubsetGap weights
      (negativeSupport relation) (positiveSupport relation) :=
  consecutive_of_integer_gap_one (unitRelation_support_gap hrelation)


-- @@ L168-179 verbatim
/-- Normalized consecutive-gap inequalities imply all unit-relation
inequalities used by the rigidity certificate. -/
theorem normalizedConsecutiveGaps_imply_unitRelations {n : ℕ}
    {reference : Relation n} {candidate : Fin n → ℝ}
    (hnormalized : SatisfiesNormalizedConsecutiveGaps reference candidate) :
    ∀ relation, IsLiftableUnit reference relation →
      1 ≤ realDot relation candidate := by
  intro relation hrelation
  have hgap := hnormalized (negativeSupport relation) (positiveSupport relation)
    (unitRelation_isConsecutiveSubsetGap hrelation)
  rw [realDot_eq_support_difference candidate relation hrelation.1]
  exact hgap


-- @@ L181-191 verbatim
/-- The Conway--Guy row is a coordinatewise lower bound for every real row
with normalized consecutive gaps relative to its subset sums. -/
theorem conwayGuyRigidity_of_normalizedConsecutiveGaps {n : ℕ}
    (candidate : Fin n → ℝ)
    (hnormalized : SatisfiesNormalizedConsecutiveGaps
      (conwayGuyArithmetic.tower.weights n) candidate) :
    ∀ coordinate,
      (conwayGuyArithmetic.tower.weights n coordinate : ℝ) ≤
        candidate coordinate :=
  conwayGuyNormalizedChamberRigidity candidate
    (normalizedConsecutiveGaps_imply_unitRelations hnormalized)


-- @@ L193-193 verbatim
end BooleanIsoperimetry.CoherentGap


-- @@ L195-195 verbatim
namespace BooleanIsoperimetry


-- @@ L197-200 verbatim
/-- Public short name for the all-dimensional Conway--Guy gap-rigidity
theorem. -/
alias conwayGuyGapRigidity :=
  CoherentGap.conwayGuyRigidity_of_normalizedConsecutiveGaps


-- @@ L202-202 verbatim
end BooleanIsoperimetry
