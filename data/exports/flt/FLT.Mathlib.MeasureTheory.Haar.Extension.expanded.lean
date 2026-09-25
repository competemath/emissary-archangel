/-
Copyright (c) 2025 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.Extension
public import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique



-- @@ L13-32 verbatim
/-!
# Haar measures on group extensions

In this file, if `1 → A → B → C → 1` is a short exact sequence of topological groups,
we construct a Haar measure on `B` from Haar measures on `A` and `B`.

## Main definitions

* `TopologicalGroup.IsSES φ ψ`: A predicate stating that `φ` is a closed embedding, `ψ` is an open
  quotient map, and `φ.range = ψ.ker`.
* `TopologicalGroup.IsSES.inducedMeasure`: The Haar measure on `B` induced by Haar measures
  on `A` and `C`.

## Main results

* `TopologicalGroup.IsSES.isHaarMeasure_inducedMeasure`: `inducedMeasure` is a Haar measure.
* `TopologicalGroup.IsSES.not_injOn_of_inducedMeasure_gt`: A sufficiently large open subset of
  `B` cannot be a fundamental domain.

-/


-- @@ L34-34 verbatim
@[expose] public section


-- @@ L36-36 verbatim
open MeasureTheory MeasureTheory.Measure


-- @@ L38-38 verbatim
open scoped Pointwise


-- @@ L40-40 verbatim
namespace TopologicalGroup.IsSES


-- @@ L42-45 verbatim
variable {A B C E : Type*} [Group A] [Group B] [Group C]
  [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
  {φ : A →* B} {ψ : B →* C} (H : TopologicalGroup.IsSES φ ψ)
  [IsTopologicalGroup B]


-- @@ L47-47 verbatim
variable [MeasurableSpace A] [BorelSpace A] (μA : Measure A) [hμA : IsHaarMeasure μA]

-- @@ L48-48 verbatim
variable [IsTopologicalGroup C] [LocallyCompactSpace B]


-- @@ L50-50 verbatim
variable [MeasurableSpace C] [BorelSpace C] (μC : Measure C) [hμC : IsHaarMeasure μC]

-- @@ L51-51 verbatim
variable [T2Space B] [MeasurableSpace B] [BorelSpace B]


-- @@ L53-59 verbatim
/-- A sufficiently large open subset of `B` cannot be a fundamental domain. -/
@[to_additive]
theorem not_injOn_of_inducedMeasure_gt (U : Set B) (hU : IsOpen U) [DiscreteTopology A]
    (h : μC Set.univ * μA {1} < inducedMeasure H μA μC U) :
    ¬ U.InjOn ψ := by
  contrapose! h
  exact H.inducedMeasure_lt_of_injOn μA μC hU h


-- @@ L61-79 verbatim
@[to_additive]
theorem not_injOn_of_measure_gt
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [PolishSpace G]
    [MeasurableSpace G] [BorelSpace G] [LocallyCompactSpace G]
    (H : Subgroup G) [H.Normal] [DiscreteTopology H] [CompactSpace (G ⧸ H)] :
    ∃ B : NNReal, ∀ U : Set G, IsOpen U → B < haar U → ¬ U.InjOn (QuotientGroup.mk' H) := by
  have h := ofClosedSubgroup H
  use ((haarScalarFactor ((h Subgroup.isClosed_of_discrete).inducedMeasure haar haar) haar)⁻¹ •
    (haar (Set.univ : Set (G ⧸ H)) * haar ({1} : Set H))).toNNReal
  intro U hU hU'
  rw [ENNReal.coe_toNNReal] at hU'
  · rw [inv_smul_lt_iff_of_pos (haarScalarFactor_pos_of_isHaarMeasure _ _)] at hU'
    apply (h Subgroup.isClosed_of_discrete).not_injOn_of_inducedMeasure_gt haar haar U hU
    rwa [measure_isHaarMeasure_eq_smul_of_isOpen ((h Subgroup.isClosed_of_discrete).inducedMeasure
      haar haar) haar hU]
  · apply ENNReal.nnreal_smul_ne_top
    apply ENNReal.mul_ne_top
    · exact isCompact_univ.measure_ne_top
    · exact isCompact_singleton.measure_ne_top


-- @@ L81-81 verbatim
end TopologicalGroup.IsSES
