/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import ToMathlib.MeasureTheory.MeasurableSpace.Option
public import VCVio.CryptoFoundations.ReplayFork
public import VCVio.CryptoFoundations.SeededFork
public import VCVio.EvalDist.PFunctorMeasure


-- @@ L13-25 verbatim
/-!
# Measure-level forking bounds

The seeded and replay forking lemmas are proved through VCVio's discrete
probability surface. This file transports their final success bounds to the
Mathlib measure denotation of the same oracle programs.

These are compatibility corollaries rather than new forking arguments. The
measure semantics is the canonical one induced by the existing per-query
probability interpretation, stated on the primary measure `𝒟[…]`, and
`evalDist_apply` identifies its measurable success event with the probability
used by the original theorem.
-/


-- @@ L27-27 verbatim
@[expose] public section


-- @@ L29-29 verbatim
open MeasureTheory OracleSpec ENNReal Finset


-- @@ L31-31 verbatim
namespace OracleComp


-- @@ L33-40 verbatim
/-- The canonical measure semantics induced by an oracle specification's
existing probability semantics. This instance is local so measure semantics
remain an explicit opt-in outside this compatibility module. -/
noncomputable local instance measureSpecOfProbability
    {ι : Type} {spec : OracleSpec ι}
    [∀ i, MeasurableSpace (spec.Range i)] [IsProbabilitySpec spec] :
    PFunctor.IsMeasureSpec spec.toPFunctor :=
  PFunctor.IsProbabilitySpec.toMeasureSpec spec.toPFunctor


-- @@ L42-42 verbatim
section seeded


-- @@ L44-48 verbatim
variable {ι : Type} [DecidableEq ι] {spec : OracleSpec ι}
  [IsUniformSpec spec] {α : Type}
  [∀ i, MeasurableSpace (spec.Range i)]
  [∀ i, DiscreteMeasurableSpace (spec.Range i)]
  [MeasurableSpace α]


-- @@ L50-62 expanded
/-- The canonical Bellare--Neven seeded-fork bound, stated as the Mathlib
measure of the successful-result event. -/
theorem le_evalDist_isSome_seededFork_sq (main : OracleComp spec α) (qb : ι → ℕ) (js : List ι)
    (i : ι) (cf : α → Option (Fin (qb i + 1))) [∀ j, SampleableType (spec.Range j)]
    [spec.DecidableEq] [SubSpec unifSpec spec] [LawfulSubSpec unifSpec spec] :
    ((∑ s, probOutput (cf <$> main) (some s)) ^ 2 / ((qb i + 1 : ℕ) : ℝ≥0∞) -
        (∑ s, probOutput (cf <$> main) (some s)) / ((Fintype.card (spec.Range i) : ℕ) : ℝ≥0∞)) ≤
      (evalDist (seededFork main qb js i cf)) {result | result.isSome} :=
  by
  rw [evalDist_apply _ Option.measurableSet_isSome]
  exact le_probEvent_isSome_seededFork_sq main qb js i cf


-- @@ L64-64 verbatim
end seeded


-- @@ L66-66 verbatim
section replay


-- @@ L68-71 verbatim
variable {ι : Type} {spec : OracleSpec ι} [IsUniformSpec spec] {α : Type}
  [∀ i, MeasurableSpace (spec.Range i)]
  [∀ i, DiscreteMeasurableSpace (spec.Range i)]
  [MeasurableSpace α]


-- @@ L73-85 expanded
/-- The replay/context forking bound, stated as the Mathlib measure of the
successful-result event. -/
theorem le_evalDist_isSome_contextFork [spec.DecidableEq] (main : OracleComp spec α) (qb : ι → ℕ)
    (i : ι) (cf : α → Option (Fin (qb i + 1))) (hreach : PathCfReachable main qb i cf) :
    (let acc : ℝ≥0∞ := ∑ s, probOutput (cf <$> main) (some s)
      let h : ℝ≥0∞ := Fintype.card (spec.Range i)
      let q := qb i + 1
      acc * (acc / q - h⁻¹)) ≤
      (evalDist (contextFork main qb i cf)) {result | result.isSome} :=
  by
  rw [evalDist_apply _ Option.measurableSet_isSome]
  exact le_probEvent_isSome_contextFork main qb i cf hreach


-- @@ L87-87 verbatim
end replay


-- @@ L89-89 verbatim
end OracleComp
