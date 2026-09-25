/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.EvalDist.ExpectationMeasure
public import VCVio.EvalDist.Defs.NeverFails
public import VCVio.EvalDist.Instances.OptionT


-- @@ L13-32 verbatim
/-!
# Failure on the measure side

On the measure side a computation's failure is *missing mass*: `𝒟[mx]` is a subprobability
measure and `Pr[⊥ | mx]` is what it lacks to be a probability measure. This module records that
account of failure against the façade bridge `DiscreteEvalDistCompatible`:

* `probFailure_eq_one_sub_evalDist_univ`, `evalDist_apply_univ_eq_one_iff`,
  `isProbabilityMeasure_evalDist_iff` — failure is the missing mass, and a computation denotes a
  probability measure exactly when it never fails; `NeverFail mx` gives the
  `IsProbabilityMeasure 𝒟[mx]` instance.
* `evalDist_failure` — `failure` denotes the zero measure.
* `evalDist_withFailure_apply_none`/`_some` — the failure-completed denotation
  `(𝒟[mx]).withFailure : Measure (Option α)` is the probability measure with the failure mass at
  `none` and the point probabilities at `some x`.
* `evalDist_bind_apply_univ`, `evalDist_map_apply_univ`, `probFailure_bind_eq_add_expectedValue`
  — how success mass moves through `bind` and `map`, in `expectedValue` form.
* `OptionT.evalDist_eq_dropNone` — an `OptionT` computation denotes the `dropNone` of its run:
  the `none` branch is discarded mass, not an output.
-/


-- @@ L34-34 verbatim
public section


-- @@ L36-36 verbatim
open MeasureTheory OracleComp.EvalDist

-- @@ L37-37 verbatim
open scoped ENNReal


-- @@ L39-39 verbatim
universe u v


-- @@ L41-41 verbatim
variable {m : Type u → Type v} {α β : Type u}


-- @@ L43-43 verbatim
section compatible


-- @@ L45-46 verbatim
variable [MonadLiftT m SPMF] [EvalDistSemantics m] [DiscreteEvalDistCompatible m]
  [MeasurableSpace α]


-- @@ L48-51 expanded
/-- Failure is the mass missing from the denoted measure. -/
theorem probFailure_eq_one_sub_evalDist_univ (mx : m α) :
    probFailure mx = 1 - (evalDist mx) Set.univ := by
  rw [evalDist_apply_univ, ENNReal.sub_sub_cancel ENNReal.one_ne_top probFailure_le_one]


-- @@ L53-59 expanded
/-- The denoted measure has total mass one exactly when the computation never fails. -/
theorem evalDist_apply_univ_eq_one_iff (mx : m α) :
    (evalDist mx) Set.univ = 1 ↔ probFailure mx = 0 :=
  by
  constructor
  · intro h
    rw [probFailure_eq_one_sub_evalDist_univ, h, tsub_self]
  · intro h
    rw [evalDist_apply_univ, h, tsub_zero]


-- @@ L61-64 expanded
/-- A computation denotes a probability measure exactly when it never fails. -/
theorem isProbabilityMeasure_evalDist_iff (mx : m α) :
    IsProbabilityMeasure (evalDist mx) ↔ probFailure mx = 0 := by
  rw [isProbabilityMeasure_iff, evalDist_apply_univ_eq_one_iff]


-- @@ L66-68 expanded
/-- A computation that never fails denotes a probability measure. -/
instance [Monad m] (mx : m α) [NeverFail mx] : IsProbabilityMeasure (evalDist mx) :=
  (isProbabilityMeasure_evalDist_iff mx).mpr probFailure_eq_zero


-- @@ L70-74 expanded
/-- `failure` denotes the zero measure. -/
@[simp]
theorem evalDist_failure [AlternativeMonad m] [MonadLiftT m SetM] [EvalDistCompatible m]
    [HasEvalSet.LawfulFailure m] : evalDist (failure : m α) = 0 := by
  rw [← Measure.measure_univ_eq_zero, evalDist_apply_univ, probFailure_failure, tsub_self]


-- @@ L76-76 verbatim
variable [DiscreteMeasurableSpace α]


-- @@ L78-83 expanded
/-- The failure-completed denotation puts the failure probability at `none`. -/
@[simp]
theorem evalDist_withFailure_apply_none (mx : m α) :
    (evalDist mx).withFailure { none } = probFailure mx := by
  rw [Measure.withFailure_apply_none, evalDist_apply_univ,
    ENNReal.sub_sub_cancel ENNReal.one_ne_top probFailure_le_one]


-- @@ L85-89 expanded
/-- The failure-completed denotation keeps every point probability at `some x`. -/
@[simp]
theorem evalDist_withFailure_apply_some (mx : m α) (x : α) :
    (evalDist mx).withFailure {some x} = probOutput mx x := by
  rw [Measure.withFailure_apply_some, evalDist_apply_singleton]


-- @@ L91-93 expanded
/-- The failure-completed denotation is a probability measure. -/
instance (mx : m α) : IsProbabilityMeasure (evalDist mx).withFailure :=
  Measure.withFailure_isProbabilityMeasure _ (evalDist_apply_univ_le_one mx)


-- @@ L95-95 verbatim
end compatible


-- @@ L97-97 verbatim
section lawful


-- @@ L99-101 verbatim
variable [Monad m] [MonadLiftT m SPMF] [EvalDistSemantics m] [DiscreteEvalDistCompatible m]
  [LawfulEvalDistSemantics m] [MeasurableSpace α] [DiscreteMeasurableSpace α]
  [MeasurableSpace β]


-- @@ L103-107 expanded
/-- The success mass of a bind is the expected success mass of the continuation. -/
theorem evalDist_bind_apply_univ (mx : m α) (f : α → m β) :
    (evalDist (mx >>= f)) Set.univ = expectedValue mx fun x => (evalDist (f x)) Set.univ := by
  rw [evalDist_bind_of_discrete,
    Measure.bind_apply MeasurableSet.univ Measurable.of_discrete.aemeasurable, lintegral_evalDist]


-- @@ L109-113 expanded
omit [MonadLiftT m SPMF] [DiscreteEvalDistCompatible m] [DiscreteMeasurableSpace α] in
/-- A measurable map preserves success mass. -/
theorem evalDist_map_apply_univ [LawfulMonad m] (mx : m α) {f : α → β} (hf : Measurable f) :
    (evalDist (f <$> mx)) Set.univ = (evalDist mx) Set.univ := by
  rw [evalDist_map mx hf, Measure.map_apply hf MeasurableSet.univ, Set.preimage_univ]


-- @@ L115-115 verbatim
end lawful


-- @@ L117-122 expanded
/-- `probFailure_bind_eq_add_tsum` with the sum packaged as an `expectedValue`: the failure of
a bind is the prefix failure plus the expected failure of the continuation. -/
theorem probFailure_bind_eq_add_expectedValue [Monad m] [MonadLiftT m SPMF]
    [LawfulMonadLiftT m SPMF] (mx : m α) (my : α → m β) :
    probFailure (mx >>= my) = probFailure mx + expectedValue mx fun x => probFailure (my x) :=
  probFailure_bind_eq_add_tsum mx my


-- @@ L124-124 verbatim
namespace OptionT


-- @@ L126-127 verbatim
variable [Monad m] [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF] [MeasurableSpace α]
  [DiscreteMeasurableSpace α]


-- @@ L129-135 expanded
/-- An `OptionT` computation denotes the `dropNone` of its run: the `none` branch is discarded
mass, not an output. -/
theorem evalDist_eq_dropNone (mx : OptionT m α) : evalDist mx = (evalDist mx.run).dropNone :=
  by
  change (evalSPMF mx).toMeasure = Measure.dropNone (evalSPMF mx.run).toMeasure
  rw [OptionT.evalSPMF_eq, OptionT.mapM', Measure.dropNone, SPMF.toMeasure_bind]
  refine Measure.bind_congr_right (Filter.Eventually.of_forall fun o => ?_)
  cases o <;> simp


-- @@ L137-137 verbatim
end OptionT
