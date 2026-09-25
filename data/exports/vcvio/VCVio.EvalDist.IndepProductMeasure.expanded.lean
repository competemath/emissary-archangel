/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.EvalDist.IndepProduct
public import Mathlib.MeasureTheory.Constructions.Pi


-- @@ L12-27 verbatim
/-!
# Independent products denote product measures

`Fin.mOfFn` and `Fintype.mPi` run a family of computations independently and collect the
results as a function. On the measure side their denotation is Mathlib's product measure
`Measure.pi`. The proof does not touch the Giry monad at all: `Measure.pi_eq` characterizes the
product measure by its values on measurable boxes, and on a box the façade bridge
`evalDist_apply` turns the question into the coordinatewise event probability, which
`probEvent_forall_coord_mOfFn`/`probEvent_forall_coord_mPi` already factor. So the statement holds
for every semantics that satisfies `DiscreteEvalDistCompatible`, with no lawfulness assumption.

The coordinate marginals `evalDist_map_eval_mOfFn`/`evalDist_map_eval_mPi` are then Mathlib's
`Measure.pi_map_eval`: pushing the product forward along a coordinate recovers that factor once
the other factors carry full mass, which is the `Pr[⊥ | _] = 0` hypothesis of the façade's
`probEvent_coord_mPi`, read through `evalDist_apply_univ`.
-/


-- @@ L29-29 verbatim
public section


-- @@ L31-31 verbatim
open MeasureTheory


-- @@ L33-33 verbatim
universe u v


-- @@ L35-35 verbatim
section mOfFn


-- @@ L37-39 verbatim
variable {α : Type u} {m : Type u → Type v} [Monad m] [MonadLiftT m SPMF]
  [LawfulMonadLiftT m SPMF] [EvalDistSemantics m] [DiscreteEvalDistCompatible m]
  [MeasurableSpace α]


-- @@ L41-49 expanded
/-- The independent product of `n` computations denotes the product measure of their
denotations. -/
theorem evalDist_mOfFn (n : ℕ) (g : Fin n → m α) :
    evalDist (Fin.mOfFn n g) = Measure.pi fun i => evalDist (g i) :=
  by
  refine (Measure.pi_eq fun s hs => ?_).symm
  rw [evalDist_apply _ (MeasurableSet.univ_pi hs)]
  simp only [Set.mem_univ_pi]
  rw [probEvent_forall_coord_mOfFn n g fun i x => x ∈ s i]
  exact Finset.prod_congr rfl fun i _ => (evalDist_apply _ (hs i)).symm


-- @@ L51-56 expanded
/-- Reading off one coordinate of an independent product recovers that factor's denotation,
provided the other factors never fail. -/
theorem evalDist_map_eval_mOfFn (n : ℕ) (g : Fin n → m α) (hg : ∀ i, probFailure (g i) = 0)
    (i : Fin n) : (evalDist (Fin.mOfFn n g)).map (Function.eval i) = evalDist (g i) :=
  by
  rw [evalDist_mOfFn, Measure.pi_map_eval]
  simp [evalDist_apply_univ, hg]


-- @@ L58-58 verbatim
end mOfFn


-- @@ L60-60 verbatim
section mPi


-- @@ L62-62 verbatim
universe v'


-- @@ L64-66 verbatim
variable {α : Type} {m : Type → Type v'} [Monad m] [LawfulMonad m] {ι : Type} [Fintype ι]
  [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF] [EvalDistSemantics m]
  [DiscreteEvalDistCompatible m] [MeasurableSpace α]


-- @@ L68-75 expanded
/-- The independent product of a finitely indexed family of computations denotes the product
measure of their denotations. -/
theorem evalDist_mPi (f : ι → m α) :
    evalDist (Fintype.mPi f) = Measure.pi fun i => evalDist (f i) :=
  by
  refine (Measure.pi_eq fun s hs => ?_).symm
  rw [evalDist_apply _ (MeasurableSet.univ_pi hs)]
  simp only [Set.mem_univ_pi]
  rw [probEvent_forall_coord_mPi f fun i x => x ∈ s i]
  exact Finset.prod_congr rfl fun i _ => (evalDist_apply _ (hs i)).symm


-- @@ L77-84 expanded
/-- Reading off one coordinate of a finite independent product recovers that factor's
denotation, provided the other factors never fail: the measure-side form of
`probEvent_coord_mPi`, with the induction replaced by `Measure.pi_map_eval`. -/
theorem evalDist_map_eval_mPi (f : ι → m α) (hf : ∀ i, probFailure (f i) = 0) (i : ι) :
    (evalDist (Fintype.mPi f)).map (Function.eval i) = evalDist (f i) := by
  classical
  rw [evalDist_mPi, Measure.pi_map_eval]
  simp [evalDist_apply_univ, hf]


-- @@ L86-86 verbatim
end mPi
