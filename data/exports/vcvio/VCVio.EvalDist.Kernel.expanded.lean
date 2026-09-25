/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import VCVio.EvalDist.Defs.Semantics
public import ToMathlib.Probability.Kernel.Subprobability


-- @@ L11-20 verbatim
/-!
# Kernel-valued evaluation semantics

This module bundles a measurably parameterized family of computations as a Mathlib kernel. Closed
computations denote measures; a family `f : ρ → m α` denotes a kernel precisely when the family
of output measures is measurable in `ρ`.

The resulting kernel is automatically subprobabilistic. If the family is lossless, it is a Markov
kernel. Monad bind is composition of the input measure with the continuation kernel.
-/


-- @@ L22-22 verbatim
@[expose] public section


-- @@ L24-24 verbatim
open MeasureTheory ProbabilityTheory

-- @@ L25-25 verbatim
open scoped ProbabilityTheory


-- @@ L27-27 verbatim
universe u v w


-- @@ L29-29 verbatim
variable {m : Type u → Type v} {α β : Type u}


-- @@ L31-31 verbatim
section


-- @@ L33-33 verbatim
variable {ρ : Type w}


-- @@ L35-39 expanded
/-- The kernel denoted by a measurably parameterized family of computations. -/
noncomputable def evalDistKernel [EvalDistSemantics m] [MeasurableSpace ρ] [MeasurableSpace α]
    (f : ρ → m α) (hf : Measurable fun r => evalDist (f r)) : Kernel ρ α :=
  ⟨fun r => evalDist (f r), hf⟩


-- @@ L41-45 verbatim
/-- On a discrete input space, every computation-valued family defines a kernel. -/
noncomputable def evalDistKernelOfDiscrete [EvalDistSemantics m]
    [MeasurableSpace ρ] [DiscreteMeasurableSpace ρ] [MeasurableSpace α]
    (f : ρ → m α) : Kernel ρ α :=
  evalDistKernel f Measurable.of_discrete


-- @@ L47-51 expanded
@[simp]
theorem evalDistKernel_apply [EvalDistSemantics m] [MeasurableSpace ρ] [MeasurableSpace α]
    (f : ρ → m α) (hf : Measurable fun r => evalDist (f r)) (r : ρ) :
    evalDistKernel f hf r = evalDist (f r) :=
  rfl


-- @@ L53-57 expanded
@[simp]
theorem evalDistKernelOfDiscrete_apply [EvalDistSemantics m] [MeasurableSpace ρ]
    [DiscreteMeasurableSpace ρ] [MeasurableSpace α] (f : ρ → m α) (r : ρ) :
    evalDistKernelOfDiscrete f r = evalDist (f r) :=
  rfl


-- @@ L59-63 expanded
instance evalDistKernel.instIsSubprobabilityKernel [EvalDistSemantics m] [MeasurableSpace ρ]
    [MeasurableSpace α] (f : ρ → m α) (hf : Measurable fun r => evalDist (f r)) :
    IsSubprobabilityKernel (evalDistKernel f hf) :=
  ⟨fun r => evalDist_apply_univ_le_one (f r)⟩


-- @@ L65-68 verbatim
instance evalDistKernelOfDiscrete.instIsSubprobabilityKernel [EvalDistSemantics m]
    [MeasurableSpace ρ] [DiscreteMeasurableSpace ρ] [MeasurableSpace α]
    (f : ρ → m α) : IsSubprobabilityKernel (evalDistKernelOfDiscrete f) :=
  ⟨fun r => evalDist_apply_univ_le_one (f r)⟩


-- @@ L70-76 expanded
/-- A lossless computation family denotes a Markov kernel. -/
theorem isMarkovKernel_evalDistKernel [EvalDistSemantics m] [MeasurableSpace ρ] [MeasurableSpace α]
    (f : ρ → m α) (hf : Measurable fun r => evalDist (f r))
    (hProbability : ∀ r, IsProbabilityMeasure (evalDist (f r))) :
    IsMarkovKernel (evalDistKernel f hf) :=
  ⟨hProbability⟩


-- @@ L78-83 expanded
/-- Monad bind is composition of a measure with the continuation kernel. -/
theorem evalDist_bind_eq_comp [Monad m] [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    [MeasurableSpace α] [MeasurableSpace β] (mx : m α) (f : α → m β)
    (hf : Measurable fun x => evalDist (f x)) :
    evalDist (mx >>= f) = evalDistKernel f hf ∘ₘ evalDist mx :=
  evalDist_bind mx f hf


-- @@ L85-90 expanded
/-- Discrete-domain specialization of `evalDist_bind_eq_comp`. -/
theorem evalDist_bind_eq_comp_of_discrete [Monad m] [EvalDistSemantics m]
    [LawfulEvalDistSemantics m] [MeasurableSpace α] [DiscreteMeasurableSpace α] [MeasurableSpace β]
    (mx : m α) (f : α → m β) : evalDist (mx >>= f) = evalDistKernelOfDiscrete f ∘ₘ evalDist mx :=
  evalDist_bind_of_discrete mx f


-- @@ L92-92 verbatim
namespace MeasureSemanticsVia


-- @@ L94-94 verbatim
variable [Monad m]


-- @@ L96-100 verbatim
/-- A local bundled semantics turns a measurable family of surface computations into a kernel. -/
noncomputable def evalDistKernel (sem : MeasureSemanticsVia m)
    [MeasurableSpace ρ] [MeasurableSpace α] (f : ρ → m α)
    (hf : Measurable fun r => sem.evalDist (f r)) : Kernel ρ α :=
  ⟨fun r => sem.evalDist (f r), hf⟩


-- @@ L102-106 verbatim
@[simp]
theorem evalDistKernel_apply (sem : MeasureSemanticsVia m)
    [MeasurableSpace ρ] [MeasurableSpace α] (f : ρ → m α)
    (hf : Measurable fun r => sem.evalDist (f r)) (r : ρ) :
    sem.evalDistKernel f hf r = sem.evalDist (f r) := rfl


-- @@ L108-112 verbatim
instance evalDistKernel.instIsSubprobabilityKernel (sem : MeasureSemanticsVia m)
    [MeasurableSpace ρ] [MeasurableSpace α] (f : ρ → m α)
    (hf : Measurable fun r => sem.evalDist (f r)) :
    IsSubprobabilityKernel (sem.evalDistKernel f hf) :=
  ⟨fun r => sem.evalDist_apply_univ_le_one (f r)⟩


-- @@ L114-114 verbatim
end MeasureSemanticsVia


-- @@ L116-116 verbatim
end


-- @@ L118-118 verbatim
namespace ReaderT


-- @@ L120-120 verbatim
variable {ρ : Type u}


-- @@ L122-126 expanded
/-- A reader computation denotes a kernel from environments to output distributions. -/
noncomputable def evalDistKernel [EvalDistSemantics m] [MeasurableSpace ρ] [MeasurableSpace α]
    (mx : ReaderT ρ m α) (hMeasurable : Measurable fun environment => evalDist (mx environment)) :
    Kernel ρ α :=
  _root_.evalDistKernel mx hMeasurable


-- @@ L128-132 verbatim
/-- Discrete environments discharge the reader kernel's measurability obligation. -/
noncomputable def evalDistKernelOfDiscrete [EvalDistSemantics m]
    [MeasurableSpace ρ] [DiscreteMeasurableSpace ρ] [MeasurableSpace α]
    (mx : ReaderT ρ m α) : Kernel ρ α :=
  _root_.evalDistKernelOfDiscrete mx


-- @@ L134-138 expanded
@[simp]
theorem evalDistKernel_apply [EvalDistSemantics m] [MeasurableSpace ρ] [MeasurableSpace α]
    (mx : ReaderT ρ m α) (hMeasurable : Measurable fun environment => evalDist (mx environment))
    (environment : ρ) :
    ReaderT.evalDistKernel mx hMeasurable environment = evalDist (mx environment) :=
  rfl


-- @@ L140-144 expanded
instance evalDistKernel.instIsSubprobabilityKernel [EvalDistSemantics m] [MeasurableSpace ρ]
    [MeasurableSpace α] (mx : ReaderT ρ m α)
    (hMeasurable : Measurable fun environment => evalDist (mx environment)) :
    IsSubprobabilityKernel (ReaderT.evalDistKernel mx hMeasurable) :=
  ⟨fun environment => evalDist_apply_univ_le_one (mx environment)⟩


-- @@ L146-152 expanded
/-- A lossless reader computation denotes a Markov kernel. -/
theorem isMarkovKernel_evalDistKernel [EvalDistSemantics m] [MeasurableSpace ρ] [MeasurableSpace α]
    (mx : ReaderT ρ m α) (hMeasurable : Measurable fun environment => evalDist (mx environment))
    (hProbability : ∀ environment, IsProbabilityMeasure (evalDist (mx environment))) :
    IsMarkovKernel (ReaderT.evalDistKernel mx hMeasurable) :=
  _root_.isMarkovKernel_evalDistKernel mx hMeasurable hProbability


-- @@ L154-154 verbatim
end ReaderT


-- @@ L156-156 verbatim
namespace StateT


-- @@ L158-158 verbatim
variable {ρ : Type u}


-- @@ L160-164 expanded
/-- A state computation denotes a kernel from initial state to result and final state. -/
noncomputable def evalDistKernel [EvalDistSemantics m] [MeasurableSpace ρ] [MeasurableSpace α]
    (mx : StateT ρ m α) (hMeasurable : Measurable fun state => evalDist (mx state)) :
    Kernel ρ (α × ρ) :=
  _root_.evalDistKernel mx hMeasurable


-- @@ L166-170 verbatim
/-- Discrete states discharge the state kernel's measurability obligation. -/
noncomputable def evalDistKernelOfDiscrete [EvalDistSemantics m]
    [MeasurableSpace ρ] [DiscreteMeasurableSpace ρ] [MeasurableSpace α]
    (mx : StateT ρ m α) : Kernel ρ (α × ρ) :=
  _root_.evalDistKernelOfDiscrete mx


-- @@ L172-176 expanded
@[simp]
theorem evalDistKernel_apply [EvalDistSemantics m] [MeasurableSpace ρ] [MeasurableSpace α]
    (mx : StateT ρ m α) (hMeasurable : Measurable fun state => evalDist (mx state)) (state : ρ) :
    StateT.evalDistKernel mx hMeasurable state = evalDist (mx state) :=
  rfl


-- @@ L178-182 expanded
instance evalDistKernel.instIsSubprobabilityKernel [EvalDistSemantics m] [MeasurableSpace ρ]
    [MeasurableSpace α] (mx : StateT ρ m α)
    (hMeasurable : Measurable fun state => evalDist (mx state)) :
    IsSubprobabilityKernel (StateT.evalDistKernel mx hMeasurable) :=
  ⟨fun state => evalDist_apply_univ_le_one (mx state)⟩


-- @@ L184-190 expanded
/-- A lossless state computation denotes a Markov kernel. -/
theorem isMarkovKernel_evalDistKernel [EvalDistSemantics m] [MeasurableSpace ρ] [MeasurableSpace α]
    (mx : StateT ρ m α) (hMeasurable : Measurable fun state => evalDist (mx state))
    (hProbability : ∀ state, IsProbabilityMeasure (evalDist (mx state))) :
    IsMarkovKernel (StateT.evalDistKernel mx hMeasurable) :=
  _root_.isMarkovKernel_evalDistKernel mx hMeasurable hProbability


-- @@ L192-200 expanded
/-- Discarding the final state is the first marginal of the state kernel. -/
theorem evalDist_run'_eq_fst [Functor m] [EvalDistSemantics m] [MeasurableSpace ρ]
    [MeasurableSpace α] (mx : StateT ρ m α)
    (hMeasurable : Measurable fun state => evalDist (mx state)) (state : ρ)
    (hMap : evalDist (Prod.fst <$> mx state) = (evalDist (mx state)).map Prod.fst) :
    evalDist (mx.run' state) = (StateT.evalDistKernel mx hMeasurable).fst state :=
  by
  change evalDist (Prod.fst <$> mx state) = (StateT.evalDistKernel mx hMeasurable).fst state
  rw [hMap, Kernel.fst_apply, StateT.evalDistKernel_apply]


-- @@ L202-202 verbatim
end StateT
