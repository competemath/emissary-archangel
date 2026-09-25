/-
Copyright (c) 2025 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio.EvalDist.Defs.Basic


-- @@ L10-17 verbatim
/-!
# Denotational Semantics Over `AlternativeMonad`.

This file defines `HasEvalSet.LawfulFailure`, a type-class refining `MonadLiftT m SetM` when
given an `AlternativeMonad` instance on the base monad, enforcing that `failure` maps to the
empty sub-distribution. Compatibility conditions then force the correct semantics for `evalSPMF`,
recorded in the `*_failure` simp lemmas below.
-/


-- @@ L19-19 verbatim
@[expose] public section


-- @@ L21-21 verbatim
open ENNReal HasEvalSet


-- @@ L23-23 verbatim
universe u v w


-- @@ L25-25 verbatim
variable {m : Type u → Type v} [AlternativeMonad m] {α β γ : Type u}


-- @@ L27-32 verbatim
/-- Refinement of `MonadLiftT m SetM` when given an `AlternativeMonad` instance on the
base monad, enforcing that `failure` maps to the empty sub-distribution. Compatibility
conditions then force the correct semantics for `evalSPMF`, see below. -/
protected class HasEvalSet.LawfulFailure (m : Type u → Type v)
    [AlternativeMonad m] [MonadLiftT m SetM] : Prop where
  support_failure' {α : Type u} : support (failure : m α) = ∅


-- @@ L34-41 verbatim
/-- `failure` in `SPMF` itself has empty support, so the generic failure laws below apply to the
finite backend directly. -/
instance : HasEvalSet.LawfulFailure SPMF where
  support_failure' := by
    intro α
    ext x
    change x ∈ (failure : SPMF _).support ↔ x ∈ (∅ : Set _)
    simp [SPMF.mem_support_iff, SPMF.failure_apply]


-- @@ L43-43 verbatim
open HasEvalSet (LawfulFailure)


-- @@ L45-48 verbatim
@[simp, grind =]
lemma support_failure [MonadLiftT m SetM] [LawfulFailure m] :
    support (failure : m α) = ∅ :=
  HasEvalSet.LawfulFailure.support_failure'


-- @@ L50-52 verbatim
@[simp, grind =]
lemma finSupport_failure [MonadLiftT m SetM] [LawfulFailure m] [HasEvalFinset m]
    [DecidableEq α] : finSupport (failure : m α) = ∅ := by grind


-- @@ L54-56 expanded
@[simp, grind =]
lemma probOutput_failure [MonadLiftT m SPMF] [MonadLiftT m SetM] [EvalDistCompatible m]
    [LawfulFailure m] (x : α) : probOutput (failure : m α) x = 0 := by simp


-- @@ L58-60 expanded
@[simp, grind =]
lemma probEvent_failure [MonadLiftT m SPMF] [MonadLiftT m SetM] [EvalDistCompatible m]
    [LawfulFailure m] (p : α → Prop) : probEvent (failure : m α) p = 0 := by simp


-- @@ L62-65 expanded
@[simp, grind =]
lemma probFailure_failure [MonadLiftT m SPMF] [MonadLiftT m SetM] [EvalDistCompatible m]
    [LawfulFailure m] : probFailure (failure : m α) = 1 := by simp


-- @@ L67-69 expanded
@[simp, grind =]
lemma evalSPMF_failure [MonadLiftT m SPMF] [MonadLiftT m SetM] [EvalDistCompatible m]
    [LawfulFailure m] : evalSPMF (failure : m α) = SPMF.mk (PMF.pure none) := by simp

