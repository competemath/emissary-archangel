/-
Copyright (c) 2025 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio.EvalDist.Monad.Basic


-- @@ L10-16 verbatim
/-!
# Lemmas for Probability Over Finite Spaces

This file houses lemmas about computations with `MonadLiftT m SPMF` semantics when
`mx : m α` is defined via a binding/mapping operation over a finite type.
In particular it provides `Finset.sum` versions of many `tsum` related probability lemmas.
-/


-- @@ L18-18 verbatim
@[expose] public section


-- @@ L20-20 verbatim
universe u v w


-- @@ L22-22 verbatim
variable {α β γ : Type u} {m : Type u → Type v} [Monad m]


-- @@ L24-24 verbatim
open ENNReal


-- @@ L26-29 expanded
lemma probOutput_bind_eq_sum_fintype [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF] (mx : m α)
    (my : α → m β) [Fintype α] (y : β) :
    probOutput (mx >>= my) y = ∑ x : α, probOutput mx x * probOutput (my x) y :=
  (probOutput_bind_eq_tsum mx my y).trans (tsum_fintype _)


-- @@ L31-34 expanded
lemma probFailure_bind_eq_sum_fintype [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF] (mx : m α)
    (my : α → m β) [Fintype α] :
    probFailure (mx >>= my) = probFailure mx + ∑ x : α, probOutput mx x * probFailure (my x) :=
  (probFailure_bind_eq_add_tsum mx my).trans (congr_arg (probFailure mx + ·) <| tsum_fintype _)


-- @@ L36-39 expanded
lemma probEvent_bind_eq_sum_fintype [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF] (mx : m α)
    (my : α → m β) [Fintype α] (q : β → Prop) :
    probEvent (mx >>= my) q = ∑ x : α, probOutput mx x * probEvent (my x) q :=
  (probEvent_bind_eq_tsum mx my q).trans (tsum_fintype _)

