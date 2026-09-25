/-
Copyright (c) 2025 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

module
public import VCVio.EvalDist.Defs.NeverFails
public import VCVio.EvalDist.Monad.Map


-- @@ L11-15 verbatim
/-!
# Evaluation Distributions on Boolean-Valued Computations

Specialization lemmas for `MonadLiftT m SPMF` computations returning `Bool`.
-/


-- @@ L17-17 verbatim
@[expose] public section


-- @@ L19-19 verbatim
variable {m : Type _ → Type _} [Monad m] [MonadLiftT m SPMF] {α β : Type _}


-- @@ L21-25 expanded
omit [Monad m] in
@[simp, grind =]
lemma probOutput_true_add_false (mx : m Bool) :
    probOutput mx true + probOutput mx false = 1 - probFailure mx := by
  simpa using tsum_probOutput_eq_sub mx


-- @@ L27-31 expanded
omit [Monad m] in
@[simp, grind =]
lemma probOutput_false_add_true (mx : m Bool) :
    probOutput mx false + probOutput mx true = 1 - probFailure mx := by
  rw [add_comm, probOutput_true_add_false]


-- @@ L33-37 expanded
omit [Monad m] in
lemma probOutput_true_eq_sub (mx : m Bool) :
    probOutput mx true = 1 - probFailure mx - probOutput mx false :=
  by
  rw [← probOutput_true_add_false]
  exact (ENNReal.add_sub_cancel_right probOutput_ne_top).symm


-- @@ L39-43 expanded
omit [Monad m] in
lemma probOutput_false_eq_sub (mx : m Bool) :
    probOutput mx false = 1 - probFailure mx - probOutput mx true :=
  by
  rw [← probOutput_false_add_true]
  exact (ENNReal.add_sub_cancel_right probOutput_ne_top).symm


-- @@ L45-48 expanded
@[simp]
lemma probOutput_not_map [LawfulMonad m] [LawfulMonadLiftT m SPMF] (mx : m Bool) :
    probOutput ((!·) <$> mx) true = probOutput mx false :=
  probOutput_map_injective mx (fun a b h => by cases a <;> cases b <;> simp_all) false


-- @@ L50-53 expanded
@[simp]
lemma probOutput_not_map' [LawfulMonad m] [LawfulMonadLiftT m SPMF] (mx : m Bool) :
    probOutput ((!·) <$> mx) false = probOutput mx true :=
  probOutput_map_injective mx (fun a b h => by cases a <;> cases b <;> simp_all) true


-- @@ L55-57 expanded
@[grind =]
lemma probOutput_true_add_false_of_neverFail {mx : m Bool} [NeverFail mx] :
    probOutput mx true + probOutput mx false = 1 := by simp


-- @@ L59-62 expanded
omit [Monad m] in
@[grind =]
lemma probEvent_true_eq_probOutput (mx : m Bool) : probEvent mx (· = true) = probOutput mx true :=
  probEvent_eq_eq_probOutput mx true


-- @@ L64-67 expanded
omit [Monad m] in
@[grind =]
lemma probEvent_not_eq_probOutput (mx : m Bool) : probEvent mx (· = false) = probOutput mx false :=
  probEvent_eq_eq_probOutput mx false


-- @@ L69-75 expanded
lemma probOutput_true_bind_map_eq_probEvent [LawfulMonad m] [LawfulMonadLiftT m SPMF] (mx : m α)
    (my : α → m β) (p : α → β → Bool) :
    probOutput (mx >>= fun x => p x <$> my x) true =
      probEvent
        (do
          let x ← mx;
          return (x, ← my x))
        fun (x, y) => p x y :=
  by
  simp only [probOutput_bind_eq_tsum, probOutput_map_eq_tsum_ite, Bool.true_eq, bind_pure_comp,
    probEvent_bind_eq_tsum, probEvent_map]
  grind

