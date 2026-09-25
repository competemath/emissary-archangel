/-
Copyright (c) 2025 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.EvalDist.Monad.Map
public import Mathlib.Control.Lawful


-- @@ L11-34 verbatim
/-!
# Evaluation Semantics for ExceptT (ErrorT)

This file provides evaluation semantics for `ExceptT ε m` computations, lifting
`MonadLiftT m PMF` to `MonadLiftT (ExceptT ε m) SPMF`.

`ExceptT ε m α` represents computations that can fail with an error of type `ε`
or succeed with a value of type `α`. The underlying type is `m (Except ε α)`.

## Main definitions

* `ExceptT.toSPMF'`: Monad homomorphism `ExceptT ε m →ᵐ SPMF` when `m` lifts into `PMF`
* Instance `MonadLiftT (ExceptT ε m) SPMF` when `[MonadLiftT m PMF] [LawfulMonadLiftT m PMF]`

## Design notes

Similar to `OptionT`, we lift `MonadLiftT m PMF` to `MonadLiftT (ExceptT ε m) SPMF` because
error cases contribute failure mass. We map:
- `Except.ok x` → probability mass at `some x`
- `Except.error e` → failure mass (mapped to `none`)

This means we only support one layer of failure. If you need nested error handling,
you'll need to work with the underlying `m (Except ε α)` type directly.
-/


-- @@ L36-36 verbatim
@[expose] public section


-- @@ L38-38 verbatim
universe u v


-- @@ L40-40 verbatim
variable {ε : Type u} {m : Type u → Type v} [Monad m] {α β γ : Type u}


-- @@ L42-42 verbatim
namespace ExceptT


-- @@ L44-44 verbatim
section EvalSet


-- @@ L46-51 verbatim
/-- Standalone `MonadLiftT (ExceptT ε m) SetM` instance under the weaker `[MonadLiftT m SetM]`
assumption. Keeping this standalone means `support` on `ExceptT ε m` works without requiring a
full `MonadLiftT m SPMF` lift — only `MonadLiftT m SetM` is needed. -/
noncomputable instance instMonadLiftTSetM (ε : Type u) (m : Type u → Type v) [Monad m]
    [MonadLiftT m SetM] : MonadLiftT (ExceptT ε m) SetM where
  monadLift mx := Except.ok ⁻¹' (support mx.run)


-- @@ L53-74 verbatim
noncomputable instance instLawfulMonadLiftTSetM (ε : Type u) (m : Type u → Type v) [Monad m]
    [MonadLiftT m SetM] [LawfulMonadLiftT m SetM] :
    LawfulMonadLiftT (ExceptT ε m) SetM where
  monadLift_pure x := by
    change Except.ok ⁻¹' (support (pure (Except.ok x) : m _)) = pure x
    ext y; simp
  monadLift_bind mx f := by
    change (Except.ok ⁻¹' (support (mx >>= f : ExceptT ε m _).run) : SetM _) =
      (Except.ok ⁻¹' (support mx.run) >>=
        fun a => Except.ok ⁻¹' support (f a).run : SetM _)
    ext x
    simp only [Set.mem_preimage]
    change Except.ok x ∈ support (mx.run >>= ExceptT.bindCont f) ↔ _
    rw [mem_support_bind_iff]
    constructor
    · rintro ⟨r, hr, hx⟩
      cases r with
      | ok a => exact Set.mem_iUnion₂.mpr ⟨a, hr, hx⟩
      | error e => simp [ExceptT.bindCont] at hx
    · intro h
      obtain ⟨a, ha, hx⟩ := Set.mem_iUnion₂.mp h
      exact ⟨.ok a, ha, hx⟩


-- @@ L76-78 verbatim
@[simp]
lemma run_liftM_eq_map_ok (mx : m α) :
    (liftM mx : ExceptT ε m α).run = Except.ok <$> mx := rfl


-- @@ L80-80 verbatim
variable [MonadLiftT m SetM]


-- @@ L82-84 verbatim
@[aesop unsafe norm, grind =]
lemma support_def (mx : ExceptT ε m α) :
    support mx = Except.ok ⁻¹' (support mx.run) := rfl


-- @@ L86-88 verbatim
@[simp low]
lemma mem_support_iff (mx : ExceptT ε m α) (x : α) :
    x ∈ support mx ↔ Except.ok x ∈ support mx.run := Iff.rfl


-- @@ L90-90 verbatim
variable [LawfulMonadLiftT m SetM]


-- @@ L92-96 verbatim
@[simp]
lemma support_liftM [LawfulMonad m] (mx : m α) :
    support (liftM mx : ExceptT ε m α) = support mx := by
  ext x
  simp [mem_support_iff]


-- @@ L98-98 verbatim
end EvalSet


-- @@ L100-100 verbatim
section EvalFinset


-- @@ L102-107 verbatim
noncomputable instance (ε : Type u) (m : Type u → Type v) [Monad m]
    [DecidableEq ε] [MonadLiftT m SetM] [LawfulMonadLiftT m SetM] [HasEvalFinset m] :
    HasEvalFinset (ExceptT ε m) where
  finSupport mx := (finSupport mx.run).preimage Except.ok
    (by intro a b; simp [Except.ok.injEq])
  coe_finSupport mx := by ext x; simp


-- @@ L109-109 verbatim
variable [DecidableEq ε] [MonadLiftT m SetM] [LawfulMonadLiftT m SetM] [HasEvalFinset m]


-- @@ L111-114 verbatim
@[aesop unsafe norm, grind =]
lemma finSupport_def [DecidableEq α] (mx : ExceptT ε m α) :
    finSupport mx = (finSupport mx.run).preimage Except.ok
      (fun a _ => by simp [Except.ok.injEq]) := rfl


-- @@ L116-120 verbatim
@[simp low]
lemma mem_finSupport_iff' [DecidableEq α] (mx : ExceptT ε m α) (x : α) :
    x ∈ finSupport mx ↔ Except.ok x ∈ finSupport mx.run := by
  rw [finSupport_def]
  exact Finset.mem_preimage


-- @@ L122-127 verbatim
@[simp]
lemma finSupport_liftM [LawfulMonad m] [DecidableEq α] (mx : m α) :
    finSupport (liftM mx : ExceptT ε m α) = finSupport mx := by
  ext x
  rw [mem_finSupport_iff', mem_finSupport_iff_mem_support, mem_finSupport_iff_mem_support]
  simp


-- @@ L129-129 verbatim
end EvalFinset


-- @@ L131-131 verbatim
section EvalSPMF


-- @@ L133-148 verbatim
/-- Monad homomorphism from `ExceptT ε m` to `SPMF`, treating errors as failure mass.
Given `mx : ExceptT ε m α`, we evaluate the underlying `m (Except ε α)` to an `SPMF`,
then route `Except.ok x` to `pure x` and `Except.error _` to `failure`. -/
noncomputable def toSPMF' [MonadLiftT m PMF] [LawfulMonadLiftT m PMF] :
    ExceptT ε m →ᵐ SPMF where
  toFun {α} (mx : ExceptT ε m α) : SPMF α :=
    (liftM mx.run : SPMF _) >>= fun r =>
      match r with
      | Except.ok x => pure x
      | Except.error _ => failure
  toFun_pure' x := by simp
  toFun_bind' mx f := by
    change (liftM (mx.run >>= ExceptT.bindCont f) : SPMF _) >>= _ = _
    simp only [liftM_bind, monad_norm]
    congr 1; funext r
    cases r <;> simp [ExceptT.bindCont, ExceptT.run]


-- @@ L150-158 verbatim
private lemma toSPMF'_apply_eq [MonadLiftT m PMF] [LawfulMonadLiftT m PMF]
    (mx : ExceptT ε m α) (x : α) :
    ExceptT.toSPMF' mx x = (liftM mx.run : SPMF _) (Except.ok x) := by
  simp only [ExceptT.toSPMF', SPMF.bind_apply_eq_tsum]
  refine (tsum_eq_single (Except.ok x) fun y hy => ?_).trans ?_
  · cases y with
    | error e => simp
    | ok a => simp [show x ≠ a from fun h => hy (h ▸ rfl)]
  · simp


-- @@ L160-165 verbatim
/-- Lift `MonadLiftT m PMF` to `MonadLiftT (ExceptT ε m) SPMF`.
Errors contribute to failure mass. -/
noncomputable instance instMonadLiftTSPMF (ε : Type u) (m : Type u → Type v) [Monad m]
    [MonadLiftT m PMF] [LawfulMonadLiftT m PMF] :
    MonadLiftT (ExceptT ε m) SPMF where
  monadLift mx := ExceptT.toSPMF' mx


-- @@ L167-171 verbatim
noncomputable instance instLawfulMonadLiftTSPMF (ε : Type u) (m : Type u → Type v) [Monad m]
    [MonadLiftT m PMF] [LawfulMonadLiftT m PMF] :
    LawfulMonadLiftT (ExceptT ε m) SPMF where
  monadLift_pure := ExceptT.toSPMF'.toFun_pure'
  monadLift_bind := ExceptT.toSPMF'.toFun_bind'


-- @@ L173-194 verbatim
/-- The successful-output support of `ExceptT ε m` agrees with the output support of its
`SPMF` semantics, provided the underlying monad has the corresponding bridge. Errors only
contribute failure mass, not successful outputs. -/
instance instEvalDistCompatible (ε : Type u) (m : Type u → Type v) [Monad m]
    [MonadLiftT m SetM] [LawfulMonadLiftT m SetM]
    [MonadLiftT m PMF] [LawfulMonadLiftT m PMF]
    [EvalDistCompatible m] :
    EvalDistCompatible (ExceptT ε m) where
  support_eq_SPMF_support {α} mx := by
    change Except.ok ⁻¹' (SetM.run (liftM mx.run : SetM (Except ε α))) =
      SPMF.support ((liftM mx.run : SPMF (Except ε α)) >>= fun r =>
        match r with | Except.ok a => pure a | Except.error _ => failure)
    rw [SPMF.support_bind]
    have hbridge : SetM.run (liftM mx.run : SetM (Except ε α)) =
        SPMF.support (liftM mx.run : SPMF (Except ε α)) :=
      EvalDistCompatible.support_eq_SPMF_support mx.run
    rw [hbridge]
    ext a
    simp only [Set.mem_preimage, Set.mem_iUnion, exists_prop]
    refine ⟨fun h => ⟨Except.ok a, h, by simp [SPMF.support_pure]⟩, ?_⟩
    rintro ⟨r, hr, ha⟩
    cases r <;> simp_all


-- @@ L196-196 verbatim
variable [MonadLiftT m PMF] [LawfulMonadLiftT m PMF]


-- @@ L198-199 expanded
lemma evalSPMF_eq (mx : ExceptT ε m α) : evalSPMF mx = ExceptT.toSPMF' mx :=
  rfl


-- @@ L201-205 expanded
@[grind =]
lemma probOutput_eq (mx : ExceptT ε m α) (x : α) :
    probOutput mx x = probOutput mx.run (Except.ok x) :=
  by
  rw [probOutput_def, probOutput_def]
  exact toSPMF'_apply_eq mx x


-- @@ L207-219 expanded
@[grind =]
lemma probFailure_eq (mx : ExceptT ε m α) :
    probFailure mx =
      probFailure mx.run +
        probEvent mx.run
          (fun r =>
            match r with
            | Except.error _ => True
            | Except.ok _ => False) :=
  by
  simp only [probFailure_def, probEvent_eq_tsum_indicator, probOutput_def]
  rw [show
      evalSPMF mx =
        ((liftM mx.run : SPMF _) >>= fun r =>
            match r with
            | Except.ok a => pure a
            | Except.error _ => failure :
          SPMF α)
      from rfl]
  simp only [SPMF.run_eq_toPMF, SPMF.toPMF_bind, Option.elimM, PMF.monad_bind_eq_bind,
    PMF.bind_apply, ENNReal.summable, tsum_option, Option.elim_none, PMF.pure_apply, ↓reduceIte,
    mul_one, Option.elim_some, evalSPMF_def, SPMF.apply_eq_toPMF_some, ne_eq, PMF.apply_ne_top,
    not_false_eq_true, add_right_inj_of_ne_top]
  refine tsum_congr fun r => ?_
  cases r <;> simp


-- @@ L221-224 expanded
lemma probOutput_liftM [LawfulMonad m] (mx : m α) (x : α) :
    probOutput (liftM mx : ExceptT ε m α) x = probOutput mx x :=
  by
  rw [probOutput_eq]
  exact probOutput_map_injective mx (fun a b h => by cases h; rfl) x


-- @@ L226-228 expanded
private lemma evalSPMF_liftM [LawfulMonad m] (mx : m α) :
    evalSPMF (liftM mx : ExceptT ε m α) = evalSPMF mx :=
  evalSPMF_ext (probOutput_liftM mx)


-- @@ L230-232 expanded
lemma probFailure_liftM [LawfulMonad m] (mx : m α) :
    probFailure (liftM mx : ExceptT ε m α) = probFailure mx := by
  simp only [probFailure_def, evalSPMF_liftM]


-- @@ L234-236 expanded
lemma probEvent_liftM [LawfulMonad m] (mx : m α) (p : α → Prop) :
    probEvent (liftM mx : ExceptT ε m α) p = probEvent mx p := by
  simp [probEvent_def, evalSPMF_liftM]


-- @@ L238-238 verbatim
end EvalSPMF


-- @@ L240-240 verbatim
end ExceptT
