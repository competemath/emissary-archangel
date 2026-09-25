/-
Copyright (c) 2025 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

module
public import ToMathlib.Control.OptionT
public import VCVio.EvalDist.Defs.AlternativeMonad
public import VCVio.EvalDist.Option


-- @@ L12-18 verbatim
/-!
# Probability Distributions on Potentially Failing Computations

This file lifts `MonadLiftT _ SetM` and `MonadLiftT _ SPMF` semantics through the
`OptionT` monad transformer, providing `support`, `finSupport`, and `evalSPMF`-based
probability lemmas for `OptionT m α` in terms of the underlying `m (Option α)`.
-/


-- @@ L20-20 verbatim
@[expose] public section


-- @@ L22-22 verbatim
universe u v w


-- @@ L24-24 verbatim
variable {m : Type u → Type v} [Monad m] {α β γ : Type u}


-- @@ L26-26 verbatim
namespace OptionT


-- @@ L28-28 verbatim
section EvalSet


-- @@ L30-38 verbatim
/-- Standalone `MonadLiftT (OptionT m) SetM` instance under the weaker `[MonadLiftT m SetM]`
assumption. Keeping this standalone means `support` on `OptionT m` works without requiring a
full `MonadLiftT m SPMF` lift — only `MonadLiftT m SetM` is needed.

We declare a `MonadLiftT` (rather than `MonadLift`) so the instance has no `semiOutParam`
arguments to synthesize — `OptionT m`'s `m` cannot be recovered from the `SetM` codomain. -/
noncomputable instance instMonadLiftTSetM {m : Type u → Type v} [Monad m]
    [MonadLiftT m SetM] : MonadLiftT (OptionT m) SetM where
  monadLift mx := some ⁻¹' (support (OptionT.run mx))


-- @@ L40-58 verbatim
noncomputable instance instLawfulMonadLiftTSetM {m : Type u → Type v} [Monad m]
    [MonadLiftT m SetM] [LawfulMonadLiftT m SetM] :
    LawfulMonadLiftT (OptionT m) SetM where
  monadLift_pure mx := by
    change some ⁻¹' (support (OptionT.run (pure mx : OptionT m _))) = pure mx
    simp [Set.ext_iff]
  monadLift_bind mx my := by
    change (some ⁻¹' (support (OptionT.run (mx >>= my))) : SetM _) =
      ((some ⁻¹' (support mx.run)) >>= fun a => some ⁻¹' (support (my a).run) : SetM _)
    ext x
    simp only [Set.mem_preimage]
    rw [OptionT.run_bind, Option.elimM, mem_support_bind_iff]
    constructor
    · rintro ⟨(_ | a), ha, hx⟩
      · simp at hx
      · exact Set.mem_iUnion₂.mpr ⟨a, ha, by simpa using hx⟩
    · intro h
      obtain ⟨a, ha, hx⟩ := Set.mem_iUnion₂.mp h
      exact ⟨some a, ha, by simpa using hx⟩


-- @@ L60-60 verbatim
variable [MonadLiftT m SetM] [LawfulMonadLiftT m SetM]


-- @@ L62-64 verbatim
omit [LawfulMonadLiftT m SetM] in
@[aesop unsafe norm, grind =]
lemma support_def (mx : OptionT m α) : support mx = some ⁻¹' (support mx.run) := rfl


-- @@ L66-69 verbatim
omit [LawfulMonadLiftT m SetM] in
@[simp low]
lemma mem_support_iff (mx : OptionT m α) (x : α) :
    x ∈ support mx ↔ some x ∈ support mx.run := by grind


-- @@ L71-73 verbatim
@[simp]
lemma support_liftM (mx : m α) :
    support (liftM mx : OptionT m α) = support mx := by grind


-- @@ L75-77 verbatim
@[simp]
lemma support_lift (mx : m α) :
    support (OptionT.lift mx) = support mx := by grind


-- @@ L79-89 verbatim
/-- Peel the leading sample off the support of an `OptionT.mk`'d bind: any element of the
support of `OptionT.mk (sample >>= body)` factors through a sample `a` in the support of
`sample`, with the element in the support of `OptionT.mk (body a)`. -/
lemma mem_support_bind_mk (sample : m α) (body : α → m (Option β)) {x : β}
    (hx : x ∈ support (OptionT.mk (sample >>= body))) :
    ∃ a, a ∈ support sample ∧ x ∈ support (OptionT.mk (body a)) := by
  rw [OptionT.mem_support_iff] at hx
  simp only [OptionT.run_mk] at hx
  rw [mem_support_bind_iff] at hx
  obtain ⟨a, ha, hx⟩ := hx
  exact ⟨a, ha, by simpa [OptionT.mem_support_iff] using hx⟩


-- @@ L91-91 verbatim
end EvalSet


-- @@ L93-93 verbatim
section HasEvalFinset


-- @@ L95-99 verbatim
/-- Lift a `HasEvalFinset` instance to `OptionT`. by just taking preimage under `some`. -/
noncomputable instance (m : Type u → Type v) [Monad m] [MonadLiftT m SetM] [HasEvalFinset m] :
    HasEvalFinset (OptionT m) where
  finSupport mx := (finSupport mx.run).preimage some (by simp)
  coe_finSupport := by aesop


-- @@ L101-101 verbatim
variable [MonadLiftT m SetM] [HasEvalFinset m]


-- @@ L103-105 verbatim
@[aesop unsafe norm, grind =]
lemma finSupport_def [DecidableEq α] (mx : OptionT m α) :
    finSupport mx = (finSupport mx.run).preimage some (by simp) := rfl


-- @@ L107-110 verbatim
@[simp low]
lemma mem_finSupport_iff [DecidableEq α] (mx : OptionT m α) (x : α) :
    x ∈ finSupport mx ↔ some x ∈ finSupport mx.run := by
  simp [finSupport_def, Finset.mem_preimage]


-- @@ L112-115 verbatim
@[simp]
lemma finSupport_liftM [LawfulMonadLiftT m SetM] [LawfulMonad m] [DecidableEq α] (mx : m α) :
    finSupport (liftM mx : OptionT m α) = finSupport mx := by
  ext x; simp [mem_finSupport_iff, mem_finSupport_iff_mem_support]


-- @@ L117-120 verbatim
@[simp]
lemma finSupport_lift [LawfulMonadLiftT m SetM] [LawfulMonad m] [DecidableEq α] (mx : m α) :
    finSupport (OptionT.lift mx) = finSupport mx := by
  ext x; simp [mem_finSupport_iff, mem_finSupport_iff_mem_support]


-- @@ L122-122 verbatim
end HasEvalFinset


-- @@ L124-124 verbatim
section EvalSPMF


-- @@ L126-131 verbatim
/-- Lift a `MonadLiftT m SPMF` instance to `MonadLiftT (OptionT m) SPMF`. Failure in `OptionT`
contributes to the failure mass of the resulting `SPMF`. -/
noncomputable instance instMonadLiftTSPMF (m : Type u → Type v) [Monad m]
    [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF] :
    MonadLiftT (OptionT m) SPMF where
  monadLift x := OptionT.mapM' (MonadHom.ofLift m SPMF) x


-- @@ L133-143 verbatim
noncomputable instance instLawfulMonadLiftTSPMF (m : Type u → Type v) [Monad m]
    [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF] :
    LawfulMonadLiftT (OptionT m) SPMF where
  monadLift_pure x := by
    change OptionT.mapM' (MonadHom.ofLift m SPMF) (pure x : OptionT m _) = pure x
    simp
  monadLift_bind mx my := by
    change OptionT.mapM' (MonadHom.ofLift m SPMF) (mx >>= my) =
      OptionT.mapM' (MonadHom.ofLift m SPMF) mx >>=
        fun a => OptionT.mapM' (MonadHom.ofLift m SPMF) (my a)
    simp


-- @@ L145-149 verbatim
instance instLawfulFailure (m : Type u → Type v) [Monad m]
    [MonadLiftT m SetM] [LawfulMonadLiftT m SetM]
    [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF] :
    HasEvalSet.LawfulFailure (OptionT m) where
  support_failure' := by aesop


-- @@ L151-170 verbatim
/-- The SetM-lift of `OptionT m` (preimage of `support mx.run` under `some`) agrees with the
SPMF-lift (the `OptionT.mapM'` bind into `SPMF`) on outputs, given `EvalDistCompatible m`. -/
instance instEvalDistCompatible (m : Type u → Type v) [Monad m]
    [MonadLiftT m SetM] [LawfulMonadLiftT m SetM]
    [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF]
    [EvalDistCompatible m] :
    EvalDistCompatible (OptionT m) where
  support_eq_SPMF_support {α} mx := by
    change some ⁻¹' (SetM.run (liftM mx.run : SetM (Option α))) =
      SPMF.support ((MonadHom.ofLift m SPMF) mx.run >>=
        fun y => match y with | some a => pure a | none => failure : SPMF α)
    rw [SPMF.support_bind]
    have hbridge : SetM.run (liftM mx.run : SetM (Option α)) =
        SPMF.support ((MonadHom.ofLift m SPMF) mx.run) :=
      EvalDistCompatible.support_eq_SPMF_support mx.run
    rw [hbridge]
    ext a
    simp only [Set.mem_preimage, Set.mem_iUnion, exists_prop]
    refine ⟨fun h => ⟨some a, h, by simp⟩, ?_⟩
    rintro ⟨(_ | y), hy, ha⟩ <;> simp_all


-- @@ L172-172 verbatim
variable [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF]


-- @@ L174-175 expanded
lemma evalSPMF_eq (mx : OptionT m α) : evalSPMF mx = OptionT.mapM' (MonadHom.ofLift m SPMF) mx :=
  rfl


-- @@ L177-184 expanded
@[grind =]
lemma probOutput_eq (mx : OptionT m α) (x : α) : probOutput mx x = probOutput mx.run (some x) :=
  by
  simp only [probOutput_def, evalSPMF_eq, OptionT.mapM', SPMF.bind_apply_eq_tsum]
  refine (tsum_eq_single (some x) fun y hy => ?_).trans (by simp)
  cases y with
  | none => simp
  | some a => simp [show ¬x = a from fun h => hy (h ▸ rfl)]


-- @@ L186-190 expanded
@[grind =]
lemma probEvent_eq (mx : OptionT m α) (p : α → Prop) [DecidablePred p] :
    probEvent mx p + probOutput mx.run none = probEvent mx.run fun x => x.all p := by
  simp [probEvent_eq_tsum_indicator, probOutput_eq, tsum_option _ ENNReal.summable,
    Set.indicator_apply, add_comm]


-- @@ L192-197 expanded
@[grind =]
lemma probFailure_eq (mx : OptionT m α) :
    probFailure mx = probFailure mx.run + probOutput mx.run none := by
  simp [probFailure_def, probOutput_def, evalSPMF_eq, OptionT.mapM', SPMF.toPMF_bind, Option.elimM,
    PMF.bind_apply, tsum_option, SPMF.toPMF_failure, SPMF.toPMF_pure, SPMF.apply_eq_toPMF_some,
    evalSPMF_def]


-- @@ L199-202 expanded
@[simp, grind =]
lemma probOutput_liftM [LawfulMonad m] (mx : m α) (x : α) :
    probOutput (liftM (n := OptionT m) mx) x = probOutput mx x := by simp [probOutput_eq]


-- @@ L204-207 expanded
@[simp, grind =]
lemma probOutput_lift [LawfulMonad m] (mx : m α) (x : α) :
    probOutput (OptionT.lift mx) x = probOutput mx x :=
  probOutput_liftM mx x


-- @@ L209-212 expanded
@[simp, grind =]
lemma probEvent_liftM [LawfulMonad m] (mx : m α) (p : α → Prop) :
    probEvent (liftM (n := OptionT m) mx) p = probEvent mx p := by
  grind only [= probEvent_eq_tsum_indicator, = probOutput_liftM]


-- @@ L214-217 expanded
@[simp, grind =]
lemma probEvent_lift [LawfulMonad m] (mx : m α) (p : α → Prop) :
    probEvent (OptionT.lift mx) p = probEvent mx p :=
  probEvent_liftM mx p


-- @@ L219-222 expanded
@[simp, grind =]
lemma probFailure_liftM [LawfulMonad m] (mx : m α) :
    probFailure (liftM (n := OptionT m) mx) = probFailure mx := by simp [probFailure_eq]


-- @@ L224-227 expanded
@[simp, grind =]
lemma probFailure_lift [LawfulMonad m] (mx : m α) :
    probFailure (OptionT.lift mx) = probFailure mx :=
  probFailure_liftM mx


-- @@ L229-238 expanded
/-- Bridge lemma: when two `OptionT` computations have underlying `run`s related by an
`Option.map` of a function `f`, their probabilities for the events `P` and `P ∘ f` agree. -/
lemma probEvent_eq_of_run_map_eq [LawfulMonad m] (mx : OptionT m α) (my : OptionT m β) (f : β → α)
    (P : α → Prop) (h : mx.run = (Option.map f) <$> my.run) :
    probEvent mx P = probEvent my (P ∘ f) :=
  by
  have hmx : mx = f <$> my := by
    change mx.run = (f <$> my).run
    rw [OptionT.run_map]; exact h
  rw [hmx, probEvent_map]


-- @@ L240-240 verbatim
end EvalSPMF


-- @@ L242-242 verbatim
end OptionT
