/-
Copyright (c) 2025 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio.EvalDist.Monad.Basic


-- @@ L10-21 verbatim
/-!
# Evaluation Distributions of Computations with `map`

File for lemmas about `evalSPMF` and `support` involving the monadic `map`.

Note: we focus on lemmas that don't hold naively when reducing `<$>` to `>>=` using monad laws,
since `map_eq_bind_pure_comp` can be applied to use `bind` lemmas fairly easily.
Instead we focus on the cases like `f <$> mx` for injective `f`, which allow stronger statements.
More generally we can consier `f` with `InjOn f (support mx)` and get good lemmas.

TODO: many lemmas should probably have mirrored `bind_pure` versions.
-/


-- @@ L23-23 verbatim
@[expose] public section


-- @@ L25-25 verbatim
universe u v w


-- @@ L27-27 verbatim
variable {α β γ : Type u} {m : Type u → Type v} [Monad m]


-- @@ L29-29 verbatim
open ENNReal


-- @@ L31-35 verbatim
@[simp, grind =]
lemma support_map [MonadLiftT m SetM] [LawfulMonadLiftT m SetM] [LawfulMonad m]
    (f : α → β) (mx : m α) :
    support (f <$> mx) = f '' support mx := by
  aesop (add simp monad_norm)


-- @@ L37-41 verbatim
@[simp, grind =]
lemma finSupport_map [MonadLiftT m SetM] [LawfulMonadLiftT m SetM] [HasEvalFinset m] [LawfulMonad m]
    [DecidableEq α] [DecidableEq β]
    (f : α → β) (mx : m α) : finSupport (f <$> mx) = (finSupport mx).image f := by
  grind [map_eq_bind_pure_comp]


-- @@ L43-46 expanded
@[grind =]
lemma evalSPMF_map [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF] [LawfulMonad m] (mx : m α)
    (f : α → β) : evalSPMF (f <$> mx) = f <$> (evalSPMF mx) := by simp [monad_norm]


-- @@ L48-51 expanded
lemma evalSPMF_map_eq_of_evalSPMF_eq [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF] [LawfulMonad m]
    {mx my : m α} (h : evalSPMF mx = evalSPMF my) (f : α → β) :
    evalSPMF (f <$> mx) = evalSPMF (f <$> my) := by
  simpa [evalSPMF_map] using congrArg (fun p => f <$> p) h


-- @@ L53-56 expanded
lemma probOutput_map_eq_of_evalSPMF_eq [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF] [LawfulMonad m]
    {mx my : m α} (h : evalSPMF mx = evalSPMF my) (f : α → β) (y : β) :
    probOutput (f <$> mx) y = probOutput (f <$> my) y :=
  evalSPMF_ext_iff.mp (evalSPMF_map_eq_of_evalSPMF_eq h f) y


-- @@ L58-60 expanded
@[simp]
lemma evalSPMF_comp_map [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF] [LawfulMonad m] (mx : m α) :
    evalSPMF ∘ (fun f => f <$> mx) = fun f : (α → β) => f <$> evalSPMF mx := by aesop


-- @@ L62-62 verbatim
variable [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF] (mx : m α) (f : α → β)


-- @@ L64-69 expanded
@[simp, grind =]
lemma probEvent_bind_pure_comp (q : β → Prop) :
    probEvent (mx >>= pure ∘ f) q = probEvent mx (q ∘ f) :=
  by
  have := Classical.decPred q
  rw [probEvent_bind_eq_tsum, probEvent_eq_tsum_ite]
  simp only [Function.comp_apply, probEvent_pure, mul_ite, mul_one, mul_zero]


-- @@ L71-71 verbatim
variable [LawfulMonad m]


-- @@ L73-84 expanded
/-- Write the probability of an output after mapping the result of a computation as a sum
over all outputs such that they map to the correct final output, using subtypes.
This lemma notably doesn't require decidable equality on the final type, unlike most
lemmas about probability when mapping a computation. -/
lemma probOutput_map_eq_tsum_subtype [MonadLiftT m SetM] [LawfulMonadLiftT m SetM]
    [EvalDistCompatible m] (y : β) :
    probOutput (f <$> mx) y = ∑' x : {x ∈ support mx | y = f x}, probOutput mx x :=
  by
  simp only [map_eq_bind_pure_comp, tsum_subtype _, probOutput_bind_eq_tsum, Function.comp_apply,
    Set.indicator, Set.mem_ofPred_eq]
  refine tsum_congr fun x => ?_
  by_cases hy : y = f x <;> by_cases hx : x ∈ support mx <;>
    simp [hy, hx, probOutput_eq_zero_of_not_mem_support]


-- @@ L86-88 expanded
lemma probOutput_map_eq_tsum (y : β) :
    probOutput (f <$> mx) y = ∑' x, probOutput mx x * probOutput (pure (f x) : m β) y := by
  simp [monad_norm, probOutput_bind_eq_tsum]


-- @@ L90-94 expanded
lemma probOutput_map_eq_tsum_subtype_ite [MonadLiftT m SetM] [LawfulMonadLiftT m SetM]
    [EvalDistCompatible m] [DecidableEq β] (y : β) :
    probOutput (f <$> mx) y = ∑' x : support mx, if y = f x then probOutput mx x else 0 := by
  simp only [map_eq_bind_pure_comp, probOutput_bind_eq_tsum_subtype, Function.comp_apply,
    probOutput_pure, mul_ite, mul_one, mul_zero]


-- @@ L96-100 expanded
@[grind =]
lemma probOutput_map_eq_tsum_ite [DecidableEq β] (y : β) :
    probOutput (f <$> mx) y = ∑' x : α, if y = f x then probOutput mx x else 0 := by
  simp only [map_eq_bind_pure_comp, probOutput_bind_eq_tsum, Function.comp_apply, probOutput_pure,
    mul_ite, mul_one, mul_zero]


-- @@ L102-106 expanded
@[grind =]
lemma probOutput_map_eq_sum_fintype_ite [Fintype α] [DecidableEq β] (y : β) :
    probOutput (f <$> mx) y = ∑ x : α, if y = f x then probOutput mx x else 0 :=
  (probOutput_map_eq_tsum_ite mx f y).trans
    (tsum_eq_sum' <| by simp only [Finset.coe_univ, Set.subset_univ])


-- @@ L108-115 expanded
@[grind =]
lemma probOutput_map_eq_sum_finSupport_ite [MonadLiftT m SetM] [LawfulMonadLiftT m SetM]
    [EvalDistCompatible m] [HasEvalFinset m] [DecidableEq α] [DecidableEq β] (y : β) :
    probOutput (f <$> mx) y = ∑ x ∈ finSupport mx, if y = f x then probOutput mx x else 0 :=
  (probOutput_map_eq_tsum_ite mx f y).trans
    (tsum_eq_sum' <| by
      simp only [coe_finSupport, Function.support_subset_iff, ne_eq, ite_eq_right_iff,
        probOutput_eq_zero_iff', mem_finSupport_iff_mem_support, Classical.not_imp, not_not,
        and_imp, imp_self, implies_true])


-- @@ L117-121 expanded
@[grind =]
lemma probOutput_map_eq_sum_filter_finSupport [MonadLiftT m SetM] [LawfulMonadLiftT m SetM]
    [EvalDistCompatible m] [HasEvalFinset m] [DecidableEq α] [DecidableEq β] (y : β) :
    probOutput (f <$> mx) y = ∑ x ∈ (finSupport mx).filter (y = f ·), probOutput mx x := by
  rw [Finset.sum_filter, probOutput_map_eq_sum_finSupport_ite]


-- @@ L123-125 expanded
@[simp, grind =]
lemma probFailure_map : probFailure (f <$> mx) = probFailure mx := by
  simp [monad_norm, probFailure_bind_eq_add_tsum]


-- @@ L127-129 expanded
@[simp, grind =]
lemma probEvent_map (q : β → Prop) : probEvent (f <$> mx) q = probEvent mx (q ∘ f) := by
  grind [= map_eq_bind_pure_comp]


-- @@ L131-139 expanded
/-- Outcome probability of a `map`, as a pulled-back event: `Pr[= y | f <$> mx]` is the probability
that the source lands in the `f`-preimage of `y`. The `probOutput` companion to `probEvent_map`.
Tagged `@[grind =]` only (not `@[simp]`): `simp` keeps its injective/equiv-map normal forms
(`probOutput_map_equiv`, `…_eq_probOutput_inverse`), which this pulled-back-event form would clash
with. -/
@[grind =]
lemma probOutput_map (y : β) : probOutput (f <$> mx) y = probEvent mx fun x => f x = y :=
  by
  rw [← probEvent_eq_eq_probOutput]
  simpa only [Function.comp_def] using probEvent_map mx f (· = y)


-- @@ L141-142 expanded
lemma probEvent_comp (q : β → Prop) : probEvent mx (q ∘ f) = probEvent (f <$> mx) q :=
  symm <| probEvent_map mx f q


-- @@ L144-146 expanded
lemma probFailure_eq_sub_sum_probOutput_map [Fintype β] (mx : m α) (f : α → β) :
    probFailure mx = 1 - ∑ y : β, probOutput (f <$> mx) y := by
  rw [← probFailure_map (f := f), probFailure_eq_sub_tsum, tsum_fintype]


-- @@ L148-159 expanded
@[aesop unsafe apply]
lemma probOutput_map_eq_single [MonadLiftT m SetM] [LawfulMonadLiftT m SetM] [EvalDistCompatible m]
    {mx : m α} {f : α → β} {y : β} (x : α) (h : ∀ x' ∈ support mx, y = f x' → x = x')
    (h' : f x = y) : probOutput (f <$> mx) y = probOutput mx x :=
  by
  rw [probOutput_map_eq_tsum]
  refine (tsum_eq_single x fun x' hx' => ?_).trans (by rw [h', probOutput_pure_self, mul_one])
  specialize h x'
  by_cases hx' : x' ∈ support mx
  · simp only [mul_eq_zero]
    aesop
  · simp [probOutput_eq_zero_of_not_mem_support hx']


-- @@ L161-161 verbatim
section const


-- @@ L163-163 verbatim
variable (mx : m α) (y : β)


-- @@ L165-170 verbatim
omit [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF] in
@[aesop safe norm, grind .]
lemma support_map_const [MonadLiftT m SetM] [LawfulMonadLiftT m SetM]
    (hx : (support mx).Nonempty) :
    support ((fun _ => y) <$> mx) = {y} := by
  aesop


-- @@ L172-178 verbatim
omit [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF] in
@[grind .]
lemma finSupport_map_const [MonadLiftT m SetM] [LawfulMonadLiftT m SetM]
    [DecidableEq α] [DecidableEq β] [HasEvalFinset m]
    (hx : (finSupport mx).Nonempty) : finSupport ((fun _ => y) <$> mx) =
      if (finSupport mx).Nonempty then {y} else ∅ := by
  grind


-- @@ L180-184 expanded
@[simp, aesop safe norm, grind =_]
lemma probOutput_map_const [MonadLiftT m SetM] [EvalDistCompatible m] (y' : β) :
    probOutput ((fun _ => y) <$> mx) y' = (1 - probFailure mx) * probOutput (pure y : m β) y' := by
  simp only [monad_norm, Function.comp_def, probOutput_bind_const]


-- @@ L186-190 expanded
@[aesop safe norm, grind =_]
lemma probEvent_map_const [MonadLiftT m SetM] [EvalDistCompatible m] (p : β → Prop) :
    probEvent ((fun _ => y) <$> mx) p = (1 - probFailure mx) * probEvent (pure y : m β) p := by
  simp only [monad_norm, Function.comp_def, probEvent_bind_const]


-- @@ L192-197 expanded
@[aesop safe norm]
lemma probEvent_map_const' [MonadLiftT m SetM] [EvalDistCompatible m] (p : β → Prop)
    [DecidablePred p] :
    probEvent ((fun _ => y) <$> mx) p = if p y then (1 - probFailure mx) else 0 := by
  simp [Function.comp_def]


-- @@ L199-199 verbatim
end const


-- @@ L201-201 verbatim
section inverse


-- @@ L203-204 verbatim
variable [MonadLiftT m SetM] [LawfulMonadLiftT m SetM] [EvalDistCompatible m]
  {f : α → β} {g : β → α} {y : β}


-- @@ L206-215 expanded
@[aesop unsafe norm]
lemma probOutput_map_eq_probOutput_of_leftInvOn (hr : Set.LeftInvOn g f (support mx))
    (hy : f (g y) = y) : probOutput (f <$> mx) y = probOutput mx (g y) :=
  by
  rw [probOutput_map_eq_tsum]
  refine (tsum_eq_single (g y) fun x hx => ?_).trans (by aesop)
  by_cases hx : x ∈ support mx
  · specialize hr hx
    aesop
  · aesop


-- @@ L217-219 expanded
lemma probOutput_map_eq_probOutput_inverse (hl : Function.LeftInverse g f) (hy : f (g y) = y) :
    probOutput (f <$> mx) y = probOutput mx (g y) := by aesop


-- @@ L221-223 expanded
lemma probOutput_map_eq_probOutput_apply (hl : f (g y) = y) (hr : ∀ y, g (f y) = y) :
    probOutput (f <$> mx) y = probOutput mx (g y) := by aesop


-- @@ L225-227 expanded
@[simp, grind =]
lemma probOutput_map_equiv (e : α ≃ β) (mx : m α) (y : β) :
    probOutput (e <$> mx) y = probOutput mx (e.symm y) := by aesop


-- @@ L229-229 verbatim
end inverse


-- @@ L231-231 verbatim
section injective


-- @@ L233-241 expanded
@[grind .]
lemma probOutput_map_injective (mx : m α) {f : α → β} (hf : f.Injective) (x : α) :
    probOutput (f <$> mx) (f x) = probOutput mx x := by
  classical
  rw [map_eq_bind_pure_comp, probOutput_bind_eq_tsum]
  refine
    (tsum_eq_single x fun y hy => ?_).trans
      (by simp only [Function.comp_apply, probOutput_pure_self, mul_one])
  simp only [Function.comp_apply, probOutput_pure, mul_ite, mul_one, mul_zero]
  exact if_neg fun h => hy (hf h.symm)


-- @@ L243-246 expanded
lemma probOutput_map_eq_probOutput (mx : m α) {f : α → β} (hf : ∀ x x', f x = f x' → x = x')
    (x : α) : probOutput (f <$> mx) (f x) = probOutput mx x :=
  probOutput_map_injective mx hf x


-- @@ L248-248 verbatim
section support


-- @@ L250-250 verbatim
variable [MonadLiftT m SetM] [LawfulMonadLiftT m SetM] [EvalDistCompatible m]


-- @@ L252-263 expanded
@[aesop unsafe norm]
lemma probOutput_map_eq_probOutput_invFunOn [Nonempty α] (mx : m α) {f : α → β}
    (hf : Set.InjOn f (support mx)) (y : β) (hy : ∃ x ∈ support mx, f x = y) :
    probOutput (f <$> mx) y = probOutput mx (Function.invFunOn f (support mx) y) :=
  by
  rw [probOutput_map_eq_probOutput_of_leftInvOn]
  · intro x hx
    have h : ∃ y ∈ support mx, f y = f x := ⟨x, hx, rfl⟩
    specialize hf (Classical.choose_spec h).1 hx (Classical.choose_spec h).2
    rw [Function.invFunOn]
    aesop
  rw [Function.invFunOn, dif_pos hy, (Classical.choose_spec hy).2]


-- @@ L265-265 verbatim
end support


-- @@ L267-267 verbatim
end injective
