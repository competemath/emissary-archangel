/-
Copyright (c) 2025 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

module
public import VCVio.EvalDist.Monad.Map


-- @@ L10-17 verbatim
/-!
# Evaluation Distributions of Computations with `seq`

File for lemmas about `evalSPMF` and `support` involving the monadic `seq`, `seqLeft`,
and `seqRight` operations.

TODO: many lemmas should probably have mirrored versions for `bind_map`.
-/


-- @@ L19-19 verbatim
@[expose] public section


-- @@ L21-21 verbatim
universe u v w


-- @@ L23-23 verbatim
variable {α β γ : Type u} {m : Type u → Type v} [Monad m] [LawfulMonad m]


-- @@ L25-25 verbatim
open ENNReal


-- @@ L27-27 verbatim
section seq


-- @@ L29-29 verbatim
section support


-- @@ L31-31 verbatim
variable [MonadLiftT m SetM] [LawfulMonadLiftT m SetM]


-- @@ L33-36 verbatim
@[simp]
lemma support_seq (mf : m (α → β)) (mx : m α) :
    support (mf <*> mx) = ⋃ f ∈ support mf, f '' support mx := by
  simp [seq_eq_bind_map]


-- @@ L38-40 verbatim
lemma mem_support_seq_iff (mf : m (α → β)) (mx : m α) (y : β) :
    y ∈ support (mf <*> mx) ↔ ∃ f ∈ support mf, ∃ x ∈ support mx, f x = y := by
  simp [support_seq]


-- @@ L42-47 verbatim
@[simp]
lemma finSupport_seq [HasEvalFinset m]
    [DecidableEq (α → β)] [DecidableEq α] [DecidableEq β]
    (mf : m (α → β)) (mx : m α) :
    finSupport (mf <*> mx) = (finSupport mf).biUnion fun f => (finSupport mx).image f := by
  simp [seq_eq_bind_map]


-- @@ L49-49 verbatim
end support


-- @@ L51-51 verbatim
section spmf


-- @@ L53-53 verbatim
variable [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF]


-- @@ L55-57 expanded
@[grind norm]
lemma evalSPMF_seq (mf : m (α → β)) (mx : m α) :
    evalSPMF (mf <*> mx) = evalSPMF mf <*> evalSPMF mx := by simp [monad_norm]


-- @@ L59-63 expanded
lemma probOutput_seq_eq_tsum (mf : m (α → β)) (mx : m α) (y : β) :
    probOutput (mf <*> mx) y =
      ∑' f, ∑' x, probOutput mf f * probOutput mx x * probOutput (pure (f x) : m β) y :=
  by
  simp [seq_eq_bind_map, probOutput_bind_eq_tsum, probOutput_map_eq_tsum, ← ENNReal.tsum_mul_left,
    mul_assoc]


-- @@ L65-70 expanded
lemma probOutput_seq_eq_tsum_ite [DecidableEq β] (mf : m (α → β)) (mx : m α) (y : β) :
    probOutput (mf <*> mx) y =
      ∑' f, ∑' x, if y = f x then probOutput mf f * probOutput mx x else 0 :=
  by
  simp [seq_eq_bind_map, probOutput_bind_eq_tsum, probOutput_map_eq_tsum_ite,
    ← ENNReal.tsum_mul_left]


-- @@ L72-74 expanded
lemma probEvent_seq_eq_tsum (mf : m (α → β)) (mx : m α) (p : β → Prop) :
    probEvent (mf <*> mx) p = ∑' f, probOutput mf f * probEvent mx (p ∘ f) := by
  simp only [seq_eq_bind_map, probEvent_bind_eq_tsum, probEvent_map]


-- @@ L76-81 expanded
lemma probEvent_seq_eq_tsum_ite (mf : m (α → β)) (mx : m α) (p : β → Prop) [DecidablePred p] :
    probEvent (mf <*> mx) p =
      ∑' (f : α → β) (x : α), if p (f x) then probOutput mf f * probOutput mx x else 0 :=
  by
  simp_rw [probEvent_seq_eq_tsum, probEvent_eq_tsum_ite, ← ENNReal.tsum_mul_left,
    Function.comp_apply, mul_ite, mul_zero]


-- @@ L83-83 verbatim
variable [MonadLiftT m SetM] [EvalDistCompatible m]


-- @@ L85-89 expanded
@[simp, grind =_]
lemma probFailure_seq (mf : m (α → β)) (mx : m α) :
    probFailure (mf <*> mx) = probFailure mf + probFailure mx - probFailure mf * probFailure mx :=
  by
  rw [seq_eq_bind_map]
  exact probFailure_bind_of_const' probFailure_ne_top (fun g _ => probFailure_map mx g)


-- @@ L91-91 verbatim
end spmf


-- @@ L93-93 verbatim
end seq


-- @@ L95-95 verbatim
section seqLeft


-- @@ L97-97 verbatim
section support


-- @@ L99-99 verbatim
variable [MonadLiftT m SetM] [LawfulMonadLiftT m SetM]


-- @@ L101-104 verbatim
@[simp]
lemma support_seqLeft (mx : m α) (my : m β) [Decidable (support my).Nonempty] :
    support (mx <* my) = if (support my).Nonempty then support mx else ∅ := by
  rw [seqLeft_eq, Set.ext_iff]; aesop


-- @@ L106-106 verbatim
end support


-- @@ L108-108 verbatim
section spmf


-- @@ L110-111 verbatim
variable [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF]
  [MonadLiftT m SetM] [EvalDistCompatible m]


-- @@ L113-117 expanded
omit [MonadLiftT m SetM] [EvalDistCompatible m] in
@[grind norm]
lemma evalSPMF_seqLeft (mx : m α) (my : m β) : evalSPMF (mx <* my) = evalSPMF mx <* evalSPMF my :=
  by simp [seqLeft_eq]


-- @@ L119-127 expanded
@[simp, grind =_]
lemma probOutput_seqLeft (mx : m α) (my : m β) (x : α) :
    probOutput (mx <* my) x = (1 - probFailure my) * probOutput mx x :=
  by
  rw [seqLeft_eq, seq_eq_bind_map, map_eq_bind_pure_comp, bind_assoc]
  simp only [Function.comp_apply, pure_bind, probOutput_bind_eq_tsum]
  simp_rw [show
      ∀ a : α,
        probOutput (Function.const β a <$> my : m α) x =
          (1 - probFailure my) * probOutput (pure a : m α) x
      from fun a => probOutput_map_const my a x,
    mul_left_comm _ (1 - probFailure my)]
  rw [ENNReal.tsum_mul_left, ← probOutput_bind_eq_tsum, bind_pure]


-- @@ L129-132 expanded
@[simp, grind =_]
lemma probFailure_seqLeft (mx : m α) (my : m β) :
    probFailure (mx <* my) = probFailure mx + probFailure my - probFailure mx * probFailure my := by
  rw [seqLeft_eq, probFailure_seq, probFailure_map]


-- @@ L134-142 expanded
@[simp, grind =_]
lemma probEvent_seqLeft (mx : m α) (my : m β) (p : α → Prop) :
    probEvent (mx <* my) p = (1 - probFailure my) * probEvent mx p :=
  by
  rw [seqLeft_eq, seq_eq_bind_map, map_eq_bind_pure_comp, bind_assoc]
  simp only [Function.comp_apply, pure_bind, probEvent_bind_eq_tsum]
  simp_rw [show
      ∀ a : α,
        probEvent (Function.const β a <$> my : m α) p =
          (1 - probFailure my) * probEvent (pure a : m α) p
      from fun a => probEvent_map_const my a p,
    mul_left_comm _ (1 - probFailure my)]
  rw [ENNReal.tsum_mul_left, ← probEvent_bind_eq_tsum, bind_pure]


-- @@ L144-144 verbatim
end spmf


-- @@ L146-146 verbatim
end seqLeft


-- @@ L148-148 verbatim
section seqRight


-- @@ L150-150 verbatim
section support


-- @@ L152-152 verbatim
variable [MonadLiftT m SetM] [LawfulMonadLiftT m SetM]


-- @@ L154-157 verbatim
@[simp]
lemma support_seqRight (mx : m α) (my : m β) [Decidable (support mx).Nonempty] :
    support (mx *> my) = if (support mx).Nonempty then support my else ∅ := by
  rw [seqRight_eq, Set.ext_iff]; aesop


-- @@ L159-159 verbatim
end support


-- @@ L161-161 verbatim
section spmf


-- @@ L163-164 verbatim
variable [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF]
  [MonadLiftT m SetM] [EvalDistCompatible m]


-- @@ L166-170 expanded
omit [MonadLiftT m SetM] [EvalDistCompatible m] in
@[grind norm]
lemma evalSPMF_seqRight (mx : m α) (my : m β) : evalSPMF (mx *> my) = evalSPMF mx *> evalSPMF my :=
  by simp [seqRight_eq]


-- @@ L172-175 expanded
@[simp, grind =_]
lemma probOutput_seqRight (mx : m α) (my : m β) (y : β) :
    probOutput (mx *> my) y = (1 - probFailure mx) * probOutput my y := by
  simp [seqRight_eq, seq_eq_bind_map, probOutput_bind_const]


-- @@ L177-180 expanded
@[simp, grind =_]
lemma probFailure_seqRight (mx : m α) (my : m β) :
    probFailure (mx *> my) = probFailure mx + probFailure my - probFailure mx * probFailure my := by
  rw [seqRight_eq, probFailure_seq, probFailure_map]


-- @@ L182-185 expanded
@[simp, grind =_]
lemma probEvent_seqRight (mx : m α) (my : m β) (p : β → Prop) :
    probEvent (mx *> my) p = (1 - probFailure mx) * probEvent my p := by
  simp [seqRight_eq, seq_eq_bind_map, probEvent_bind_const]


-- @@ L187-187 verbatim
end spmf


-- @@ L189-189 verbatim
end seqRight


-- @@ L191-191 verbatim
section seq_map


-- @@ L193-193 verbatim
variable (mx : m α) (my : m β) (f : α → β → γ)


-- @@ L195-195 verbatim
section support


-- @@ L197-197 verbatim
variable [MonadLiftT m SetM] [LawfulMonadLiftT m SetM]


-- @@ L199-201 verbatim
lemma support_seq_map_eq_image2 :
    support (f <$> mx <*> my) = Set.image2 f (support mx) (support my) := by
  ext z; simp [seq_eq_bind_map, Set.mem_image2]


-- @@ L203-207 verbatim
@[simp low + 1]
lemma finSupport_seq_map_eq_image2 [HasEvalFinset m]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ] :
    finSupport (f <$> mx <*> my) = Finset.image₂ f (finSupport mx) (finSupport my) := by
  ext z; simp [seq_eq_bind_map, Finset.mem_image₂]


-- @@ L209-209 verbatim
end support


-- @@ L211-211 verbatim
section spmf


-- @@ L213-213 verbatim
variable [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF]


-- @@ L215-217 expanded
lemma evalSPMF_seq_map : evalSPMF (f <$> mx <*> my) = f <$> evalSPMF mx <*> evalSPMF my := by
  rw [evalSPMF_seq, evalSPMF_map]


-- @@ L219-223 expanded
lemma probOutput_seq_map_eq_tsum (z : γ) :
    probOutput (f <$> mx <*> my) z =
      ∑' (x : α) (y : β), probOutput mx x * probOutput my y * probOutput (pure (f x y) : m γ) z :=
  by
  simp only [monad_norm, Function.comp, probOutput_bind_eq_tsum, ← ENNReal.tsum_mul_left, mul_assoc]


-- @@ L225-228 expanded
lemma probOutput_seq_map_eq_tsum_ite [DecidableEq γ] (z : γ) :
    probOutput (f <$> mx <*> my) z =
      ∑' (x : α) (y : β), if z = f x y then probOutput mx x * probOutput my y else 0 :=
  by simp only [probOutput_seq_map_eq_tsum, probOutput_pure, mul_ite, mul_one, mul_zero]


-- @@ L230-230 verbatim
section injective2


-- @@ L232-240 expanded
lemma probOutput_seq_map_eq_mul_of_injective2 (hf : f.Injective2) (x : α) (y : β) :
    probOutput (f <$> mx <*> my) (f x y) = probOutput mx x * probOutput my y :=
  by
  rw [probOutput_seq_map_eq_tsum]
  simp only [probOutput_pure_eq_indicator, Set.indicator, mul_ite, mul_zero]
  refine (tsum_eq_single x fun x' hx' => ?_).trans ?_
  · exact ENNReal.tsum_eq_zero.mpr fun b => if_neg fun h' => hx' (hf h').1.symm
  · refine (tsum_eq_single y fun y' hy' => ?_).trans ?_
    · exact if_neg fun h' => hy' (hf h').2.symm
    · simp


-- @@ L242-242 verbatim
end injective2


-- @@ L244-244 verbatim
section swap


-- @@ L246-250 expanded
lemma probOutput_seq_map_swap (z : γ) :
    probOutput (Function.swap f <$> my <*> mx) z = probOutput (f <$> mx <*> my) z :=
  by
  simp only [probOutput_seq_map_eq_tsum, Function.swap]
  rw [ENNReal.tsum_comm]
  exact tsum_congr fun x' => tsum_congr fun y' => by ring


-- @@ L252-254 expanded
lemma evalSPMF_seq_map_swap :
    evalSPMF (Function.swap f <$> my <*> mx) = evalSPMF (f <$> mx <*> my) :=
  evalSPMF_ext (probOutput_seq_map_swap mx my f)


-- @@ L256-258 expanded
lemma probEvent_seq_map_swap (p : γ → Prop) :
    probEvent (Function.swap f <$> my <*> mx) p = probEvent (f <$> mx <*> my) p := by
  simp only [probEvent_eq_tsum_indicator, probOutput_seq_map_swap]


-- @@ L260-260 verbatim
end swap


-- @@ L262-267 expanded
lemma probEvent_seq_map_eq_probEvent_comp_uncurry (p : γ → Prop) :
    probEvent (f <$> mx <*> my) p = probEvent (Prod.mk <$> mx <*> my) (p ∘ Function.uncurry f) :=
  by
  rw [← probEvent_map]
  congr 1
  rw [map_seq, Functor.map_map]
  rfl


-- @@ L269-271 expanded
lemma probEvent_seq_map_eq_probEvent (p : γ → Prop) :
    probEvent (f <$> mx <*> my) p = probEvent (Prod.mk <$> mx <*> my) fun z => p (f z.1 z.2) :=
  probEvent_seq_map_eq_probEvent_comp_uncurry mx my f p


-- @@ L273-273 verbatim
end spmf


-- @@ L275-275 verbatim
section mixed


-- @@ L277-278 verbatim
variable [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF]
  [MonadLiftT m SetM] [LawfulMonadLiftT m SetM] [EvalDistCompatible m]


-- @@ L280-283 verbatim
omit [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF] [EvalDistCompatible m] in
lemma mem_support_seq_map_iff_of_injective2 (hf : f.Injective2) (x : α) (y : β) :
    f x y ∈ support (f <$> mx <*> my) ↔ x ∈ support mx ∧ y ∈ support my := by
  rw [support_seq_map_eq_image2, Set.mem_image2_iff hf]


-- @@ L285-290 verbatim
omit [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF] [EvalDistCompatible m] in
lemma mem_finSupport_seq_map_iff_of_injective2 [HasEvalFinset m]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (hf : f.Injective2) (x : α) (y : β) :
    f x y ∈ finSupport (f <$> mx <*> my) ↔ x ∈ finSupport mx ∧ y ∈ finSupport my := by
  rw [finSupport_seq_map_eq_image2, Finset.mem_image₂_iff hf]


-- @@ L292-295 verbatim
omit [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF] [EvalDistCompatible m] in
lemma support_seq_map_swap :
    support (Function.swap f <$> my <*> mx) = support (f <$> mx <*> my) := by
  simp only [support_seq_map_eq_image2, Set.image2_swap f]


-- @@ L297-301 verbatim
omit [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF] [EvalDistCompatible m] in
lemma finSupport_seq_map_swap [HasEvalFinset m] [DecidableEq γ] :
    finSupport (Function.swap f <$> my <*> mx) = finSupport (f <$> mx <*> my) := by
  classical
  simp only [finSupport_seq_map_eq_image2, Finset.image₂_swap f]


-- @@ L303-324 expanded
omit [LawfulMonadLiftT m SetM] in
lemma probEvent_seq_map_eq_mul (p : γ → Prop) (q1 : α → Prop) (q2 : β → Prop)
    (h : ∀ x ∈ support mx, ∀ y ∈ support my, p (f x y) ↔ q1 x ∧ q2 y) :
    probEvent (f <$> mx <*> my) p = probEvent mx q1 * probEvent my q2 := by
  classical
  rw [show f <$> mx <*> my = mx >>= fun x => f x <$> my by simp [seq_eq_bind_map]]
  rw [probEvent_bind_eq_tsum]
  simp only [probEvent_map]
  suffices hs :
    ∀ x,
      probOutput mx x * probEvent my (p ∘ f x) =
        (if q1 x then probOutput mx x else 0) * probEvent my q2
    by
    trans (∑' x, (if q1 x then probOutput mx x else 0) * probEvent my q2)
    · exact tsum_congr hs
    · rw [ENNReal.tsum_mul_right]; symm; rw [probEvent_eq_tsum_ite]
  intro x
  by_cases hx : x ∈ support mx
  · by_cases hq : q1 x
    · simp only [if_pos hq]; congr 1
      exact probEvent_ext fun y hy => (h x hx y hy).trans (by simp [hq])
    · simp only [if_neg hq, zero_mul]
      rw [probEvent_eq_zero fun y hy => by simp only [Function.comp_apply, h x hx y hy]; simp [hq],
        mul_zero]
  · simp [probOutput_eq_zero_of_not_mem_support hx]


-- @@ L326-331 expanded
omit [LawfulMonadLiftT m SetM] in
lemma probOutput_seq_map_eq_mul (x : α) (y : β) (z : γ)
    (h : ∀ x' ∈ support mx, ∀ y' ∈ support my, z = f x' y' ↔ x' = x ∧ y' = y) :
    probOutput (f <$> mx <*> my) z = probOutput mx x * probOutput my y := by
  simpa only [← probEvent_eq_eq_probOutput] using
    probEvent_seq_map_eq_mul mx my f (· = z) (· = x) (· = y) fun x' hx' y' hy' =>
      eq_comm.trans (h x' hx' y' hy')


-- @@ L333-333 verbatim
end mixed


-- @@ L335-335 verbatim
end seq_map
