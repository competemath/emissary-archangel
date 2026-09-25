/-
Copyright (c) 2025 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

module
public import VCVio.EvalDist.Defs.Basic
public import ToMathlib.Data.ENNReal.Gauss


-- @@ L11-15 verbatim
/-!
# Evaluation Distributions of Computations with `Bind`

File for lemmas about `evalSPMF` and `support` involving the monadic `pure` and `bind`.
-/


-- @@ L17-17 verbatim
@[expose] public section


-- @@ L19-19 verbatim
universe u v w


-- @@ L21-21 verbatim
variable {α β γ : Type u} {m : Type u → Type v} [Monad m]


-- @@ L23-34 verbatim
open ENNReal OracleComp.EvalDist

/- The monad/functor laws are confluent (terminating) rewrites. Tagging them for `grind` lets it
normalize a computation's structure (`mx >>= pure = mx`, reassociation, `f <$> pure a = pure (f a)`)
*before* it falls into `probOutput`/`tsum` expansion — turning what would otherwise be a `grind`
explosion on a structured-computation equality into a quick solve. `pure_bind` is not listed: core
already ships it in the default set (`attribute [grind <=] pure_bind` in `Init.Control.Lawful`),
and re-tagging it would add a redundant E-match entry. (The analogous
`bind_pure_comp`/`map_eq_bind` laws are deliberately omitted: their function argument sits under a
binder that `grind`'s pattern compiler cannot index; so do `pure_seq`/`seq_pure`, whose `Seq.seq`
thunk argument makes even their LHS an invalid pattern. `Functor.map_map` is binder-free and joins
the set.) -/

-- @@ L35-35 verbatim
attribute [grind =] bind_pure bind_assoc map_pure Functor.map_map


-- @@ L37-37 verbatim
/-! ## Probabilities of `pure` -/


-- @@ L39-39 verbatim
section pure


-- @@ L41-42 verbatim
@[simp, grind =] lemma support_pure [MonadLiftT m SetM] [LawfulMonadLiftT m SetM] (x : α) :
    support (pure x : m α) = {x} := monadLift_pure x


-- @@ L44-45 verbatim
lemma mem_support_pure_iff [MonadLiftT m SetM] [LawfulMonadLiftT m SetM] (x y : α) :
    x ∈ support (pure y : m α) ↔ x = y := by grind

-- @@ L46-47 verbatim
lemma mem_support_pure_iff' [MonadLiftT m SetM] [LawfulMonadLiftT m SetM] (x y : α) :
    x ∈ support (pure y : m α) ↔ y = x := by aesop


-- @@ L49-53 verbatim
/-- `obtain`-friendly forward direction of `mem_support_pure_iff`: membership in the support
of a `pure` forces equality with the pure value. -/
lemma eq_of_mem_support_pure [MonadLiftT m SetM] [LawfulMonadLiftT m SetM]
    {x y : α} (h : y ∈ support (pure x : m α)) : y = x := by
  simpa [mem_support_pure_iff] using h


-- @@ L55-57 verbatim
@[simp, grind =]
lemma finSupport_pure [MonadLiftT m SetM] [LawfulMonadLiftT m SetM] [HasEvalFinset m]
    [DecidableEq α] (x : α) : finSupport (pure x : m α) = {x} := by aesop


-- @@ L59-60 verbatim
lemma mem_finSupport_pure_iff [MonadLiftT m SetM] [LawfulMonadLiftT m SetM] [HasEvalFinset m]
    [DecidableEq α] (x y : α) : x ∈ finSupport (pure y : m α) ↔ x = y := by grind

-- @@ L61-62 verbatim
lemma mem_finSupport_pure_iff' [MonadLiftT m SetM] [LawfulMonadLiftT m SetM] [HasEvalFinset m]
    [DecidableEq α] (x y : α) : x ∈ finSupport (pure y : m α) ↔ y = x := by aesop


-- @@ L64-66 expanded
@[grind =, game_rule]
lemma evalSPMF_pure [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF] {α : Type u} (x : α) :
    evalSPMF (pure x : m α) = pure x := by simp [evalSPMF]


-- @@ L68-70 verbatim
@[simp]
lemma evalSPMF_comp_pure [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF] :
    evalSPMF ∘ (pure : α → m α) = pure := by aesop


-- @@ L72-74 verbatim
@[simp]
lemma evalSPMF_comp_pure' [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF] (f : α → β) :
    evalSPMF ∘ (pure : β → m β) ∘ f = pure ∘ f := by grind


-- @@ L76-79 expanded
@[simp, grind =, game_rule]
lemma probOutput_pure [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF] [DecidableEq α] (x y : α) :
    probOutput (pure y : m α) x = if x = y then 1 else 0 := by
  aesop  (rule_sets := [UnfoldEvalDist])


-- @@ L81-84 expanded
@[simp, grind =]
lemma probOutput_pure_self [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF] (x : α) :
    probOutput (pure x : m α) x = 1 := by aesop  (rule_sets := [UnfoldEvalDist])


-- @@ L86-94 expanded
/-- Boolean monotonicity of `pure` outcome probability into a disjunction: if `win` implies
`inner ∨ outer`, then the probability of outcome `true` under `pure win` is bounded by the sum of
the probabilities under `pure inner` and `pure outer`. -/
lemma probOutput_pure_bool_le_or {m : Type → Type} [Monad m] [MonadLiftT m SPMF]
    [LawfulMonadLiftT m SPMF] (win inner outer : Bool)
    (h : win = true → inner = true ∨ outer = true) :
    probOutput (pure win : m Bool) true ≤
      probOutput (pure inner : m Bool) true + probOutput (pure outer : m Bool) true :=
  by cases win <;> cases inner <;> cases outer <;> simp_all


-- @@ L96-102 expanded
/-- Boolean monotonicity of `pure` outcome probability: if `b₁` implies `b₂`, then the probability
of outcome `true` under `pure b₁` is bounded by that under `pure b₂`. -/
lemma probOutput_pure_bool_le {m : Type → Type} [Monad m] [MonadLiftT m SPMF]
    [LawfulMonadLiftT m SPMF] (b₁ b₂ : Bool) (h : b₁ = true → b₂ = true) :
    probOutput (pure b₁ : m Bool) true ≤ probOutput (pure b₂ : m Bool) true := by
  simpa using probOutput_pure_bool_le_or (m := m) b₁ b₂ false (fun hw => Or.inl (h hw))


-- @@ L104-108 expanded
/-- Fallback when we don't have decidable equality. -/
@[grind =]
lemma probOutput_pure_eq_indicator [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF] (x y : α) :
    probOutput (pure y : m α) x = Set.indicator { y } (Function.const α 1) x := by
  aesop  (rule_sets := [UnfoldEvalDist])


-- @@ L110-114 expanded
@[simp, grind =]
lemma probEvent_pure [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF] (x : α) (p : α → Prop)
    [DecidablePred p] : probEvent (pure x : m α) p = if p x then 1 else 0 := by
  aesop  (rule_sets := [UnfoldEvalDist])


-- @@ L116-121 expanded
/-- Fallback when we don't have decidable equality. -/
@[grind =]
lemma probEvent_pure_eq_indicator [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF] (x : α)
    (p : α → Prop) : probEvent (pure x : m α) p = Set.indicator {x | p x} (Function.const α 1) x :=
  by aesop  (rule_sets := [UnfoldEvalDist])


-- @@ L123-125 expanded
@[simp, grind =]
lemma probFailure_pure [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF] (x : α) :
    probFailure (pure x : m α) = 0 := by aesop  (rule_sets := [UnfoldEvalDist])


-- @@ L127-130 expanded
@[simp]
lemma tsum_probOutput_pure [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF] (x : α) :
    ∑' y : α, probOutput (pure x : m α) y = 1 := by have : DecidableEq α := Classical.decEq α; simp


-- @@ L132-135 expanded
@[simp]
lemma tsum_probOutput_pure' [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF] (x : α) :
    ∑' y : α, probOutput (pure y : m α) x = 1 := by have : DecidableEq α := Classical.decEq α; simp


-- @@ L137-140 expanded
@[simp]
lemma sum_probOutput_pure [Fintype α] [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF] (x : α) :
    ∑ y : α, probOutput (pure x : m α) y = 1 := by have : DecidableEq α := Classical.decEq α; simp


-- @@ L142-145 expanded
@[simp]
lemma sum_probOutput_pure' [Fintype α] [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF] (x : α) :
    ∑ y : α, probOutput (pure y : m α) x = 1 := by have : DecidableEq α := Classical.decEq α; simp


-- @@ L147-147 verbatim
end pure


-- @@ L149-149 verbatim
/-! ## Probabilities of `bind` -/


-- @@ L151-151 verbatim
section bind


-- @@ L153-156 verbatim
@[simp, grind =]
lemma support_bind [MonadLiftT m SetM] [LawfulMonadLiftT m SetM] (mx : m α) (my : α → m β) :
    support (mx >>= my) = ⋃ x ∈ support mx, support (my x) :=
  monadLift_bind mx my


-- @@ L158-161 verbatim
@[grind =]
lemma mem_support_bind_iff [MonadLiftT m SetM] [LawfulMonadLiftT m SetM] (mx : m α)
    (my : α → m β) (y : β) :
    y ∈ support (mx >>= my) ↔ ∃ x ∈ support mx, y ∈ support (my x) := by simp


-- @@ L163-168 verbatim
/-- `obtain`-friendly forward direction of `mem_support_bind_iff`: peel an element of the
support of a bind into a witness for the first computation and membership for the second. -/
lemma support_bind_exists [MonadLiftT m SetM] [LawfulMonadLiftT m SetM]
    {x : m α} {f : α → m β} {y : β}
    (hy : y ∈ support (x >>= f)) : ∃ a, a ∈ support x ∧ y ∈ support (f a) := by
  simpa [mem_support_bind_iff] using hy


-- @@ L170-173 verbatim
@[simp, grind =]
lemma finSupport_bind [MonadLiftT m SetM] [LawfulMonadLiftT m SetM] [HasEvalFinset m]
    [DecidableEq α] [DecidableEq β] (mx : m α) (my : α → m β) : finSupport (mx >>= my) =
      Finset.biUnion (finSupport mx) fun x => finSupport (my x) := by aesop


-- @@ L175-178 verbatim
@[grind =]
lemma mem_finSupport_bind_iff [MonadLiftT m SetM] [LawfulMonadLiftT m SetM] [HasEvalFinset m]
    [DecidableEq α] [DecidableEq β] (mx : m α) (my : α → m β) (y : β) : y ∈ finSupport (mx >>= my) ↔
      ∃ x ∈ finSupport mx, y ∈ finSupport (my x) := by aesop


-- @@ L180-183 expanded
@[grind =, game_rule]
lemma evalSPMF_bind [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF] (mx : m α) (my : α → m β) :
    evalSPMF (mx >>= my) = evalSPMF mx >>= fun x => evalSPMF (my x) :=
  monadLift_bind mx my


-- @@ L185-188 expanded
lemma evalSPMF_bind_of_support_eq_empty [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF]
    [MonadLiftT m SetM] [EvalDistCompatible m] (mx : m α) (my : α → m β) (h : support mx = ∅) :
    evalSPMF (mx >>= my) = failure := by simp [SPMF.ext_iff, ← probOutput_def, h]


-- @@ L190-190 verbatim
section bind_tsum


-- @@ L192-192 verbatim
variable [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF]


-- @@ L194-198 expanded
@[grind =, game_rule]
lemma probOutput_bind_eq_tsum (mx : m α) (my : α → m β) (y : β) :
    probOutput (mx >>= my) y = ∑' x : α, probOutput mx x * probOutput (my x) y := by
  simp [probOutput_def]


-- @@ L200-207 expanded
@[grind =]
lemma probEvent_bind_eq_tsum (mx : m α) (my : α → m β) (q : β → Prop) :
    probEvent (mx >>= my) q = ∑' x : α, probOutput mx x * probEvent (my x) q :=
  by
  simp only [probEvent_eq_tsum_indicator, Set.indicator, Set.mem_ofPred_eq, probOutput_bind_eq_tsum,
    ← ENNReal.tsum_mul_left, mul_ite, mul_zero]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun x => by split_ifs <;> simp


-- @@ L209-214 expanded
/-- `probOutput_bind_eq_tsum` with the sum packaged as an `expectedValue`, the head `gcongr`
descends through. -/
lemma probOutput_bind_eq_expectedValue (mx : m α) (my : α → m β) (y : β) :
    probOutput (mx >>= my) y = expectedValue mx fun x => probOutput (my x) y :=
  probOutput_bind_eq_tsum mx my y


-- @@ L216-220 expanded
/-- `probEvent_bind_eq_tsum` with the sum packaged as an `expectedValue`. -/
lemma probEvent_bind_eq_expectedValue (mx : m α) (my : α → m β) (q : β → Prop) :
    probEvent (mx >>= my) q = expectedValue mx fun x => probEvent (my x) q :=
  probEvent_bind_eq_tsum mx my q


-- @@ L222-222 verbatim
end bind_tsum


-- @@ L224-229 expanded
@[grind =]
lemma probFailure_bind_eq_add_tsum [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF] (mx : m α)
    (my : α → m β) :
    probFailure (mx >>= my) = probFailure mx + ∑' x : α, probOutput mx x * probFailure (my x) := by
  simp [probFailure_def, Option.elimM, tsum_option, probOutput_def, SPMF.apply_eq_toPMF_some]


-- @@ L231-242 expanded
@[grind =]
lemma probFailure_bind_eq_add_tsum_support [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF]
    [MonadLiftT m SetM] [EvalDistCompatible m] (mx : m α) (my : α → m β) :
    probFailure (mx >>= my) =
      probFailure mx + ∑' x : support mx, probOutput mx x * probFailure (my x) :=
  by
  rw [probFailure_bind_eq_add_tsum]
  congr 1
  rw [tsum_subtype (support mx) fun x => probOutput mx x * probFailure (my x)]
  refine tsum_congr fun x => ?_
  aesop
     (add simp Set.indicator)
      -- `grind`-safe in isolation: this support-quantifier characterization saturates `grind` only in
      -- combination with the `probEvent_eq_one_iff` family (kept `simp`-only). See `probability.md`.


-- @@ L243-247 expanded
@[simp, grind =]
lemma probFailure_bind_eq_zero_iff [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF] [MonadLiftT m SetM]
    [EvalDistCompatible m] (mx : m α) (my : α → m β) :
    probFailure (mx >>= my) = 0 ↔ probFailure mx = 0 ∧ ∀ x ∈ support mx, probFailure (my x) = 0 :=
  by simp [probFailure_bind_eq_add_tsum, or_iff_not_imp_left]


-- @@ L249-258 expanded
/-- Version of `probOutput_bind_eq_tsum` that sums only over the subtype given by the support
of the first computation. This can be useful to avoid looking at edge cases that can't actually
happen in practice after the first computation. A common example is if the first computation
does some error handling to avoids returning malformed outputs. -/
lemma probOutput_bind_eq_tsum_subtype [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF]
    [MonadLiftT m SetM] [EvalDistCompatible m] (mx : m α) (my : α → m β) (y : β) :
    probOutput (mx >>= my) y = ∑' x : support mx, probOutput mx x * probOutput (my x) y :=
  by
  rw [tsum_subtype _ (fun x => probOutput mx x * probOutput (my x) y), probOutput_bind_eq_tsum]
  refine tsum_congr (fun x => ?_)
  by_cases hx : x ∈ support mx <;> aesop


-- @@ L260-265 expanded
lemma probEvent_bind_eq_tsum_subtype [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF]
    [MonadLiftT m SetM] [EvalDistCompatible m] (mx : m α) (my : α → m β) (q : β → Prop) :
    probEvent (mx >>= my) q = ∑' x : support mx, probOutput mx x * probEvent (my x) q :=
  by
  rw [tsum_subtype _ (fun x ↦ probOutput mx x * probEvent (my x) q), probEvent_bind_eq_tsum]
  refine tsum_congr (fun x ↦ ?_)
  by_cases hx : x ∈ support mx <;> aesop


-- @@ L267-275 expanded
/-- If `Pr[q | my x] ≤ ε` for every `x` in the support of `mx`, then the bound also
holds for the bind. -/
lemma probEvent_bind_le_of_forall_le [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF]
    [MonadLiftT m SetM] [EvalDistCompatible m] {mx : m α} {my : α → m β} {q : β → Prop}
    {ε : ENNReal} (h : ∀ x ∈ support mx, probEvent (my x) q ≤ ε) : probEvent (mx >>= my) q ≤ ε :=
  by
  rw [probEvent_bind_eq_expectedValue]
  exact expectedValue_le_of_support h


-- @@ L277-290 expanded
/-- If the continuation can satisfy `q` only after a support point satisfying `p`,
then the probability of `q` after the bind is at most the probability of `p` in
the prefix computation. -/
lemma probEvent_bind_le_probEvent [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF] [MonadLiftT m SetM]
    [EvalDistCompatible m] {mx : m α} {my : α → m β} {q : β → Prop} {p : α → Prop}
    (h : ∀ x ∈ support mx, ¬p x → probEvent (my x) q = 0) :
    probEvent (mx >>= my) q ≤ probEvent mx p := by
  classical
  rw [probEvent_bind_eq_expectedValue, ← expectedValue_ite_one]
  gcongr with x hx
  by_cases hp : p x
  · simp only [if_pos hp]; exact probEvent_le_one
  · simp only [if_neg hp, h x hx hp, le_refl]


-- @@ L292-305 expanded
/-- If a continuation event is bounded by `ε` exactly on a prefix event and is
impossible off that event, then only the prefix mass is charged. -/
lemma probEvent_bind_le_probEvent_mul [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF]
    [MonadLiftT m SetM] [EvalDistCompatible m] {mx : m α} {my : α → m β} {q : β → Prop}
    {p : α → Prop} {ε : ENNReal} (hle : ∀ x ∈ support mx, p x → probEvent (my x) q ≤ ε)
    (hzero : ∀ x ∈ support mx, ¬p x → probEvent (my x) q = 0) :
    probEvent (mx >>= my) q ≤ probEvent mx p * ε := by
  classical
  rw [probEvent_bind_eq_expectedValue, ← expectedValue_ite_one, ← expectedValue_mul_const]
  gcongr with x hx
  by_cases hp : p x
  · simp only [if_pos hp, one_mul]; exact hle x hx hp
  · simp only [if_neg hp, zero_mul, hzero x hx hp, le_refl]


-- @@ L307-314 expanded
/-- Division-form corollary of `probEvent_bind_le_probEvent_mul`. -/
lemma probEvent_bind_le_probEvent_div [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF]
    [MonadLiftT m SetM] [EvalDistCompatible m] {mx : m α} {my : α → m β} {q : β → Prop}
    {p : α → Prop} {c : ENNReal} (hle : ∀ x ∈ support mx, p x → probEvent (my x) q ≤ c⁻¹)
    (hzero : ∀ x ∈ support mx, ¬p x → probEvent (my x) q = 0) :
    probEvent (mx >>= my) q ≤ probEvent mx p / c := by
  simpa [div_eq_mul_inv] using probEvent_bind_le_probEvent_mul hle hzero


-- @@ L316-323 expanded
omit [Monad m] in
/-- Partition an event pointwise into a main event and an exceptional event. -/
lemma probEvent_le_add_of_imp_or [MonadLiftT m SPMF] [MonadLiftT m SetM] [EvalDistCompatible m]
    {mx : m α} {p q r : α → Prop} (h : ∀ x ∈ support mx, p x → q x ∨ r x) :
    probEvent mx p ≤ probEvent mx q + probEvent mx r :=
  (probEvent_mono h).trans (probEvent_or_le mx q r)


-- @@ L325-344 expanded
/-- Prefix-event split for a bind. Prefix points satisfying `p` are charged in
full; off-prefix continuations are charged by the uniform tail bound `ε`. -/
lemma probEvent_bind_le_probEvent_add [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF]
    [MonadLiftT m SetM] [EvalDistCompatible m] {mx : m α} {my : α → m β} {q : β → Prop}
    {p : α → Prop} {ε : ENNReal} (h : ∀ x ∈ support mx, ¬p x → probEvent (my x) q ≤ ε) :
    probEvent (mx >>= my) q ≤ probEvent mx p + ε := by
  classical
  rw [probEvent_bind_eq_expectedValue]
  calc
    expectedValue mx (fun x => probEvent (my x) q) ≤
        expectedValue mx (fun x => (if p x then 1 else 0) + ε) :=
      by
      gcongr with x hx
      by_cases hp : p x
      · simp only [if_pos hp]; exact probEvent_le_one.trans le_self_add
      · simp only [if_neg hp, zero_add]; exact h x hx hp
    _ = probEvent mx p + expectedValue mx (fun _ => ε) := by
      rw [expectedValue_add, expectedValue_ite_one]
    _ ≤ probEvent mx p + ε := by
      gcongr
      exact expectedValue_le_of_le mx fun _ => le_rfl


-- @@ L346-368 expanded
/-- Convex prefix-event split for a bind. The off-prefix tail bound `ε` is charged
only on the mass outside `p`, giving `Pr[p] + (1 - Pr[p]) * ε`. -/
lemma probEvent_bind_le_probEvent_convex [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF]
    [MonadLiftT m SetM] [EvalDistCompatible m] {mx : m α} {my : α → m β} {q : β → Prop}
    {p : α → Prop} {ε : ENNReal} (h : ∀ x ∈ support mx, ¬p x → probEvent (my x) q ≤ ε) :
    probEvent (mx >>= my) q ≤ probEvent mx p + (1 - probEvent mx p) * ε := by
  classical
  rw [probEvent_bind_eq_expectedValue]
  calc
    expectedValue mx (fun x => probEvent (my x) q) ≤
        expectedValue mx (fun x => (if p x then 1 else 0) + (if ¬p x then 1 else 0) * ε) :=
      by
      gcongr with x hx
      by_cases hp : p x
      · simp only [if_pos hp, if_neg (not_not_intro hp), zero_mul, add_zero]
        exact probEvent_le_one
      · simp only [if_neg hp, if_pos hp, zero_add, one_mul]; exact h x hx hp
    _ = probEvent mx p + (probEvent mx fun x => ¬p x) * ε := by
      rw [expectedValue_add, expectedValue_mul_const, expectedValue_ite_one, expectedValue_ite_one]
    _ ≤ probEvent mx p + (1 - probEvent mx p) * ε :=
      by
      gcongr
      exact
        ENNReal.le_sub_of_add_le_left probEvent_ne_top
          ((probEvent_compl mx p).trans_le tsub_le_self)


-- @@ L370-374 expanded
lemma probOutput_bind_eq_sum_finSupport [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF]
    [MonadLiftT m SetM] [EvalDistCompatible m] [HasEvalFinset m] (mx : m α) (my : α → m β)
    [DecidableEq α] (y : β) :
    probOutput (mx >>= my) y = ∑ x ∈ finSupport mx, probOutput mx x * probOutput (my x) y :=
  (probOutput_bind_eq_tsum mx my y).trans (tsum_eq_sum' <| by simp)


-- @@ L376-380 expanded
lemma probEvent_bind_eq_sum_finSupport [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF]
    [MonadLiftT m SetM] [EvalDistCompatible m] [HasEvalFinset m] (mx : m α) (my : α → m β)
    [DecidableEq α] (q : β → Prop) :
    probEvent (mx >>= my) q = ∑ x ∈ finSupport mx, probOutput mx x * probEvent (my x) q :=
  (probEvent_bind_eq_tsum mx my q).trans (tsum_eq_sum' <| by simp)


-- @@ L382-382 verbatim
section const


-- @@ L384-384 verbatim
section support


-- @@ L386-386 verbatim
variable [MonadLiftT m SetM] [LawfulMonadLiftT m SetM]


-- @@ L388-390 verbatim
lemma support_bind_const (mx : m α) (my : m β) :
    support (mx >>= fun _ => my) = {y ∈ support my | (support mx).Nonempty} := by
  grind [= Set.Nonempty]


-- @@ L392-397 verbatim
lemma finSupport_bind_const [HasEvalFinset m]
    [DecidableEq β] [DecidableEq α] (mx : m α) (my : m β) :
    finSupport (mx >>= fun _ => my) = if (finSupport mx).Nonempty then finSupport my else ∅ := by
  ext x
  simp only [finSupport_bind, Finset.mem_biUnion]
  split_ifs <;> simp_all [Finset.nonempty_def]


-- @@ L399-399 verbatim
end support


-- @@ L401-402 verbatim
variable [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF]
  [MonadLiftT m SetM] [EvalDistCompatible m]


-- @@ L404-415 expanded
omit [MonadLiftT m SetM] [EvalDistCompatible m] in
/-- The compatibility adapter satisfies the Giry `pure`/`bind` laws for every lawful `SPMF`
lift, so the `𝒟`-level laws (`evalDist_pure`, `evalDist_bind`, `evalDist_map`, …) hold with no
measure specification in scope. -/
instance instLawfulEvalDistSemanticsOfMonadLiftTSPMF : LawfulEvalDistSemantics m
    where
  denote_pure
    x := by
    change (evalSPMF (pure x : m _)).toMeasure = _
    simp
  denote_bind mx f
    hf := by
    change (evalSPMF (mx >>= f)).toMeasure = _
    rw [evalSPMF_bind]
    exact (evalSPMF mx).toMeasure_bind' _ hf


-- @@ L417-421 expanded
lemma probOutput_bind_of_const (mx : m α) {my : α → m β} {y : β} {r : ℝ≥0∞}
    (h : ∀ x ∈ support mx, probOutput (my x) y = r) :
    probOutput (mx >>= my) y = (1 - probFailure mx) * r :=
  by
  rw [probOutput_bind_eq_expectedValue, ← tsum_probOutput_eq_sub, ← ENNReal.tsum_mul_right]
  exact expectedValue_congr_of_support h


-- @@ L423-426 expanded
@[simp, grind =_]
lemma probOutput_bind_const (mx : m α) (my : m β) (y : β) :
    probOutput (mx >>= fun _ => my) y = (1 - probFailure mx) * probOutput my y := by
  rw [probOutput_bind_of_const mx fun _ _ => rfl]


-- @@ L428-433 expanded
lemma probEvent_bind_of_const (mx : m α) {my : α → m β} {p : β → Prop} {r : ℝ≥0∞}
    (h : ∀ x ∈ support mx, probEvent (my x) p = r) :
    probEvent (mx >>= my) p = (1 - probFailure mx) * r :=
  by
  rw [probEvent_bind_eq_expectedValue, ← tsum_probOutput_eq_sub, ← ENNReal.tsum_mul_right]
  exact expectedValue_congr_of_support h


-- @@ L435-438 expanded
@[simp, grind =_]
lemma probEvent_bind_const (mx : m α) (my : m β) (p : β → Prop) :
    probEvent (mx >>= fun _ => my) p = (1 - probFailure mx) * probEvent my p := by
  rw [probEvent_bind_of_const mx fun _ _ => rfl]


-- @@ L440-449 expanded
/-- Write the probability of `mx >>= my` failing given that `my` has constant failure chance over
the possible outputs in `support mx` as a fixed expression without any sums. -/
lemma probFailure_bind_of_const {mx : m α} {my : α → m β} {r : ℝ≥0∞}
    (h : ∀ x ∈ support mx, probFailure (my x) = r) :
    probFailure (mx >>= my) = probFailure mx + r * (1 - probFailure mx) := by
  calc
    probFailure (mx >>= my)
    _ = probFailure mx + ∑' x : support mx, probOutput mx x * probFailure (my x) := by grind
    _ = probFailure mx + ∑' x : support mx, probOutput mx x * r := by grind
    _ = probFailure mx + r * (1 - probFailure mx) := by
      rw [ENNReal.tsum_mul_right, mul_comm, tsum_support_probOutput_eq_sub]


-- @@ L451-455 expanded
lemma probFailure_bind_of_const' {mx : m α} {my : α → m β} {r : ℝ≥0∞} (hr : r ≠ ⊤)
    (h : ∀ x ∈ support mx, probFailure (my x) = r) :
    probFailure (mx >>= my) = probFailure mx + r - probFailure mx * r := by
  rw [probFailure_bind_of_const h, ENNReal.mul_sub, AddLECancellable.add_tsub_assoc_of_le,
      mul_comm (probFailure mx) r, mul_one] <;>
    simp [hr, ENNReal.mul_eq_top]


-- @@ L457-460 expanded
@[simp, grind =_]
lemma probFailure_bind_const (mx : m α) (my : m β) :
    probFailure (mx >>= fun _ => my) =
      probFailure mx + probFailure my - probFailure mx * probFailure my :=
  by rw [probFailure_bind_of_const' (by simp) fun _ _ => rfl]


-- @@ L462-469 expanded
lemma probFailure_bind_eq_sub_mul (mx : m α) (my : α → m β) (r : ℝ≥0∞) (hr : r ≠ ⊤)
    (h : ∀ x ∈ support mx, probFailure (my x) = r) :
    probFailure (mx >>= my) = 1 - (1 - probFailure mx) * (1 - r) :=
  by
  rcases (support mx).eq_empty_or_nonempty with h' | ⟨x, hx⟩
  · rw [probFailure_bind_of_const' hr h, probFailure_eq_one h']
    simp [ENNReal.add_sub_cancel_right hr]
  ·
    rw [probFailure_bind_of_const' hr h,
      ENNReal.one_sub_one_sub_mul_one_sub (by simp) (h x hx ▸ probFailure_le_one)]


-- @@ L471-471 verbatim
end const


-- @@ L473-473 verbatim
section mono


-- @@ L475-476 verbatim
variable [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF]
  [MonadLiftT m SetM] [EvalDistCompatible m]


-- @@ L478-488 expanded
lemma probFailure_bind_le_add_of_forall {mx : m α} {my : α → m β} {r : ℝ≥0∞}
    (hr : ∀ x ∈ support mx, probFailure (my x) ≤ r) :
    probFailure (mx >>= my) ≤ probFailure mx + (1 - probFailure mx) * r := by
  calc
    probFailure (mx >>= my)
    _ = probFailure mx + ∑' x : support mx, probOutput mx x * probFailure (my x) := by
      rw [probFailure_bind_eq_add_tsum_support]
    _ ≤ probFailure mx + ∑' x : support mx, probOutput mx x * r :=
      by
      gcongr with x
      exact hr x.1 x.2
    _ ≤ probFailure mx + (1 - probFailure mx) * r := by simp [ENNReal.tsum_mul_right]


-- @@ L490-502 expanded
/-- Version of `probFailure_bind_le_of_forall` with that allows a manual `Pr[⊥ | mx]` value. -/
lemma probFailure_bind_le_of_forall' {mx : m α} {s : ℝ≥0∞} (h' : probFailure mx = s) (my : α → m β)
    {r : ℝ≥0∞} (hr : ∀ x ∈ support mx, probFailure (my x) ≤ r) : probFailure (mx >>= my) ≤ s + r :=
  by
  rw [probFailure_bind_eq_add_tsum_support]
  refine add_le_add (le_of_eq h') ?_
  calc
    ∑' x : support mx, probOutput mx x * probFailure (my x)
    _ ≤ ∑' x : support mx, probOutput mx x * r :=
      (ENNReal.tsum_le_tsum fun ⟨x, hx⟩ => mul_le_mul' le_rfl (hr x hx))
    _ = (1 - probFailure mx) * r := by rw [ENNReal.tsum_mul_right, tsum_support_probOutput_eq_sub]
    _ = (1 - s) * r := by rw [h']
    _ ≤ 1 * r := (mul_le_mul' tsub_le_self le_rfl)
    _ = r := one_mul r


-- @@ L504-508 expanded
/-- Version of `probFailure_bind_le_of_forall` when `mx` never fails. -/
lemma probFailure_bind_le_of_forall {mx : m α} (h' : probFailure mx = 0) {my : α → m β} {r : ℝ≥0∞}
    (hr : ∀ x ∈ support mx, probFailure (my x) ≤ r) : probFailure (mx >>= my) ≤ r := by
  refine (probFailure_bind_le_add_of_forall hr).trans (by simp [h'])


-- @@ L510-510 verbatim
end mono


-- @@ L512-515 expanded
lemma probFailure_bind_of_probFailure_eq_zero [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF]
    {mx : m α} (h' : probFailure mx = 0) {my : α → m β} :
    probFailure (mx >>= my) = ∑' x : α, probOutput mx x * probFailure (my x) := by
  rw [probFailure_bind_eq_add_tsum, h', zero_add]


-- @@ L517-517 verbatim
end bind


-- @@ L519-519 verbatim
section forall_support


-- @@ L521-521 verbatim
variable [MonadLiftT m SetM] [LawfulMonadLiftT m SetM]


-- @@ L523-525 verbatim
@[simp] lemma allOutputsSatisfy_pure (p : α → Prop) (x : α) :
    allOutputsSatisfy p (pure x : m α) ↔ p x := by
  simp [allOutputsSatisfy]


-- @@ L527-529 verbatim
@[simp] lemma someOutputSatisfies_pure (p : α → Prop) (x : α) :
    someOutputSatisfies p (pure x : m α) ↔ p x := by
  simp [someOutputSatisfies]


-- @@ L531-536 verbatim
@[simp] lemma allOutputsSatisfy_bind
    (mx : m α) (my : α → m β) (p : β → Prop) :
    allOutputsSatisfy p (mx >>= my) ↔
      allOutputsSatisfy (fun a => allOutputsSatisfy p (my a)) mx := by
  simp only [allOutputsSatisfy, support_bind]
  aesop


-- @@ L538-543 verbatim
@[simp] lemma someOutputSatisfies_bind
    (mx : m α) (my : α → m β) (p : β → Prop) :
    someOutputSatisfies p (mx >>= my) ↔
      someOutputSatisfies (fun a => someOutputSatisfies p (my a)) mx := by
  simp only [someOutputSatisfies, support_bind]
  aesop


-- @@ L545-545 verbatim
end forall_support


-- @@ L547-547 verbatim
/-! ## Congruence and monotonicity for `bind` -/


-- @@ L549-549 verbatim
section congr_mono


-- @@ L551-552 verbatim
variable [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF]
  [MonadLiftT m SetM] [EvalDistCompatible m]


-- @@ L554-570 expanded
lemma mul_le_probEvent_bind {mx : m α} {my : α → m β} {p : α → Prop} {q : β → Prop} {r r' : ℝ≥0∞}
    (h : r ≤ probEvent mx p) (h' : ∀ x ∈ support mx, p x → r' ≤ probEvent (my x) q) :
    r * r' ≤ probEvent (mx >>= my) q := by
  classical
  rw [probEvent_bind_eq_tsum]
  calc
    r * r'
    _ ≤ probEvent mx p * r' := by gcongr
    _ = ∑' x, (if p x then probOutput mx x else 0) * r' := by
      rw [probEvent_eq_tsum_ite, ENNReal.tsum_mul_right]
    _ ≤ ∑' x, probOutput mx x * probEvent (my x) q :=
      by
      refine ENNReal.tsum_le_tsum fun x => ?_
      by_cases hx : x ∈ support mx
      · split_ifs with hp
        · exact mul_le_mul' le_rfl (h' x hx hp)
        · simp
      · simp [probOutput_eq_zero_of_not_mem_support hx]


-- @@ L572-581 expanded
lemma probFailure_bind_congr (mx : m α) {my : α → m β} {oc : α → m γ}
    (h : ∀ x ∈ support mx, probFailure (my x) = probFailure (oc x)) :
    probFailure (mx >>= my) = probFailure (mx >>= oc) :=
  by
  simp only [probFailure_bind_eq_add_tsum]
  congr 1
  refine tsum_congr fun x => ?_
  by_cases hx : x ∈ support mx
  · rw [h x hx]
  · simp [probOutput_eq_zero_of_not_mem_support hx]


-- @@ L583-587 expanded
lemma probFailure_bind_congr' (mx : m α) {my : α → m β} {oc : α → m γ}
    (h : ∀ x, probFailure (my x) = probFailure (oc x)) :
    probFailure (mx >>= my) = probFailure (mx >>= oc) :=
  probFailure_bind_congr mx fun x _ => h x


-- @@ L589-596 expanded
lemma probOutput_bind_congr {mx : m α} {ob₁ ob₂ : α → m β} {y : β}
    (h : ∀ x ∈ support mx, probOutput (ob₁ x) y = probOutput (ob₂ x) y) :
    probOutput (mx >>= ob₁) y = probOutput (mx >>= ob₂) y :=
  by
  simp only [probOutput_bind_eq_tsum]
  refine tsum_congr fun x => ?_
  by_cases hx : x ∈ support mx
  · rw [h x hx]
  · simp [probOutput_eq_zero_of_not_mem_support hx]


-- @@ L598-601 expanded
lemma probOutput_bind_congr' (mx : m α) {ob₁ ob₂ : α → m β} (y : β)
    (h : ∀ x, probOutput (ob₁ x) y = probOutput (ob₂ x) y) :
    probOutput (mx >>= ob₁) y = probOutput (mx >>= ob₂) y :=
  probOutput_bind_congr fun x _ => h x


-- @@ L603-609 expanded
lemma probOutput_bind_mono {mx : m α} {my : α → m β} {oc : α → m γ} {y : β} {z : γ}
    (h : ∀ x ∈ support mx, probOutput (my x) y ≤ probOutput (oc x) z) :
    probOutput (mx >>= my) y ≤ probOutput (mx >>= oc) z :=
  by
  rw [probOutput_bind_eq_expectedValue, probOutput_bind_eq_expectedValue]
  gcongr with x hx
  exact h x hx


-- @@ L611-618 expanded
lemma probEvent_bind_congr {mx : m α} {ob₁ ob₂ : α → m β} {q : β → Prop}
    (h : ∀ x ∈ support mx, probEvent (ob₁ x) q = probEvent (ob₂ x) q) :
    probEvent (mx >>= ob₁) q = probEvent (mx >>= ob₂) q :=
  by
  simp only [probEvent_bind_eq_tsum]
  refine tsum_congr fun x => ?_
  by_cases hx : x ∈ support mx
  · rw [h x hx]
  · simp [probOutput_eq_zero_of_not_mem_support hx]


-- @@ L620-623 expanded
lemma probEvent_bind_congr' (mx : m α) {ob₁ ob₂ : α → m β} (q : β → Prop)
    (h : ∀ x, probEvent (ob₁ x) q = probEvent (ob₂ x) q) :
    probEvent (mx >>= ob₁) q = probEvent (mx >>= ob₂) q :=
  probEvent_bind_congr fun x _ => h x


-- @@ L625-628 expanded
lemma evalSPMF_bind_congr {mx : m α} {ob₁ ob₂ : α → m β}
    (h : ∀ x ∈ support mx, evalSPMF (ob₁ x) = evalSPMF (ob₂ x)) :
    evalSPMF (mx >>= ob₁) = evalSPMF (mx >>= ob₂) :=
  evalSPMF_ext fun y => probOutput_bind_congr fun x hx => evalSPMF_ext_iff.mp (h x hx) y


-- @@ L630-633 expanded
lemma evalSPMF_bind_congr' (mx : m α) {ob₁ ob₂ : α → m β}
    (h : ∀ x, evalSPMF (ob₁ x) = evalSPMF (ob₂ x)) :
    evalSPMF (mx >>= ob₁) = evalSPMF (mx >>= ob₂) :=
  evalSPMF_bind_congr fun x _ => h x


-- @@ L635-640 expanded
lemma probEvent_bind_mono {mx : m α} {my oc : α → m β} {q : β → Prop}
    (h : ∀ x ∈ support mx, probEvent (my x) q ≤ probEvent (oc x) q) :
    probEvent (mx >>= my) q ≤ probEvent (mx >>= oc) q :=
  by
  rw [probEvent_bind_eq_expectedValue, probEvent_bind_eq_expectedValue]
  gcongr with x hx
  exact h x hx


-- @@ L642-652 expanded
/-- Pointwise division bounds on bind continuations factor through the bind. -/
lemma probOutput_bind_mono_div_const {mx : m α} {ob₁ ob₂ : α → m β} {y : β} {r : ℝ≥0∞}
    (h : ∀ x ∈ support mx, probOutput (ob₁ x) y ≤ probOutput (ob₂ x) y / r) :
    probOutput (mx >>= ob₁) y ≤ probOutput (mx >>= ob₂) y / r :=
  by
  simp only [probOutput_bind_eq_tsum, div_eq_mul_inv]
  rw [← ENNReal.tsum_mul_right]
  refine ENNReal.tsum_le_tsum fun x ↦ ?_
  by_cases hx : x ∈ support mx
  · simpa only [div_eq_mul_inv, mul_assoc] using mul_le_mul' le_rfl (h x hx)
  · simp [probOutput_eq_zero_of_not_mem_support hx]


-- @@ L654-664 expanded
/-- Event form of `probOutput_bind_mono_div_const`. -/
lemma probEvent_bind_mono_div_const {mx : m α} {ob₁ ob₂ : α → m β} {q : β → Prop} {r : ℝ≥0∞}
    (h : ∀ x ∈ support mx, probEvent (ob₁ x) q ≤ probEvent (ob₂ x) q / r) :
    probEvent (mx >>= ob₁) q ≤ probEvent (mx >>= ob₂) q / r :=
  by
  simp only [probEvent_bind_eq_tsum, div_eq_mul_inv]
  rw [← ENNReal.tsum_mul_right]
  refine ENNReal.tsum_le_tsum fun x ↦ ?_
  by_cases hx : x ∈ support mx
  · simpa only [div_eq_mul_inv, mul_assoc] using mul_le_mul' le_rfl (h x hx)
  · simp [probOutput_eq_zero_of_not_mem_support hx]


-- @@ L666-675 expanded
lemma probOutput_bind_congr_div_const {mx : m α} {ob₁ ob₂ : α → m β} {y : β} {r : ℝ≥0∞}
    (h : ∀ x ∈ support mx, probOutput (ob₁ x) y = probOutput (ob₂ x) y / r) :
    probOutput (mx >>= ob₁) y = probOutput (mx >>= ob₂) y / r :=
  by
  simp only [probOutput_bind_eq_tsum, div_eq_mul_inv]
  rw [← ENNReal.tsum_mul_right]
  refine tsum_congr fun x => ?_
  by_cases hx : x ∈ support mx
  · rw [h x hx, div_eq_mul_inv, mul_assoc]
  · simp [probOutput_eq_zero_of_not_mem_support hx]


-- @@ L677-686 expanded
lemma probEvent_bind_congr_div_const {mx : m α} {ob₁ ob₂ : α → m β} {q : β → Prop} {r : ℝ≥0∞}
    (h : ∀ x ∈ support mx, probEvent (ob₁ x) q = probEvent (ob₂ x) q / r) :
    probEvent (mx >>= ob₁) q = probEvent (mx >>= ob₂) q / r :=
  by
  simp only [probEvent_bind_eq_tsum, div_eq_mul_inv]
  rw [← ENNReal.tsum_mul_right]
  refine tsum_congr fun x => ?_
  by_cases hx : x ∈ support mx
  · rw [h x hx, div_eq_mul_inv, mul_assoc]
  · simp [probOutput_eq_zero_of_not_mem_support hx]


-- @@ L688-698 expanded
lemma probOutput_bind_congr_eq_add {γ₁ γ₂ : Type u} {mx : m α} {my : α → m β} {oc₁ : α → m γ₁}
    {oc₂ : α → m γ₂} {y : β} {z₁ : γ₁} {z₂ : γ₂}
    (h : ∀ x ∈ support mx, probOutput (my x) y = probOutput (oc₁ x) z₁ + probOutput (oc₂ x) z₂) :
    probOutput (mx >>= my) y = probOutput (mx >>= oc₁) z₁ + probOutput (mx >>= oc₂) z₂ :=
  by
  simp only [probOutput_bind_eq_tsum, ← ENNReal.tsum_add]
  refine tsum_congr fun x => ?_
  by_cases hx : x ∈ support mx
  · rw [h x hx, left_distrib]
  · simp [probOutput_eq_zero_of_not_mem_support hx]


-- @@ L700-710 expanded
lemma probEvent_bind_congr_eq_add {γ₁ γ₂ : Type u} {mx : m α} {my : α → m β} {oc₁ : α → m γ₁}
    {oc₂ : α → m γ₂} {q : β → Prop} {q₁ : γ₁ → Prop} {q₂ : γ₂ → Prop}
    (h : ∀ x ∈ support mx, probEvent (my x) q = probEvent (oc₁ x) q₁ + probEvent (oc₂ x) q₂) :
    probEvent (mx >>= my) q = probEvent (mx >>= oc₁) q₁ + probEvent (mx >>= oc₂) q₂ :=
  by
  simp only [probEvent_bind_eq_tsum, ← ENNReal.tsum_add]
  refine tsum_congr fun x => ?_
  by_cases hx : x ∈ support mx
  · rw [h x hx, left_distrib]
  · simp [probOutput_eq_zero_of_not_mem_support hx]


-- @@ L712-724 expanded
lemma probOutput_bind_congr_le_add {γ₁ γ₂ : Type u} {mx : m α} {my : α → m β} {oc₁ : α → m γ₁}
    {oc₂ : α → m γ₂} {y : β} {z₁ : γ₁} {z₂ : γ₂}
    (h : ∀ x ∈ support mx, probOutput (my x) y ≤ probOutput (oc₁ x) z₁ + probOutput (oc₂ x) z₂) :
    probOutput (mx >>= my) y ≤ probOutput (mx >>= oc₁) z₁ + probOutput (mx >>= oc₂) z₂ :=
  by
  simp only [probOutput_bind_eq_tsum, ← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun x => ?_
  by_cases hx : x ∈ support mx
  ·
    calc
      probOutput mx x * probOutput (my x) y
      _ ≤ probOutput mx x * (probOutput (oc₁ x) z₁ + probOutput (oc₂ x) z₂) :=
        (mul_le_mul' le_rfl (h x hx))
      _ = probOutput mx x * probOutput (oc₁ x) z₁ + probOutput mx x * probOutput (oc₂ x) z₂ :=
        left_distrib ..
  · simp [probOutput_eq_zero_of_not_mem_support hx]


-- @@ L726-734 expanded
lemma probOutput_bind_congr_add_le {γ₁ γ₂ : Type u} {mx : m α} {my : α → m β} {oc₁ : α → m γ₁}
    {oc₂ : α → m γ₂} {y : β} {z₁ : γ₁} {z₂ : γ₂}
    (h : ∀ x ∈ support mx, probOutput (oc₁ x) z₁ + probOutput (oc₂ x) z₂ ≤ probOutput (my x) y) :
    probOutput (mx >>= oc₁) z₁ + probOutput (mx >>= oc₂) z₂ ≤ probOutput (mx >>= my) y :=
  by
  simp only [probOutput_bind_eq_expectedValue, ← expectedValue_add]
  gcongr with x hx
  exact h x hx


-- @@ L736-744 expanded
lemma probEvent_bind_congr_add_le {γ₁ γ₂ : Type u} {mx : m α} {my : α → m β} {oc₁ : α → m γ₁}
    {oc₂ : α → m γ₂} {q : β → Prop} {q₁ : γ₁ → Prop} {q₂ : γ₂ → Prop}
    (h : ∀ x ∈ support mx, probEvent (oc₁ x) q₁ + probEvent (oc₂ x) q₂ ≤ probEvent (my x) q) :
    probEvent (mx >>= oc₁) q₁ + probEvent (mx >>= oc₂) q₂ ≤ probEvent (mx >>= my) q :=
  by
  simp only [probEvent_bind_eq_expectedValue, ← expectedValue_add]
  gcongr with x hx
  exact h x hx


-- @@ L746-761 expanded
lemma probOutput_bind_congr_le_sub {γ₁ γ₂ : Type u} {mx : m α} {my : α → m β} {oc₁ : α → m γ₁}
    {oc₂ : α → m γ₂} {y : β} {z₁ : γ₁} {z₂ : γ₂}
    (h : ∀ x ∈ support mx, probOutput (my x) y ≤ probOutput (oc₁ x) z₁ - probOutput (oc₂ x) z₂)
    (h' : ∀ x ∈ support mx, probOutput (oc₂ x) z₂ ≤ probOutput (oc₁ x) z₁) :
    probOutput (mx >>= my) y ≤ probOutput (mx >>= oc₁) z₁ - probOutput (mx >>= oc₂) z₂ :=
  by
  have hadd : probOutput (mx >>= my) y + probOutput (mx >>= oc₂) z₂ ≤ probOutput (mx >>= oc₁) z₁ :=
    by
    simp only [probOutput_bind_eq_tsum, ← ENNReal.tsum_add]
    refine ENNReal.tsum_le_tsum fun x => ?_
    by_cases hx : x ∈ support mx
    · rw [← left_distrib]
      exact
        mul_le_mul' le_rfl ((add_le_add (h x hx) le_rfl).trans_eq (tsub_add_cancel_of_le (h' x hx)))
    · simp [probOutput_eq_zero_of_not_mem_support hx]
  exact (ENNReal.cancel_of_ne probOutput_ne_top).le_tsub_of_add_le_right hadd


-- @@ L763-778 expanded
lemma probEvent_bind_congr_le_sub {γ₁ γ₂ : Type u} {mx : m α} {my : α → m β} {oc₁ : α → m γ₁}
    {oc₂ : α → m γ₂} {q : β → Prop} {q₁ : γ₁ → Prop} {q₂ : γ₂ → Prop}
    (h : ∀ x ∈ support mx, probEvent (my x) q ≤ probEvent (oc₁ x) q₁ - probEvent (oc₂ x) q₂)
    (h' : ∀ x ∈ support mx, probEvent (oc₂ x) q₂ ≤ probEvent (oc₁ x) q₁) :
    probEvent (mx >>= my) q ≤ probEvent (mx >>= oc₁) q₁ - probEvent (mx >>= oc₂) q₂ :=
  by
  have hadd : probEvent (mx >>= my) q + probEvent (mx >>= oc₂) q₂ ≤ probEvent (mx >>= oc₁) q₁ :=
    by
    simp only [probEvent_bind_eq_tsum, ← ENNReal.tsum_add]
    refine ENNReal.tsum_le_tsum fun x => ?_
    by_cases hx : x ∈ support mx
    · rw [← left_distrib]
      exact
        mul_le_mul' le_rfl ((add_le_add (h x hx) le_rfl).trans_eq (tsub_add_cancel_of_le (h' x hx)))
    · simp [probOutput_eq_zero_of_not_mem_support hx]
  exact (ENNReal.cancel_of_ne probEvent_ne_top).le_tsub_of_add_le_right hadd


-- @@ L780-792 expanded
lemma probOutput_bind_congr_sub_le {γ₁ γ₂ : Type u} {mx : m α} {my : α → m β} {oc₁ : α → m γ₁}
    {oc₂ : α → m γ₂} {y : β} {z₁ : γ₁} {z₂ : γ₂}
    (h : ∀ x ∈ support mx, probOutput (oc₁ x) z₁ - probOutput (oc₂ x) z₂ ≤ probOutput (my x) y) :
    probOutput (mx >>= oc₁) z₁ - probOutput (mx >>= oc₂) z₂ ≤ probOutput (mx >>= my) y :=
  by
  simp only [probOutput_bind_eq_tsum]
  rw [tsub_le_iff_right, ← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun x => ?_
  by_cases hx : x ∈ support mx
  · rw [← left_distrib]
    exact mul_le_mul' le_rfl (tsub_le_iff_right.mp (h x hx))
  · simp [probOutput_eq_zero_of_not_mem_support hx]


-- @@ L794-806 expanded
lemma probEvent_bind_congr_sub_le {γ₁ γ₂ : Type u} {mx : m α} {my : α → m β} {oc₁ : α → m γ₁}
    {oc₂ : α → m γ₂} {q : β → Prop} {q₁ : γ₁ → Prop} {q₂ : γ₂ → Prop}
    (h : ∀ x ∈ support mx, probEvent (oc₁ x) q₁ - probEvent (oc₂ x) q₂ ≤ probEvent (my x) q) :
    probEvent (mx >>= oc₁) q₁ - probEvent (mx >>= oc₂) q₂ ≤ probEvent (mx >>= my) q :=
  by
  simp only [probEvent_bind_eq_tsum]
  rw [tsub_le_iff_right, ← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun x => ?_
  by_cases hx : x ∈ support mx
  · rw [← left_distrib]
    exact mul_le_mul' le_rfl (tsub_le_iff_right.mp (h x hx))
  · simp [probOutput_eq_zero_of_not_mem_support hx]


-- @@ L808-830 expanded
/-- Union bound for bind: if `Pr[ ¬p | mx] ≤ ε₁` and `Pr[ ¬q | my x] ≤ ε₂` for all `x` satisfying
`p`, then `Pr[ ¬q | mx >>= my] ≤ ε₁ + ε₂`. Useful for sequential composition of error bounds. -/
lemma probEvent_bind_le_add {mx : m α} {my : α → m β} {p : α → Prop} {q : β → Prop} {ε₁ ε₂ : ℝ≥0∞}
    (h₁ : (probEvent mx fun x => ¬p x) ≤ ε₁)
    (h₂ : ∀ x ∈ support mx, p x → (probEvent (my x) fun y => ¬q y) ≤ ε₂) :
    (probEvent (mx >>= my) fun y => ¬q y) ≤ ε₁ + ε₂ := by
  classical
  rw [probEvent_bind_eq_tsum]
  calc
    (∑' x, probOutput mx x * probEvent (my x) fun y => ¬q y) ≤
        ∑' x, (probOutput mx x * ε₂ + if ¬p x then probOutput mx x else 0) :=
      by
      refine ENNReal.tsum_le_tsum fun x => ?_
      by_cases hx : x ∈ support mx
      · by_cases hp : p x
        · rw [if_neg (not_not_intro hp), add_zero]
          exact mul_le_mul' le_rfl (h₂ x hx hp)
        · rw [if_pos hp]
          exact (mul_le_of_le_one_right zero_le probEvent_le_one).trans le_add_self
      · simp [probOutput_eq_zero_of_not_mem_support hx]
    _ = (∑' x, probOutput mx x) * ε₂ + probEvent mx fun x => ¬p x := by
      rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, probEvent_eq_tsum_ite]
    _ ≤ 1 * ε₂ + ε₁ := (add_le_add (mul_le_mul' tsum_probOutput_le_one le_rfl) h₁)
    _ = ε₁ + ε₂ := by ring


-- @@ L832-847 expanded
/-- `probEvent` version of `probEvent_bind_mono` with additive error bound. -/
lemma probEvent_bind_congr_le_add {mx : m α} {my oc : α → m β} {q : β → Prop} {ε : ℝ≥0∞}
    (h : ∀ x ∈ support mx, probEvent (my x) q ≤ probEvent (oc x) q + ε) :
    probEvent (mx >>= my) q ≤ probEvent (mx >>= oc) q + ε :=
  by
  simp only [probEvent_bind_eq_tsum]
  calc
    ∑' x, probOutput mx x * probEvent (my x) q ≤
        ∑' x, (probOutput mx x * probEvent (oc x) q + probOutput mx x * ε) :=
      by
      refine ENNReal.tsum_le_tsum fun x => ?_
      by_cases hx : x ∈ support mx
      · exact (mul_le_mul' le_rfl (h x hx)).trans_eq (left_distrib ..)
      · simp [probOutput_eq_zero_of_not_mem_support hx]
    _ ≤ (∑' x, probOutput mx x * probEvent (oc x) q) + ε :=
      by
      rw [ENNReal.tsum_add, ENNReal.tsum_mul_right]
      gcongr
      exact mul_le_of_le_one_left zero_le tsum_probOutput_le_one


-- @@ L849-849 verbatim
end congr_mono


-- @@ L851-851 verbatim
/-! ## Swapping independent draws -/


-- @@ L853-853 verbatim
section swap_compl


-- @@ L855-855 verbatim
variable [MonadLiftT m SPMF]


-- @@ L857-869 expanded
/-- Swapping two independent random draws preserves the output distribution: although
`mx >>= fun a => my >>= fun b => f a b` and `my >>= fun b => mx >>= fun a => f a b` need not be
equal as `m`-computations when `m` is non-commutative, the two draws are independent, so their
output distributions agree. The `probEvent`/`probOutput` forms (`probEvent_bind_bind_swap`,
`probOutput_bind_bind_swap`) are corollaries. -/
lemma evalSPMF_bind_bind_swap [LawfulMonadLiftT m SPMF] (mx : m α) (my : m β) (f : α → β → m γ) :
    evalSPMF (mx >>= fun a => my >>= fun b => f a b) =
      evalSPMF (my >>= fun b => mx >>= fun a => f a b) :=
  by
  refine evalSPMF_ext fun x => ?_
  simp only [probOutput_bind_eq_tsum, ← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  exact tsum_congr fun b => tsum_congr fun a => mul_left_comm _ _ _


-- @@ L871-877 expanded
/-- Swapping two independent random draws preserves probability of any event. Corollary of
`evalSPMF_bind_bind_swap`. -/
lemma probEvent_bind_bind_swap [LawfulMonadLiftT m SPMF] (mx : m α) (my : m β) (f : α → β → m γ)
    (q : γ → Prop) :
    probEvent (mx >>= fun a => my >>= fun b => f a b) q =
      probEvent (my >>= fun b => mx >>= fun a => f a b) q :=
  by rw [probEvent_def, probEvent_def, evalSPMF_bind_bind_swap]


-- @@ L879-885 expanded
/-- Swapping two independent random draws preserves the probability of any fixed output. Corollary
of `evalSPMF_bind_bind_swap`. -/
lemma probOutput_bind_bind_swap [LawfulMonadLiftT m SPMF] (mx : m α) (my : m β) (f : α → β → m γ)
    (z : γ) :
    probOutput (mx >>= fun a => my >>= fun b => f a b) z =
      probOutput (my >>= fun b => mx >>= fun a => f a b) z :=
  by rw [probOutput_def, probOutput_def, evalSPMF_bind_bind_swap]


-- @@ L887-887 verbatim
/-! ## Complement bounds -/


-- @@ L889-898 expanded
omit [Monad m] in
/-- If `1 - ε ≤ Pr[ p | mx]` and `mx` never fails, then `Pr[ ¬p | mx] ≤ ε`. -/
lemma probEvent_compl_le_of_one_sub_le {mx : m α} {p : α → Prop} {ε : ℝ≥0∞}
    (hfail : probFailure mx = 0) (h : 1 - ε ≤ probEvent mx p) : (probEvent mx fun x => ¬p x) ≤ ε :=
  by
  have hsum : (probEvent mx fun x => ¬p x) + probEvent mx p = 1 := by
    simpa [hfail, add_comm] using probEvent_compl mx p
  rwa [ENNReal.eq_sub_of_add_eq probEvent_ne_top hsum, tsub_le_iff_tsub_le]


-- @@ L900-910 expanded
omit [Monad m] in
/-- If `Pr[ ¬p | mx] ≤ ε` and `mx` never fails, then `1 - ε ≤ Pr[ p | mx]`. -/
lemma probEvent_one_sub_le_of_compl_le {mx : m α} {p : α → Prop} {ε : ℝ≥0∞}
    (hfail : probFailure mx = 0) (h : (probEvent mx fun x => ¬p x) ≤ ε) : 1 - ε ≤ probEvent mx p :=
  by
  have hsum : (probEvent mx p + probEvent mx fun x => ¬p x) = 1 := by
    simpa [hfail] using probEvent_compl mx p
  rw [ENNReal.eq_sub_of_add_eq probEvent_ne_top hsum]
  exact tsub_le_tsub_left h _


-- @@ L912-912 verbatim
end swap_compl


-- @@ L914-914 verbatim
/-! ## Union bounds -/


-- @@ L916-916 verbatim
section union_bound


-- @@ L918-918 verbatim
variable [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF]


-- @@ L920-931 expanded
omit [Monad m] [LawfulMonadLiftT m SPMF] in
/-- Union bound for finset-indexed events: the probability that *some* event in `s` holds
is at most the sum of the individual event probabilities. -/
lemma probEvent_exists_finset_le_sum {ι : Type*} (s : Finset ι) (mx : m α) (E : ι → α → Prop) :
    probEvent mx (fun x => ∃ i ∈ s, E i x) ≤ Finset.sum s (fun i => probEvent mx (E i)) := by
  classical
  refine Finset.induction_on s (by simp) fun a s ha ih => ?_
  rw [Finset.sum_insert ha,
    show (fun x => ∃ i ∈ insert a s, E i x) = (fun x => E a x ∨ ∃ i ∈ s, E i x) by simp]
  refine (probEvent_or_le mx (E a) _).trans ?_
  gcongr


-- @@ L933-933 verbatim
end union_bound


-- @@ L935-935 verbatim
/-! ## Expectation algebra for nonnegative functionals -/


-- @@ L937-937 verbatim
section tsum_probOutput_mul


-- @@ L939-939 verbatim
variable [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF]


-- @@ L941-946 expanded
/-- Expectation of a nonnegative functional under a `pure` computation. -/
@[simp]
lemma tsum_probOutput_pure_mul (y : α) (f : α → ℝ≥0∞) :
    ∑' z, probOutput (pure y : m α) z * f z = f y := by classical simp


-- @@ L948-955 expanded
/-- Tonelli-style rearrangement: the expectation of a nonnegative functional under a
`bind` is the outer expectation of the inner expectations. -/
lemma tsum_probOutput_bind_mul (mx : m α) (g : α → m β) (f : β → ℝ≥0∞) :
    ∑' z, probOutput (mx >>= g) z * f z = ∑' x, probOutput mx x * ∑' z, probOutput (g x) z * f z :=
  by
  simp_rw [probOutput_bind_eq_tsum, ← ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_comm]
  simp_rw [mul_assoc, ENNReal.tsum_mul_left]


-- @@ L957-962 expanded
/-- Expectation of a nonnegative functional under a `Functor.map`: the functional is
precomposed with the map. -/
lemma tsum_probOutput_map_mul [LawfulMonad m] (mx : m α) (f : α → β) (g : β → ℝ≥0∞) :
    ∑' z, probOutput (f <$> mx) z * g z = ∑' x, probOutput mx x * g (f x) := by
  simp only [map_eq_bind_pure_comp, tsum_probOutput_bind_mul, Function.comp_apply,
    tsum_probOutput_pure_mul]


-- @@ L964-968 expanded
omit [Monad m] [LawfulMonadLiftT m SPMF] in
/-- Expectation is monotone in the functional. -/
lemma tsum_probOutput_mul_mono (mx : m α) {f g : α → ℝ≥0∞} (h : ∀ x, f x ≤ g x) :
    ∑' x, probOutput mx x * f x ≤ ∑' x, probOutput mx x * g x :=
  expectedValue_mono mx h


-- @@ L970-976 expanded
omit [Monad m] [LawfulMonadLiftT m SPMF] in
/-- A finite sum inside an expectation may be taken outside: linearity of expectation over a
`Finset` of summands. -/
lemma tsum_probOutput_mul_finsetSum {ι' : Type*} (mx : m α) (s : Finset ι') (f : ι' → α → ℝ≥0∞) :
    ∑' x, probOutput mx x * (∑ i ∈ s, f i x) = ∑ i ∈ s, ∑' x, probOutput mx x * f i x :=
  by
  simp_rw [Finset.mul_sum]
  exact Summable.tsum_finsetSum fun _ _ => ENNReal.summable


-- @@ L978-987 expanded
omit [Monad m] [LawfulMonadLiftT m SPMF] in
/-- The expectation of a nonnegative functional `F` that is constant (equal to `c`) on the
support of a never-failing (sub)probability computation equals `c`. -/
lemma tsum_probOutput_mul_of_const_on_support [MonadLiftT m SetM] [EvalDistCompatible m] (mx : m α)
    {c : ℝ≥0∞} {F : α → ℝ≥0∞} (hconst : ∀ z ∈ support mx, F z = c) (hmass : probFailure mx = 0) :
    ∑' z, probOutput mx z * F z = c :=
  by
  change expectedValue mx F = c
  rw [expectedValue_congr_of_support hconst]
  rw [expectedValue_def, ENNReal.tsum_mul_right, tsum_probOutput_eq_one' hmass, one_mul]


-- @@ L989-989 verbatim
end tsum_probOutput_mul
