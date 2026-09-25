/-
Copyright (c) 2025 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

module
public import VCVio.EvalDist.Defs.Measure


-- @@ L10-18 verbatim
/-!
# Typeclasses for Denotational Monad Semantics

The primary distribution `evalDist` is a Mathlib `Measure`. The explicit `evalSPMF` / `𝒮[…]`
surface remains available for finite executable distributions, and `probOutput`, `probEvent`, and
`probFailure` are discrete scalar adapters with theorems stating their meaning in `evalDist`.

-- dtumad: document various probability notation definitions here
-/


-- @@ L20-20 verbatim
@[expose] public section


-- @@ L22-22 verbatim
open MeasureTheory ENNReal


-- @@ L24-24 verbatim
universe u v w


-- @@ L26-26 verbatim
variable {m : Type u → Type v} {α β γ : Type u}


-- @@ L28-57 verbatim
/-! ## `MonadLiftT m SetM` and `MonadLiftT m SPMF`

The `SetM` / `SPMF` lifts exposed by this layer are declared as `MonadLiftT`,
not `MonadLift`. Total semantic sources may still expose a plain `MonadLift`
into `PMF`; the important point here is that support is never obtained by a
transitive `m → SPMF → SetM` path, and parameterized/typeclass-gated
probability lifts avoid `MonadLift` instance search. There are two independent
reasons.

**No transitive `SPMF → SetM` lift.** The `MonadLiftT SPMF SetM` instance below
exists so `support` and friends work on raw `SPMF α`. Crucially it is declared
as `MonadLiftT` rather than `MonadLift`, which means Lean's `monadLiftTrans`
(which requires `MonadLift n o` for the outer hop) cannot chain it: a monad
`m` with `MonadLiftT m SPMF` does **not** automatically gain `MonadLiftT m SetM`
via transitivity. Each monad declares its `MonadLiftT m SetM` directly — e.g.
`OracleComp` uses the syntactic `simulateQ` into `SetM` (which doesn't require
`[spec.Fintype]`), and `EvalDistCompatible` records the propositional coherence
between that syntactic support and `SPMF.support ∘ evalSPMF`.

**Resolution fragility for parameterized + typeclass-gated lifts.** Lifts whose
source is parameterized (`OracleComp spec`, `OptionT m`, `StateT σ m`, …) and
which are gated by a typeclass on the parameter (`[IsProbabilitySpec spec]`,
`[MonadLiftT m SPMF]`, …) must also be `MonadLiftT`, not `MonadLift`. Demoting
to `MonadLift` forces Lean to find the instance through its transitive
instance, whose outer hop is `MonadLift n o` with `n` a `semiOutParam`. When
the recursion lands on a parameterized head like `MonadLift (OracleComp ?spec) PMF`,
Lean has to simultaneously unify `?spec` through the `semiOutParam`, discharge
the typeclass premise on `?spec`, and pin down `?spec` from the inner reflexive
premise — a combination Lean's instance search refuses to chase. The direct
`MonadLiftT` declaration sidesteps this with a single-step head match. -/


-- @@ L59-62 verbatim
/-- Direct `MonadLiftT SPMF SetM` (only on `SPMF` itself — not the transitive
`MonadLift` that would create a diamond). -/
instance instMonadLiftTSPMFSetM : MonadLiftT SPMF SetM where
  monadLift := SPMF.support


-- @@ L64-66 verbatim
instance instLawfulMonadLiftTSPMFSetM : LawfulMonadLiftT SPMF SetM where
  monadLift_pure := SPMF.support_pure
  monadLift_bind := SPMF.support_bind


-- @@ L68-78 verbatim
/-- Coherence between `support` (via `MonadLiftT m SetM`) and `evalSPMF`
(via `MonadLiftT m SPMF`): `x ∈ support mx` iff `Pr[= x | mx] ≠ 0`.

This typeclass is exported by every monad that admits both lifts and they
agree on outputs — i.e. `support mx = SPMF.support (evalSPMF mx)`. -/
class EvalDistCompatible (m : Type u → Type v) [MonadLiftT m SetM]
    [MonadLiftT m SPMF] : Prop where
  /-- The reachable outputs of `mx` (via `support`) are exactly the outputs with
  nonzero probability in `evalSPMF mx`. -/
  support_eq_SPMF_support {α : Type u} (mx : m α) :
    SetM.run (liftM mx : SetM α) = SPMF.support (liftM mx : SPMF α)


-- @@ L80-80 verbatim
export EvalDistCompatible (support_eq_SPMF_support)


-- @@ L82-84 verbatim
/-- `SPMF` is trivially compatible: both lifts coincide on the nose. -/
instance : EvalDistCompatible SPMF where
  support_eq_SPMF_support _ := rfl


-- @@ L86-88 verbatim
/-- The resulting distribution of running the monadic computation `mx`. -/
@[reducible, inline]
def evalSPMF [MonadLiftT m SPMF] {α : Type u} (mx : m α) : SPMF α := liftM mx


-- @@ L90-91 verbatim
/-- Evaluation distribution notation for any monad lifting into `SPMF`. -/
notation "𝒮[" mx "]" => evalSPMF mx


-- @@ L93-94 expanded
lemma evalSPMF_def [MonadLiftT m SPMF] {α : Type u} (mx : m α) : evalSPMF mx = liftM mx :=
  rfl


-- @@ L96-98 expanded
@[simp]
lemma evalSPMF_id (p : SPMF α) : evalSPMF p = p :=
  monadLift_self p


-- @@ L100-107 expanded
/-- The whole-denotation unfolding of the compatibility adapter.

The theorem has only the legacy `MonadLiftT m SPMF` assumption, so the measure on the left is
the adapter instance defined in `Defs.Measure`; a measure-native semantics is reasoned about
through the `DiscreteEvalDistCompatible` bridges instead of being converted back to an `SPMF`. -/
theorem evalDist_eq_evalSPMF_toMeasure [MonadLiftT m SPMF] [MeasurableSpace α] (mx : m α) :
    evalDist mx = (evalSPMF mx).toMeasure :=
  rfl


-- @@ L109-109 verbatim
section probability_notation


-- @@ L111-116 verbatim
/-- Probability that a computation `mx` returns the value `x`.

This remains definitionally the point mass of the executable `SPMF` semantics;
`evalDist_apply_singleton` is the equivalent measure-level reading. -/
def probOutput [MonadLiftT m SPMF] (mx : m α) (x : α) : ℝ≥0∞ :=
  evalSPMF mx x


-- @@ L118-124 verbatim
/-- Probability that a computation `mx` outputs a value satisfying `p`.

The traditional notation remains the executable `SPMF` event API and is therefore usable for
arbitrary predicates. General measure developments should apply `𝒟[mx]` to a measurable event;
`evalDist_apply_setOf` bridges the two on discrete spaces. -/
noncomputable def probEvent [MonadLiftT m SPMF] (mx : m α) (p : α → Prop) : ℝ≥0∞ :=
  (evalSPMF mx).run.toOuterMeasure (some '' {x | p x})


-- @@ L126-128 verbatim
/-- Probability that a computation `mx` will fail to return a value. -/
def probFailure [MonadLiftT m SPMF] (mx : m α) : ℝ≥0∞ :=
  (evalSPMF mx).run none


-- @@ L130-131 verbatim
/-- Probability that a computation returns a particular output. -/
notation "Pr[= " x " | " mx "]" => probOutput mx x


-- @@ L133-135 verbatim
/-- Probability that a computation returns a value satisfying a predicate. -/
macro (name := probEventNotation) "Pr[ " p:term " | " mx:term "]" : term =>
  `(probEvent $mx $p)


-- @@ L137-138 verbatim
/-- Probability that a computation fails to return a value. -/
notation "Pr[⊥" " | " mx "]" => probFailure mx


-- @@ L140-140 verbatim
section probOutput


-- @@ L142-144 verbatim
variable [MonadLiftT m SPMF]

-- dtumad: I think maybe we want to simp in the `←` direction here?

-- @@ L145-146 expanded
@[aesop norm (rule_sets := [UnfoldEvalDist]), grind =]
lemma probOutput_def (mx : m α) (x : α) : probOutput mx x = evalSPMF mx x :=
  rfl


-- @@ L148-148 verbatim
variable [MonadLiftT m SetM] [EvalDistCompatible m]


-- @@ L150-154 expanded
@[grind =]
lemma mem_support_iff (mx : m α) (x : α) : x ∈ support mx ↔ probOutput mx x ≠ 0 := by
  rw [support_def, support_eq_SPMF_support, SPMF.mem_support_iff, probOutput_def, evalSPMF_def]


-- @@ L156-157 expanded
lemma mem_support_iff_evalSPMF_apply_ne_zero (mx : m α) (x : α) :
    x ∈ support mx ↔ (evalSPMF mx) x ≠ 0 := by grind


-- @@ L159-161 expanded
@[grind =]
lemma mem_finSupport_iff [DecidableEq α] [HasEvalFinset m] (mx : m α) (x : α) :
    x ∈ finSupport mx ↔ probOutput mx x ≠ 0 := by grind


-- @@ L163-165 expanded
@[aesop unsafe 50% forward]
lemma probOutput_ne_zero_of_mem_support {mx : m α} {x : α} (h : x ∈ support mx) :
    probOutput mx x ≠ 0 := by rwa [mem_support_iff] at h


-- @@ L167-169 expanded
@[aesop safe norm, grind =]
lemma probOutput_eq_zero_of_not_mem_support {mx : m α} {x : α} (h : x ∉ support mx) :
    probOutput mx x = 0 := by rwa [mem_support_iff, not_not] at h


-- @@ L171-172 expanded
@[simp low, grind =]
lemma probOutput_eq_zero_iff (mx : m α) (x : α) : probOutput mx x = 0 ↔ x ∉ support mx := by aesop


-- @@ L174-174 verbatim
alias ⟨not_mem_support_of_probOutput_eq_zero, probOutput_eq_zero⟩ := probOutput_eq_zero_iff


-- @@ L176-176 verbatim
variable (mx : m α) (x : α)


-- @@ L178-179 expanded
@[simp low]
lemma zero_eq_probOutput_iff : 0 = probOutput mx x ↔ x ∉ support mx := by
  rw [eq_comm, probOutput_eq_zero_iff]


-- @@ L180-180 verbatim
alias ⟨_, zero_eq_probOutput⟩ := zero_eq_probOutput_iff


-- @@ L182-183 expanded
@[simp, grind =]
lemma probOutput_eq_zero_iff' [HasEvalFinset m] [DecidableEq α] :
    probOutput mx x = 0 ↔ x ∉ finSupport mx := by rw [mem_finSupport_iff_mem_support]; aesop


-- @@ L184-184 verbatim
alias ⟨not_mem_fin_support_of_probOutput_eq_zero, probOutput_eq_zero'⟩ := probOutput_eq_zero_iff'


-- @@ L186-187 expanded
@[simp, grind =]
lemma zero_eq_probOutput_iff' [HasEvalFinset m] [DecidableEq α] :
    0 = probOutput mx x ↔ x ∉ finSupport mx := by rw [eq_comm, probOutput_eq_zero_iff']


-- @@ L188-188 verbatim
alias ⟨_, zero_eq_probOutput'⟩ := zero_eq_probOutput_iff'


-- @@ L190-192 expanded
@[simp, grind =]
lemma probOutput_pos_iff : 0 < probOutput mx x ↔ x ∈ support mx := by
  rw [pos_iff_ne_zero, ne_eq, probOutput_eq_zero_iff, not_not]


-- @@ L193-193 verbatim
alias ⟨mem_support_of_probOutput_pos, probOutput_pos⟩ := probOutput_pos_iff


-- @@ L195-197 expanded
@[grind =]
lemma probOutput_pos_iff' [HasEvalFinset m] [DecidableEq α] :
    0 < probOutput mx x ↔ x ∈ finSupport mx := by grind


-- @@ L198-198 verbatim
alias ⟨mem_finSupport_of_probOutput_pos, probOutput_pos'⟩ := probOutput_pos_iff'


-- @@ L200-204 expanded
instance decidablePred_probOutput_eq_zero [hm : HasEvalSet.Decidable m] (mx : m α) :
    DecidablePred (probOutput mx · = 0) :=
  by
  simp only [probOutput_eq_zero_iff]
  infer_instance


-- @@ L206-207 expanded
@[aesop unsafe apply]
lemma probOutput_ne_zero (h : x ∈ support mx) : probOutput mx x ≠ 0 := by simp [h]


-- @@ L209-212 expanded
@[aesop unsafe apply]
lemma probOutput_ne_zero' [HasEvalFinset m] [DecidableEq α] (h : x ∈ finSupport mx) :
    probOutput mx x ≠ 0 :=
  probOutput_ne_zero mx x (mem_support_of_mem_finSupport h)


-- @@ L214-215 verbatim
@[simp]
lemma support_probOutput : Function.support (probOutput mx) = support mx := by aesop


-- @@ L217-217 verbatim
end probOutput


-- @@ L219-219 verbatim
section probEvent


-- @@ L221-223 expanded
@[aesop norm (rule_sets := [UnfoldEvalDist])]
lemma probEvent_def [MonadLiftT m SPMF] (mx : m α) (p : α → Prop) :
    probEvent mx p = (evalSPMF mx).run.toOuterMeasure (some '' {x | p x}) :=
  rfl


-- @@ L225-230 expanded
@[grind =]
lemma probEvent_eq_tsum_indicator [MonadLiftT m SPMF] (mx : m α) (p : α → Prop) :
    probEvent mx p = ∑' x : α, {x | p x}.indicator (probOutput mx ·) x := by
  simp [probEvent_def, PMF.toOuterMeasure_apply, tsum_option _ ENNReal.summable,
    Set.indicator_image (Option.some_injective _), Function.comp_def, probOutput_def,
    SPMF.apply_eq_toPMF_some]


-- @@ L232-235 expanded
@[grind =]
lemma probEvent_eq_sum_fintype_indicator [MonadLiftT m SPMF] [Fintype α] (mx : m α) (p : α → Prop) :
    probEvent mx p = ∑ x : α, {x | p x}.indicator (probOutput mx ·) x :=
  (probEvent_eq_tsum_indicator mx p).trans (tsum_fintype _)


-- @@ L237-240 expanded
@[grind =]
lemma probEvent_eq_tsum_ite [MonadLiftT m SPMF] (mx : m α) (p : α → Prop) [DecidablePred p] :
    probEvent mx p = ∑' x : α, if p x then probOutput mx x else 0 := by grind [Set.indicator]


-- @@ L242-245 expanded
@[grind =]
lemma probEvent_eq_sum_fintype_ite [MonadLiftT m SPMF] [Fintype α] (mx : m α) (p : α → Prop)
    [DecidablePred p] : probEvent mx p = ∑ x : α, if p x then probOutput mx x else 0 := by
  grind [Set.indicator]


-- @@ L247-249 expanded
lemma probEvent_eq_tsum_subtype [MonadLiftT m SPMF] (mx : m α) (p : α → Prop) :
    probEvent mx p = ∑' x : {x | p x}, probOutput mx x := by
  rw [probEvent_eq_tsum_indicator, tsum_subtype]


-- @@ L251-254 expanded
lemma probEvent_eq_sum_filter_univ [MonadLiftT m SPMF] [Fintype α] (mx : m α) (p : α → Prop)
    [DecidablePred p] : probEvent mx p = ∑ x ∈ Finset.univ.filter p, probOutput mx x := by
  rw [probEvent_eq_sum_fintype_ite, Finset.sum_filter]


-- @@ L256-256 verbatim
variable [MonadLiftT m SPMF]


-- @@ L258-258 verbatim
section zero


-- @@ L260-262 verbatim
variable [MonadLiftT m SetM] [EvalDistCompatible m] {mx : m α} {p : α → Prop}

-- `simp`-only: `grind` saturates on this support-quantifier characterization.

-- @@ L263-266 expanded
@[simp]
lemma probEvent_eq_zero_iff : probEvent mx p = 0 ↔ ∀ x ∈ support mx, ¬p x := by
  rw [probEvent_eq_tsum_indicator]; aesop


-- @@ L267-270 verbatim
alias ⟨_, probEvent_eq_zero⟩ := probEvent_eq_zero_iff

-- Named finite-support rewrite; not registered for `grind`, which saturates on this
-- support-quantifier characterization.

-- @@ L271-272 expanded
lemma probEvent_eq_zero_iff' [HasEvalFinset m] [DecidableEq α] :
    probEvent mx p = 0 ↔ ∀ x ∈ finSupport mx, ¬p x := by grind [probEvent_eq_zero_iff]


-- @@ L273-276 verbatim
alias ⟨_, probEvent_eq_zero'⟩ := probEvent_eq_zero_iff'

-- Named rewrite; not registered for `grind`, which saturates on this support-quantifier
-- characterization.

-- @@ L277-278 expanded
lemma probEvent_ne_zero_iff : probEvent mx p ≠ 0 ↔ ∃ x ∈ support mx, p x := by
  grind [probEvent_eq_zero_iff]


-- @@ L279-281 verbatim
alias ⟨_, probEvent_ne_zero⟩ := probEvent_ne_zero_iff

-- Named finite-support rewrite; no `grind` registration for the same reason.

-- @@ L282-283 expanded
lemma probEvent_ne_zero_iff' [HasEvalFinset m] [DecidableEq α] :
    probEvent mx p ≠ 0 ↔ ∃ x ∈ finSupport mx, p x := by aesop


-- @@ L284-287 verbatim
alias ⟨_, probEvent_ne_zero'⟩ := probEvent_ne_zero_iff'

-- `grind`-safe in isolation: this support-quantifier characterization saturates `grind` only in
-- combination with the `probEvent_eq_one_iff` family (kept `simp`-only). See `probability.md`.

-- @@ L288-290 expanded
@[simp, grind =]
lemma probEvent_pos_iff : 0 < probEvent mx p ↔ ∃ x ∈ support mx, p x := by simp [pos_iff_ne_zero]


-- @@ L291-293 verbatim
alias ⟨_, probEvent_pos⟩ := probEvent_pos_iff

-- `grind`-safe in isolation; see `probEvent_pos_iff`.

-- @@ L294-296 expanded
@[grind =]
lemma probEvent_pos_iff' [HasEvalFinset m] [DecidableEq α] :
    0 < probEvent mx p ↔ ∃ x ∈ finSupport mx, p x := by grind [probEvent_pos_iff]


-- @@ L297-297 verbatim
alias ⟨_, probEvent_pos'⟩ := probEvent_pos_iff'


-- @@ L299-312 expanded
/-- `Set.Nonempty` companion to the named rewrite `probEvent_ne_zero_iff`: the event has positive
probability iff some reachable output satisfies `p`. The `Set.Nonempty` witness stays atomic under
`grind` (unlike the saturating `∃ x ∈ support mx, p x` form). Mirrors
`probFailure_eq_one_iff_not_nonempty`.

Deliberately NOT in the default `grind` set: together with `probEvent_eq_zero_iff_not_nonempty`
and `probFailure_eq_one_iff_not_nonempty` it re-forms a saturation cycle in the generic-monad
context (`grind` times out on the `probEvent_eq_one_iff` statement shape with all three tagged;
dropping any one of the trio restores fail-fast, and dropping this one is free: `grind` recovers
`≠ 0 ↔ Nonempty` from the kept `= 0 ↔ ¬ Nonempty` sibling by classical negation). Gated by
`VCVioTest/GrindFailFast.lean`. -/
lemma probEvent_ne_zero_iff_nonempty : probEvent mx p ≠ 0 ↔ {x ∈ support mx | p x}.Nonempty := by
  rw [probEvent_ne_zero_iff]; simp [Set.nonempty_def]


-- @@ L314-321 expanded
/-- `grind`-friendly companion to the `simp`-only `probEvent_eq_zero_iff`: the event has probability
zero iff no reachable output satisfies `p`, phrased via `Set.Nonempty` rather than the saturating
`∀ x ∈ support mx, ¬ p x`. The negation of `probEvent_ne_zero_iff_nonempty`. -/
@[grind =]
lemma probEvent_eq_zero_iff_not_nonempty : probEvent mx p = 0 ↔ ¬{x ∈ support mx | p x}.Nonempty :=
  by
  rw [probEvent_eq_zero_iff]
  simp [Set.not_nonempty_iff_eq_empty, Set.eq_empty_iff_forall_notMem]


-- @@ L323-323 verbatim
end zero


-- @@ L325-325 verbatim
section supportMixed


-- @@ L327-327 verbatim
variable [MonadLiftT m SetM] [EvalDistCompatible m]


-- @@ L329-333 expanded
lemma probEvent_eq_tsum_subtype_mem_support (mx : m α) (p : α → Prop) :
    probEvent mx p = ∑' x : {x ∈ support mx | p x}, probOutput mx x :=
  by
  rw [probEvent_eq_tsum_subtype, tsum_subtype, tsum_subtype, ← support_probOutput, ←
    Set.indicator_inter_support]
  simp [Set.inter_def, and_comm]


-- @@ L335-338 expanded
lemma probEvent_eq_tsum_subtype_support_ite (mx : m α) (p : α → Prop) [DecidablePred p] :
    probEvent mx p = ∑' x : support mx, if p x then probOutput mx x else 0 :=
  by
  rw [probEvent_eq_tsum_ite, ← tsum_subtype_eq_of_support_subset (s := support mx)]
  grind [Function.support_subset_iff]


-- @@ L340-345 expanded
lemma probEvent_eq_sum_filter_finSupport [HasEvalFinset m] [DecidableEq α] (mx : m α) (p : α → Prop)
    [DecidablePred p] : probEvent mx p = ∑ x ∈ (finSupport mx).filter p, probOutput mx x :=
  (probEvent_eq_tsum_ite mx p).trans <|
    (tsum_eq_sum' <| by simp; tauto).trans
      (Finset.sum_congr rfl <| fun x hx ↦ if_pos (Finset.mem_filter.1 hx).2)


-- @@ L347-350 expanded
lemma probEvent_eq_sum_finSupport_ite [HasEvalFinset m] [DecidableEq α] (mx : m α) (p : α → Prop)
    [DecidablePred p] : probEvent mx p = ∑ x ∈ finSupport mx, if p x then probOutput mx x else 0 :=
  by rw [probEvent_eq_sum_filter_finSupport, Finset.sum_filter]


-- @@ L352-359 expanded
/-- If two events are equivalent on the support of `mx` then they have the same output chance. -/
@[aesop unsafe apply, grind .]
lemma probEvent_ext {mx : m α} {p q : α → Prop} (h : ∀ x ∈ support mx, p x ↔ q x) :
    probEvent mx p = probEvent mx q := by
  classical
  rw [probEvent_eq_tsum_ite, probEvent_eq_tsum_ite]
  refine tsum_congr fun x => ?_
  split_ifs <;> grind


-- @@ L361-361 verbatim
end supportMixed


-- @@ L363-367 expanded
@[simp, grind =_, aesop unsafe norm]
lemma probEvent_eq_eq_probOutput (mx : m α) (x : α) : probEvent mx (· = x) = probOutput mx x := by
  simp [probEvent_def, PMF.toOuterMeasure_apply_singleton, probOutput_def, SPMF.apply_eq_toPMF_some]


-- @@ L369-373 expanded
@[simp, grind =_, aesop unsafe norm]
lemma probEvent_eq_eq_probOutput' (mx : m α) (x : α) : probEvent mx (x = ·) = probOutput mx x :=
  by
  have h : (fun y => x = y) = (fun y => y = x) := funext fun _ => propext eq_comm
  rw [h]; exact probEvent_eq_eq_probOutput mx x


-- @@ L375-375 verbatim
end probEvent


-- @@ L377-377 verbatim
section probFailure


-- @@ L379-381 expanded
@[aesop norm (rule_sets := [UnfoldEvalDist]), grind =]
lemma probFailure_def [MonadLiftT m SPMF] (mx : m α) : probFailure mx = (evalSPMF mx).run none :=
  rfl


-- @@ L383-386 expanded
@[simp]
lemma probOutput_evalSPMF [MonadLiftT m SPMF] (mx : m α) (x : α) :
    probOutput (evalSPMF mx) x = probOutput mx x := by
  rw [probOutput_def, probOutput_def, evalSPMF_id]


-- @@ L388-391 expanded
@[simp]
lemma probEvent_evalSPMF [MonadLiftT m SPMF] (mx : m α) (p : α → Prop) :
    probEvent (evalSPMF mx) p = probEvent mx p := by rw [probEvent_def, probEvent_def, evalSPMF_id]


-- @@ L393-396 expanded
@[simp]
lemma probFailure_evalSPMF [MonadLiftT m SPMF] (mx : m α) :
    probFailure (evalSPMF mx) = probFailure mx := by
  rw [probFailure_def, probFailure_def, evalSPMF_id]


-- @@ L398-398 verbatim
end probFailure


-- @@ L400-402 verbatim
/-- Probability that a computation returns a value satisfying a predicate. -/
syntax (name := probEventBinding1)
  "Pr[ " term " | " ident " ← " term "]" : term


-- @@ L404-405 expanded
macro_rules (kind:=probEventBinding1)
  | `(Pr[ $cond:term | $var:ident ← $src:term]) => `(probEvent $src fun $var => $cond)


-- @@ L407-409 verbatim
/-- Probability that a computation returns a value satisfying a predicate.
See `probOutput_true_eq_probEvent` for relation to the above definitions. -/
syntax (name := probEventBinding2) "Pr{" doSeq "}[" term "]" : term


-- @@ L411-415 expanded
macro_rules (kind:=probEventBinding2)
  -- `doSeqBracketed`
  
  |
  `(probOutput
        (do $items*
          return $t)
        True) =>
    `(probOutput
        (do $items:doSeqItem*
          return $t:term)
        True)
      -- `doSeqIndent`
      
  |
  `(probOutput
        (do $items*
          return $t)
        True) =>
    `(probOutput
        (do $items:doSeqItem*
          return $t:term)
        True)


-- @@ L417-424 expanded
/-- Tests for all the different probability notations. -/
noncomputable example {m : Type → Type u} [Monad m] [MonadLiftT m SPMF] (mx : m ℕ) : Unit :=
  let _ := probOutput mx 10
  let _ := probEvent mx fun x => x ^ 2 + x < 10
  let _ := probEvent mx fun x => x ^ 2 + x < 10
  let _ :=
    probOutput
      (do
        let x ← mx
        return x = 10)
      True
  let _ := probFailure mx
  ()


-- @@ L426-426 verbatim
end probability_notation


-- @@ L428-432 expanded
@[simp] -- TODO: versions for other constructions?
  
lemma evalSPMF_cast {m} [Monad m] [MonadLiftT m SPMF] (h : α = β) (mx : m α) :
    evalSPMF (cast (congrArg m h) mx) = cast (congrArg SPMF h) (evalSPMF mx) := by induction h; rfl


-- @@ L434-438 expanded
lemma evalSPMF_ext {m n} [Monad m] [MonadLiftT m SPMF] [Monad n] [MonadLiftT n SPMF] {mx : m α}
    {mx' : n α} (h : ∀ x, probOutput mx x = probOutput mx' x) : evalSPMF mx = evalSPMF mx' :=
  by
  apply SPMF.ext
  intro x
  simpa only [probOutput_def] using h x


-- @@ L440-443 expanded
lemma evalSPMF_ext_iff {m n} [Monad m] [MonadLiftT m SPMF] [Monad n] [MonadLiftT n SPMF] {mx : m α}
    {mx' : n α} : evalSPMF mx = evalSPMF mx' ↔ ∀ x, probOutput mx x = probOutput mx' x :=
  by
  refine ⟨fun h => ?_, evalSPMF_ext⟩
  simp [probOutput_def, h]


-- @@ L445-450 expanded
@[simp, grind =]
lemma evalSPMF_eq_liftM_iff [MonadLiftT m SPMF] (mx : m α) (p : PMF α) :
    evalSPMF mx = liftM p ↔ ∀ x, probOutput mx x = p x :=
  by
  refine ⟨fun h x => ?_, fun h => ?_⟩
  · simp [probOutput_def, h]
  · simpa [SPMF.eq_liftM_iff_forall, probOutput_def] using h


-- @@ L452-463 expanded
@[simp, grind =]
lemma evalSPMF_eq_mk_iff [MonadLiftT m SPMF] (mx : m α) (p : PMF (Option α)) :
    evalSPMF mx = SPMF.mk p ↔ ∀ x, probOutput mx x = p (some x) :=
  by
  constructor
  · intro h x
    rw [probOutput_def, h]
    rfl
  · intro h
    apply SPMF.ext
    intro x
    change (evalSPMF mx) x = p (some x)
    simpa only [probOutput_def] using h x


-- @@ L465-467 expanded
@[aesop unsafe apply]
lemma evalSPMF_eq_liftM [MonadLiftT m SPMF] {mx : m α} {p : PMF α}
    (h : ∀ x, probOutput mx x = p x) : evalSPMF mx = liftM p := by aesop


-- @@ L469-475 expanded
lemma evalSPMF_apply_eq_zero_iff [MonadLiftT m SPMF] [MonadLiftT m SetM] [EvalDistCompatible m]
    (mx : m α) (x : Option α) :
    (evalSPMF mx).run x = 0 ↔ x.rec (probFailure mx = 0) (· ∉ support mx) := by
  induction x with
  | none => simp [probFailure_def]
  | some y =>
    simp [OptionT.run, mem_support_iff_evalSPMF_apply_ne_zero, SPMF.apply_eq_toPMF_some, SPMF.toPMF]


-- @@ L477-481 expanded
lemma evalSPMF_apply_eq_zero_iff' [MonadLiftT m SPMF] [MonadLiftT m SetM] [EvalDistCompatible m]
    [HasEvalFinset m] [DecidableEq α] (mx : m α) (x : Option α) :
    (evalSPMF mx).run x = 0 ↔ x.rec (probFailure mx = 0) (· ∉ finSupport mx) :=
  by
  rw [evalSPMF_apply_eq_zero_iff]
  grind


-- @@ L483-483 verbatim
/-! ## Pushing probabilities through `ite`, `dite`, and `Eq.rec` -/


-- @@ L485-485 verbatim
section ite


-- @@ L487-487 verbatim
variable (p : Prop) [Decidable p]


-- @@ L489-490 expanded
@[simp]
lemma evalSPMF_ite [MonadLiftT m SPMF] (mx mx' : m α) :
    evalSPMF (if p then mx else mx') = if p then evalSPMF mx else evalSPMF mx' := by grind


-- @@ L492-493 expanded
@[simp]
lemma probOutput_ite [MonadLiftT m SPMF] (x : α) (mx mx' : m α) :
    probOutput (if p then mx else mx') x = if p then probOutput mx x else probOutput mx' x := by
  aesop


-- @@ L495-496 expanded
@[simp]
lemma probFailure_ite [MonadLiftT m SPMF] (mx mx' : m α) :
    probFailure (if p then mx else mx') = if p then probFailure mx else probFailure mx' := by grind


-- @@ L498-499 expanded
@[simp]
lemma probEvent_ite [MonadLiftT m SPMF] (mx mx' : m α) (q : α → Prop) :
    probEvent (if p then mx else mx') q = if p then probEvent mx q else probEvent mx' q := by aesop


-- @@ L501-503 expanded
@[simp]
lemma evalSPMF_dite [MonadLiftT m SPMF] (mx : p → m α) (mx' : ¬p → m α) :
    evalSPMF (if h : p then mx h else mx' h) =
      if h : p then evalSPMF (mx h) else evalSPMF (mx' h) :=
  by split <;> rfl


-- @@ L505-508 expanded
@[simp]
lemma probOutput_dite [MonadLiftT m SPMF] (x : α) (mx : p → m α) (mx' : ¬p → m α) :
    probOutput (if h : p then mx h else mx' h) x =
      if h : p then probOutput (mx h) x else probOutput (mx' h) x :=
  by split <;> rfl


-- @@ L510-513 expanded
@[simp]
lemma probFailure_dite [MonadLiftT m SPMF] (mx : p → m α) (mx' : ¬p → m α) :
    probFailure (if h : p then mx h else mx' h) =
      if h : p then probFailure (mx h) else probFailure (mx' h) :=
  by split <;> rfl


-- @@ L515-518 expanded
@[simp]
lemma probEvent_dite [MonadLiftT m SPMF] (mx : p → m α) (mx' : ¬p → m α) (q : α → Prop) :
    probEvent (if h : p then mx h else mx' h) q =
      if h : p then probEvent (mx h) q else probEvent (mx' h) q :=
  by split <;> rfl


-- @@ L520-520 verbatim
end ite


-- @@ L522-522 verbatim
section eqRec


-- @@ L524-525 expanded
lemma evalSPMF_eqRec [MonadLiftT m SPMF] (h : α = β) (mx : m α) :
    evalSPMF (h ▸ mx : m β) = h ▸ evalSPMF mx := by grind


-- @@ L527-528 expanded
lemma probOutput_eqRec [MonadLiftT m SPMF] (h : α = β) (mx : m α) (y : β) :
    probOutput (h ▸ mx) y = probOutput mx (h ▸ y) := by induction h; rfl


-- @@ L530-531 expanded
@[simp]
lemma probFailure_eqRec [MonadLiftT m SPMF] (h : α = β) (mx : m α) :
    probFailure (h ▸ mx) = probFailure mx := by induction h; rfl


-- @@ L533-534 expanded
lemma probEvent_eqRec [MonadLiftT m SPMF] (h : α = β) (mx : m α) (q : β → Prop) :
    probEvent (h ▸ mx) q = probEvent mx fun x ↦ q (h ▸ x) := by induction h; rfl


-- @@ L536-536 verbatim
end eqRec


-- @@ L538-538 verbatim
section sums


-- @@ L540-545 expanded
/-- Connection between the two different probability notations. -/
lemma probOutput_true_eq_probEvent {α} {m : Type → Type u} [Monad m] [MonadLiftT m SPMF]
    [LawfulMonadLiftT m SPMF] (mx : m α) (p : α → Prop) :
    probOutput
        (do
          let x ← mx
          return p x)
        True =
      probEvent mx p :=
  by
  simp [probEvent_eq_tsum_indicator, probOutput_def, evalSPMF, map_eq_bind_pure_comp]
  congr 1; aesop


-- @@ L547-549 expanded
lemma tsum_probOutput_add_probFailure [MonadLiftT m SPMF] (mx : m α) :
    (∑' x, probOutput mx x) + probFailure mx = 1 := by aesop  (rule_sets := [UnfoldEvalDist])


-- @@ L551-553 expanded
lemma probFailure_add_tsum_probOutput [MonadLiftT m SPMF] (mx : m α) :
    probFailure mx + ∑' x, probOutput mx x = 1 := by aesop  (rule_sets := [UnfoldEvalDist])


-- @@ L555-555 verbatim
end sums


-- @@ L557-557 verbatim
/-! ## Probability bounds and total-probability sums -/


-- @@ L559-559 verbatim
section bounds


-- @@ L561-561 verbatim
variable {mx : m α} {mxe : OptionT m α} {x : α} {p : α → Prop}


-- @@ L563-563 verbatim
section spmf


-- @@ L565-565 verbatim
variable [MonadLiftT m SPMF]


-- @@ L567-568 expanded
@[simp, grind .]
lemma probOutput_le_one : probOutput mx x ≤ 1 := by rw [probOutput_def];
  exact PMF.coe_le_one (evalSPMF mx) x


-- @@ L569-571 expanded
@[simp, grind ., aesop (rule_sets := [finiteness]) safe apply]
lemma probOutput_ne_top : probOutput mx x ≠ ∞ := by rw [probOutput_def];
  exact PMF.apply_ne_top (evalSPMF mx) x


-- @@ L572-573 expanded
@[simp, grind .]
lemma probOutput_lt_top : probOutput mx x < ∞ := by rw [probOutput_def];
  exact PMF.apply_lt_top (evalSPMF mx) x


-- @@ L574-575 expanded
@[simp, grind .]
lemma not_one_lt_probOutput : ¬1 < probOutput mx x :=
  not_lt.2 probOutput_le_one


-- @@ L577-578 expanded
lemma tsum_probOutput_le_one : ∑' x : α, probOutput mx x ≤ 1 :=
  le_of_le_of_eq (le_add_self) (probFailure_add_tsum_probOutput mx)


-- @@ L579-581 expanded
@[aesop (rule_sets := [finiteness]) safe apply]
lemma tsum_probOutput_ne_top : ∑' x : α, probOutput mx x ≠ ⊤ :=
  ne_top_of_le_ne_top one_ne_top tsum_probOutput_le_one


-- @@ L583-586 expanded
@[simp, grind .]
lemma probEvent_le_one : probEvent mx p ≤ 1 :=
  by
  rw [probEvent_def, PMF.toOuterMeasure_apply]
  refine le_of_le_of_eq (ENNReal.tsum_le_tsum ?_) ((evalSPMF mx).tsum_coe)
  exact Set.indicator_le_self (some '' {x | p x}) _


-- @@ L588-590 expanded
@[simp, grind ., aesop (rule_sets := [finiteness]) safe apply]
lemma probEvent_ne_top : probEvent mx p ≠ ∞ :=
  ne_top_of_le_ne_top one_ne_top probEvent_le_one


-- @@ L591-592 expanded
@[simp, grind .]
lemma probEvent_lt_top : probEvent mx p < ∞ :=
  lt_top_iff_ne_top.2 probEvent_ne_top


-- @@ L593-594 expanded
@[simp, grind .]
lemma not_one_lt_probEvent : ¬1 < probEvent mx p :=
  not_lt.2 probEvent_le_one


-- @@ L596-597 expanded
@[simp, grind .]
lemma probFailure_le_one : probFailure mx ≤ 1 := by rw [probFailure_def];
  exact PMF.coe_le_one (evalSPMF mx) none


-- @@ L598-600 expanded
@[simp, grind ., aesop (rule_sets := [finiteness]) safe apply]
lemma probFailure_ne_top : probFailure mx ≠ ∞ := by rw [probFailure_def];
  exact PMF.apply_ne_top (evalSPMF mx) none


-- @@ L601-602 expanded
@[simp, grind .]
lemma probFailure_lt_top : probFailure mx < ∞ := by rw [probFailure_def];
  exact PMF.apply_lt_top (evalSPMF mx) none


-- @@ L603-604 expanded
@[simp, grind .]
lemma not_one_lt_probFailure : ¬1 < probFailure mx :=
  not_lt.2 probFailure_le_one


-- @@ L606-606 verbatim
end spmf


-- @@ L608-610 expanded
@[simp, grind =]
lemma one_le_probOutput_iff [MonadLiftT m SPMF] : 1 ≤ probOutput mx x ↔ probOutput mx x = 1 := by
  simp only [le_iff_eq_or_lt, not_one_lt_probOutput, or_false, eq_comm]


-- @@ L612-614 expanded
@[simp, grind =]
lemma one_le_probEvent_iff [MonadLiftT m SPMF] : 1 ≤ probEvent mx p ↔ probEvent mx p = 1 := by
  simp only [le_iff_eq_or_lt, not_one_lt_probEvent, or_false, eq_comm]


-- @@ L616-620 expanded
@[simp, grind =]
lemma one_le_probFailure_iff [MonadLiftT m SPMF] : 1 ≤ probFailure mx ↔ probFailure mx = 1 := by
  simp only [le_iff_eq_or_lt, not_one_lt_probFailure, or_false, eq_comm]
    -- `simp`-only: `grind` saturates on this support-quantifier characterization.


-- @@ L621-626 expanded
@[simp]
lemma probOutput_eq_one_iff [MonadLiftT m SPMF] [MonadLiftT m SetM] [EvalDistCompatible m] :
    probOutput mx x = 1 ↔ probFailure mx = 0 ∧ support mx = { x } :=
  by
  rw [← probEvent_eq_eq_probOutput]
  simp [probOutput_def, probFailure_def, SPMF.apply_eq_toPMF_some, PMF.apply_eq_one_iff,
    Set.ext_iff, Option.forall, mem_support_iff_evalSPMF_apply_ne_zero]


-- @@ L627-629 verbatim
alias ⟨_, probOutput_eq_one⟩ := probOutput_eq_one_iff

-- `simp`-only: `grind` saturates on this support-quantifier characterization.

-- @@ L630-633 expanded
@[simp]
lemma one_eq_probOutput_iff [MonadLiftT m SPMF] [MonadLiftT m SetM] [EvalDistCompatible m] :
    1 = probOutput mx x ↔ probFailure mx = 0 ∧ support mx = { x } := by
  rw [eq_comm, probOutput_eq_one_iff]


-- @@ L634-637 verbatim
alias ⟨_, one_eq_probOutput⟩ := one_eq_probOutput_iff

-- `grind`-safe in isolation, and the natural mirror of `one_eq_probOutput_iff'` (which kept its
-- `grind` tag): both are the `finSupport`-singleton characterization. See `probability.md`.

-- @@ L638-642 expanded
@[grind =]
lemma probOutput_eq_one_iff' [MonadLiftT m SPMF] [MonadLiftT m SetM] [EvalDistCompatible m]
    [HasEvalFinset m] [DecidableEq α] :
    probOutput mx x = 1 ↔ probFailure mx = 0 ∧ finSupport mx = { x } := by
  rw [probOutput_eq_one_iff, finSupport_eq_iff_support_eq_coe, Finset.coe_singleton]


-- @@ L643-643 verbatim
alias ⟨_, probOutput_eq_one'⟩ := probOutput_eq_one_iff'


-- @@ L645-649 expanded
@[grind =]
lemma one_eq_probOutput_iff' [MonadLiftT m SPMF] [MonadLiftT m SetM] [EvalDistCompatible m]
    [HasEvalFinset m] [DecidableEq α] :
    1 = probOutput mx x ↔ probFailure mx = 0 ∧ finSupport mx = { x } := by
  rw [eq_comm, probOutput_eq_one_iff']


-- @@ L650-650 verbatim
alias ⟨_, one_eq_probOutput'⟩ := one_eq_probOutput_iff'


-- @@ L652-659 expanded
/-- If a non-failing computation can only return `x`, then it returns `x` with probability one. -/
lemma probOutput_eq_one_of_support_subset_singleton [MonadLiftT m SPMF] [MonadLiftT m SetM]
    [EvalDistCompatible m] (hnf : probFailure mx = 0) (huniq : ∀ y ∈ support mx, y = x) :
    probOutput mx x = 1 := by
  simpa [hnf,
    tsum_eq_single (f := (probOutput mx ·)) x fun y hy ↦
        (probOutput_eq_zero_iff _ _).mpr fun hmem ↦ hy (huniq y hmem)] using
    probFailure_add_tsum_probOutput mx


-- @@ L661-661 verbatim
end bounds


-- @@ L663-663 verbatim
section mono_le


-- @@ L665-665 verbatim
variable [MonadLiftT m SPMF] (mx : m α) (r : ℝ≥0∞)


-- @@ L667-669 expanded
@[simp]
lemma probFailure_mul_le : probFailure mx * r ≤ r :=
  mul_le_of_le_one_left' <| by simp


-- @@ L671-673 expanded
@[simp]
lemma mul_probFailure_le : r * probFailure mx ≤ r :=
  mul_le_of_le_one_right' <| by simp


-- @@ L675-676 expanded
@[simp]
lemma probOutput_mul_le (x : α) : probOutput mx x * r ≤ r :=
  mul_le_of_le_one_left' <| by simp


-- @@ L678-679 expanded
@[simp]
lemma mul_probOutput_le (x : α) : r * probOutput mx x ≤ r :=
  mul_le_of_le_one_right' <| by simp


-- @@ L681-682 expanded
@[simp]
lemma probEvent_mul_le (p : α → Prop) : probEvent mx p * r ≤ r :=
  mul_le_of_le_one_left' <| by simp


-- @@ L684-685 expanded
@[simp]
lemma mul_probEvent_le (p : α → Prop) : r * probEvent mx p ≤ r :=
  mul_le_of_le_one_right' <| by simp


-- @@ L687-687 verbatim
end mono_le


-- @@ L689-689 verbatim
section sum_probOutput


-- @@ L691-691 verbatim
variable [MonadLiftT m SPMF]


-- @@ L693-696 expanded
@[simp]
lemma tsum_probOutput_eq_sub (mx : m α) : ∑' x : α, probOutput mx x = 1 - probFailure mx := by
  refine ENNReal.eq_sub_of_add_eq probFailure_ne_top (tsum_probOutput_add_probFailure mx)


-- @@ L698-699 expanded
lemma tsum_probOutput_eq_one' {mx : m α} (h : probFailure mx = 0) : ∑' x : α, probOutput mx x = 1 :=
  by simp [h]


-- @@ L701-704 expanded
@[simp]
lemma tsum_support_probOutput_eq_sub [MonadLiftT m SetM] [EvalDistCompatible m] (mx : m α) :
    ∑' x : support mx, probOutput mx x = 1 - probFailure mx := by
  rw [tsum_subtype_eq_of_support_subset] <;> simp


-- @@ L706-708 expanded
lemma tsum_support_probOutput_eq_one' [MonadLiftT m SetM] [EvalDistCompatible m] {mx : m α}
    (h : probFailure mx = 0) : ∑' x : support mx, probOutput mx x = 1 := by simp [h]


-- @@ L710-713 expanded
@[simp]
lemma sum_probOutput_eq_sub [Fintype α] (mx : m α) :
    ∑ x : α, probOutput mx x = 1 - probFailure mx := by
  rw [← tsum_fintype (L := .unconditional _), tsum_probOutput_eq_sub]


-- @@ L715-716 expanded
lemma sum_probOutput_eq_one [Fintype α] {mx : m α} (h : probFailure mx = 0) :
    ∑ x : α, probOutput mx x = 1 := by simp [h]


-- @@ L718-723 expanded
@[simp]
lemma sum_finSupport_probOutput_eq_sub [MonadLiftT m SetM] [EvalDistCompatible m] [HasEvalFinset m]
    [DecidableEq α] (mx : m α) : ∑ x ∈ finSupport mx, probOutput mx x = 1 - probFailure mx :=
  by
  rw [← tsum_probOutput_eq_sub, tsum_eq_sum]
  simp


-- @@ L725-727 expanded
lemma sum_finSupport_probOutput_eq_one [MonadLiftT m SetM] [EvalDistCompatible m] [HasEvalFinset m]
    [DecidableEq α] {mx : m α} (h : probFailure mx = 0) :
    ∑ x ∈ finSupport mx, probOutput mx x = 1 := by simp [h]


-- @@ L729-729 verbatim
end sum_probOutput


-- @@ L731-735 expanded
@[grind =]
lemma probFailure_eq_sub_tsum [MonadLiftT m SPMF] (mx : m α) :
    probFailure mx = 1 - ∑' x : α, probOutput mx x := by
  refine
    ENNReal.eq_sub_of_add_eq (ne_top_of_le_ne_top one_ne_top tsum_probOutput_le_one)
      (probFailure_add_tsum_probOutput mx)


-- @@ L737-739 expanded
lemma probFailure_eq_sub_sum [MonadLiftT m SPMF] [Fintype α] (mx : m α) :
    probFailure mx = 1 - ∑ x : α, probOutput mx x := by
  rw [← tsum_fintype (L := .unconditional _), probFailure_eq_sub_tsum]


-- @@ L741-741 verbatim
section bool


-- @@ L743-746 verbatim
variable [MonadLiftT m SPMF]

-- also `@[grind =]`: without the tag `grind` routes the impossible event through the support
-- machinery and fails on `Pr[ fun _ => False | mx] = 0`

-- @@ L747-750 expanded
@[simp, grind =]
lemma probEvent_False (mx : m α) : (probEvent mx fun _ => False) = 0 := by
  simp [probEvent_eq_tsum_indicator]


-- @@ L752-754 expanded
@[grind =]
lemma probEvent_false (mx : m α) : (probEvent mx fun _ => false) = 0 := by aesop


-- @@ L756-759 expanded
@[simp, grind =]
lemma probEvent_True_eq_sub (mx : m α) : (probEvent mx fun _ => True) = 1 - probFailure mx := by
  simp [probEvent_eq_tsum_indicator]


-- @@ L761-762 expanded
lemma probEvent_true_eq_sub (mx : m α) : (probEvent mx fun _ => true) = 1 - probFailure mx := by
  grind


-- @@ L764-767 expanded
lemma probFailure_eq_sub_probEvent (mx : m α) : probFailure mx = 1 - probEvent mx fun _ => True :=
  by
  refine ENNReal.eq_sub_of_add_eq (by simp only [ne_eq, probEvent_ne_top, not_false_eq_true]) ?_
  simp only [probEvent_True_eq_sub, probFailure_le_one, add_tsub_cancel_of_le]


-- @@ L769-775 expanded
lemma probFailure_eq_one_iff_probEvent_true (mx : m α) :
    probFailure mx = 1 ↔ (probEvent mx fun _ => True) = 0 :=
  by
  rw [probFailure_eq_sub_probEvent, ← ENNReal.toReal_eq_one_iff]
  rw [ENNReal.toReal_sub_of_le (by grind) (by simp)]
  simp [tsub_eq_zero_iff_le, ENNReal.toReal_eq_one_iff]
    -- `simp`-only: `grind` saturates on this support-quantifier characterization.


-- @@ L776-779 expanded
@[simp]
lemma probFailure_eq_one_iff [MonadLiftT m SetM] [EvalDistCompatible m] (mx : m α) :
    probFailure mx = 1 ↔ support mx = ∅ := by
  simp [probFailure_eq_one_iff_probEvent_true, probEvent_eq_tsum_subtype_mem_support, Set.ext_iff]


-- @@ L781-783 expanded
@[aesop unsafe forward]
lemma probFailure_eq_one [MonadLiftT m SetM] [EvalDistCompatible m] {mx : m α}
    (h : support mx = ∅) : probFailure mx = 1 :=
  (probFailure_eq_one_iff mx).mpr h


-- @@ L785-791 expanded
/-- `grind`-friendly companion to `probFailure_eq_one_iff`: phrasing "fails with probability one"
via `Set.Nonempty` — which `grind` keeps atomic — avoids the support quantifier that makes the
`support = ∅` form saturate, so this stays in the default `grind` set. -/
@[grind =]
lemma probFailure_eq_one_iff_not_nonempty [MonadLiftT m SetM] [EvalDistCompatible m] (mx : m α) :
    probFailure mx = 1 ↔ ¬(support mx).Nonempty := by
  simp only [probFailure_eq_one_iff, Set.not_nonempty_iff_eq_empty]


-- @@ L793-796 expanded
@[simp, aesop norm]
lemma probEvent_const (mx : m α) (p : Prop) [Decidable p] :
    (probEvent mx fun _ => p) = if p then (1 - probFailure mx) else 0 := by aesop


-- @@ L798-798 verbatim
end bool


-- @@ L800-803 verbatim
/-! ### Lemmas for monads with a total `PMF` denotation

These lemmas hold when `m` lifts into `PMF` (so computations never fail). They expose the
absence of failure mass and total normalization of the resulting distribution. -/


-- @@ L805-805 verbatim
section pmf_denotation


-- @@ L807-808 verbatim
variable {α β γ : Type u} {m : Type u → Type v}
  [MonadLiftT m PMF]


-- @@ L810-815 expanded
/-- A computation interpreted via a `PMF` lift has zero failure probability. -/
@[simp, grind =]
lemma probFailure_of_liftM_PMF (mx : m α) : probFailure mx = 0 :=
  by
  rw [probFailure_def, SPMF.run_eq_toPMF]
  change (some <$> (liftM mx : PMF α)) none = 0
  simp [PMF.monad_map_eq_map, PMF.map_apply]


-- @@ L817-818 expanded
lemma tsum_probOutput_of_liftM_PMF (mx : m α) : ∑' x, probOutput mx x = 1 := by simp


-- @@ L820-821 expanded
lemma tsum_support_probOutput_of_liftM_PMF [MonadLiftT m SetM] [EvalDistCompatible m] (mx : m α) :
    ∑' x : support mx, probOutput mx x = 1 := by simp


-- @@ L823-824 expanded
lemma sum_probOutput_of_liftM_PMF [Fintype α] (mx : m α) : ∑ x : α, probOutput mx x = 1 := by simp


-- @@ L826-828 expanded
lemma sum_finSupport_probOutput_of_liftM_PMF [MonadLiftT m SetM] [EvalDistCompatible m]
    [HasEvalFinset m] [DecidableEq α] (mx : m α) : ∑ x ∈ finSupport mx, probOutput mx x = 1 := by
  simp


-- @@ L830-836 verbatim
lemma finSupport_nonempty_of_liftM_PMF [MonadLiftT m SetM] [EvalDistCompatible m]
    [HasEvalFinset m] [DecidableEq α] (mx : m α) :
    (finSupport mx).Nonempty := by
  by_contra h
  have hsum := sum_finSupport_probOutput_of_liftM_PMF (m := m) mx
  rw [Finset.not_nonempty_iff_eq_empty.mp h, Finset.sum_empty] at hsum
  exact zero_ne_one hsum


-- @@ L838-845 expanded
lemma probOutput_eq_inv_finSupport_card_of_liftM_PMF [MonadLiftT m SetM] [EvalDistCompatible m]
    [HasEvalFinset m] [DecidableEq α] {mx : m α} {c : ENNReal}
    (hconst : ∀ x ∈ support mx, probOutput mx x = c) : c = 1 / (finSupport mx).card :=
  by
  have h := sum_finSupport_probOutput_of_liftM_PMF (m := m) mx
  rw [Finset.sum_congr rfl fun x hx => hconst x (mem_support_of_mem_finSupport hx),
    Finset.sum_const, nsmul_eq_mul, mul_comm] at h
  simpa using ENNReal.eq_inv_of_mul_eq_one_left h


-- @@ L847-847 verbatim
end pmf_denotation


-- @@ L849-849 verbatim
/-! ## Monotonicity and complementation for `probEvent` -/


-- @@ L851-851 verbatim
section probEvent_mono_compl


-- @@ L853-854 verbatim
variable [MonadLiftT m SPMF]
  {mx : m α} {p q : α → Prop}


-- @@ L856-860 expanded
lemma probEvent_compl (mx : m α) (p : α → Prop) :
    (probEvent mx p + probEvent mx fun x => ¬p x) = 1 - probFailure mx :=
  by
  have := Classical.decPred p
  simp only [probEvent_eq_tsum_ite, ← ENNReal.tsum_add, ← tsum_probOutput_eq_sub]
  exact tsum_congr fun x => by split_ifs <;> simp_all


-- @@ L862-868 expanded
/-- Union bound: the probability of `p ∨ q` is at most the sum of probabilities. -/
lemma probEvent_or_le (mx : m α) (p q : α → Prop) :
    (probEvent mx fun x => p x ∨ q x) ≤ probEvent mx p + probEvent mx q :=
  by
  have := Classical.decPred p; have := Classical.decPred q
  simp only [probEvent_eq_tsum_ite, ← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun x => ?_
  by_cases hp : p x <;> by_cases hq : q x <;> simp [hp, hq]


-- @@ L870-883 expanded
/-- **First-moment / Markov bound.** The probability of `p` is at most the expectation of any
`ℝ≥0∞`-valued cost `c` that is `≥ 1` wherever `p` holds. This is the elementary core of a
first-moment (union) argument: a monotone "bad" event whose occurrence forces a unit of some
nonnegative cost has probability bounded by the expected cost. -/
lemma probEvent_le_tsum_probOutput_mul_cost (mx : m α) (p : α → Prop) (c : α → ℝ≥0∞)
    (hc : ∀ x, p x → 1 ≤ c x) : probEvent mx p ≤ ∑' x : α, probOutput mx x * c x :=
  by
  have := Classical.decPred p
  rw [probEvent_eq_tsum_ite mx p]
  refine ENNReal.tsum_le_tsum fun x => ?_
  split_ifs with hp
  ·
    calc
      probOutput mx x = probOutput mx x * 1 := (mul_one _).symm
      _ ≤ probOutput mx x * c x := by gcongr; exact hc x hp
  · exact zero_le


-- @@ L885-885 verbatim
variable [MonadLiftT m SetM] [EvalDistCompatible m]


-- @@ L887-905 expanded
/-- **First-moment / Markov bound** (`support`-restricted cost). Variant of
`probEvent_le_tsum_probOutput_mul_cost` whose `c ≥ 1` hypothesis need only hold on the
`support` of `mx`. -/
lemma probEvent_le_tsum_probOutput_mul_cost_of_mem_support (mx : m α) (p : α → Prop) (c : α → ℝ≥0∞)
    (hc : ∀ x ∈ support mx, p x → 1 ≤ c x) : probEvent mx p ≤ ∑' x : α, probOutput mx x * c x :=
  by
  have := Classical.decPred p
  rw [probEvent_eq_tsum_ite mx p]
  refine ENNReal.tsum_le_tsum fun x => ?_
  by_cases hx : x ∈ support mx
  · split_ifs with hp
    ·
      calc
        probOutput mx x = probOutput mx x * 1 := (mul_one _).symm
        _ ≤ probOutput mx x * c x := by
          gcongr
          exact hc x hx hp
    · exact zero_le
  · rw [probOutput_eq_zero_of_not_mem_support hx]
    simp


-- @@ L907-917 expanded
/-- If `p` implies `q` on the `support` of a computation then it is more likely to happen. -/
@[gcongr]
lemma probEvent_mono (h : ∀ x ∈ support mx, p x → q x) : probEvent mx p ≤ probEvent mx q :=
  by
  have := Classical.decPred p; have := Classical.decPred q
  simp only [probEvent_eq_tsum_ite]
  refine ENNReal.tsum_le_tsum fun x => ?_
  split_ifs with hp hq <;>
    first
    | rfl
    | exact zero_le
    | exact le_of_eq (probOutput_eq_zero_of_not_mem_support fun hx => hq (h x hx hp))


-- @@ L919-922 expanded
/-- If `p` implies `q` on the `finSupport` of a computation then it is more likely to happen. -/
lemma probEvent_mono' [HasEvalFinset m] [DecidableEq α] (h : ∀ x ∈ finSupport mx, p x → q x) :
    probEvent mx p ≤ probEvent mx q :=
  probEvent_mono (fun x hx hpx => h x (mem_finSupport_of_mem_support hx) hpx)


-- @@ L924-935 expanded
omit [MonadLiftT m SetM] [EvalDistCompatible m] in
/-- If `p` implies `q` everywhere then `p` is less likely than `q`. Convenience
specialisation of `probEvent_mono` that drops the support hypothesis. -/
@[gcongr low]
lemma probEvent_mono'' (h : ∀ x, p x → q x) : probEvent mx p ≤ probEvent mx q :=
  by
  have := Classical.decPred p
  have := Classical.decPred q
  simp only [probEvent_eq_tsum_ite]
  refine ENNReal.tsum_le_tsum fun x => ?_
  by_cases hp : p x <;> by_cases hq : q x <;>
    simp_all
      -- `simp`-only: `grind` saturates on this support-quantifier characterization.


-- @@ L936-945 expanded
@[simp low]
lemma probEvent_eq_one_iff : probEvent mx p = 1 ↔ probFailure mx = 0 ∧ ∀ x ∈ support mx, p x :=
  by
  rw [show (∀ x ∈ support mx, p x) ↔ (probEvent mx fun x => ¬p x) = 0 by
      simp [probEvent_eq_zero_iff]]
  have hadd : probEvent mx p + ((probEvent mx fun x => ¬p x) + probFailure mx) = 1 := by
    rw [← add_assoc, probEvent_compl mx p, tsub_add_cancel_of_le probFailure_le_one]
  refine ⟨fun h => ?_, fun ⟨hf, hb⟩ => by simpa [hf, hb] using hadd⟩
  rw [h] at hadd
  exact and_comm.1 (add_eq_zero.1 (by simpa using hadd))


-- @@ L947-947 verbatim
alias ⟨_, probEvent_eq_one⟩ := probEvent_eq_one_iff


-- @@ L949-958 expanded
/-- Pointwise variant of `probOutput_eq_one_iff`: `Pr[= x | mx] = 1` iff the support is
a subset of `{x}` (phrased as a forall over the support) and the computation never fails.

More usable than `probOutput_eq_one_iff` when the caller wants to iterate over arbitrary
support elements rather than prove a set equality. -/
lemma probOutput_eq_one_iff_forall (mx : m α) (x : α) :
    probOutput mx x = 1 ↔ probFailure mx = 0 ∧ ∀ y ∈ support mx, y = x := by
  rw [← probEvent_eq_eq_probOutput, probEvent_eq_one_iff]
    -- `simp`-only: `grind` saturates on this support-quantifier characterization.


-- @@ L959-962 expanded
@[simp low]
lemma one_eq_probEvent_iff : 1 = probEvent mx p ↔ probFailure mx = 0 ∧ ∀ x ∈ support mx, p x := by
  rw [eq_comm, probEvent_eq_one_iff]


-- @@ L964-966 verbatim
alias ⟨_, one_eq_probEvent⟩ := one_eq_probEvent_iff

-- `simp`-only: `grind` saturates on this support-quantifier characterization.

-- @@ L967-970 expanded
@[simp]
lemma probEvent_eq_one_iff' [HasEvalFinset m] [DecidableEq α] :
    probEvent mx p = 1 ↔ probFailure mx = 0 ∧ ∀ x ∈ finSupport mx, p x := by
  simp_rw [probEvent_eq_one_iff, mem_finSupport_iff_mem_support]


-- @@ L972-974 verbatim
alias ⟨_, probEvent_eq_one'⟩ := probEvent_eq_one_iff'

-- `simp`-only: `grind` saturates on this support-quantifier characterization.

-- @@ L975-978 expanded
@[simp]
lemma one_eq_probEvent_iff' [HasEvalFinset m] [DecidableEq α] :
    1 = probEvent mx p ↔ probFailure mx = 0 ∧ ∀ x ∈ finSupport mx, p x := by
  rw [eq_comm, probEvent_eq_one_iff']


-- @@ L980-980 verbatim
alias ⟨_, one_eq_probEvent'⟩ := one_eq_probEvent_iff'


-- @@ L982-984 expanded
lemma function_support_probOutput : Function.support (probOutput mx ·) = support mx := by
  simp only [Function.support, ne_eq, probOutput_eq_zero_iff, not_not, Set.ofPred_mem_eq]


-- @@ L986-991 expanded
lemma mem_support_iff_of_evalSPMF_eq {m n} [Monad m] [MonadLiftT m SPMF] [MonadLiftT m SetM]
    [EvalDistCompatible m] [Monad n] [MonadLiftT n SPMF] [MonadLiftT n SetM] [EvalDistCompatible n]
    {mx : m α} {mx' : n α} (h : evalSPMF mx = evalSPMF mx') (x : α) :
    x ∈ support mx ↔ x ∈ support mx' := by simp only [mem_support_iff, probOutput_def, h]


-- @@ L993-999 expanded
lemma mem_finSupport_iff_of_evalSPMF_eq {m n} [Monad m] [MonadLiftT m SPMF] [MonadLiftT m SetM]
    [EvalDistCompatible m] [Monad n] [MonadLiftT n SPMF] [MonadLiftT n SetM] [EvalDistCompatible n]
    [HasEvalFinset m] [HasEvalFinset n] [DecidableEq α] {mx : m α} {mx' : n α}
    (h : evalSPMF mx = evalSPMF mx') (x : α) : x ∈ finSupport mx ↔ x ∈ finSupport mx' := by
  simp only [mem_finSupport_iff_mem_support, mem_support_iff_of_evalSPMF_eq h]


-- @@ L1001-1007 expanded
open Classical in
omit [MonadLiftT m SetM] [EvalDistCompatible m] in
lemma indicator_objective_eq_probEvent (mx : m (α × β)) (R : α → β → Prop) :
    (∑' z, probOutput mx z * (if R z.1 z.2 then 1 else 0)) = probEvent mx fun z => R z.1 z.2 :=
  by
  rw [probEvent_eq_tsum_ite]
  refine tsum_congr fun z => ?_
  by_cases hR : R z.1 z.2 <;> simp [hR]


-- @@ L1009-1009 verbatim
end probEvent_mono_compl


-- @@ L1011-1011 verbatim
/-! ## Expected values -/


-- @@ L1013-1013 verbatim
section expectedValue


-- @@ L1015-1015 verbatim
variable [MonadLiftT m SPMF]


-- @@ L1017-1017 verbatim
namespace OracleComp.EvalDist


-- @@ L1019-1024 expanded
/-- The expected value `∑' x, Pr[= x | mx] * g x` of `g` on the output of `mx`. Failing runs
contribute nothing, so on a computation that can fail this is the expectation of the
conditional-on-success value scaled by the success probability, not a conditional expectation.
`expectedValue` is the head symbol `gcongr` keys on for bind bounds (see
`probEvent_bind_eq_expectedValue`). -/
noncomputable def expectedValue (mx : m α) (g : α → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' x, probOutput mx x * g x


-- @@ L1026-1027 expanded
theorem expectedValue_def (mx : m α) (g : α → ℝ≥0∞) :
    expectedValue mx g = ∑' x, probOutput mx x * g x :=
  rfl


-- @@ L1029-1034 verbatim
/-- Expectation is monotone in the functional. Tagged at low `gcongr` priority so that
`expectedValue_mono_of_support`, which only asks for the bound on `support mx`, is tried first. -/
@[gcongr low]
theorem expectedValue_mono (mx : m α) {g h : α → ℝ≥0∞} (hgh : ∀ x, g x ≤ h x) :
    expectedValue mx g ≤ expectedValue mx h :=
  ENNReal.tsum_le_tsum fun x => mul_le_mul' le_rfl (hgh x)


-- @@ L1036-1042 verbatim
/-- A pointwise bound on the functional bounds the expectation, since the total mass is at most
one. -/
theorem expectedValue_le_of_le (mx : m α) {g : α → ℝ≥0∞} {c : ℝ≥0∞} (h : ∀ x, g x ≤ c) :
    expectedValue mx g ≤ c :=
  (expectedValue_mono mx h).trans <| by
    rw [expectedValue, ENNReal.tsum_mul_right]
    exact mul_le_of_le_one_left zero_le tsum_probOutput_le_one


-- @@ L1044-1047 verbatim
theorem expectedValue_add (mx : m α) (g h : α → ℝ≥0∞) :
    expectedValue mx (fun x => g x + h x) = expectedValue mx g + expectedValue mx h := by
  simp only [expectedValue, mul_add]
  exact ENNReal.tsum_add


-- @@ L1049-1052 expanded
/-- The expectation of an indicator is the event probability. -/
theorem expectedValue_ite_one (mx : m α) (p : α → Prop) [DecidablePred p] :
    expectedValue mx (fun x => if p x then 1 else 0) = probEvent mx p := by
  simp only [expectedValue_def, probEvent_eq_tsum_ite, mul_ite, mul_one, mul_zero]


-- @@ L1054-1057 verbatim
/-- A constant factor scales the expectation. -/
theorem expectedValue_mul_const (mx : m α) (g : α → ℝ≥0∞) (c : ℝ≥0∞) :
    expectedValue mx (fun x => g x * c) = expectedValue mx g * c := by
  simp only [expectedValue_def, ← mul_assoc, ENNReal.tsum_mul_right]


-- @@ L1059-1059 verbatim
variable [MonadLiftT m SetM] [EvalDistCompatible m]


-- @@ L1061-1069 verbatim
/-- `expectedValue_mono` with the hypothesis restricted to `support mx`. After `gcongr with x hx`
the goal is `g x ≤ h x` with `hx : x ∈ support mx` in context. -/
@[gcongr]
theorem expectedValue_mono_of_support {mx : m α} {g h : α → ℝ≥0∞}
    (hgh : ∀ x ∈ support mx, g x ≤ h x) : expectedValue mx g ≤ expectedValue mx h := by
  refine ENNReal.tsum_le_tsum fun x => ?_
  by_cases hx : x ∈ support mx
  · exact mul_le_mul' le_rfl (hgh x hx)
  · simp [probOutput_eq_zero_of_not_mem_support hx]


-- @@ L1071-1074 verbatim
/-- A bound on the functional over `support mx` bounds the expectation. -/
theorem expectedValue_le_of_support {mx : m α} {g : α → ℝ≥0∞} {c : ℝ≥0∞}
    (h : ∀ x ∈ support mx, g x ≤ c) : expectedValue mx g ≤ c :=
  (expectedValue_mono_of_support h).trans (expectedValue_le_of_le mx fun _ => le_rfl)


-- @@ L1076-1080 verbatim
/-- Functionals that agree on `support mx` have the same expectation. -/
theorem expectedValue_congr_of_support {mx : m α} {g h : α → ℝ≥0∞}
    (hgh : ∀ x ∈ support mx, g x = h x) : expectedValue mx g = expectedValue mx h :=
  le_antisymm (expectedValue_mono_of_support fun x hx => (hgh x hx).le)
    (expectedValue_mono_of_support fun x hx => (hgh x hx).ge)


-- @@ L1082-1082 verbatim
end OracleComp.EvalDist


-- @@ L1084-1087 expanded
/-- A constant bound on the functional bounds the expectation `∑' x, Pr[= x | mx] * f x`. -/
lemma tsum_probOutput_mul_le_of_le (mx : m α) {f : α → ℝ≥0∞} {c : ℝ≥0∞} (h : ∀ x, f x ≤ c) :
    ∑' x, probOutput mx x * f x ≤ c :=
  OracleComp.EvalDist.expectedValue_le_of_le mx h


-- @@ L1089-1089 verbatim
end expectedValue


-- @@ L1091-1104 verbatim
/-! ## The measure-to-façade bridge

`DiscreteEvalDistCompatible` is the one fact that connects the primary measure semantics to the
discrete façade: integrating a measurable functional against `𝒟[mx]` is the mass-weighted sum
`∑' x, Pr[= x | mx] * g x`. Every singleton, event and mass bridge below derives from it, so the
measure side reduces *into* the façade, where the `simp`/`grind` contract takes over, instead of
carrying a second family of sum lemmas. The compatibility adapter satisfies it definitionally;
the free-monad fold satisfies it whenever its measure specification agrees with the probability
specification (`PFunctor.IsMeasureSpec.Compatible`).

The `SPMF` layer behind the façade is transitional. This class and the lemmas derived from it are
the surface that survives the switch to measure-native definitions: once `Pr[…]` is defined from
`𝒟[…]` they become definitional, while the `SPMF.` glue that proves the adapter instance is what
that switch deletes. -/


-- @@ L1106-1106 verbatim
section measure_bridge


-- @@ L1108-1108 verbatim
variable [MonadLiftT m SPMF]


-- @@ L1110-1116 expanded
/-- The primary measure semantics agrees with the discrete façade: integrating a measurable
functional against `𝒟[mx]` is the façade expectation `∑' x, Pr[= x | mx] * g x`. -/
class DiscreteEvalDistCompatible (m : Type u → Type v) [MonadLiftT m SPMF] [EvalDistSemantics m] :
    Prop where
  /-- Integrals against the denoted measure are mass-weighted sums over the façade. -/
  lintegral_evalDist {α : Type u} [MeasurableSpace α] (mx : m α) {g : α → ℝ≥0∞}
    (hg : Measurable g) : ∫⁻ x, g x ∂evalDist mx = ∑' x, probOutput mx x * g x


-- @@ L1118-1121 expanded
/-- The compatibility adapter denotes `(𝒮[mx]).toMeasure`, so the bridge is
`SPMF.lintegral_toMeasure`. Stated with only the lift in scope, so the semantics instance is
the adapter itself. -/
instance : DiscreteEvalDistCompatible m :=
  ⟨fun mx _ hg => SPMF.lintegral_toMeasure (evalSPMF mx) hg⟩


-- @@ L1123-1123 verbatim
variable [EvalDistSemantics m] [DiscreteEvalDistCompatible m] [MeasurableSpace α]


-- @@ L1125-1131 expanded
/-- The measure of a measurable event is the façade probability of membership. -/
theorem evalDist_apply (mx : m α) {s : Set α} (hs : MeasurableSet s) :
    (evalDist mx) s = probEvent mx (· ∈ s) :=
  by
  rw [← lintegral_indicator_one hs,
    DiscreteEvalDistCompatible.lintegral_evalDist mx (measurable_one.indicator hs),
    probEvent_eq_tsum_indicator]
  exact tsum_congr fun x => by by_cases hx : x ∈ s <;> simp [hx]


-- @@ L1133-1139 expanded
/-- Singleton mass is the point probability. -/
@[simp]
theorem evalDist_apply_singleton [MeasurableSingletonClass α] (mx : m α) (x : α) :
    (evalDist mx) { x } = probOutput mx x :=
  by
  rw [evalDist_apply mx (measurableSet_singleton x)]
  simp only [Set.mem_singleton_iff]
  exact probEvent_eq_eq_probOutput mx x


-- @@ L1141-1145 expanded
/-- On a discrete space the measure of a predicate's event is its façade probability. -/
@[simp]
theorem evalDist_apply_setOf [DiscreteMeasurableSpace α] (mx : m α) (p : α → Prop) :
    (evalDist mx) {x | p x} = probEvent mx p :=
  evalDist_apply mx MeasurableSet.of_discrete


-- @@ L1147-1151 expanded
/-- Success mass is one minus the failure probability. -/
@[simp]
theorem evalDist_apply_univ (mx : m α) : (evalDist mx) Set.univ = 1 - probFailure mx :=
  by
  rw [evalDist_apply mx MeasurableSet.univ]
  simp


-- @@ L1153-1160 expanded
/-- Reachable outputs are exactly the positive-mass singletons. General measures can have
support points of mass zero, so the statement is deliberately restricted to singleton-measurable
spaces. -/
theorem mem_support_iff_evalDist_singleton_ne_zero [MonadLiftT m SetM] [EvalDistCompatible m]
    [MeasurableSingletonClass α] (mx : m α) (x : α) : x ∈ support mx ↔ (evalDist mx) { x } ≠ 0 :=
  by
  rw [evalDist_apply_singleton]
  exact mem_support_iff mx x


-- @@ L1162-1162 verbatim
end measure_bridge
