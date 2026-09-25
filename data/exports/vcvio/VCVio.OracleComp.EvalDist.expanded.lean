/-
Copyright (c) 2025 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

module
public import VCVio.EvalDist.Defs.NeverFails
public import VCVio.EvalDist.Instances.OptionT
public import VCVio.EvalDist.PFunctor
public import VCVio.OracleComp.SimSemantics.SimulateQ
public import ToMathlib.Data.Set.Functor


-- @@ L14-18 verbatim
/-!
# Output Distribution of Computations

This file defines the `MonadLiftT`-based probability and support semantics for `OracleComp`.
-/


-- @@ L20-20 verbatim
@[expose] public section


-- @@ L22-22 verbatim
open OracleSpec Option ENNReal


-- @@ L24-24 verbatim
universe u v w


-- @@ L26-26 verbatim
open scoped OracleSpec.PrimitiveQuery


-- @@ L28-28 verbatim
namespace OracleSpec


-- @@ L30-30 verbatim
variable {ι} {spec : OracleSpec ι}


-- @@ L32-35 verbatim
/-- A per-query distribution on an `OracleSpec`, definitionally the generic
probability specification on its underlying polynomial functor. -/
abbrev IsProbabilitySpec (spec : OracleSpec ι) :=
  PFunctor.IsProbabilitySpec spec.toPFunctor


-- @@ L37-37 verbatim
namespace IsProbabilitySpec


-- @@ L39-41 verbatim
/-- The distribution of responses to query `t`. -/
abbrev toPMF [IsProbabilitySpec spec] (t : spec.Domain) : PMF (spec.Range t) :=
  PFunctor.IsProbabilitySpec.toPMF (P := spec.toPFunctor) t


-- @@ L43-43 verbatim
end IsProbabilitySpec


-- @@ L45-57 verbatim
/-- An `OracleSpec` whose responses are uniformly sampled from finite, inhabited
ranges. Bundles `spec.Fintype`, `spec.Inhabited`, and `IsProbabilitySpec spec`
together with a `Prop` witness that the per-query distribution agrees with
`PMF.uniformOfFintype`. Use this as the canonical input to lemmas that
mention `Fintype.card (spec.Range _)` or `PMF.uniformOfFintype` in their
statements. -/
class IsUniformSpec (spec : OracleSpec ι) extends IsProbabilitySpec spec where
  /-- Every response set is finite. -/
  fintype : spec.Fintype
  /-- Every response set is inhabited. -/
  inhabited : spec.Inhabited
  /-- The per-query distribution is the uniform distribution on the response set. -/
  toPMF_eq_uniform : ∀ t, toPMF t = PMF.uniformOfFintype (spec.Range t)


-- @@ L59-59 verbatim
attribute [reducible, instance] IsUniformSpec.fintype IsUniformSpec.inhabited


-- @@ L61-72 verbatim
/-- Bridge from `[spec.Fintype] [spec.Inhabited]` to `IsUniformSpec spec`.
Deliberately **not** an instance — `IsUniformSpec` must be opted into per
spec so that uniform-sampling semantics never attach silently to a spec
whose author didn't intend a probabilistic interpretation. Use this
helper when declaring `IsUniformSpec` for a concrete spec. -/
@[reducible] noncomputable def IsUniformSpec.ofFintypeInhabited
    {ι : Type u} (spec : OracleSpec ι)
    [hF : spec.Fintype] [hI : spec.Inhabited] : IsUniformSpec spec where
  toPMF t := PMF.uniformOfFintype (spec.Range t)
  fintype := hF
  inhabited := hI
  toPMF_eq_uniform _ := rfl


-- @@ L74-74 verbatim
noncomputable instance : IsUniformSpec unifSpec := IsUniformSpec.ofFintypeInhabited _

-- @@ L75-75 verbatim
noncomputable instance : IsUniformSpec coinSpec := IsUniformSpec.ofFintypeInhabited _


-- @@ L77-82 verbatim
/-- Propagate `IsUniformSpec` through `+`: each summand's uniformity is
preserved on its branch. `IsProbabilitySpec (spec + spec')` is derived via
the `extends` chain. -/
noncomputable instance instIsUniformSpecAdd {ι ι'} (spec : OracleSpec ι)
    (spec' : OracleSpec ι') [IsUniformSpec spec] [IsUniformSpec spec'] :
    IsUniformSpec (spec + spec') := IsUniformSpec.ofFintypeInhabited _


-- @@ L84-93 verbatim
/-- Package uniform oracle semantics as generic uniform semantics on the
underlying polynomial functor. This is an explicit conversion rather than an
instance so it cannot participate in overly broad `toPFunctor` unification. -/
@[reducible]
noncomputable def IsUniformSpec.toPFunctor [h : IsUniformSpec spec] :
    PFunctor.IsUniformSpec spec.toPFunctor where
  toPMF := h.toPMF
  fintype := h.fintype.toFintype
  inhabited := h.inhabited.toInhabited
  toPMF_eq_uniform := h.toPMF_eq_uniform


-- @@ L95-95 verbatim
end OracleSpec


-- @@ L97-97 verbatim
export OracleSpec (IsProbabilitySpec IsUniformSpec)


-- @@ L99-99 verbatim
namespace OracleComp


-- @@ L101-101 verbatim
variable {ι ι'} {spec : OracleSpec ι} {spec' : OracleSpec ι'} {α β γ : Type w}


-- @@ L103-103 verbatim
/-! ## Oracle-facing semantics -/


-- @@ L105-105 verbatim
section evalSPMF_main


-- @@ L107-108 expanded
lemma evalSPMF_eq_simulateQ [IsProbabilitySpec spec] (mx : OracleComp spec α) :
    evalSPMF mx = simulateQ IsProbabilitySpec.toPMF mx :=
  rfl


-- @@ L110-116 expanded
/-- Abstract distribution of a single lifted query under `IsProbabilitySpec`:
the per-query distribution `toPMF` is pushed forward through the query's
continuation. Uniform-content sibling: `evalSPMF_liftM`. -/
lemma evalSPMF_liftM_toPMF [IsProbabilitySpec spec] (q : OracleQuery spec α) :
    evalSPMF (liftM q : OracleComp spec α) = (IsProbabilitySpec.toPMF q.input).map q.cont := by
  simp [evalSPMF_eq_simulateQ, SPMF.liftM_eq_map, PMF.map_comp, PMF.monad_map_eq_map]


-- @@ L118-123 expanded
/-- `liftM (query t) : OracleComp spec _` evaluates to the per-query distribution
`IsProbabilitySpec.toPMF t`, lifted to `SPMF`. -/
lemma evalSPMF_query_toPMF [IsProbabilitySpec spec] (t : spec.Domain) :
    evalSPMF (OracleSpec.query t : OracleComp spec _) =
      (IsProbabilitySpec.toPMF t : SPMF (spec.Range t)) :=
  by rw [evalSPMF_liftM_toPMF]; simp [PMF.map_id]


-- @@ L125-128 verbatim
@[simp, grind =] lemma support_liftM (q : OracleQuery spec α) :
    support (liftM q : OracleComp spec α) = Set.range q.cont := by
  rw [OracleComp.liftM_def]
  exact PFunctor.FreeM.support_liftObj q


-- @@ L130-132 expanded
@[grind =]
lemma support_query (t : spec.Domain) :
    support (OracleSpec.query t : OracleComp spec _) = Set.univ := by rw [support_liftM];
  exact Set.range_id


-- @@ L134-136 verbatim
lemma mem_support_liftM_iff (q : OracleQuery spec α) (u : α) :
    u ∈ support (liftM q : OracleComp spec α) ↔ ∃ t, q.cont t = u := by
  rw [support_liftM]; exact Set.mem_range


-- @@ L138-140 expanded
lemma mem_support_query (t : spec.Domain) (u : spec.Range t) :
    u ∈ support (OracleSpec.query t : OracleComp spec _) := by rw [support_query]; trivial


-- @@ L142-142 verbatim
alias support_liftM_query := support_query


-- @@ L144-155 expanded
/-- Support-aware bind congruence: if two continuations agree on all elements in the support
    of `mx`, the resulting bind computations are equal. -/
theorem bind_congr_of_forall_mem_support (mx : OracleComp spec α) {f g : α → OracleComp spec β}
    (h : ∀ x ∈ support mx, f x = g x) : mx >>= f = mx >>= g := by
  induction mx using OracleComp.inductionOn with
  | pure a => simpa only [monad_norm] using h a (by simp)
  | query_bind q k
    ih =>
    change
      (OracleSpec.query q : OracleComp spec _) >>= (fun u => k u >>= f) =
        (OracleSpec.query q : OracleComp spec _) >>= (fun u => k u >>= g)
    exact
      bind_congr fun u => ih u fun x hx => h x ((mem_support_bind_iff _ _ _).mpr ⟨u, by simp, hx⟩)


-- @@ L157-161 verbatim
@[simp, grind .]
lemma support_finite [spec.Fintype] (mx : OracleComp spec α) : (support mx).Finite := by
  induction mx using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t f h => simpa using Set.finite_iUnion h


-- @@ L163-163 verbatim
end evalSPMF_main


-- @@ L165-165 verbatim
section finSupport


-- @@ L167-167 verbatim
variable [spec.Fintype]


-- @@ L169-177 verbatim
/-- Finite version of support for when oracles have a finite set of possible outputs.
NOTE: we can't use `simulateQ` because `Finset` lacks a `Monad` instance. -/
instance : HasEvalFinset (OracleComp spec) where
  finSupport {α} _ mx := OracleComp.construct
    (fun x => {x}) (fun _ _ r => Finset.univ.biUnion r) mx
  coe_finSupport {α} _ mx := by
    induction mx using OracleComp.inductionOn with
    | pure x => simp
    | query_bind t mx h => simp [h]


-- @@ L179-180 verbatim
@[simp, grind =] lemma finSupport_liftM [DecidableEq α] (q : OracleQuery spec α) :
    finSupport (liftM q : OracleComp spec α) = Finset.univ.image q.cont := by grind


-- @@ L182-183 expanded
lemma finSupport_query [spec.DecidableEq] (t : spec.Domain) :
    finSupport (OracleSpec.query t : OracleComp spec _) = Finset.univ := by grind


-- @@ L185-186 verbatim
lemma mem_finSupport_liftM_iff [DecidableEq α] (q : OracleQuery spec α) (x : α) :
    x ∈ finSupport (liftM q : OracleComp spec α) ↔ ∃ t, q.cont t = x := by simp


-- @@ L188-189 expanded
lemma mem_finSupport_query [spec.DecidableEq] (t : spec.Domain) (u : spec.Range t) :
    u ∈ finSupport (OracleSpec.query t : OracleComp spec _) := by grind


-- @@ L191-191 verbatim
end finSupport


-- @@ L193-193 verbatim
section evalSPMF


-- @@ L195-195 verbatim
variable [IsUniformSpec spec]


-- @@ L197-204 expanded
@[simp low, grind =]
lemma evalSPMF_liftM (q : OracleQuery spec α) :
    evalSPMF (liftM q : OracleComp spec α) =
      (PMF.uniformOfFintype (spec.Range q.input)).map q.cont :=
  by
  rw [evalSPMF_liftM_toPMF]
  exact
    congrArg (fun p : PMF (spec.Range q.input) => ((PMF.map q.cont p : PMF α) : SPMF α))
      (IsUniformSpec.toPMF_eq_uniform q.input)


-- @@ L206-209 expanded
@[simp, grind =]
lemma evalSPMF_query (t : spec.Domain) :
    evalSPMF (OracleSpec.query t : OracleComp spec _) = PMF.uniformOfFintype (spec.Range t) := by
  rw [evalSPMF_liftM]; simp [PMF.map_id]


-- @@ L211-217 expanded
@[simp low, grind =]
lemma probOutput_liftM_eq_div (q : OracleQuery spec α) (x : α) :
    probOutput (liftM q : OracleComp spec α) x =
      (∑' u : spec.Range q.input, probOutput (return q.cont u : OracleComp spec α) x) /
        Fintype.card (spec.Range q.input) :=
  by
  have : DecidableEq α := Classical.decEq α
  simp [probOutput_def, div_eq_mul_inv]


-- @@ L219-223 expanded
@[simp, grind =]
lemma probOutput_query (t : spec.Domain) (u : spec.Range t) :
    probOutput (OracleSpec.query t : OracleComp spec _) u =
      (Fintype.card (spec.Range t) : ℝ≥0∞)⁻¹ :=
  by simp; rfl


-- @@ L225-235 expanded
@[grind =]
lemma probEvent_liftM_eq_div (q : OracleQuery spec α) (p : α → Prop) :
    probEvent (liftM q : OracleComp spec α) p =
      (∑' u : spec.Range q.input, probEvent (return q.cont u : OracleComp spec α) p) /
        Fintype.card (spec.Range q.input) :=
  by
  have : DecidablePred p := Classical.decPred p
  simp only [probEvent_eq_tsum_ite, probOutput_liftM_eq_div, tsum_fintype, div_eq_mul_inv]
  rw [sum_eq_tsum_indicator]
  simp only [Finset.coe_univ, Set.mem_univ, Set.indicator_of_mem]
  rw [ENNReal.tsum_comm, ← ENNReal.tsum_mul_right]
  exact tsum_congr fun x => by aesop


-- @@ L237-240 expanded
@[grind =]
lemma probOutput_query_eq_div (t : spec.Domain) (u : spec.Range t) :
    probOutput (OracleSpec.query t : OracleComp spec _) u = 1 / Fintype.card (spec.Range t) := by
  simp


-- @@ L242-246 expanded
@[simp, grind =]
lemma probEvent_query (t : spec.Domain) (p : spec.Range t → Prop) [DecidablePred p] :
    probEvent (OracleSpec.query t : OracleComp spec _) p =
      Finset.card {x | p x} / Fintype.card (spec.Range t) :=
  by simp [probEvent_liftM_eq_div]; rfl


-- @@ L248-259 expanded
/-- An event selecting at most one response to a uniform oracle query has
probability at most the inverse response-space cardinality. -/
lemma probEvent_query_le_inv_of_unique (t : spec.Domain) (p : spec.Range t → Prop)
    (hunique : ∀ x y, p x → p y → x = y) :
    probEvent (OracleSpec.query t : OracleComp spec _) p ≤ (Fintype.card (spec.Range t) : ℝ≥0∞)⁻¹ :=
  by
  classical
  rw [probEvent_query, div_eq_mul_inv]
  refine (mul_le_mul' ?_ le_rfl).trans_eq (one_mul _)
  exact_mod_cast
    Finset.card_le_one.mpr fun x hx y hy ↦
      by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
      exact hunique x y hx hy


-- @@ L261-261 verbatim
end evalSPMF


-- @@ L263-263 verbatim
section supportEvalDist


-- @@ L265-265 verbatim
variable [IsUniformSpec spec] (oa : OracleComp spec α) (x : α)


-- @@ L267-271 verbatim
/-- `OracleComp spec` admits the bridge between its direct `support` semantics and the
`SPMF.support` of its `evalSPMF`. -/
instance instEvalDistCompatible : EvalDistCompatible (OracleComp spec) := by
  let : PFunctor.IsUniformSpec spec.toPFunctor := IsUniformSpec.toPFunctor
  exact PFunctor.FreeM.instEvalDistCompatible


-- @@ L273-279 expanded
/-- The reachable outputs of `oa` are exactly the outputs its distribution semantics gives
nonzero probability. This is `EvalDistCompatible.support_eq_SPMF_support` specialized to the
oracle façade, and it is the named bridge to reach for when a proof needs to move between the
two semantics without unfolding either into its `SetM` / `SPMF` interpreter. -/
lemma support_eq_evalSPMF_support : support oa = SPMF.support (evalSPMF oa) :=
  EvalDistCompatible.support_eq_SPMF_support oa


-- @@ L281-285 expanded
/-- An output has non-zero probability in `evalSPMF` iff it is in computation support. -/
lemma mem_support_evalSPMF_iff : some x ∈ (evalSPMF oa).run.support ↔ x ∈ support oa := by
  rw [support_eq_evalSPMF_support, PMF.mem_support_iff, SPMF.mem_support_iff,
    SPMF.apply_eq_toPMF_some, SPMF.run_eq_toPMF]


-- @@ L287-287 verbatim
alias ⟨mem_support_of_mem_support_evalSPMF, mem_support_evalSPMF⟩ := mem_support_evalSPMF_iff


-- @@ L289-292 expanded
/-- Finite-support variant of `mem_support_evalSPMF_iff`. -/
lemma mem_support_evalSPMF_iff' [DecidableEq α] :
    some x ∈ (evalSPMF oa).run.support ↔ x ∈ finSupport oa := by
  rw [mem_support_evalSPMF_iff (oa := oa) (x := x), mem_finSupport_iff_mem_support]


-- @@ L294-294 verbatim
alias ⟨mem_finSupport_of_mem_support_evalSPMF, mem_support_evalSPMF'⟩ := mem_support_evalSPMF_iff'


-- @@ L296-296 verbatim
end supportEvalDist


-- @@ L298-298 verbatim
section NeverFail


-- @@ L300-300 verbatim
variable [IsProbabilitySpec spec]


-- @@ L302-303 verbatim
lemma probFailure_eq_zero_iff (oa : OracleComp spec α) : probFailure oa = 0 ↔ NeverFail oa := by
  simp [neverFail_iff]


-- @@ L305-306 verbatim
lemma probFailure_pos_iff (oa : OracleComp spec α) : 0 < probFailure oa ↔ ¬ NeverFail oa := by
  simp [neverFail_iff]


-- @@ L308-309 verbatim
lemma noFailure_of_probFailure_eq_zero {oa : OracleComp spec α} (h : probFailure oa = 0) :
    NeverFail oa := by rwa [← probFailure_eq_zero_iff]


-- @@ L311-312 verbatim
lemma not_noFailure_of_probFailure_pos {oa : OracleComp spec α} (h : 0 < probFailure oa) :
    ¬ NeverFail oa := by rwa [← probFailure_pos_iff]


-- @@ L314-314 verbatim
end NeverFail


-- @@ L316-316 verbatim
section evalSPMFConvenience


-- @@ L318-318 verbatim
variable [IsUniformSpec spec] [IsProbabilitySpec spec']


-- @@ L320-325 expanded
lemma evalSPMF_query_bind (t : spec.Domain) (ou : spec.Range t → OracleComp spec α) :
    evalSPMF ((OracleSpec.query t : OracleComp spec _) >>= ou) =
      (PMF.uniformOfFintype (spec.Range t) : SPMF _) >>= fun u => evalSPMF (ou u) :=
  by rw [evalSPMF_bind, evalSPMF_query]


-- @@ L327-329 expanded
lemma probOutput_congr {x y : α} {oa : OracleComp spec α} {oa' : OracleComp spec' α} (h1 : x = y)
    (h2 : evalSPMF oa = evalSPMF oa') : probOutput oa x = probOutput oa' y := by
  simp_rw [probOutput_def, h1, h2]


-- @@ L331-345 expanded
/-- Two events have equal probabilities when their predicates agree on the support of the
first computation and the two computations share an evaluation distribution. -/
lemma probEvent_congr' {p q : α → Prop} {oa : OracleComp spec α} {oa' : OracleComp spec' α}
    (h1 : ∀ x, x ∈ support oa → (p x ↔ q x)) (h2 : evalSPMF oa = evalSPMF oa') :
    probEvent oa p = probEvent oa' q :=
  by
  have hpr : (probOutput oa ·) = (probOutput oa' ·) := funext fun x => probOutput_congr rfl h2
  rw [probEvent_eq_tsum_indicator, probEvent_eq_tsum_indicator, hpr]
  refine tsum_congr fun x => ?_
  by_cases hx : x ∈ support oa
  · have hs : x ∈ ({x | p x} : Set α) ↔ x ∈ ({x | q x} : Set α) := h1 x hx
    by_cases hp : x ∈ ({x | p x} : Set α)
    · rw [Set.indicator_of_mem hp, Set.indicator_of_mem (hs.mp hp)]
    · rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem (hs.not.mp hp)]
  · have hz : probOutput oa' x = 0 := congrFun hpr.symm x ▸ probOutput_eq_zero_of_not_mem_support hx
    rw [Set.indicator_apply_eq_zero.2 fun _ => hz, Set.indicator_apply_eq_zero.2 fun _ => hz]


-- @@ L347-350 expanded
lemma evalSPMF_ext_probEvent {oa : OracleComp spec α} {oa' : OracleComp spec' α}
    (h : ∀ x, probOutput oa x = probOutput oa' x) : (evalSPMF oa).run = (evalSPMF oa').run :=
  by
  have heval : evalSPMF oa = evalSPMF oa' := evalSPMF_ext h
  simp [heval]


-- @@ L352-354 expanded
lemma probFailure_eq_sub_probEvent' (oa : OracleComp spec α) :
    probFailure oa = 1 - probEvent oa fun _ => True :=
  _root_.probFailure_eq_sub_probEvent oa


-- @@ L356-356 verbatim
end evalSPMFConvenience


-- @@ L358-358 verbatim
section guard


-- @@ L360-360 verbatim
variable [IsProbabilitySpec spec]


-- @@ L362-370 expanded
lemma probOutput_guard {p : Prop} [Decidable p] :
    probOutput (guard p : OptionT (OracleComp spec) Unit) () = if p then 1 else 0 :=
  by
  rw [OracleComp.guard_eq]
  split_ifs with h
  · exact probOutput_pure_self ()
  · -- `probOutput_failure ()` would suit, but `LawfulFailure (OptionT (OracleComp spec))` does
        -- not resolve through `OptionT.instLawfulFailure` due to a universe-inference quirk in the
        -- post-refactor diamond. Compute directly.
    simp [OptionT.probOutput_eq, OptionT.run_failure, probOutput_pure]


-- @@ L372-379 expanded
@[simp]
lemma probFailure_guard {p : Prop} [Decidable p] :
    probFailure (guard p : OptionT (OracleComp spec) Unit) = if p then 0 else 1 :=
  by
  rw [OracleComp.guard_eq]
  split_ifs with h
  · exact probFailure_pure ()
  · -- See note above.
    simp [OptionT.probFailure_eq, OptionT.run_failure]


-- @@ L381-383 verbatim
lemma support_guard {p : Prop} [Decidable p] :
    support (guard p : OptionT (OracleComp spec) Unit) = if p then {()} else ∅ := by
  rw [OracleComp.guard_eq]; split_ifs <;> simp


-- @@ L385-394 expanded
/-- For any `PUnit`-valued computation in an arbitrary monad with an `SPMF` denotation, the
probability of returning `()` is the complementary mass of its failure probability. -/
lemma probOutput_punit_eq_sub_probFailure {m : Type → Type*} [Monad m] [MonadLiftT m SPMF]
    {oa : m PUnit} : probOutput oa () = 1 - probFailure oa :=
  by
  have h := tsum_probOutput_add_probFailure oa
  have hunit : ∑' x : PUnit, probOutput oa x = probOutput oa () :=
    tsum_eq_single () (fun x hx => absurd (Subsingleton.elim x ()) hx)
  rw [hunit] at h
  exact ENNReal.eq_sub_of_add_eq (ne_top_of_le_ne_top one_ne_top probFailure_le_one) h


-- @@ L396-401 expanded
/-- The `OracleComp` instance of `probOutput_punit_eq_sub_probFailure`: for a `PUnit`-valued
oracle computation, the probability of returning `()` is the complementary mass of its failure
probability. -/
lemma probOutput_eq_sub_probFailure_of_unit {oa : OracleComp spec PUnit} :
    probOutput oa () = 1 - probFailure oa :=
  probOutput_punit_eq_sub_probFailure


-- @@ L403-412 expanded
/-- Guarding a computation `oa` by a decidable predicate `p` and asking for the probability of a
successful `()` output recovers exactly the event probability `Pr[p | oa]`: the failure mass of the
`guard` removes precisely the outputs falsifying `p`. Public guard-section API used by failure-based
security experiments. -/
lemma probOutput_bind_guard_eq_probEvent {α : Type} (oa : OracleComp spec α) (p : α → Prop)
    [DecidablePred p] :
    probOutput
        (do
          let a ← oa;
          guard (p a) : OptionT (OracleComp spec) Unit)
        () =
      probEvent oa p :=
  by
  simp only [probOutput_bind_eq_tsum, OptionT.probOutput_liftM, probOutput_guard,
    probEvent_eq_tsum_ite]
  exact tsum_congr fun a => by split_ifs <;> simp


-- @@ L414-420 expanded
lemma probOutput_guard_eq_sub_probOutput_guard_not {α : Type} {oa : OracleComp spec α}
    [NeverFail oa] {p : α → Prop} [DecidablePred p] :
    probOutput
        (do
          let a ← oa;
          guard (p a) : OptionT (OracleComp spec) Unit)
        () =
      1 -
        probOutput
          (do
            let a ← oa;
            guard (¬p a) : OptionT (OracleComp spec) Unit)
          () :=
  by
  simp only [probOutput_bind_guard_eq_probEvent]
  exact
    ENNReal.eq_sub_of_add_eq (ne_top_of_le_ne_top one_ne_top probEvent_le_one)
      (by simpa only [probFailure_of_liftM_PMF, tsub_zero] using probEvent_compl oa p)


-- @@ L422-422 verbatim
end guard


-- @@ L424-429 verbatim
/-! ## Probabilities of `orElse` (`<|>`)

`oa <|> oa'` runs `oa`, falling back to `oa'` only when `oa` returns `none`. The base `OracleComp`
never fails, so the two failure events are independent: `oa <|> oa'` fails exactly when both do, and
an output comes either from `oa` or — on `oa`'s failure mass — from `oa'`. (`support_orElse` is left
as a future addition; it follows from `probOutput_orElse` via the support↔probability bridge.) -/


-- @@ L431-431 verbatim
section orElse


-- @@ L433-433 verbatim
variable [IsProbabilitySpec spec] {α : Type}


-- @@ L435-442 expanded
@[simp]
lemma probFailure_orElse (oa oa' : OptionT (OracleComp spec) α) :
    probFailure (oa <|> oa') = probFailure oa * probFailure oa' := by
  classical
  rw [OracleComp.orElse_def, OptionT.probFailure_eq, OptionT.probFailure_eq, OptionT.probFailure_eq,
    OptionT.run_mk, probFailure_of_liftM_PMF, probFailure_of_liftM_PMF, probFailure_of_liftM_PMF,
    zero_add, zero_add, zero_add, probOutput_bind_eq_tsum, tsum_option _ ENNReal.summable]
  simp [probOutput_pure]


-- @@ L444-452 expanded
@[simp]
lemma probOutput_orElse (oa oa' : OptionT (OracleComp spec) α) (x : α) :
    probOutput (oa <|> oa') x = probOutput oa x + probFailure oa * probOutput oa' x := by
  classical
  rw [OracleComp.orElse_def, OptionT.probOutput_eq, OptionT.probOutput_eq, OptionT.probFailure_eq,
    OptionT.probOutput_eq, OptionT.run_mk, probFailure_of_liftM_PMF, zero_add,
    probOutput_bind_eq_tsum, tsum_option _ ENNReal.summable,
    tsum_eq_single x (fun b hb => by simp [probOutput_pure, Ne.symm hb])]
  simp [probOutput_pure, add_comm]


-- @@ L454-460 expanded
@[simp]
lemma probEvent_orElse (oa oa' : OptionT (OracleComp spec) α) (p : α → Prop) :
    probEvent (oa <|> oa') p = probEvent oa p + probFailure oa * probEvent oa' p := by
  classical
  simp only [probEvent_eq_tsum_ite, probOutput_orElse]
  conv_rhs => rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
  refine tsum_congr fun b => ?_; split_ifs <;> ring


-- @@ L462-462 verbatim
end orElse


-- @@ L464-464 verbatim
section simulateQ_evalSPMF


-- @@ L466-466 verbatim
variable [IsProbabilitySpec spec] [IsProbabilitySpec spec']


-- @@ L468-481 expanded
/-- If an oracle implementation preserves the distribution of each source query, then
`simulateQ` preserves the distribution of every source computation. -/
lemma evalSPMF_simulateQ_eq_evalSPMF (so : QueryImpl spec' (OracleComp spec))
    (h :
      ∀ t : spec'.Domain,
        evalSPMF (so t) = evalSPMF (OracleSpec.query t : OracleComp spec' (spec'.Range t)))
    (oa : OracleComp spec' α) : evalSPMF (simulateQ so oa) = evalSPMF oa := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t mx ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, id_map,
      OracleQuery.input_query, evalSPMF_bind, ih, h t]


-- @@ L483-483 verbatim
end simulateQ_evalSPMF


-- @@ L485-485 verbatim
section supportWhen


-- @@ L487-490 verbatim
/-- The possible outputs of `mx` when queries can output values in the specified sets.
NOTE: currently proofs using this should reduce to `simulateQ`. A full API would be better -/
def supportWhen (o : QueryImpl spec Set) (mx : OracleComp spec α) : Set α :=
  SetM.run (simulateQ (r := SetM) (fun t => SetM.ofSet (o t)) mx)


-- @@ L492-496 verbatim
@[simp]
lemma supportWhen_pure (o : QueryImpl spec Set) (x : α) :
    supportWhen o (pure x : OracleComp spec α) = {x} := by
  unfold supportWhen
  rw [simulateQ_pure, SetM.run_pure]


-- @@ L498-503 expanded
lemma supportWhen_query_bind (o : QueryImpl spec Set) (q : spec.Domain)
    (oa : spec.Range q → OracleComp spec α) :
    supportWhen o ((OracleSpec.query q : OracleComp spec _) >>= oa) =
      ⋃ x ∈ o q, supportWhen o (oa x) :=
  by
  unfold supportWhen
  rw [simulateQ_bind, simulateQ_spec_query, SetM.run_bind, SetM.run_ofSet]


-- @@ L505-512 verbatim
/-- Reachable outputs of a bind are the reachable outputs of the continuation over reachable
outputs of the first computation. -/
@[simp]
lemma supportWhen_bind (o : QueryImpl spec Set) (oa : OracleComp spec α)
    (ob : α → OracleComp spec β) :
    supportWhen o (oa >>= ob) = ⋃ x ∈ supportWhen o oa, supportWhen o (ob x) := by
  unfold supportWhen
  rw [simulateQ_bind, SetM.run_bind]


-- @@ L514-519 verbatim
/-- Membership form of [`OracleComp.supportWhen_bind`]. -/
lemma mem_supportWhen_bind_iff (o : QueryImpl spec Set) (oa : OracleComp spec α)
    (ob : α → OracleComp spec β) (y : β) :
    y ∈ supportWhen o (oa >>= ob) ↔
      ∃ x ∈ supportWhen o oa, y ∈ supportWhen o (ob x) := by
  simp [supportWhen_bind]


-- @@ L521-533 verbatim
/-- Enlarging the set of possible oracle outputs only enlarges the reachable output set. -/
@[gcongr]
lemma supportWhen_mono {o₁ o₂ : QueryImpl spec Set}
    (h : ∀ q, o₁ q ⊆ o₂ q) (oa : OracleComp spec α) :
    supportWhen o₁ oa ⊆ supportWhen o₂ oa := by
  intro y hy
  induction oa using OracleComp.inductionOn generalizing y with
  | pure x =>
      simpa [supportWhen_pure] using hy
  | query_bind q oa ih =>
      simp only [supportWhen_query_bind, Set.mem_iUnion, exists_prop] at hy ⊢
      rcases hy with ⟨u, hu, hy⟩
      exact ⟨u, h q hu, ih u hy⟩


-- @@ L535-535 verbatim
end supportWhen


-- @@ L537-537 verbatim
section evalSPMFWhen


-- @@ L539-542 verbatim
/-- The output distribution of `mx` when queries follow the specified distribution. -/
@[reducible, simp]
noncomputable def evalSPMFWhen (d : QueryImpl spec SPMF) (mx : OracleComp spec α) : SPMF α :=
  simulateQ (r := SPMF) d mx


-- @@ L544-544 verbatim
end evalSPMFWhen


-- @@ L546-546 verbatim
section supportPeel


-- @@ L548-556 verbatim
/-- `obtain`-friendly bind support peeler at the bare `OracleComp` level. Unlike `rw
[mem_support_bind_iff]`, applying this lemma to a hypothesis uses *definitional* unification to
match `mx >>= f`, so it engages through the `Monad`/`MonadLift` instance-tree mismatches that block
the syntactic `rw` (the elaborated `OracleComp.instMonad`/`Bind.bind` spelling produced by
unfolding nested protocol definitions differs syntactically from the canonical `>>=`). -/
lemma mem_support_bind_peel (mx : OracleComp spec α) (f : α → OracleComp spec β) {y : β}
    (hy : y ∈ support (mx >>= f)) :
    ∃ a, a ∈ support mx ∧ y ∈ support (f a) := by
  rwa [mem_support_bind_iff] at hy


-- @@ L558-563 verbatim
/-- `obtain`-friendly `pure` support resolver at the bare `OracleComp` level: `y ∈ support (pure
a)` forces `y = a`, matched by definitional unification (so it engages on the
`PFunctor.FreeM.pure` spelling that the syntactic `support_pure` `rw` rejects). -/
lemma eq_of_mem_support_pure (a : α) {y : α}
    (hy : y ∈ support (pure a : OracleComp spec α)) : y = a := by
  rwa [support_pure, Set.mem_singleton_iff] at hy


-- @@ L565-574 verbatim
/-- `obtain`-friendly `<$>` (map) support peeler at the bare `OracleComp` level: `y ∈ support (g
<$> mx)` yields a preimage `a ∈ support mx` with `y = g a`, matched by definitional unification
(so it engages on the elaborated `Functor.map`/`OracleComp.instMonad` spelling that the syntactic
`support_map` `rw` rejects). -/
lemma mem_support_map_peel (g : α → β) (mx : OracleComp spec α) {y : β}
    (hy : y ∈ support (g <$> mx)) :
    ∃ a, a ∈ support mx ∧ y = g a := by
  rw [support_map, Set.mem_image] at hy
  obtain ⟨a, ha, hy⟩ := hy
  exact ⟨a, ha, hy.symm⟩


-- @@ L576-576 verbatim
end supportPeel


-- @@ L578-578 verbatim
section freeMProbability


-- @@ L580-580 verbatim
variable [IsProbabilitySpec spec]


-- @@ L582-588 expanded
/-- Probability of an event after mapping a raw polynomial free program,
viewed through the `OracleComp` semantic bridge. -/
lemma probEvent_ofFreeM_map (mx : spec.toPFunctor.FreeM α) (f : α → β) (event : β → Prop) :
    probEvent (OracleComp.ofFreeM (PFunctor.FreeM.map f mx)) event =
      probEvent (OracleComp.ofFreeM mx) (event ∘ f) :=
  probEvent_map (OracleComp.ofFreeM mx) f event


-- @@ L590-596 expanded
/-- Probability of an event for a raw polynomial `pure`, viewed through
`OracleComp`. -/
lemma probEvent_ofFreeM_pure (x : α) (event : α → Prop) [DecidablePred event] :
    probEvent (OracleComp.ofFreeM (pure x : spec.toPFunctor.FreeM α)) event =
      if event x then 1 else 0 :=
  by
  change probEvent (pure x : OracleComp spec α) event = _
  exact probEvent_pure x event


-- @@ L598-606 expanded
/-- Bind decomposition for a raw polynomial free program, viewed through
`OracleComp`. -/
lemma probEvent_ofFreeM_bind_eq_tsum (mx : spec.toPFunctor.FreeM α)
    (next : α → spec.toPFunctor.FreeM β) (event : β → Prop) :
    probEvent (OracleComp.ofFreeM (PFunctor.FreeM.bind mx next)) event =
      ∑' x, probOutput (OracleComp.ofFreeM mx) x * probEvent (OracleComp.ofFreeM (next x)) event :=
  probEvent_bind_eq_tsum (OracleComp.ofFreeM mx) (fun x => OracleComp.ofFreeM (next x)) event


-- @@ L608-608 verbatim
end freeMProbability


-- @@ L610-610 verbatim
end OracleComp


-- @@ L612-612 verbatim
namespace OptionT


-- @@ L614-614 verbatim
variable {ι : Type} {spec : OracleSpec ι} {α β : Type}


-- @@ L616-634 verbatim
/-- Support-level peeler for an `OptionT`-monadic bind, stated at the underlying
`OracleComp`-level `.run`: every element `y` of the support of the *run* of `mx >>= f` factors
through an intermediate `some a` in `mx`'s run support and a `y` in the run support of `f a`,
unless `mx`'s run can produce `none` (in which case `y` may be that `none`). Companion to
`OptionT.mem_support_bind_mk` for the case where the `OptionT.run` has already been stripped to
the bare underlying computation.

Applies to a hypothesis `y ∈ support oa` whenever `oa` is *definitionally* `(mx >>= f).run`
(the `OptionT.run` is identity), so callers need not respell the full bind term. -/
lemma mem_support_run_bind
    (mx : OptionT (OracleComp spec) α) (f : α → OptionT (OracleComp spec) β) {y : Option β}
    (hy : y ∈ support ((mx >>= f : OptionT (OracleComp spec) β).run)) :
    (none ∈ support mx.run ∧ y = none) ∨
      ∃ a, some a ∈ support mx.run ∧ y ∈ support ((f a).run) := by
  rw [OptionT.run_bind, Option.elimM, mem_support_bind_iff] at hy
  obtain ⟨o, ho, hy⟩ := hy
  cases o with
  | none => exact Or.inl ⟨ho, by simpa using hy⟩
  | some a => exact Or.inr ⟨a, ho, hy⟩


-- @@ L636-644 verbatim
/-- `OptionT.lift`-headed specialization of `mem_support_run_bind`: a `lift`ed (hence
never-failing) first computation `oa` peels cleanly, with the intermediate value living in
`support oa` directly (no `none` branch). -/
lemma mem_support_run_lift_bind
    (oa : OracleComp spec α) (f : α → OptionT (OracleComp spec) β) {y : Option β}
    (hy : y ∈ support ((OptionT.lift oa >>= f : OptionT (OracleComp spec) β).run)) :
    ∃ a, a ∈ support oa ∧ y ∈ support ((f a).run) := by
  rwa [OptionT.run_bind, OptionT.run_lift, Option.elimM, bind_pure_comp, bind_map_left,
    mem_support_bind_iff] at hy


-- @@ L646-646 verbatim
end OptionT
