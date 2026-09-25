/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import PolyFun.PFunctor.Free.Cursor.Fork
public import ToMathlib.Data.ENNReal.SumSquares
public import VCVio.EvalDist.Option
public import VCVio.OracleComp.Constructions.Fork
public import VCVio.OracleComp.QueryTracking.LoggingOracle
public import VCVio.OracleComp.QueryTracking.Structures


-- @@ L15-55 verbatim
/-!
# Replay-Based Forking

This file proves a replay-style forking lemma using PolyFun's typed execution
paths and occurrence contexts. A first path selects an oracle occurrence; the
same context is then completed independently a second time. The shared prefix
and both suffixes are intrinsic in `PFunctor.FreeM.Cursor.ForkView`, leaving the
VCVio layer responsible only for probability and collision estimates.

The accompanying `QueryLog` view is an erasure interface for applications such
as Fiat--Shamir that state postconditions over transcripts.

Dependent path and zipper APIs identify `QueryLog` entries with erased polynomial
trace events, so this file makes `PFunctor.Idx` locally reducible in order for
`simp` and `rw` to match through it. The attribute is scoped to this file because
`PFunctor.Idx` is a Mathlib definition.

## Main definitions

* `replayFirstRun`: the first run of the main computation, instrumented with a query log.
* `replayFirstPath`: the intrinsic execution path taken by that first run.
* `CfReachable` / `PathCfReachable`: reachability of a selected occurrence from an output.
* `contextFork`: two independent completions of the occurrence context chosen by the first path.
* `contextForkWitness`: the fork together with the transcript data witnessing success.
* `guardedContextFork`: `contextFork` restricted to forks whose focused answers differ.
* `contextForkCollision`: the event that both completions return the same focused answer.

## Main results

* `contextForkWitness_success`: a successful witness yields two accepting transcripts.
* `contextFork_success`: the analogous statement for `contextFork`.
* `contextFork_propertyTransfer`: postconditions of the main computation transfer to both branches.
* `sq_probOutput_main_le_contextForkPair`: the squaring step for two independent completions.
* `le_probEvent_isSome_contextFork`: the replay forking bound.

## References

* M. Bellare and G. Neven, *Multi-Signatures in the Plain Public-Key Model and a General
  Forking Lemma*, CCS 2006. The seed-based presentation is mechanized in
  `VCVio.CryptoFoundations.SeededFork`.
-/


-- @@ L57-57 verbatim
@[expose] public section


-- @@ L59-59 verbatim
open OracleSpec OracleComp ENNReal Function Finset


-- @@ L61-61 verbatim
open scoped OracleSpec.PrimitiveQuery

-- @@ L62-65 verbatim
open scoped PFunctor

/- Replay logs and intrinsic paths meet through their list and dependent-pair
presentations; these two reducers are needed only while matching that seam. -/

-- @@ L66-66 verbatim
attribute [local implicit_reducible] FreeMonoid PFunctor.Idx


-- @@ L68-68 verbatim
namespace OracleComp


-- @@ L70-70 verbatim
variable {ι : Type} {spec : OracleSpec ι} {α : Type}


-- @@ L72-75 verbatim
/-- Run `main` with query logging. This is the first-run object for replay forks. -/
@[reducible]
def replayFirstRun (main : OracleComp spec α) : OracleComp spec (α × QueryLog spec) :=
  main.withQueryLog


-- @@ L77-80 verbatim
/-- The first run represented intrinsically: executing `main` returns the
typed root-to-leaf path selected by its oracle answers. -/
def replayFirstPath (main : OracleComp spec α) : OracleComp spec (PFunctor.FreeM.Path main) :=
  PFunctor.FreeM.withPath main


-- @@ L82-86 verbatim
/-- Forget an intrinsic first-run path into the output/transcript pair used by
the probability-facing replay API. -/
def replayPathResult (main : OracleComp spec α) (path : PFunctor.FreeM.Path main) :
    α × QueryLog spec :=
  pathLogResult main path


-- @@ L88-97 expanded
/-- The intrinsic first-run path of a query-bind: query `t`, then for each answer `u`
prepend that answer to the path taken by the continuation `next u`. -/
@[simp]
theorem replayFirstPath_query_bind (t : spec.Domain) (next : spec.Range t → OracleComp spec α) :
    replayFirstPath (liftM (OracleSpec.query t) >>= next) =
      OracleComp.queryBind t fun u =>
        PFunctor.FreeM.map
          (fun path : PFunctor.FreeM.Path (next u) =>
            (⟨u, path⟩ : PFunctor.FreeM.Path (OracleComp.queryBind t next)))
          (replayFirstPath (next u)) :=
  rfl


-- @@ L99-104 verbatim
/-- Intrinsic path execution and writer-style query logging are the same first
run after erasing the path to its output and trace. This is the bridge that
lets replay proofs use typed paths without changing their probability API. -/
theorem map_replayPathResult_replayFirstPath (main : OracleComp spec α) :
    PFunctor.FreeM.map (replayPathResult main) (replayFirstPath main) = replayFirstRun main :=
  map_pathLogResult_withPath main


-- @@ L106-113 verbatim
/-- A supported intrinsic path erases to a supported legacy first-run result. -/
lemma replayPathResult_mem_support_replayFirstRun
    (main : OracleComp spec α) (path : PFunctor.FreeM.Path main)
    (hpath : path ∈ support (replayFirstPath main)) :
    replayPathResult main path ∈ support (replayFirstRun main) := by
  rw [← map_replayPathResult_replayFirstPath]
  exact (support_map (replayPathResult main) (replayFirstPath main)).symm ▸
    Set.mem_image_of_mem _ hpath


-- @@ L115-135 verbatim
/-- Every well-typed path through an oracle computation is supported. Oracle
queries have universal symbolic support, so a `Path` already contains all the
evidence needed to select its successive branches. -/
lemma mem_support_replayFirstPath (main : OracleComp spec α) (path : PFunctor.FreeM.Path main) :
    path ∈ support (replayFirstPath main) := by
  induction main with
  | pure x =>
      cases path
      change PUnit.unit ∈ support (pure PUnit.unit : OracleComp spec PUnit)
      simp
  | queryBind t next ih =>
      rcases path with ⟨answer, tail⟩
      change (⟨answer, tail⟩ : PFunctor.FreeM.Path (OracleComp.queryBind t next)) ∈
        support ((spec.query t : OracleComp spec _) >>= fun u =>
          (((fun inner : PFunctor.FreeM.Path (next u) =>
              (⟨u, inner⟩ : PFunctor.FreeM.Path (OracleComp.queryBind t next))) <$>
            replayFirstPath (next u)) : OracleComp spec _))
      rw [mem_support_bind_iff]
      refine ⟨answer, by simp, ?_⟩
      rw [support_map]
      exact Set.mem_image_of_mem _ (ih answer tail)


-- @@ L137-141 verbatim
/-- Forgetting the path produced by the intrinsic first run recovers the
original oracle computation. -/
@[simp] theorem map_output_replayFirstPath (main : OracleComp spec α) :
    PFunctor.FreeM.output main <$> replayFirstPath main = main :=
  PFunctor.FreeM.map_output_withPath main


-- @@ L143-151 verbatim
/-- The selected entry of an occurrence completion's erased trace is exactly
its focused answer. -/
lemma getQueryValue?_completion_path_eq_answer [spec.DecidableEq] {main : OracleComp spec α} {i : ι}
    {n : Nat} (occurrence : PFunctor.FreeM.Cursor.Occurrence i main n)
    (completion : occurrence.Completion) :
    QueryLog.getQueryValue? (PFunctor.FreeM.Path.trace main completion.path) i n =
      some completion.answer := by
  rw [QueryLog.getQueryValue?_eq_getAt?]
  exact occurrence.getAt?_trace_completion_path completion


-- @@ L153-153 verbatim
section quantitative


-- @@ L155-155 verbatim
variable [spec.DecidableEq]


-- @@ L157-167 verbatim
/-- Reachability hypothesis on the fork-index selector `cf`: whenever the first run
of `main` outputs `x` and the recorded log is `log`, every selected fork index
`s = cf x` actually corresponds to an `i`-query in `log` (i.e. the `s`-th
`i`-query exists in the log). In Fiat--Shamir applications `cf` extracts the
index of a recorded query, so this property holds by construction. -/
def CfReachable (main : OracleComp spec α) (qb : ι → ℕ) (i : ι) (cf : α → Option (Fin (qb i + 1))) :
    Prop :=
  ∀ {x : α} {log : QueryLog spec},
    (x, log) ∈ support (replayFirstRun main) →
    ∀ s : Fin (qb i + 1), cf x = some s →
      (QueryLog.getQueryValue? log i ↑s).isSome


-- @@ L169-175 verbatim
/-- Intrinsic form of selector reachability: every selected ordinal is an
actual occurrence on the typed execution path. -/
def PathCfReachable (main : OracleComp spec α) (qb : ι → ℕ) (i : ι)
    (cf : α → Option (Fin (qb i + 1))) : Prop :=
  ∀ (path : PFunctor.FreeM.Path main) (s : Fin (qb i + 1)),
    cf (PFunctor.FreeM.output main path) = some s →
      (PFunctor.FreeM.Cursor.locateAt? (P := spec.toPFunctor) i main path s).isSome


-- @@ L177-185 verbatim
/-- Transcript reachability implies the canonical path-level condition. -/
theorem CfReachable.toPathCfReachable {main : OracleComp spec α} {qb : ι → ℕ} {i : ι}
    {cf : α → Option (Fin (qb i + 1))} (hreach : CfReachable main qb i cf) :
    PathCfReachable main qb i cf := by
  intro path s hcf
  rw [PFunctor.FreeM.Cursor.locateAt?_isSome_iff_lt_occurrences,
    ← PFunctor.TraceList.getAt?_isSome_iff_lt_occurrences, ← QueryLog.getQueryValue?_eq_getAt?]
  exact hreach (replayPathResult_mem_support_replayFirstRun main path
    (mem_support_replayFirstPath main path)) s (by simpa [replayPathResult] using hcf)


-- @@ L187-187 verbatim
/-! ## Intrinsic quantitative games -/


-- @@ L189-195 verbatim
/-- Two independent completions of occurrence `s`, represented entirely by
PolyFun's typed context machinery. -/
def contextForkView (main : OracleComp spec α) (i : ι) (s : Nat) :
    OracleComp spec (Option (PFunctor.FreeM.Cursor.ForkView i main s)) :=
  PFunctor.FreeM.Cursor.locateAndForkAt (P := spec.toPFunctor) i main s

-- Shared success classifier for the fixed and dynamically selected context-fork experiments.

-- @@ L196-203 verbatim
def classifyForkView (main : OracleComp spec α) (qb : ι → ℕ) (i : ι)
    (cf : α → Option (Fin (qb i + 1))) (s : Fin (qb i + 1))
    (view : PFunctor.FreeM.Cursor.ForkView i main s) : Option (α × α) :=
  let x₁ := PFunctor.FreeM.output main view.firstPath
  let x₂ := PFunctor.FreeM.output main view.secondPath
  if view.firstAnswer = view.secondAnswer then none
  else if cf x₁ = some s ∧ cf x₂ = some s then some (x₁, x₂)
  else none


-- @@ L205-212 verbatim
@[simp] private theorem classifyForkView_isSome
    (main : OracleComp spec α) (qb : ι → ℕ) (i : ι) (cf : α → Option (Fin (qb i + 1)))
    (s : Fin (qb i + 1)) (view : PFunctor.FreeM.Cursor.ForkView i main s) :
    (classifyForkView main qb i cf s view).isSome ↔
      view.firstAnswer ≠ view.secondAnswer ∧
        cf (PFunctor.FreeM.output main view.firstPath) = some s ∧
        cf (PFunctor.FreeM.output main view.secondPath) = some s := by
  grind [classifyForkView]


-- @@ L214-219 verbatim
private theorem classifyForkView_component_iff
    (main : OracleComp spec α) (qb : ι → ℕ) (i : ι) (cf : α → Option (Fin (qb i + 1)))
    (s : Fin (qb i + 1)) (view : PFunctor.FreeM.Cursor.ForkView i main s) :
    (classifyForkView main qb i cf s view).map (cf ∘ Prod.fst) = some (some s) ↔
      (classifyForkView main qb i cf s view).isSome := by
  grind [classifyForkView]


-- @@ L221-225 verbatim
/-- Semantic result of a dynamically selected fork.  The selecting ordinal,
shared occurrence context, and both completions remain available to
reduction-facing proofs. -/
abbrev ContextForkWitness (main : OracleComp spec α) (qb : ι → ℕ) (i : ι) :=
  PFunctor.FreeM.Cursor.SelectedForkView i main (Fin (qb i + 1)) Fin.val


-- @@ L227-231 verbatim
def acceptContextForkWitness (main : OracleComp spec α) (qb : ι → ℕ) (i : ι)
    (cf : α → Option (Fin (qb i + 1))) (s : Fin (qb i + 1))
    (view : PFunctor.FreeM.Cursor.ForkView i main s) :
    Option (ContextForkWitness main qb i) :=
  if (classifyForkView main qb i cf s view).isSome then some ⟨s, view⟩ else none


-- @@ L233-240 verbatim
@[simp] private theorem acceptContextForkWitness_eq_some
    (main : OracleComp spec α) (qb : ι → ℕ) (i : ι) (cf : α → Option (Fin (qb i + 1)))
    (s : Fin (qb i + 1)) (view : PFunctor.FreeM.Cursor.ForkView i main s) :
    acceptContextForkWitness main qb i cf s view = some ⟨s, view⟩ ↔
      view.firstAnswer ≠ view.secondAnswer ∧
        cf (PFunctor.FreeM.output main view.firstPath) = some s ∧
        cf (PFunctor.FreeM.output main view.secondPath) = some s := by
  simp [acceptContextForkWitness]


-- @@ L242-250 verbatim
/-- Canonical rich forking experiment. Probability statements may project
its output pair, while Fiat--Shamir reductions can consume the typed
occurrence and the two completions directly. -/
def contextForkWitness (main : OracleComp spec α) (qb : ι → ℕ) (i : ι)
    (cf : α → Option (Fin (qb i + 1))) :
    OracleComp spec (Option (ContextForkWitness main qb i)) :=
  PFunctor.FreeM.Cursor.filterMapLocateAndForkSelected (P := spec.toPFunctor)
    i main cf Fin.val fun selected =>
      acceptContextForkWitness main qb i cf selected.label selected.view


-- @@ L252-259 verbatim
omit [spec.DecidableEq] in
/-- The `outputs` pair of a contextual-fork witness is the pair of oracle outputs read at its
first and second fork paths. -/
@[simp] theorem contextForkWitness_outputs (main : OracleComp spec α) (qb : ι → ℕ) (i : ι)
    (witness : ContextForkWitness main qb i) :
    (PFunctor.FreeM.Cursor.SelectedForkView.outputs witness) =
      (PFunctor.FreeM.output main witness.view.firstPath,
        PFunctor.FreeM.output main witness.view.secondPath) := rfl


-- @@ L261-264 verbatim
def contextForkByClassify (main : OracleComp spec α) (qb : ι → ℕ) (i : ι)
    (cf : α → Option (Fin (qb i + 1))) : OracleComp spec (Option (α × α)) :=
  PFunctor.FreeM.Cursor.filterMapLocateAndForkBy (P := spec.toPFunctor)
    i main cf Fin.val (classifyForkView main qb i cf)


-- @@ L266-291 verbatim
private theorem map_contextForkWitness_outputs_eq_contextForkByClassify
    (main : OracleComp spec α) (qb : ι → ℕ) (i : ι)
    (cf : α → Option (Fin (qb i + 1))) :
    PFunctor.FreeM.map
        (Option.map PFunctor.FreeM.Cursor.SelectedForkView.outputs)
        (contextForkWitness main qb i cf) = contextForkByClassify main qb i cf := by
  unfold contextForkWitness contextForkByClassify
  rw [PFunctor.FreeM.Cursor.filterMapLocateAndForkSelected_eq_filterMapLocateAndForkBy]
  unfold PFunctor.FreeM.Cursor.filterMapLocateAndForkBy
  rw [← PFunctor.FreeM.comp_map,
    PFunctor.FreeM.Cursor.map_locateAndForkBy,
    PFunctor.FreeM.Cursor.map_locateAndForkBy]
  apply congrArg (PFunctor.FreeM.bind (PFunctor.FreeM.withPath main))
  funext path
  rcases hcf : cf (PFunctor.FreeM.output main path) with _ | s
  · rfl
  · rcases hlocate : PFunctor.FreeM.Cursor.locateAt?
        (P := spec.toPFunctor) i main path s with _ | located
    · simp [hlocate]
    · simp only [hlocate]
      apply congrArg (fun f => PFunctor.FreeM.map f located.fork)
      funext view
      simp only [Function.comp_apply, Option.join, Option.map]
      unfold acceptContextForkWitness classifyForkView
      split <;> split <;> simp_all
      grind


-- @@ L293-300 verbatim
/-- Canonical dynamically selected fork. The first execution chooses an
ordinal through `cf`; PolyFun locates that occurrence and independently
completes the same typed context a second time. -/
def contextFork (main : OracleComp spec α) (qb : ι → ℕ) (i : ι) (cf : α → Option (Fin (qb i + 1))) :
    OracleComp spec (Option (α × α)) :=
  PFunctor.FreeM.map
    (Option.map PFunctor.FreeM.Cursor.SelectedForkView.outputs)
    (contextForkWitness main qb i cf)


-- @@ L302-305 verbatim
private theorem contextFork_eq_contextForkByClassify (main : OracleComp spec α) (qb : ι → ℕ) (i : ι)
    (cf : α → Option (Fin (qb i + 1))) :
    contextFork main qb i cf = contextForkByClassify main qb i cf :=
  map_contextForkWitness_outputs_eq_contextForkByClassify main qb i cf


-- @@ L307-337 verbatim
/-- Every supported rich witness carries a supported second completion and
the pure success conditions checked by the contextual fork. -/
theorem contextForkWitness_success
    (main : OracleComp spec α) (qb : ι → ℕ) (i : ι)
    (cf : α → Option (Fin (qb i + 1)))
    {witness : ContextForkWitness main qb i}
    (h : some witness ∈ support (contextForkWitness main qb i cf)) :
    witness.view.second ∈ support (Cursor.completeOccurrence witness.view.occurrence) ∧
      witness.view.firstAnswer ≠ witness.view.secondAnswer ∧
      cf (PFunctor.FreeM.output main witness.view.firstPath) = some witness.label ∧
      cf (PFunctor.FreeM.output main witness.view.secondPath) = some witness.label := by
  rw [contextForkWitness,
    PFunctor.FreeM.Cursor.filterMapLocateAndForkSelected_eq_filterMapLocateAndForkBy,
    PFunctor.FreeM.Cursor.filterMapLocateAndForkBy_eq_bind_complete] at h
  obtain ⟨path, _, h⟩ := mem_support_bind_peel _ _ h
  rcases hcf : cf (PFunctor.FreeM.output main path) with _ | s
  · simp only [hcf] at h
    cases eq_of_mem_support_pure none h
  rcases hlocated : PFunctor.FreeM.Cursor.locateAt?
      (P := spec.toPFunctor) i main path s with _ | located
  · simp only [hcf, hlocated] at h
    cases eq_of_mem_support_pure none h
  simp only [hcf, hlocated] at h
  obtain ⟨second, hsecond, hresult⟩ := mem_support_map_peel _ _ h
  by_cases haccept : (classifyForkView main qb i cf s
      { occurrence := located.occurrence, first := located.completion, second := second }).isSome
  · rw [acceptContextForkWitness, if_pos haccept, Option.some.injEq] at hresult
    subst hresult
    exact ⟨hsecond, (classifyForkView_isSome main qb i cf s _).mp haccept⟩
  · rw [acceptContextForkWitness, if_neg haccept] at hresult
    cases hresult


-- @@ L339-365 verbatim
/-- Successful contextual forks expose the selected path, its certified
occurrence, and the independently sampled second completion. -/
theorem contextFork_success
    (main : OracleComp spec α) (qb : ι → ℕ) (i : ι)
    (cf : α → Option (Fin (qb i + 1))) {x₁ x₂ : α}
    (h : some (x₁, x₂) ∈ support (contextFork main qb i cf)) :
    ∃ (path : PFunctor.FreeM.Path main) (s : Fin (qb i + 1))
      (located : PFunctor.FreeM.Cursor.Located i main path s)
      (second : located.occurrence.Completion),
      path ∈ support (Cursor.withPath main) ∧
      cf (PFunctor.FreeM.output main path) = some s ∧
      second ∈ support (Cursor.completeOccurrence located.occurrence) ∧
      located.completion.answer ≠ second.answer ∧
      cf (PFunctor.FreeM.output main second.path) = some s ∧
      x₁ = PFunctor.FreeM.output main path ∧
      x₂ = PFunctor.FreeM.output main second.path := by
  rw [contextFork] at h
  obtain ⟨result, hresult, houtputs⟩ := mem_support_map_peel _ _ h
  rcases result with _ | witness
  · simp at houtputs
  · simp only [Option.map, Option.some.injEq] at houtputs
    obtain ⟨hsecond, hne, hcf₁, hcf₂⟩ :=
      contextForkWitness_success main qb i cf hresult
    exact ⟨witness.view.firstPath, witness.label,
      .ofCompletion witness.view.first, witness.view.second,
      mem_support_replayFirstPath main witness.view.firstPath, hcf₁, hsecond, hne,
      hcf₂, congrArg Prod.fst houtputs, congrArg Prod.snd houtputs⟩


-- @@ L367-396 verbatim
/-- Transfer first-run log invariants through a successful contextual fork.
The differing selected entries follow directly from the two completions of
the retained occurrence. -/
theorem contextFork_propertyTransfer [IsUniformSpec spec]
    (main : OracleComp spec α) (qb : ι → ℕ) (i : ι)
    (cf : α → Option (Fin (qb i + 1)))
    (P_out : α → QueryLog spec → Prop)
    (hP : ∀ {x log}, (x, log) ∈ support (replayFirstRun main) → P_out x log)
    {x₁ x₂ : α}
    (h : some (x₁, x₂) ∈ support (contextFork main qb i cf)) :
    ∃ (log₁ log₂ : QueryLog spec) (s : Fin (qb i + 1)),
      cf x₁ = some s ∧ cf x₂ = some s ∧
      P_out x₁ log₁ ∧ P_out x₂ log₂ ∧
      QueryLog.getQueryValue? log₁ i s ≠
        QueryLog.getQueryValue? log₂ i s := by
  obtain ⟨path, s, located, second, hpath, hcf₁, _hsecond,
      hne, hcf₂, hx₁, hx₂⟩ := contextFork_success main qb i cf h
  let log₁ : QueryLog spec := PFunctor.FreeM.Path.trace main path
  let log₂ : QueryLog spec := PFunctor.FreeM.Path.trace main second.path
  have hlookup₁ : QueryLog.getQueryValue? log₁ i s = some located.completion.answer := by
    simpa [log₁] using congrArg (PFunctor.FreeM.Path.trace main) located.path_eq ▸
      getQueryValue?_completion_path_eq_answer located.occurrence located.completion
  refine ⟨log₁, log₂, s, hx₁ ▸ hcf₁, hx₂ ▸ hcf₂, hP ?_, hP ?_, ?_⟩
  · simpa [log₁, replayPathResult, hx₁] using
      replayPathResult_mem_support_replayFirstRun main path hpath
  · simpa [log₂, replayPathResult, hx₂] using
      replayPathResult_mem_support_replayFirstRun main second.path
        (mem_support_replayFirstPath main second.path)
  · rw [hlookup₁, getQueryValue?_completion_path_eq_answer located.occurrence second]
    exact fun heq => hne (Option.some.inj heq)


-- @@ L398-403 verbatim
/-- The fixed-index guarded context experiment. It succeeds exactly when both
outputs select `s` and the two focused oracle answers differ. -/
def guardedContextFork (main : OracleComp spec α) (qb : ι → ℕ) (i : ι)
    (cf : α → Option (Fin (qb i + 1))) (s : Fin (qb i + 1)) :
    OracleComp spec (Option (α × α)) :=
  PFunctor.FreeM.Cursor.filterMapLocateAndForkAt i main s (classifyForkView main qb i cf s)


-- @@ L405-412 verbatim
def collideForkView (main : OracleComp spec α) (qb : ι → ℕ) (i : ι)
    (cf : α → Option (Fin (qb i + 1))) (s : Fin (qb i + 1)) :
    Option (PFunctor.FreeM.Cursor.ForkView i main s) → Option (Fin (qb i + 1))
  | none => none
  | some view => if view.firstAnswer = view.secondAnswer ∧
      cf (PFunctor.FreeM.output main view.firstPath) = some s ∧
      cf (PFunctor.FreeM.output main view.secondPath) = some s
      then some s else none


-- @@ L414-421 verbatim
@[simp] private theorem collideForkView_eq_some
    (main : OracleComp spec α) (qb : ι → ℕ) (i : ι) (cf : α → Option (Fin (qb i + 1)))
    (s : Fin (qb i + 1)) (view : PFunctor.FreeM.Cursor.ForkView i main s) :
    collideForkView main qb i cf s (some view) = some s ↔
      view.firstAnswer = view.secondAnswer ∧
        cf (PFunctor.FreeM.output main view.firstPath) = some s ∧
        cf (PFunctor.FreeM.output main view.secondPath) = some s := by
  simp [collideForkView]


-- @@ L423-426 verbatim
def contextForkViewCollision (main : OracleComp spec α) (qb : ι → ℕ) (i : ι)
    (cf : α → Option (Fin (qb i + 1))) (s : Fin (qb i + 1)) :
    OracleComp spec (Option (Fin (qb i + 1))) :=
  PFunctor.FreeM.map (collideForkView main qb i cf s) (contextForkView main i s)


-- @@ L428-439 verbatim
/-- Per-path continuation of `contextForkCollision`. Locate occurrence `s` on `path`; if it is
present, resample the focused answer and report `some s` exactly when the fresh answer collides
with the first completion's answer and the path already selected `s`. -/
def contextForkCollisionCont (main : OracleComp spec α) (qb : ι → ℕ) (i : ι)
    (cf : α → Option (Fin (qb i + 1))) (s : Fin (qb i + 1)) (path : PFunctor.FreeM.Path main) :
    OracleComp spec (Option (Fin (qb i + 1))) :=
  match PFunctor.FreeM.Cursor.locateAt? (P := spec.toPFunctor) i main path s with
  | none => pure none
  | some located => do
      let secondAnswer ← spec.query i
      if located.completion.answer = secondAnswer ∧ cf (PFunctor.FreeM.output main path) = some s
        then pure (some s) else pure none


-- @@ L441-446 verbatim
/-- Equal focused answers form the sole collision branch removed by
`guardedContextFork`. -/
def contextForkCollision (main : OracleComp spec α) (qb : ι → ℕ) (i : ι)
    (cf : α → Option (Fin (qb i + 1))) (s : Fin (qb i + 1)) :
    OracleComp spec (Option (Fin (qb i + 1))) :=
  PFunctor.FreeM.withPath main >>= contextForkCollisionCont main qb i cf s


-- @@ L448-462 expanded
private theorem probEvent_classifyForkView_isSome_eq_zero_of_first_ne [IsProbabilitySpec spec]
    (main : OracleComp spec α) (qb : ι → ℕ) (i : ι) (cf : α → Option (Fin (qb i + 1)))
    (s : Fin (qb i + 1)) {path : PFunctor.FreeM.Path main}
    (located : PFunctor.FreeM.Cursor.Located i main path s)
    (hfirst : cf (PFunctor.FreeM.output main located.completion.path) ≠ some s) :
    (probEvent
        (OracleComp.ofFreeM
          (PFunctor.FreeM.map
            (fun second =>
              classifyForkView main qb i cf s
                { occurrence := located.occurrence
                  first := located.completion
                  second := second })
            located.occurrence.complete))
        fun result : Option (α × α) => result.isSome) =
      0 :=
  by
  rw [probEvent_ofFreeM_map]
  convert probEvent_False (ofFreeM located.occurrence.complete)
  simp [PFunctor.FreeM.Cursor.ForkView.firstPath, hfirst]


-- @@ L464-478 expanded
private theorem probEvent_classifyForkView_component_eq_zero_of_ne [IsProbabilitySpec spec]
    (main : OracleComp spec α) (qb : ι → ℕ) (i : ι) (cf : α → Option (Fin (qb i + 1)))
    (t s : Fin (qb i + 1)) {path : PFunctor.FreeM.Path main}
    (located : PFunctor.FreeM.Cursor.Located i main path t) (hne : t ≠ s) :
    (probEvent
        (OracleComp.ofFreeM
          (PFunctor.FreeM.map
            (fun second =>
              classifyForkView main qb i cf t
                { occurrence := located.occurrence
                  first := located.completion
                  second := second })
            located.occurrence.complete))
        fun result : Option (α × α) => result.map (cf ∘ Prod.fst) = some (some s)) =
      0 :=
  by
  rw [probEvent_ofFreeM_map]
  convert probEvent_False _
  grind [classifyForkView]


-- @@ L480-486 verbatim
/-- The pair of `cf`-classifications observed from the two completions of the fixed
occurrence at index `i` and position `s`: the `contextForkView`-family specialization of
`observedForkPair` over which the replay-forking squaring and partition bounds are stated. -/
def contextForkPair (main : OracleComp spec α) (qb : ι → ℕ) (i : ι)
    (cf : α → Option (Fin (qb i + 1))) (s : Fin (qb i + 1)) :
    OracleComp spec (Option (Option (Fin (qb i + 1)) × Option (Fin (qb i + 1)))) :=
  observedForkPair main i s cf


-- @@ L488-499 expanded
/-- Fixed-index success squares under two independent completions of the
PolyFun occurrence context. This is the analytic core of replay forking and
does not use query logs, replay cursors, or a bespoke oracle interpreter. -/
theorem sq_probOutput_main_le_contextForkPair [IsUniformSpec spec] (main : OracleComp spec α)
    (qb : ι → ℕ) (i : ι) (cf : α → Option (Fin (qb i + 1))) (hreach : PathCfReachable main qb i cf)
    (s : Fin (qb i + 1)) :
    probOutput (cf <$> main) s ^ 2 ≤
      probOutput (contextForkPair main qb i cf s)
        (some (some s, some s) : Option (Option (Fin (qb i + 1)) × Option (Fin (qb i + 1)))) :=
  sq_probOutput_map_le_observedForkPair main i s cf s (fun path => hreach path s)


-- @@ L501-557 expanded
/-- Fixed-index pair success partitions into a genuine guarded fork or an
equal-answer collision, all as observations of the same `ForkView`. -/
theorem probOutput_contextForkPair_le_guarded_add_collision [IsUniformSpec spec]
    (main : OracleComp spec α) (qb : ι → ℕ) (i : ι) (cf : α → Option (Fin (qb i + 1)))
    (s : Fin (qb i + 1)) :
    probOutput (contextForkPair main qb i cf s)
        (some (some s, some s) : Option (Option (Fin (qb i + 1)) × Option (Fin (qb i + 1)))) ≤
      (probEvent (guardedContextFork main qb i cf s) fun result : Option (α × α) => result.isSome) +
        probOutput (contextForkViewCollision main qb i cf s) (some s : Option (Fin (qb i + 1))) :=
  by
  let source := contextForkView main i s
  let pairGood : Option (PFunctor.FreeM.Cursor.ForkView i main (s : Nat)) → Prop
    | none => False
    | some view =>
      cf (PFunctor.FreeM.output main view.firstPath) = some s ∧
        cf (PFunctor.FreeM.output main view.secondPath) = some s
  let guardGood : Option (PFunctor.FreeM.Cursor.ForkView i main (s : Nat)) → Prop := fun view? =>
    (view?.bind (classifyForkView main qb i cf s)).isSome
  let collisionGood : Option (PFunctor.FreeM.Cursor.ForkView i main (s : Nat)) → Prop :=
    fun view? => collideForkView main qb i cf s view? = some s
  have hpoint : ∀ view?, pairGood view? → guardGood view? ∨ collisionGood view? := by
    rintro (_ | view) <;> simp only [pairGood] <;> grind [classifyForkView, collideForkView]
  have hpair :
    probOutput (contextForkPair main qb i cf s)
        (some (some s, some s) : Option (Option (Fin (qb i + 1)) × Option (Fin (qb i + 1)))) =
      probEvent source pairGood :=
    by
    rw [← probEvent_eq_eq_probOutput, contextForkPair, observedForkPair, probEvent_map]
    congr 1 with (_ | view) <;> simp [pairGood]
  have hguard :
    probEvent source guardGood =
      probEvent (guardedContextFork main qb i cf s) fun result : Option (α × α) => result.isSome :=
    by
    unfold guardedContextFork PFunctor.FreeM.Cursor.filterMapLocateAndForkAt
    rw [probEvent_ofFreeM_map]
    unfold source contextForkView guardGood
    apply
      congrArg (probEvent (PFunctor.FreeM.Cursor.locateAndForkAt (P := spec.toPFunctor) i main s))
    funext view?
    rw [Function.comp_apply]
  have hcollision :
    probEvent source collisionGood =
      probOutput (contextForkViewCollision main qb i cf s) (some s : Option (Fin (qb i + 1))) :=
    by
    rw [← probEvent_eq_eq_probOutput, contextForkViewCollision]
    change
      probEvent source collisionGood =
        probEvent (collideForkView main qb i cf s <$> source) fun x => x = some s
    rw [probEvent_map]
    apply congrArg (probEvent source)
    funext view?
    rw [Function.comp_apply]
  rw [hpair]
  calc
    probEvent source pairGood ≤
        probEvent source fun view? => guardGood view? ∨ collisionGood view? :=
      probEvent_mono (mx := source) fun view? _ => hpoint view?
    _ ≤ probEvent source guardGood + probEvent source collisionGood :=
      (probEvent_or_le source guardGood collisionGood)
    _ = _ := by rw [hguard, hcollision]


-- @@ L559-614 expanded
/-- A fresh focused answer collides with the first completion's answer with
probability at most the inverse answer-space cardinality. -/
theorem probOutput_contextForkCollision_le_main_div [IsUniformSpec spec] (main : OracleComp spec α)
    (qb : ι → ℕ) (i : ι) (cf : α → Option (Fin (qb i + 1))) (s : Fin (qb i + 1)) :
    probOutput (contextForkCollision main qb i cf s) (some s : Option (Fin (qb i + 1))) ≤
      probOutput (cf <$> main) (some s : Option (Fin (qb i + 1))) / Fintype.card (spec.Range i) :=
  by
  let paths : OracleComp spec (PFunctor.FreeM.Path main) := PFunctor.FreeM.withPath main
  let collision : PFunctor.FreeM.Path main → OracleComp spec (Option (Fin (qb i + 1))) :=
    contextForkCollisionCont main qb i cf s
  rw [← probEvent_eq_eq_probOutput]
  calc
    (probEvent (paths >>= collision) fun result => result = some s) ≤
        (probEvent paths fun path => cf (PFunctor.FreeM.output main path) = some s) /
          Fintype.card (spec.Range i) :=
      by
      apply probEvent_bind_le_probEvent_div
      · intro path _ hcf
        simp only [collision, contextForkCollisionCont]
        rcases hlocated : PFunctor.FreeM.Cursor.locateAt? (P := spec.toPFunctor) i main path s with
          _ | located
        · simp
        · have hevent :
            (probEvent
                (do
                  let secondAnswer ← (liftM (spec.query i) : OracleComp spec (spec.Range i))
                  if
                      located.completion.answer = secondAnswer ∧
                        cf (PFunctor.FreeM.output main path) = some s then
                    
                    pure (some s)
                  else
                    pure none)
                fun result => result = some s) =
              probEvent (liftM (spec.query i) : OracleComp spec (spec.Range i)) fun secondAnswer =>
                located.completion.answer = secondAnswer :=
            by
            rw [probEvent_bind_eq_tsum, probEvent_eq_tsum_ite]
            refine tsum_congr fun secondAnswer => ?_
            by_cases heq : located.completion.answer = secondAnswer <;> simp [hcf, heq]
          rw [hevent]
          simp [eq_comm]
      · intro path _ hcf
        simp only [collision, contextForkCollisionCont]
        rcases hlocated : PFunctor.FreeM.Cursor.locateAt? (P := spec.toPFunctor) i main path s with
          _ | located
        · simp
        · rw [probEvent_bind_eq_tsum]
          refine ENNReal.tsum_eq_zero.mpr fun secondAnswer => ?_
          by_cases heq : located.completion.answer = secondAnswer <;> simp [hcf, heq]
    _ = probOutput (cf <$> main) (some s : Option (Fin (qb i + 1))) / Fintype.card (spec.Range i) :=
      by
      have hpaths : (PFunctor.FreeM.output main <$> paths : OracleComp spec α) = main :=
        PFunctor.FreeM.map_output_withPath main
      congr 1
      rw [← probEvent_eq_eq_probOutput]
      conv_rhs => rw [← hpaths, probEvent_map, probEvent_map]
      apply congrArg (probEvent paths)
      funext path
      rw [Function.comp_apply, Function.comp_apply]


-- @@ L616-705 expanded
/-- Requiring the colliding second completion to finish successfully can only
decrease the path-first equal-answer collision probability. -/
theorem probOutput_contextForkViewCollision_le_collision [IsUniformSpec spec]
    (main : OracleComp spec α) (qb : ι → ℕ) (i : ι) (cf : α → Option (Fin (qb i + 1)))
    (s : Fin (qb i + 1)) :
    probOutput (contextForkViewCollision main qb i cf s) (some s : Option (Fin (qb i + 1))) ≤
      probOutput (contextForkCollision main qb i cf s) (some s : Option (Fin (qb i + 1))) :=
  by
  let paths : OracleComp spec (PFunctor.FreeM.Path main) := PFunctor.FreeM.withPath main
  let viewCollision : PFunctor.FreeM.Path main → OracleComp spec (Option (Fin (qb i + 1))) :=
    fun path =>
    match PFunctor.FreeM.Cursor.locateAt? (P := spec.toPFunctor) i main path s with
    | none => pure none
    | some located =>
      PFunctor.FreeM.bind (PFunctor.FreeM.lift (P := spec.toPFunctor) i) fun secondAnswer =>
        (fun secondSuffix =>
            collideForkView main qb i cf s
              (some
                { occurrence := located.occurrence
                  first := located.completion
                  second := ⟨secondAnswer, secondSuffix⟩ })) <$>
          PFunctor.FreeM.withPath (located.occurrence.resume secondAnswer)
  let answerCollision : PFunctor.FreeM.Path main → OracleComp spec (Option (Fin (qb i + 1))) :=
    fun path =>
    match PFunctor.FreeM.Cursor.locateAt? (P := spec.toPFunctor) i main path s with
    | none => pure none
    | some located => do
      let secondAnswer ← spec.query i
      if
          located.completion.answer = secondAnswer ∧
            cf (PFunctor.FreeM.output main path) = some s then
        
        pure (some s)
      else
        pure none
  have hsource : contextForkViewCollision main qb i cf s = paths >>= viewCollision :=
    by
    let : spec.toPFunctor.DecidableEq := (inferInstance : spec.DecidableEq).toDecidableEq
    unfold contextForkViewCollision contextForkView
    rw [PFunctor.FreeM.Cursor.map_locateAndForkAt]
    apply congrArg (fun k => paths >>= k)
    funext path
    simp only [viewCollision]
    rcases PFunctor.FreeM.Cursor.locateAt? (P := spec.toPFunctor) i main path s with _ | located
    · rfl
    · simp [PFunctor.FreeM.Cursor.Located.fork]
  have hinner :
    ∀ path : PFunctor.FreeM.Path main,
      probOutput (viewCollision path) (some s : Option (Fin (qb i + 1))) ≤
        probOutput (answerCollision path) (some s : Option (Fin (qb i + 1))) :=
    by
    intro path
    simp only [viewCollision, answerCollision]
    rcases hlocated : PFunctor.FreeM.Cursor.locateAt? (P := spec.toPFunctor) i main path s with _ |
      located
    · simp
    · let continuation : spec.Range i → OracleComp spec (Option (Fin (qb i + 1))) :=
        fun secondAnswer =>
        (fun secondSuffix =>
            collideForkView main qb i cf s
              (some
                { occurrence := located.occurrence
                  first := located.completion
                  second := ⟨secondAnswer, secondSuffix⟩ })) <$>
          PFunctor.FreeM.withPath (located.occurrence.resume secondAnswer)
      change
        probOutput (OracleComp.lift (spec.query i) >>= continuation)
            (some s : Option (Fin (qb i + 1))) ≤
          _
      rw [probOutput_bind_eq_tsum, probOutput_bind_eq_tsum]
      refine ENNReal.tsum_le_tsum fun secondAnswer => ?_
      let firstAnswer : spec.Range i := located.completion.answer
      by_cases heq : firstAnswer = secondAnswer
      · by_cases hcf : cf (PFunctor.FreeM.output main path) = some s
        · simp [continuation, firstAnswer, heq, hcf, collideForkView, probOutput_query]
        · have hfirst : cf (PFunctor.FreeM.output main located.completion.path) ≠ some s := by
            rw [located.path_eq]; exact hcf
          simp [continuation, firstAnswer, heq, hcf, hfirst, collideForkView,
            PFunctor.FreeM.Cursor.ForkView.firstPath, probOutput_query]
      ·
        simp [continuation, firstAnswer, heq, collideForkView,
          PFunctor.FreeM.Cursor.ForkView.firstAnswer, PFunctor.FreeM.Cursor.ForkView.secondAnswer,
          probOutput_query]
  calc
    probOutput (contextForkViewCollision main qb i cf s) (some s : Option (Fin (qb i + 1))) =
        ∑' path,
          probOutput paths path *
            probOutput (viewCollision path) (some s : Option (Fin (qb i + 1))) :=
      by rw [hsource, probOutput_bind_eq_tsum]
    _ ≤
        ∑' path,
          probOutput paths path *
            probOutput (answerCollision path) (some s : Option (Fin (qb i + 1))) :=
      (ENNReal.tsum_le_tsum fun path => mul_le_mul' le_rfl (hinner path))
    _ = probOutput (contextForkCollision main qb i cf s) (some s : Option (Fin (qb i + 1))) := by
      exact (probOutput_bind_eq_tsum paths answerCollision (some s)).symm


-- @@ L707-717 expanded
/-- The successful equal-answer branch of the intrinsic context experiment is
bounded by one uniform-answer collision against the original success event. -/
theorem probOutput_contextForkViewCollision_le_main_div [IsUniformSpec spec]
    (main : OracleComp spec α) (qb : ι → ℕ) (i : ι) (cf : α → Option (Fin (qb i + 1)))
    (s : Fin (qb i + 1)) :
    probOutput (contextForkViewCollision main qb i cf s) (some s : Option (Fin (qb i + 1))) ≤
      probOutput (cf <$> main) (some s : Option (Fin (qb i + 1))) / Fintype.card (spec.Range i) :=
  (probOutput_contextForkViewCollision_le_collision main qb i cf s).trans
    (probOutput_contextForkCollision_le_main_div main qb i cf s)


-- @@ L719-734 expanded
/-- Fixed-occurrence forking succeeds with the usual square-minus-collision
lower bound, stated directly for the guarded PolyFun context experiment. -/
theorem sq_sub_div_le_probEvent_guardedContextFork [IsUniformSpec spec] (main : OracleComp spec α)
    (qb : ι → ℕ) (i : ι) (cf : α → Option (Fin (qb i + 1))) (hreach : PathCfReachable main qb i cf)
    (s : Fin (qb i + 1)) :
    let h : ℝ≥0∞ := ↑(Fintype.card (spec.Range i))
    probOutput (cf <$> main) s ^ 2 - probOutput (cf <$> main) s / h ≤
      probEvent (guardedContextFork main qb i cf s) fun result : Option (α × α) => result.isSome :=
  by
  set h : ℝ≥0∞ := ↑(Fintype.card (spec.Range i))
  refine
    tsub_le_iff_right.2 <|
      (sq_probOutput_main_le_contextForkPair main qb i cf hreach s).trans <|
        (probOutput_contextForkPair_le_guarded_add_collision main qb i cf s).trans <|
          add_le_add_right
            (by simpa [h] using probOutput_contextForkViewCollision_le_main_div main qb i cf s) _


-- @@ L736-748 expanded
/-- Finite aggregation of the fixed-occurrence bounds. This is the
probability-facing interface consumed by the dynamic context fork. -/
theorem sum_sq_sub_div_le_probEvent_guardedContextFork [IsUniformSpec spec]
    (main : OracleComp spec α) (qb : ι → ℕ) (i : ι) (cf : α → Option (Fin (qb i + 1)))
    (hreach : PathCfReachable main qb i cf) :
    let h : ℝ≥0∞ := ↑(Fintype.card (spec.Range i))
    ∑ s : Fin (qb i + 1), (probOutput (cf <$> main) s ^ 2 - probOutput (cf <$> main) s / h) ≤
      ∑ s : Fin (qb i + 1),
        probEvent (guardedContextFork main qb i cf s) fun result : Option (α × α) =>
          result.isSome :=
  Finset.sum_le_sum fun s _ => sq_sub_div_le_probEvent_guardedContextFork main qb i cf hreach s


-- @@ L750-815 expanded
/-- A fixed guarded fork is the corresponding component of the dynamic
semantic fork. -/
theorem probEvent_guardedContextFork_eq_contextFork_component [IsProbabilitySpec spec]
    (main : OracleComp spec α) (qb : ι → ℕ) (i : ι) (cf : α → Option (Fin (qb i + 1)))
    (s : Fin (qb i + 1)) :
    (probEvent (guardedContextFork main qb i cf s) fun result : Option (α × α) => result.isSome) =
      probEvent (contextFork main qb i cf) fun result : Option (α × α) =>
        result.map (cf ∘ Prod.fst) = some (some s) :=
  by
  let : spec.toPFunctor.DecidableEq := (inferInstance : spec.DecidableEq).toDecidableEq
  rw [contextFork_eq_contextForkByClassify]
  unfold guardedContextFork contextForkByClassify
  rw [PFunctor.FreeM.Cursor.filterMapLocateAndForkAt_eq_bind_complete,
    PFunctor.FreeM.Cursor.filterMapLocateAndForkBy_eq_bind_complete, probEvent_ofFreeM_bind_eq_tsum,
    probEvent_ofFreeM_bind_eq_tsum]
  refine tsum_congr fun path => ?_
  congr 1
  rcases hcf : cf (PFunctor.FreeM.output main path) with _ | t
  · rcases hloc : PFunctor.FreeM.Cursor.locateAt? (P := spec.toPFunctor) i main path s with _ |
      located
    · rw [probEvent_ofFreeM_pure, probEvent_ofFreeM_pure]
      simp
    · have hfirst : cf (PFunctor.FreeM.output main located.completion.path) = none := by
        simpa only [located.path_eq] using hcf
      rw [probEvent_classifyForkView_isSome_eq_zero_of_first_ne main qb i cf s located
          (by simp [hfirst]),
        probEvent_ofFreeM_pure]
      simp
  · by_cases hts : t = s
    · subst t
      rcases hloc : PFunctor.FreeM.Cursor.locateAt? (P := spec.toPFunctor) i main path s with _ |
        located
      · simp only [hloc]
        rw [probEvent_ofFreeM_pure, probEvent_ofFreeM_pure]
        simp
      · simp only [hloc]
        rw [probEvent_ofFreeM_map, probEvent_ofFreeM_map]
        congr 1
        funext second
        exact
          propext
            (classifyForkView_component_iff main qb i cf s
                { occurrence := located.occurrence
                  first := located.completion
                  second := second }).symm
    · trans (0 : ℝ≥0∞)
      · rcases hlocFixed : PFunctor.FreeM.Cursor.locateAt? (P := spec.toPFunctor) i main path s with
          _ | locatedFixed
        · rw [probEvent_ofFreeM_pure]
          simp
        · dsimp only
          have hfirstNe : cf (PFunctor.FreeM.output main locatedFixed.completion.path) ≠ some s :=
            by
            simp only [locatedFixed.path_eq, hcf]
            grind
          rw [probEvent_classifyForkView_isSome_eq_zero_of_first_ne main qb i cf s locatedFixed
              hfirstNe]
      · dsimp only
        rcases hlocDynamic :
          PFunctor.FreeM.Cursor.locateAt? (P := spec.toPFunctor) i main path t with _ |
          locatedDynamic
        · rw [probEvent_ofFreeM_pure]
          simp
        ·
          rw [probEvent_classifyForkView_component_eq_zero_of_ne main qb i cf t s locatedDynamic
              hts]


-- @@ L817-832 expanded
/-- The summed success probabilities of the per-selector guarded context forks
are bounded by the success probability of the context fork. -/
theorem sum_probEvent_guardedContextFork_le_isSome [IsProbabilitySpec spec]
    (main : OracleComp spec α) (qb : ι → ℕ) (i : ι) (cf : α → Option (Fin (qb i + 1))) :
    (∑ s : Fin (qb i + 1),
        probEvent (guardedContextFork main qb i cf s) fun result : Option (α × α) =>
          result.isSome) ≤
      probEvent (contextFork main qb i cf) fun result : Option (α × α) => result.isSome :=
  by
  calc
    _ =
        ∑ s : Fin (qb i + 1),
          probEvent (contextFork main qb i cf) fun result : Option (α × α) =>
            result.map (cf ∘ Prod.fst) = some (some s) :=
      Finset.sum_congr rfl fun s _ =>
        probEvent_guardedContextFork_eq_contextFork_component main qb i cf s
    _ ≤ _ :=
      sum_probEvent_option_map_eq_some_le_isSome (mx := contextFork main qb i cf) (cf ∘ Prod.fst)


-- @@ L834-859 expanded
/-- Direct probability bound for the canonical semantic context fork. The
program manipulation is discharged by PolyFun; this theorem contains only
the finite selector aggregation and the usual Cauchy--Schwarz estimate. -/
theorem le_probEvent_isSome_contextFork [IsUniformSpec spec] (main : OracleComp spec α) (qb : ι → ℕ)
    (i : ι) (cf : α → Option (Fin (qb i + 1))) (hreach : PathCfReachable main qb i cf) :
    (let acc : ℝ≥0∞ := ∑ s, probOutput (cf <$> main) (some s)
      let h : ℝ≥0∞ := Fintype.card (spec.Range i)
      let q := qb i + 1
      acc * (acc / q - h⁻¹)) ≤
      probEvent (contextFork main qb i cf) fun r => r.isSome :=
  by
  simp only
  set ps : Fin (qb i + 1) → ℝ≥0∞ := fun s => probOutput (cf <$> main) (some s : Option _)
  set h : ℝ≥0∞ := ↑(Fintype.card (spec.Range i))
  have hsum : (∑ s, ps s) ≠ ⊤ :=
    ne_top_of_le_ne_top one_ne_top (sum_probOutput_some_le_one (mx := cf <$> main))
  calc
    (∑ s, ps s) * ((∑ s, ps s) / ↑(qb i + 1) - h⁻¹) ≤ ∑ s, (ps s ^ 2 - ps s / h) := by
      simpa [Finset.card_univ, Fintype.card_fin] using
        ENNReal.mul_tsub_inv_le_sum_sq_sub_div univ ps h hsum
    _ ≤
        ∑ s,
          probEvent (guardedContextFork main qb i cf s) fun result : Option (α × α) =>
            result.isSome :=
      by simpa only [ps, h] using sum_sq_sub_div_le_probEvent_guardedContextFork main qb i cf hreach
    _ ≤ _ := sum_probEvent_guardedContextFork_le_isSome main qb i cf


-- @@ L861-861 verbatim
end quantitative


-- @@ L863-863 verbatim
end OracleComp
