/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Realizability.Instances
public import PolyFun.Realizability.Quantitative.BoundedClosure


-- @@ L12-22 verbatim
/-!
# Bounded quantitative-closure checks

Concrete checks for ranked termination, input precomposition, result postcomposition, and bounded
sequential composition. A zero-cost fixture exercises structural trace transport and theorem
elaboration. A separate constant-positive fixture checks that two typed queries cross a handoff,
retain answer-dependent state, and compose through an exact universal cost certificate. Neither
synthetic backend is evidence that an arbitrary function is efficiently realizable;
application-level results must provide executable code and inequalities over that code's actual
cost.
-/


-- @@ L24-24 verbatim
public section


-- @@ L26-26 verbatim
namespace PFunctor.QuantitativeBoundedClosureTest


-- @@ L28-28 verbatim
open DynSystem.DynComputation


-- @@ L30-36 verbatim
/-- Synthetic structural-smoke backend, explicitly excluded from complexity evidence. -/
@[expose]
def zeroBackend : QuantitativeStepClass.{0, 0, 0} StepClass.unconstrained.{0, 0} where
  Realizer _ _ _ := PUnit
  size _ _ := 0
  cost _ _ := 0
  admissible _ := True.intro


-- @@ L38-42 verbatim
instance : zeroBackend.HasCategory where
  identity _ := PUnit.unit
  compose _ _ := PUnit.unit
  composeOverhead _ _ _ := 0
  cost_compose_le _ _ _ := le_rfl


-- @@ L44-47 verbatim
instance : zeroBackend.HasProd where
  fst _ _ := PUnit.unit
  snd _ _ := PUnit.unit
  pair _ _ := PUnit.unit


-- @@ L49-52 verbatim
instance : zeroBackend.HasSum where
  inl _ _ := PUnit.unit
  inr _ _ := PUnit.unit
  elim _ _ := PUnit.unit


-- @@ L54-57 verbatim
instance : zeroBackend.HasOption where
  map _ := PUnit.unit
  none _ _ := PUnit.unit
  bindContext _ := PUnit.unit


-- @@ L59-60 verbatim
instance : zeroBackend.IsDistributive where
  distribute _ _ _ := PUnit.unit


-- @@ L62-64 verbatim
/-- Interface with one position and no possible answer. -/
abbrev emptyResponse : PFunctor.{0, 0} :=
  PFunctor.mk PUnit.{1} fun _ ↦ PEmpty.{1}


-- @@ L66-69 verbatim
/-- Unconstrained unit boundary for the returning fixture. -/
abbrev unitBoundary : Boundary StepClass.unconstrained.{0, 0} emptyResponse
    PUnit.{1} PUnit.{1} :=
  Boundary.unconstrained emptyResponse PUnit.{1} PUnit.{1}


-- @@ L71-78 verbatim
/-- An explicitly costed realization that returns its unit input immediately. -/
@[expose]
def returnRealization : QuantitativeRealization zeroBackend unitBoundary where
  machine := ofFn (p := emptyResponse) id
  state := PUnit.unit
  initCode := PUnit.unit
  headCode := PUnit.unit
  updateCode := PUnit.unit


-- @@ L80-87 verbatim
/-- Rank zero is sufficient because every state of the fixture has already returned. -/
def returnRanked : RankedRunCertificate returnRealization (fun _ _ ↦ True) where
  rank _ := 0
  returns_of_rank_zero state _ := ⟨state, rfl⟩
  decreases _ direction := nomatch direction
  progress hview := by
    rw [show returnRealization.machine.view _ = Sum.inl PUnit.unit by rfl] at hview
    exact nomatch hview


-- @@ L89-90 verbatim
/-- The all-zero exact bound for the cost-free returning fixture. -/
def zeroBound : PUnit.{1} → ExecutionCost := fun _ ↦ 0


-- @@ L92-106 verbatim
/-- The ranked certificate and exact pathwise accounting close the full restricted run bound. -/
theorem returnRunsWithin :
    returnRealization.RunsWithinUnder (fun _ _ ↦ True) zeroBound := by
  apply returnRanked.runsWithinUnder zeroBound
  · intro input finish trace htrace
    have hview : returnRealization.machine.view
        (returnRealization.machine.init input) = Sum.inl input := by
      rfl
    obtain ⟨hfinish, hcost⟩ := trace.finish_eq_and_cost_eq_zero_of_view_return hview
    change ExecutionCost.ofWork 0 + trace.cost + ExecutionCost.ofWork 0 +
      ExecutionCost.observe 0 0 ≤ 0
    rw [hcost]
    rfl
  · intro input
    simp [returnRanked, zeroBound]


-- @@ L108-110 verbatim
/-- Executable identity code with indices fixed for input precomposition. -/
def unitInputCode : zeroBackend.Realizer unitBoundary.input unitBoundary.input id :=
  PUnit.unit


-- @@ L112-120 verbatim
/-- Precomposition is immediately usable and adds only the backend's certified zero overhead. -/
example :
    (returnRealization.precomp unitInputCode).RunsWithinUnder (fun _ _ ↦ True)
      (fun input ↦
        ExecutionCost.ofWork
            (zeroBackend.cost unitInputCode input +
              zeroBackend.composeOverhead unitInputCode returnRealization.initCode input) +
          zeroBound input) :=
  returnRunsWithin.precomp unitInputCode


-- @@ L122-124 verbatim
/-- Executable identity code with indices fixed for result postcomposition. -/
def unitResultCode : zeroBackend.Realizer unitBoundary.out unitBoundary.out id :=
  PUnit.unit


-- @@ L126-147 verbatim
/-- Zero-overhead result mapping certificate for the cost-free fixture. -/
def returnMapCost : MapResultCostCertificate returnRealization unitResultCode
    (fun _ _ ↦ True) where
  overhead _ := 0
  cost_le := by
    intro input finish trace htrace
    have hview : (returnRealization.mapResult unitResultCode).machine.view
        ((returnRealization.mapResult unitResultCode).machine.init input) = Sum.inl input := by
      rfl
    obtain ⟨hfinish, hcost⟩ := trace.finish_eq_and_cost_eq_zero_of_view_return hview
    have hsourceView : returnRealization.machine.view
        (returnRealization.machine.init input) = Sum.inl input := by
      rfl
    obtain ⟨_, hsourceCost⟩ :=
      QuantitativeRealization.ExecutionTrace.finish_eq_and_cost_eq_zero_of_view_return
        (trace.ofMapResult returnRealization unitResultCode) hsourceView
    change ExecutionCost.ofWork 0 + trace.cost + ExecutionCost.ofWork 0 +
        ExecutionCost.observe 0 0 ≤
      ExecutionCost.ofWork 0 + (trace.ofMapResult returnRealization unitResultCode).cost +
          ExecutionCost.ofWork 0 + ExecutionCost.observe 0 0 + 0
    rw [hcost, hsourceCost]
    rfl


-- @@ L149-153 verbatim
/-- Result postcomposition reuses source termination/progress and the explicit cost certificate. -/
example :
    (returnRealization.mapResult unitResultCode).RunsWithinUnder (fun _ _ ↦ True)
      (fun input ↦ zeroBound input + returnMapCost.overhead input) :=
  returnRunsWithin.mapResult unitResultCode returnMapCost


-- @@ L155-155 verbatim
/-! ## Bounded sequential composition -/


-- @@ L157-163 verbatim
/-- The reachable second phase of two immediate returns needs no resource envelope. -/
def returnHandoffBound :
    SeqCompHandoffBound returnRealization (fun _ _ ↦ True) zeroBound where
  bound := zeroBound
  returned_le := by
    intro input finish trace htrace value view_eq
    exact le_rfl


-- @@ L165-184 verbatim
/-- Structural assembly has exactly zero cost in the synthetic backend. -/
def returnSeqCompCost :
    SeqCompCostCertificate returnRealization returnRealization (fun _ _ ↦ True) where
  overhead _ := 0
  cost_le := by
    intro input finish trace htrace
    have hview : (returnRealization.seqComp returnRealization).machine.view
        ((returnRealization.seqComp returnRealization).machine.init input) =
        Sum.inl input := by
      rfl
    obtain ⟨hfinish, hcost⟩ := trace.finish_eq_and_cost_eq_zero_of_view_return hview
    subst finish
    change ExecutionCost.ofWork 0 + trace.cost + ExecutionCost.ofWork 0 +
        ExecutionCost.observe 0 0 ≤
      (trace.seqCompSource returnRealization returnRealization).cost input + 0
    rw [hcost]
    have hzero : ExecutionCost.ofWork 0 + 0 + ExecutionCost.ofWork 0 +
        ExecutionCost.observe 0 0 = 0 := rfl
    rw [hzero, add_zero]
    exact ExecutionCost.zero_le _


-- @@ L186-193 verbatim
/-- The zero-cost fixture exercises the real bounded-composition theorem, including reconstructed
resolution and syntactic progress. -/
theorem returnSeqCompRunsWithin :
    (returnRealization.seqComp returnRealization).RunsWithinUnder (fun _ _ ↦ True)
      (fun input ↦
        zeroBound input + returnHandoffBound.bound input + returnSeqCompCost.overhead input) :=
  QuantitativeRealization.RunsWithinUnder.seqComp returnRunsWithin returnRunsWithin
    returnHandoffBound returnSeqCompCost


-- @@ L195-204 verbatim
/-- The empty composite prefix is classified at the zero-query handoff, so the second
initialization and readout cannot disappear from the source-cost comparison. -/
example (input : PUnit.{1}) :
    match (QuantitativeRealization.ExecutionTrace.nil
      (R := returnRealization.seqComp returnRealization)
      (Sum.inl (returnRealization.machine.init input))).seqCompSource
        returnRealization returnRealization with
    | .handoff _ _ => True
    | .left _ _ => False := by
  trivial


-- @@ L206-206 verbatim
/-! ## Query-crossing sequential composition -/


-- @@ L208-209 verbatim
/-- A typed Boolean-answer interface used to exercise both phases of composition. -/
abbrev boolResponse : PFunctor.{0, 0} := y^ Bool


-- @@ L211-219 verbatim
/-- A deliberately simple backend whose every executable map costs one unit of work and whose
every represented value has encoded size one. Unlike `zeroBackend`, this exposes every resource
component touched by the query-crossing canary. -/
@[expose]
def unitCostBackend : QuantitativeStepClass.{0, 0, 0} StepClass.unconstrained.{0, 0} where
  Realizer _ _ _ := PUnit
  size _ _ := 1
  cost _ _ := 1
  admissible _ := True.intro


-- @@ L221-227 verbatim
instance : unitCostBackend.HasCategory where
  identity _ := PUnit.unit
  compose _ _ := PUnit.unit
  composeOverhead _ _ _ := 0
  cost_compose_le _ _ _ := by
    change 1 ≤ 1 + 1 + 0
    omega


-- @@ L229-232 verbatim
instance : unitCostBackend.HasProd where
  fst _ _ := PUnit.unit
  snd _ _ := PUnit.unit
  pair _ _ := PUnit.unit


-- @@ L234-237 verbatim
instance : unitCostBackend.HasSum where
  inl _ _ := PUnit.unit
  inr _ _ := PUnit.unit
  elim _ _ := PUnit.unit


-- @@ L239-242 verbatim
instance : unitCostBackend.HasOption where
  map _ := PUnit.unit
  none _ _ := PUnit.unit
  bindContext _ := PUnit.unit


-- @@ L244-245 verbatim
instance : unitCostBackend.IsDistributive where
  distribute _ _ _ := PUnit.unit


-- @@ L247-258 verbatim
/-- The first phase asks one Boolean query and returns the typed answer unchanged. -/
@[expose]
def firstQueryMachine : DynSystem.DynComputation boolResponse PUnit Bool where
  State := Option Bool
  toDynSystem :=
    (fun
      | none => Sum.inl PUnit.unit
      | some answer => Sum.inr answer) ⇆
    fun
      | none => fun answer => some answer
      | some _ => PEmpty.elim
  init := fun _ ↦ none


-- @@ L260-272 verbatim
/-- The second phase asks another Boolean query and returns a value depending on both the first
answer and its own typed answer. -/
@[expose]
def secondQueryMachine : DynSystem.DynComputation boolResponse Bool Nat where
  State := Bool × Option Bool
  toDynSystem :=
    (fun state : Bool × Option Bool => match state.2 with
      | none => Sum.inl PUnit.unit
      | some answer => Sum.inr (if state.1 = answer then (9 : Nat) else (4 : Nat))) ⇆
    fun state : Bool × Option Bool => match state.2 with
      | none => fun answer => (state.1, some answer)
      | some _ => PEmpty.elim
  init := fun first ↦ (first, none)


-- @@ L274-276 verbatim
/-- Pinned unconstrained boundary for the first query phase. -/
abbrev firstQueryBoundary : Boundary StepClass.unconstrained.{0, 0} boolResponse PUnit Bool :=
  Boundary.unconstrained boolResponse PUnit Bool


-- @@ L278-279 verbatim
/-- Pinned output representation for the natural-number result of the second phase. -/
abbrev natOutputRep : StepClass.unconstrained.{0, 0}.Str Nat := PUnit.unit


-- @@ L281-288 verbatim
/-- Positive-cost realization of the first typed query. -/
@[expose]
def firstQueryRealization : QuantitativeRealization unitCostBackend firstQueryBoundary where
  machine := firstQueryMachine
  state := PUnit.unit
  initCode := PUnit.unit
  headCode := PUnit.unit
  updateCode := PUnit.unit


-- @@ L290-298 verbatim
/-- Positive-cost realization of the answer-dependent second typed query. -/
@[expose]
def secondQueryRealization :
    QuantitativeRealization unitCostBackend (firstQueryBoundary.mid natOutputRep) where
  machine := secondQueryMachine
  state := PUnit.unit
  initCode := PUnit.unit
  headCode := PUnit.unit
  updateCode := PUnit.unit


-- @@ L300-302 verbatim
/-- Exact envelope for either one-query phase under `unitCostBackend`. -/
@[expose]
def oneQueryBound : ExecutionCost := ⟨4, 1, 2, 1, 1⟩


-- @@ L304-306 verbatim
/-- Exact envelope for the two-query composite under `unitCostBackend`. -/
@[expose]
def twoQueryBound : ExecutionCost := ⟨6, 2, 4, 1, 1⟩


-- @@ L308-313 verbatim
/-- A concrete first-phase trace carrying an arbitrary typed Boolean answer. -/
def firstQueryTrace (answer : Bool) :
    firstQueryRealization.ExecutionTrace
      (firstQueryRealization.machine.init PUnit.unit) (some answer) :=
  .query (position := PUnit.unit) (next := fun answer ↦ some answer)
    rfl answer (.nil (R := firstQueryRealization) (some answer))


-- @@ L315-320 verbatim
/-- A concrete second-phase trace whose initial state retains the first typed answer. -/
def secondQueryTrace (first answer : Bool) :
    secondQueryRealization.ExecutionTrace
      (secondQueryRealization.machine.init first) (first, some answer) :=
  .query (position := PUnit.unit) (next := fun answer ↦ (first, some answer))
    rfl answer (.nil (R := secondQueryRealization) (first, some answer))


-- @@ L322-332 verbatim
/-- A two-query composite trace. The first answer changes the second machine's initial state; the
second query then moves the composite into the right state summand. -/
def queryCrossingTrace (first answer : Bool) :
    (firstQueryRealization.seqComp secondQueryRealization).ExecutionTrace
      ((firstQueryRealization.seqComp secondQueryRealization).machine.init PUnit.unit)
      (Sum.inr (first, some answer)) :=
  .query (position := PUnit.unit) (next := fun first ↦ Sum.inl (some first)) rfl first
    (.query (position := PUnit.unit)
      (next := fun answer ↦ Sum.inr (first, some answer)) rfl answer
      (.nil (R := firstQueryRealization.seqComp secondQueryRealization)
        (Sum.inr (first, some answer))))


-- @@ L334-335 verbatim
/-- Both query transitions are visible in the fully syntactic composite trace. -/
example : (queryCrossingTrace true false).length = 2 := rfl


-- @@ L337-340 verbatim
/-- The first typed answer is genuinely handed to phase two and affects its returned result. -/
example :
    (firstQueryRealization.seqComp secondQueryRealization).machine.view
      (Sum.inr (true, some false)) = Sum.inl 4 := rfl


-- @@ L342-346 verbatim
/-- The full query-crossing trace realizes every nonzero resource component selected by the
test backend. -/
example :
    (firstQueryRealization.seqComp secondQueryRealization).executionCost PUnit.unit
      (queryCrossingTrace true false) = twoQueryBound := rfl


-- @@ L348-350 verbatim
/-- Every well-typed Boolean response is admitted by the querying fixtures. -/
@[expose]
def allowsBool : ∀ position, boolResponse.B position → Prop := fun _ _ ↦ True


-- @@ L352-363 verbatim
/-- Transition work is exactly two units per typed query in `unitCostBackend`. -/
theorem traceWork_unitCost {p : PFunctor.{0, 0}} [DecidableEq p.A]
    {input output : Type} {bd : Boundary StepClass.unconstrained.{0, 0} p input output}
    {R : QuantitativeRealization unitCostBackend bd} {start finish : R.machine.State}
    (trace : R.ExecutionTrace start finish) : trace.cost.work = 2 * trace.length := by
  induction trace with
  | nil => rfl
  | query view_eq direction tail ih =>
      change 2 + tail.cost.work = 2 * (tail.length + 1)
      calc
        2 + tail.cost.work = 2 + 2 * tail.length := congrArg (fun work ↦ 2 + work) ih
        _ = 2 * (tail.length + 1) := by omega


-- @@ L365-377 verbatim
/-- Encoded boundary traffic is exactly two units per typed query in `unitCostBackend`. -/
theorem traceTraffic_unitCost {p : PFunctor.{0, 0}} [DecidableEq p.A]
    {input output : Type} {bd : Boundary StepClass.unconstrained.{0, 0} p input output}
    {R : QuantitativeRealization unitCostBackend bd} {start finish : R.machine.State}
    (trace : R.ExecutionTrace start finish) : trace.cost.traffic = 2 * trace.length := by
  induction trace with
  | nil => rfl
  | query view_eq direction tail ih =>
      change 2 + tail.cost.traffic = 2 * (tail.length + 1)
      calc
        2 + tail.cost.traffic = 2 + 2 * tail.length :=
          congrArg (fun traffic ↦ 2 + traffic) ih
        _ = 2 * (tail.length + 1) := by omega


-- @@ L379-388 verbatim
/-- Every transition observation has the backend's selected unit state-size envelope. -/
theorem tracePeakState_unitCost {p : PFunctor.{0, 0}} [DecidableEq p.A]
    {input output : Type} {bd : Boundary StepClass.unconstrained.{0, 0} p input output}
    {R : QuantitativeRealization unitCostBackend bd} {start finish : R.machine.State}
    (trace : R.ExecutionTrace start finish) : trace.cost.peakStateSize ≤ 1 := by
  induction trace with
  | nil => exact Nat.zero_le 1
  | query view_eq direction tail ih =>
      change max 1 tail.cost.peakStateSize ≤ 1
      exact Nat.max_le.mpr ⟨le_rfl, ih⟩


-- @@ L390-399 verbatim
/-- Every transition readout has the backend's selected unit size envelope. -/
theorem tracePeakHead_unitCost {p : PFunctor.{0, 0}} [DecidableEq p.A]
    {input output : Type} {bd : Boundary StepClass.unconstrained.{0, 0} p input output}
    {R : QuantitativeRealization unitCostBackend bd} {start finish : R.machine.State}
    (trace : R.ExecutionTrace start finish) : trace.cost.peakHeadSize ≤ 1 := by
  induction trace with
  | nil => exact Nat.zero_le 1
  | query view_eq direction tail ih =>
      change max 1 tail.cost.peakHeadSize ≤ 1
      exact Nat.max_le.mpr ⟨le_rfl, ih⟩


-- @@ L401-403 verbatim
/-- Exact resource envelope determined by a syntactic query count in `unitCostBackend`. -/
abbrev unitCostEnvelope (queries : Nat) : ExecutionCost :=
  ⟨2 * queries + 2, queries, 2 * queries, 1, 1⟩


-- @@ L405-427 verbatim
/-- Exact execution cost as a function of syntactic query length in `unitCostBackend`. -/
theorem executionCost_unitCost {p : PFunctor.{0, 0}} [DecidableEq p.A]
    {input output : Type} {bd : Boundary StepClass.unconstrained.{0, 0} p input output}
    {R : QuantitativeRealization unitCostBackend bd} (inputValue : input)
    {finish : R.machine.State}
    (trace : R.ExecutionTrace (R.machine.init inputValue) finish) :
    R.executionCost inputValue trace = unitCostEnvelope trace.length := by
  apply ExecutionCost.ext
  · change 1 + trace.cost.work + 1 = 2 * trace.length + 2
    calc
      1 + trace.cost.work + 1 = 1 + 2 * trace.length + 1 :=
        congrArg (fun work ↦ 1 + work + 1) (traceWork_unitCost trace)
      _ = 2 * trace.length + 2 := by omega
  · exact R.queries_executionCost inputValue trace
  · simp only [QuantitativeRealization.executionCost, ExecutionCost.traffic_add,
      ExecutionCost.traffic_ofWork, ExecutionCost.traffic_observe, Nat.zero_add, Nat.add_zero]
    exact traceTraffic_unitCost trace
  · simp only [QuantitativeRealization.executionCost, ExecutionCost.peakStateSize_add,
      ExecutionCost.peakStateSize_observe, ExecutionCost.ofWork, Nat.zero_max, Nat.max_zero]
    exact Nat.max_eq_right (tracePeakState_unitCost trace)
  · simp only [QuantitativeRealization.executionCost, ExecutionCost.peakHeadSize_add,
      ExecutionCost.peakHeadSize_observe, ExecutionCost.ofWork, Nat.zero_max, Nat.max_zero]
    exact Nat.max_eq_right (tracePeakHead_unitCost trace)


-- @@ L429-434 verbatim
/-- The exact unit-cost envelope is monotone in its syntactic query count. -/
theorem unitCostEnvelope_mono {left right : Nat} (h : left ≤ right) :
    unitCostEnvelope left ≤ unitCostEnvelope right := by
  change 2 * left + 2 ≤ 2 * right + 2 ∧ left ≤ right ∧
    2 * left ≤ 2 * right ∧ 1 ≤ 1 ∧ 1 ≤ 1
  exact ⟨by omega, h, Nat.mul_le_mul_left 2 h, le_rfl, le_rfl⟩


-- @@ L436-443 verbatim
/-- Splitting a run into two source phases can only increase the unit-cost envelope: each phase
has its own initialization and final readout. -/
theorem unitCostEnvelope_add (left right : Nat) :
    unitCostEnvelope (left + right) ≤ unitCostEnvelope left + unitCostEnvelope right := by
  change 2 * (left + right) + 2 ≤ (2 * left + 2) + (2 * right + 2) ∧
    left + right ≤ left + right ∧ 2 * (left + right) ≤ 2 * left + 2 * right ∧
      1 ≤ max 1 1 ∧ 1 ≤ max 1 1
  exact ⟨by omega, le_rfl, by omega, Nat.le_max_left 1 1, Nat.le_max_left 1 1⟩


-- @@ L445-455 verbatim
/-- A syntactic trace-length bound induces the corresponding positive resource envelope for every
machine represented in the constant-positive test backend. -/
theorem executionCost_le_unitCost {p : PFunctor.{0, 0}} [DecidableEq p.A]
    {input output : Type} {bd : Boundary StepClass.unconstrained.{0, 0} p input output}
    {R : QuantitativeRealization unitCostBackend bd} (inputValue : input)
    {finish : R.machine.State}
    (trace : R.ExecutionTrace (R.machine.init inputValue) finish) (queries : Nat)
    (hlength : trace.length ≤ queries) :
    R.executionCost inputValue trace ≤ unitCostEnvelope queries := by
  rw [executionCost_unitCost]
  exact unitCostEnvelope_mono hlength


-- @@ L457-485 verbatim
/-- The first phase has the exact one-query resource envelope. -/
theorem firstQueryRunsWithin :
    firstQueryRealization.RunsWithinUnder allowsBool (fun _ ↦ oneQueryBound) := by
  refine ⟨?_, ?_, ?_⟩
  · intro input finish trace htrace
    cases input
    cases trace with
    | nil =>
        exact executionCost_le_unitCost PUnit.unit (.nil _) 1 (by change 0 ≤ 1; omega)
    | query view_eq direction tail =>
        simp only [purePower_A] at view_eq
        cases view_eq
        have hreturn : firstQueryRealization.machine.view (some direction) =
            Sum.inl direction := rfl
        obtain ⟨rfl, hcost⟩ := tail.finish_eq_and_cost_eq_zero_of_view_return hreturn
        have hlength : tail.length = 0 := by
          rw [← tail.queries_cost, hcost]
          rfl
        apply executionCost_le_unitCost PUnit.unit _ 1
        change tail.length + 1 ≤ 1
        omega
  · intro input
    cases input
    apply (firstQueryMachine.resolvesInUnder_query_succ_iff allowsBool 0 none PUnit.unit
      (fun answer ↦ some answer) rfl).mpr
    intro direction hdirection
    exact firstQueryMachine.resolvesInUnder_return allowsBool 0 (some direction) direction rfl
  · intro input state trace htrace position next view_eq
    exact ⟨false, trivial⟩


-- @@ L487-516 verbatim
/-- The second, answer-dependent phase has the same exact one-query resource envelope. -/
theorem secondQueryRunsWithin :
    secondQueryRealization.RunsWithinUnder allowsBool (fun _ ↦ oneQueryBound) := by
  refine ⟨?_, ?_, ?_⟩
  · intro input finish trace htrace
    cases trace with
    | nil =>
        exact executionCost_le_unitCost input (.nil _) 1 (by change 0 ≤ 1; omega)
    | query view_eq direction tail =>
        simp only [purePower_A] at view_eq
        cases view_eq
        change Bool at direction
        have hreturn : secondQueryRealization.machine.view (input, some direction) =
            Sum.inl (if input = direction then 9 else 4) := rfl
        obtain ⟨rfl, hcost⟩ := tail.finish_eq_and_cost_eq_zero_of_view_return hreturn
        have hlength : tail.length = 0 := by
          rw [← tail.queries_cost, hcost]
          rfl
        apply executionCost_le_unitCost input _ 1
        change tail.length + 1 ≤ 1
        omega
  · intro input
    apply (secondQueryMachine.resolvesInUnder_query_succ_iff allowsBool 0 (input, none)
      PUnit.unit (fun answer ↦ (input, some answer)) rfl).mpr
    intro direction hdirection
    change Bool at direction
    exact secondQueryMachine.resolvesInUnder_return allowsBool 0 (input, some direction)
      (if input = direction then 9 else 4) rfl
  · intro input state trace htrace position next view_eq
    exact ⟨false, trivial⟩


-- @@ L518-525 verbatim
/-- Every reached first-phase answer fits the uniform one-query envelope of phase two. -/
@[expose]
def queryHandoffBound :
    SeqCompHandoffBound firstQueryRealization allowsBool (fun _ ↦ oneQueryBound) where
  bound _ := oneQueryBound
  returned_le := by
    intro input finish trace htrace value view_eq
    exact le_rfl


-- @@ L527-566 verbatim
/-- A universal zero-overhead cost certificate for the query-crossing composite.

The exact unit-cost formula and exact phase-source query accounting show that the source phases
already dominate the composite in all five resource components. A two-phase source pays for one
additional initialization and final readout, while its query count and encoded traffic agree
exactly with the composite prefix. -/
@[expose]
def querySeqCompCost :
    SeqCompCostCertificate firstQueryRealization secondQueryRealization allowsBool where
  overhead _ := 0
  cost_le := by
    intro input finish trace htrace
    have hlength :=
      trace.length_seqCompSource firstQueryRealization secondQueryRealization
    have hcompositeCost := executionCost_unitCost
      (R := firstQueryRealization.seqComp secondQueryRealization) input trace
    rw [hcompositeCost, add_zero]
    generalize hsourceEq :
      trace.seqCompSource firstQueryRealization secondQueryRealization = source
      at hlength ⊢
    cases source with
    | left leftTrace leftView =>
        simp only [SeqCompTraceSource.length] at hlength
        simp only [SeqCompTraceSource.cost]
        rw [executionCost_unitCost (R := firstQueryRealization)]
        exact unitCostEnvelope_mono (Nat.le_of_eq hlength.symm)
    | handoff leftTrace returned =>
        simp only [SeqCompTraceSource.length] at hlength
        simp only [SeqCompTraceSource.cost]
        rw [executionCost_unitCost (R := firstQueryRealization),
          executionCost_unitCost (R := secondQueryRealization)]
        exact (unitCostEnvelope_mono (Nat.le_of_eq hlength.symm)).trans
          (ExecutionCost.le_add_right _ _)
    | right leftTrace returned rightTrace =>
        simp only [SeqCompTraceSource.length] at hlength
        simp only [SeqCompTraceSource.cost]
        rw [executionCost_unitCost (R := firstQueryRealization),
          executionCost_unitCost (R := secondQueryRealization)]
        exact (unitCostEnvelope_mono (Nat.le_of_eq hlength.symm)).trans
          (unitCostEnvelope_add leftTrace.length rightTrace.length)


-- @@ L568-575 verbatim
/-- The real bounded sequential-composition theorem closes the two querying phases from their
independent run bounds, the handoff envelope, and the universal structural-cost certificate. -/
theorem querySeqCompRunsWithin :
    (firstQueryRealization.seqComp secondQueryRealization).RunsWithinUnder allowsBool
      (fun input ↦ oneQueryBound + queryHandoffBound.bound input +
        querySeqCompCost.overhead input) :=
  QuantitativeRealization.RunsWithinUnder.seqComp firstQueryRunsWithin
    secondQueryRunsWithin queryHandoffBound querySeqCompCost


-- @@ L577-583 verbatim
/-- The mechanically reconstructed phase source preserves both concrete query steps. -/
example :
    ((queryCrossingTrace true false).seqCompSource firstQueryRealization
      secondQueryRealization).length = 2 := by
  rw [(queryCrossingTrace true false).length_seqCompSource firstQueryRealization
    secondQueryRealization]
  rfl


-- @@ L585-597 verbatim
/-- The derived composite resource function reduces to an explicit nonzero five-component
bound, making the theorem usable without inspecting the certificate internals. -/
example :
    (firstQueryRealization.seqComp secondQueryRealization).RunsWithinUnder allowsBool
      (fun _ ↦ ⟨8, 2, 4, 1, 1⟩) := by
  have hbound :
      (fun input ↦ oneQueryBound + queryHandoffBound.bound input +
        querySeqCompCost.overhead input) = (fun _ ↦ ⟨8, 2, 4, 1, 1⟩) := by
    funext input
    simp only [oneQueryBound, queryHandoffBound, querySeqCompCost]
    apply ExecutionCost.ext <;> rfl
  rw [← hbound]
  exact querySeqCompRunsWithin


-- @@ L599-599 verbatim
#check RankedRunCertificate.resolvesInUnder

-- @@ L600-600 verbatim
#check RankedRunCertificate.runsWithinUnder

-- @@ L601-601 verbatim
#check QuantitativeRealization.ExecutionTrace.toPrecomp

-- @@ L602-602 verbatim
#check QuantitativeRealization.ExecutionTrace.ofPrecomp

-- @@ L603-603 verbatim
#check QuantitativeRealization.ExecutionTrace.toMapResult

-- @@ L604-604 verbatim
#check QuantitativeRealization.ExecutionTrace.ofMapResult

-- @@ L605-605 verbatim
#check QuantitativeRealization.ExecutionTrace.seqCompAnyDecomposition

-- @@ L606-606 verbatim
#check QuantitativeRealization.ExecutionTrace.conforms_seqCompSource

-- @@ L607-607 verbatim
#check QuantitativeRealization.ExecutionTrace.length_seqCompSource

-- @@ L608-608 verbatim
#check QuantitativeRealization.RunsWithinUnder.precomp

-- @@ L609-609 verbatim
#check QuantitativeRealization.RunsWithinUnder.mapResult

-- @@ L610-610 verbatim
#check QuantitativeRealization.resolvesInUnder_seqComp

-- @@ L611-611 verbatim
#check QuantitativeRealization.RunsWithinUnder.seqComp


-- @@ L613-613 verbatim
end PFunctor.QuantitativeBoundedClosureTest
