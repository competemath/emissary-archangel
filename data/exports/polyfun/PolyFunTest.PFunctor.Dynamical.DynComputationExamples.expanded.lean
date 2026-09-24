/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.PFunctor.Dynamical.DynComputation
import Mathlib.Tactic.NormNum


-- @@ L11-11 verbatim
/-! # Returning dynamical computation examples -/


-- @@ L13-13 verbatim
@[expose] public section


-- @@ L15-15 verbatim
open PFunctor


-- @@ L17-17 verbatim
namespace PFunctor.DynSystem.DynComputation


-- @@ L19-21 verbatim
/-- Immediately returning computations exist even over the empty interface,
which has no point that could supply unreachable interaction data. -/
def emptyOfFn : DynComputation 0 Nat Nat := ofFn (· + 1)


-- @@ L23-23 verbatim
example : emptyOfFn.view (emptyOfFn.init 4) = Sum.inl 5 := by simp [emptyOfFn]


-- @@ L25-25 verbatim
example : emptyOfFn.denote 4 = Resumption.pure 5 := by simp [emptyOfFn]


-- @@ L27-28 verbatim
/-- The `Pure` instance ignores the input and returns its constant value. -/
def emptyPure : DynComputation 0 Nat Nat := pure 5


-- @@ L30-30 verbatim
example : emptyPure.view (emptyPure.init 4) = Sum.inl 5 := by simp [emptyPure]


-- @@ L32-32 verbatim
example : emptyPure.denote 4 = Resumption.pure 5 := by simp [emptyPure]


-- @@ L34-36 verbatim
example : emptyPure = ofFn (fun _ : Nat => 5) := by
  unfold emptyPure
  exact pure_eq_ofFn 5


-- @@ L38-42 verbatim
/-- A computation that perpetually exposes the unique query of `y`. -/
def querying : DynComputation.{0} y.{0, 0} Unit Nat where
  State := Unit
  toDynSystem := (fun _ : Unit => Sum.inl PUnit.unit) ⇆ fun _ _ => ()
  init := id


-- @@ L44-45 verbatim
example : querying.view (querying.init ()) =
    Sum.inr ⟨PUnit.unit, fun _ => querying.init ()⟩ := rfl


-- @@ L47-50 verbatim
example : Resumption.dest (querying.denote ()) =
    Sum.map (fun value : Nat => value) (y.map querying.toDynSystem.behavior)
      (querying.view (querying.init ())) :=
  by simpa only using dest_denote querying ()


-- @@ L52-52 verbatim
/-! ## Canonical resumption realizations -/


-- @@ L54-57 verbatim
/-- A resumption realization preserves both its state-level view and its
state-free denotation. -/
def realizedQuerying : DynComputation y Unit Nat :=
  ofResumption fun _ => querying.denote ()


-- @@ L59-61 verbatim
example : realizedQuerying.view (realizedQuerying.init ()) =
    Resumption.dest (querying.denote ()) := by
  simp [realizedQuerying]


-- @@ L63-64 verbatim
example : realizedQuerying.denote () = querying.denote () := by
  simp [realizedQuerying]


-- @@ L66-66 verbatim
universe uA uB uα uβ uγ uState uState₂


-- @@ L68-72 verbatim
/-- Inputs, outputs, and both polynomial universes remain independent in the
canonical realization. -/
def universeSeparatedOfResumption {p : PFunctor.{uA, uB}} {α : Type uα}
    {β : Type uβ} (semantics : α → Resumption p β) : DynComputation p α β :=
  ofResumption semantics


-- @@ L74-78 verbatim
/-- Qualitative implementation does not couple the hidden-state universe to
the interface, input, or output universes. -/
example {p : PFunctor.{uA, uB}} {α : Type uα} {β : Type uβ}
    (M : DynComputation.{uState} p α β) (program : α → FreeM p β) : Prop :=
  M.Implements program


-- @@ L80-80 verbatim
/-! ## Finite programs and qualitative implementation -/


-- @@ L82-85 verbatim
/-- A one-query finite program used to exercise the residual-program
realization. -/
def oneQuery (_ : Unit) : FreeM y Nat :=
  FreeM.liftBind PUnit.unit fun _ => pure 7


-- @@ L87-88 verbatim
example : (ofFreeM oneQuery).denote () = FreeM.toResumption (oneQuery ()) :=
  denote_ofFreeM oneQuery ()


-- @@ L90-93 verbatim
example :
    (ofResumption fun input => FreeM.toResumption (oneQuery input)).denote () =
      FreeM.toResumption (oneQuery ()) :=
  denote_ofResumption _ ()


-- @@ L95-95 verbatim
open scoped PFunctor.DynComputation


-- @@ L97-98 verbatim
example : ofFreeM oneQuery ⊨ oneQuery :=
  implements_ofFreeM oneQuery


-- @@ L100-110 verbatim
/-- A noncanonical realization uses `Bool` states instead of residual programs. -/
def boolRealization : DynComputation y Unit Nat where
  State := Bool
  toDynSystem :=
    (fun
      | false => Sum.inl PUnit.unit
      | true => Sum.inr (7 : Nat)) ⇆
    fun
      | false => fun _ => true
      | true => PEmpty.elim
  init := fun _ => false


-- @@ L112-115 verbatim
/-- Relate the implementation states to the corresponding residual programs. -/
inductive BoolResidual : Bool → FreeM y Nat → Prop
  | start : BoolResidual false (oneQuery ())
  | done : BoolResidual true (FreeM.pure 7)


-- @@ L117-126 verbatim
theorem boolSimulation : IsSimulation boolRealization.toDynSystem
    (ofFreeM oneQuery).toDynSystem BoolResidual where
  expose_eq := by
    intro state residual related
    cases related <;> rfl
  update_rel := by
    intro state residual related direction
    cases related with
    | start => exact BoolResidual.done
    | done => exact PEmpty.elim direction


-- @@ L128-134 verbatim
/-- The simulation bridge proves semantics for a genuinely different state
representation, rather than only for the two canonical realizations. -/
theorem boolImplements : boolRealization ⊨ oneQuery := by
  apply implements_of_isSimulation boolRealization oneQuery BoolResidual boolSimulation
  intro input
  cases input
  exact BoolResidual.start


-- @@ L136-137 verbatim
example : ObsEq boolRealization (ofFreeM oneQuery) :=
  ObsEq.of_implements boolImplements (implements_ofFreeM oneQuery)


-- @@ L139-141 verbatim
example : ObsEq (boolRealization.mapResult (· + 1))
    ((ofFreeM oneQuery).mapResult (· + 1)) :=
  (ObsEq.of_implements boolImplements (implements_ofFreeM oneQuery)).mapResult (· + 1)


-- @@ L143-143 verbatim
/-! ## Sequential composition -/


-- @@ L145-150 verbatim
/-- Both hidden-state universes remain independent under composition. -/
def seqCompUniverseCanary {p : PFunctor.{uA, uB}} {α : Type uα}
    {β : Type uβ} {γ : Type uγ} (M₁ : DynComputation.{uState} p α β)
    (M₂ : DynComputation.{uState₂} p β γ) :
    DynComputation.{max uState uState₂} p α γ :=
  M₁.seqComp M₂


-- @@ L152-154 verbatim
/-- Over the empty interface, two immediate computations compose without any
chosen query or extra transition. -/
def emptyDouble : DynComputation (0 : PFunctor.{0, 0}) Nat Nat := ofFn (· * 2)


-- @@ L156-165 verbatim
example : (emptyOfFn.{0, 0}.seqComp emptyDouble).view
    ((emptyOfFn.{0, 0}.seqComp emptyDouble).init 4) = Sum.inl 10 := by
  calc
    _ = (emptyOfFn.{0, 0}.seqComp emptyDouble).view
        (Sum.inl (emptyOfFn.{0, 0}.init 4)) :=
      congrArg (emptyOfFn.{0, 0}.seqComp emptyDouble).view
        (seqComp_init emptyOfFn.{0, 0} emptyDouble 4)
    _ = Sum.inl 10 := by
      rw [seqComp_view_inl]
      rfl


-- @@ L167-168 verbatim
example : (emptyOfFn.{0, 0}.seqComp emptyDouble).denote 4 = Resumption.pure 10 := by
  simp [emptyOfFn, emptyDouble]


-- @@ L170-170 verbatim
def plusOneProgram (value : Nat) : FreeM y Nat := pure (value + 1)


-- @@ L172-174 verbatim
example : (ofFreeM oneQuery).seqComp (ofFreeM plusOneProgram) ⊨
    (fun input => FreeM.bind (oneQuery input) plusOneProgram) :=
  (implements_ofFreeM oneQuery).seqComp (implements_ofFreeM plusOneProgram)


-- @@ L176-182 verbatim
/-- Composition congruence compares genuinely different hidden-state
realizations on the first phase. -/
example : ObsEq
    (boolRealization.seqComp (ofFn (p := y) (· + 1)))
    ((ofFreeM oneQuery).seqComp (ofFn (p := y) (· + 1))) :=
  (ObsEq.of_implements boolImplements (implements_ofFreeM oneQuery)).seqComp
    (ObsEq.refl _)


-- @@ L184-189 verbatim
example : ObsEq
    (((ofFreeM oneQuery).seqComp (ofFn (p := y) (· + 1))).seqComp
      (ofFn (p := y) (· * 2)))
    ((ofFreeM oneQuery).seqComp
      ((ofFn (p := y) (· + 1)).seqComp (ofFn (p := y) (· * 2)))) :=
  seqComp_assoc_obsEq _ _ _


-- @@ L191-194 verbatim
example : ObsEq
    ((ofFn (p := y) (fun _ : Unit => (3 : Nat))).seqComp (ofFreeM plusOneProgram))
    ((ofFreeM plusOneProgram).contramapInput (fun _ : Unit => (3 : Nat))) :=
  ofFn_seqComp_obsEq _ _


-- @@ L196-199 verbatim
example : ObsEq
    ((ofFreeM oneQuery).seqComp (ofFn (p := y) (· + 1)))
    ((ofFreeM oneQuery).mapResult (· + 1)) :=
  seqComp_ofFn_obsEq _ _


-- @@ L201-201 verbatim
/-! ## Variance and observational equivalence -/


-- @@ L203-203 verbatim
universe uA₂ uB₂ uδ


-- @@ L205-211 verbatim
/-- Every relevant universe remains independent, including the source and
target direction universes of interface transport. -/
def varianceUniverseCanary {p : PFunctor.{uA, uB}} {q : PFunctor.{uA₂, uB₂}}
    {α : Type uα} {β : Type uβ} {γ : Type uγ} {δ : Type uδ}
    (M : DynComputation.{uState} p α β) (inputMap : γ → α)
    (resultMap : β → δ) (lens : Lens p q) : DynComputation.{uState} q γ δ :=
  (M.dimap inputMap resultMap).wrap lens


-- @@ L213-214 verbatim
example : (emptyOfFn.contramapInput (fun n : Nat => n + 1)).denote 3 =
    Resumption.pure 5 := by simp [emptyOfFn]


-- @@ L216-216 verbatim
example : emptyOfFn.contramapInput id = emptyOfFn := by simp


-- @@ L218-224 verbatim
example (f g : Nat → Nat) :
    (emptyOfFn.contramapInput f).contramapInput g =
      emptyOfFn.contramapInput (f ∘ g) :=
  contramapInput_comp emptyOfFn f g

-- Lean 4.33: the example unfolds these constants at implicit transparency
-- (`mapResult` carries the attribute at its definition site).

-- @@ L225-227 verbatim
attribute [local implicit_reducible] emptyOfFn ofFn in
example : (emptyOfFn.mapResult (· % 2)).view (emptyOfFn.init 4) = Sum.inl 1 := by
  simp [emptyOfFn]


-- @@ L229-232 verbatim
example : (querying.mapResult (· + 1)).view (querying.init ()) =
    Sum.inr ⟨PUnit.unit, fun _ => querying.init ()⟩ := by
  rw [mapResult_view]
  rfl


-- @@ L234-235 verbatim
example : emptyOfFn.mapResult id = emptyOfFn :=
  mapResult_id emptyOfFn


-- @@ L237-239 verbatim
example (f g : Nat → Nat) :
    (emptyOfFn.mapResult f).mapResult g = emptyOfFn.mapResult (g ∘ f) :=
  mapResult_comp emptyOfFn f g


-- @@ L241-242 verbatim
example : (emptyOfFn.dimap (· + 1) (· * 2)).denote 3 = Resumption.pure 10 := by
  simp [emptyOfFn]


-- @@ L244-244 verbatim
example : emptyOfFn.dimap id id = emptyOfFn := by simp


-- @@ L246-249 verbatim
example (f₁ g₁ f₂ g₂ : Nat → Nat) :
    (emptyOfFn.dimap f₁ g₁).dimap f₂ g₂ =
      emptyOfFn.dimap (f₁ ∘ f₂) (g₂ ∘ g₁) :=
  dimap_comp emptyOfFn f₁ g₁ f₂ g₂


-- @@ L251-252 verbatim
/-- A branch-sensitive interface with a genuinely nonidentity answer map. -/
def branchSource : PFunctor.{0, 0} := Bool y^ Bool


-- @@ L254-254 verbatim
def branchTarget : PFunctor.{0, 0} := (Fin 2) y^ (Fin 3)


-- @@ L256-256 verbatim
def branchFinal : PFunctor.{0, 0} := Bool y^ Bool


-- @@ L258-266 verbatim
def branchLens : Lens branchSource branchTarget where
  toFunA output := by
    change Bool at output
    change Fin 2
    exact if output then 1 else 0
  toFunB _ answer := by
    change Fin 3 at answer
    change Bool
    exact decide (answer = 2)


-- @@ L268-276 verbatim
def branchLens₂ : Lens branchTarget branchFinal where
  toFunA output := by
    change Fin 2 at output
    change Bool
    exact decide (output = 1)
  toFunB _ answer := by
    change Bool at answer
    change Fin 3
    exact if answer then 2 else 1


-- @@ L278-291 verbatim
def branchMachine : DynComputation branchSource Unit Nat where
  State := Bool
  toDynSystem :=
    (fun
      | false => Sum.inl false
      | true => Sum.inr (9 : Nat)) ⇆
    fun
      | false => fun answer => answer
      | true => PEmpty.elim
  init := fun _ => false

/- Lean 4.33 compares assigned metavariable types at implicit transparency;
the branch-machine examples below unfold these constants there (`wrap`
carries the attribute at its definition site). -/

-- @@ L292-293 verbatim
attribute [local implicit_reducible] PFunctor.monomial branchSource branchTarget
  branchFinal branchLens branchLens₂ branchMachine seqComp


-- @@ L295-295 verbatim
def handoffResult (answer : Bool) : Nat := if answer = true then 11 else 7


-- @@ L297-309 verbatim
/-- A second phase whose initial view is a branch-sensitive query. -/
def handoffSecond : DynComputation branchSource Bool Nat where
  State := Bool ⊕ Nat
  toDynSystem :=
    (fun
      | Sum.inl position => Sum.inl position
      | Sum.inr result => Sum.inr result) ⇆
    fun
      | Sum.inl _ => fun answer => by
          change Bool at answer
          exact Sum.inr (handoffResult answer)
      | Sum.inr _ => PEmpty.elim
  init := Sum.inl


-- @@ L311-314 verbatim
def handoffFirst : DynComputation branchSource Unit Bool :=
  ofFn fun _ => true

-- Lean 4.33: the handoff examples below unfold these at implicit transparency.

-- @@ L315-315 verbatim
attribute [local implicit_reducible] handoffFirst handoffSecond


-- @@ L317-324 verbatim
/-- A returned intermediate value exposes the second phase's actual query in
the same view, with its continuation tagged as phase two. -/
example : (handoffFirst.seqComp handoffSecond).view
    ((handoffFirst.seqComp handoffSecond).init ()) =
    Sum.inr ⟨true, fun answer =>
      Sum.inr (Sum.inr (handoffResult answer))⟩ := by
  rw [seqComp_init, seqComp_view_inl]
  rfl


-- @@ L326-329 verbatim
example : (handoffFirst.seqComp handoffSecond).view
    (Sum.inr (Sum.inr 11)) = Sum.inl 11 := by
  rw [seqComp_view_inr]
  rfl


-- @@ L331-334 verbatim
example : (handoffFirst.seqComp handoffSecond).view
    (Sum.inr (Sum.inr 7)) = Sum.inl 7 := by
  rw [seqComp_view_inr]
  rfl


-- @@ L336-346 verbatim
/-- A first phase with two answer-dependent intermediate results. -/
def answerFirst : DynComputation branchSource Unit Bool where
  State := Unit ⊕ Bool
  toDynSystem :=
    (fun
      | Sum.inl _ => Sum.inl false
      | Sum.inr value => Sum.inr value) ⇆
    fun
      | Sum.inl _ => fun answer => Sum.inr answer
      | Sum.inr _ => PEmpty.elim
  init := fun _ => Sum.inl ()


-- @@ L348-351 verbatim
def answerSecond : DynComputation branchSource Bool Nat :=
  ofFn fun answer => if answer then 1 else 2

-- Lean 4.33: the answer examples below unfold these at implicit transparency.

-- @@ L352-352 verbatim
attribute [local implicit_reducible] answerFirst answerSecond


-- @@ L354-360 verbatim
/-- A first-phase answer stays tagged as phase one until its returned value is
observed; the very next view is the corresponding second-phase initial view. -/
example : (answerFirst.seqComp answerSecond).view
    ((answerFirst.seqComp answerSecond).init ()) =
    Sum.inr ⟨false, fun answer => Sum.inl (Sum.inr answer)⟩ := by
  rw [seqComp_init, seqComp_view_inl]
  rfl


-- @@ L362-365 verbatim
example : (answerFirst.seqComp answerSecond).view
    (Sum.inl (Sum.inr true)) = Sum.inl 1 := by
  rw [seqComp_view_inl]
  rfl


-- @@ L367-370 verbatim
example : (answerFirst.seqComp answerSecond).view
    (Sum.inl (Sum.inr false)) = Sum.inl 2 := by
  rw [seqComp_view_inl]
  rfl


-- @@ L372-377 verbatim
example : (branchMachine.wrap branchLens).view false =
    Sum.inr ⟨(0 : Fin 2), fun answer => by
      change Fin 3 at answer
      exact decide (answer = 2)⟩ := by
  rw [wrap_view]
  rfl


-- @@ L379-381 verbatim
example : (branchMachine.wrap branchLens).view true = Sum.inl 9 := by
  rw [wrap_view]
  rfl


-- @@ L383-384 verbatim
example : branchMachine.wrap (Lens.id branchSource) = branchMachine :=
  wrap_id branchMachine


-- @@ L386-388 verbatim
example : (branchMachine.wrap branchLens).wrap branchLens₂ =
    branchMachine.wrap (Lens.comp branchLens₂ branchLens) :=
  wrap_comp branchMachine branchLens branchLens₂


-- @@ L390-392 verbatim
example : (Lens.comp branchLens₂ branchLens).toFunA false = false := by
  change decide ((0 : Fin 2) = 1) = false
  decide


-- @@ L394-397 verbatim
example (answer : Bool) :
    (Lens.comp branchLens₂ branchLens).toFunB false answer = answer := by
  change decide ((if answer then 2 else 1 : Fin 3) = 2) = answer
  cases answer <;> decide


-- @@ L399-401 verbatim
example : (branchMachine.mapResult (· + 1)).wrap branchLens =
    (branchMachine.wrap branchLens).mapResult (· + 1) :=
  mapResult_wrap branchMachine (· + 1) branchLens


-- @@ L403-404 verbatim
/-! Lossy maps preserve equivalence but do not reflect it. These countermodels
pin the intended one-way API. -/


-- @@ L406-407 verbatim
def boolResult (value : Bool) : DynComputation 0 Unit Bool :=
  ofFn fun _ => value


-- @@ L409-413 verbatim
example : ¬ ObsEq (boolResult false) (boolResult true) := by
  intro h
  have hdenote := h ()
  have hdest := congrArg Resumption.dest hdenote
  simp [boolResult] at hdest


-- @@ L415-419 verbatim
example : ObsEq
    ((boolResult false).mapResult (fun _ => ()))
    ((boolResult true).mapResult (fun _ => ())) := by
  intro input
  simp [boolResult]


-- @@ L421-422 verbatim
/-- The outer interface can observe only the `false` source answer. -/
def lossySource : PFunctor.{0, 0} := Unit y^ Bool


-- @@ L424-426 verbatim
def lossyLens : Lens lossySource y where
  toFunA _ := PUnit.unit
  toFunB _ _ := false


-- @@ L428-431 verbatim
def sourceTree (trueResult : Nat) : Resumption lossySource Nat :=
  Resumption.query () fun answer => by
    change Bool at answer
    exact Resumption.pure (if answer then trueResult else 0)


-- @@ L433-437 verbatim
def sourceMachine (trueResult : Nat) : DynComputation lossySource Unit Nat :=
  ofResumption fun _ => sourceTree trueResult

/- Lean 4.33 compares assigned metavariable types at implicit transparency;
the observation examples below unfold these constants there. -/

-- @@ L438-439 verbatim
attribute [local implicit_reducible] PFunctor.y lossySource lossyLens sourceTree
  sourceMachine


-- @@ L441-447 verbatim
def observeTrueResult (tree : Resumption lossySource Nat) : Option Nat :=
  match Resumption.dest tree with
  | Sum.inl _ => none
  | Sum.inr ⟨_, next⟩ =>
      match Resumption.dest (next true) with
      | Sum.inl value => some value
      | Sum.inr _ => none


-- @@ L449-453 verbatim
example : ¬ ObsEq (sourceMachine 1) (sourceMachine 2) := by
  intro h
  have hdenote := h ()
  have hobserved := congrArg observeTrueResult hdenote
  norm_num [sourceMachine, sourceTree, observeTrueResult, lossySource] at hobserved


-- @@ L455-463 verbatim
example : ObsEq
    ((sourceMachine 1).wrap lossyLens)
    ((sourceMachine 2).wrap lossyLens) := by
  intro input
  cases input
  -- Lean 4.33: `DynComputation.wrap` is only `implicit_reducible`, so
  -- `wrap_denote` is passed to `simp` explicitly.
  simp [sourceMachine, sourceTree, lossyLens, lossySource,
    DynComputation.wrap_denote]


-- @@ L465-467 verbatim
example : (ofFreeM oneQuery).mapResult (· + 1) ⊨
    (fun input => FreeM.map (· + 1) (oneQuery input)) :=
  (implements_ofFreeM oneQuery).mapResult (· + 1)


-- @@ L469-471 verbatim
example : (ofFreeM oneQuery).wrap (Lens.id y) ⊨
    (fun input => (oneQuery input).mapLens (Lens.id y)) :=
  (implements_ofFreeM oneQuery).wrap (Lens.id y)


-- @@ L473-473 verbatim
/-! ## Semantic transport producer canaries -/


-- @@ L475-477 verbatim
/-- An input-dependent program makes input precomposition observable. -/
def inputProgram (input : Nat) : FreeM y Nat :=
  FreeM.liftBind PUnit.unit fun _ => pure (input + 1)


-- @@ L479-479 verbatim
def inputFreeMachine : DynComputation y Nat Nat := ofFreeM inputProgram


-- @@ L481-482 verbatim
def inputResumptionMachine : DynComputation y Nat Nat :=
  ofResumption fun input => FreeM.toResumption (inputProgram input)


-- @@ L484-486 verbatim
theorem inputMachinesObsEq : ObsEq inputFreeMachine inputResumptionMachine :=
  ObsEq.of_implements (implements_ofFreeM inputProgram)
    (implements_ofResumption inputProgram)


-- @@ L488-488 verbatim
def boolInput : Bool → Nat := Bool.rec 3 7


-- @@ L490-493 verbatim
example : ObsEq
    (inputFreeMachine.contramapInput boolInput)
    (inputResumptionMachine.contramapInput boolInput) :=
  inputMachinesObsEq.contramapInput boolInput


-- @@ L495-498 verbatim
example : ObsEq
    (inputFreeMachine.dimap boolInput (· * 2))
    (inputResumptionMachine.dimap boolInput (· * 2)) :=
  inputMachinesObsEq.dimap boolInput (· * 2)


-- @@ L500-502 verbatim
example : inputResumptionMachine ⊨ inputProgram :=
  (inputMachinesObsEq.implements_iff inputProgram).mp
    (implements_ofFreeM inputProgram)


-- @@ L504-506 verbatim
example : inputFreeMachine ⊨ inputProgram :=
  (inputMachinesObsEq.implements_iff inputProgram).mpr
    (implements_ofResumption inputProgram)


-- @@ L508-510 verbatim
example : (inputFreeMachine.contramapInput boolInput) ⊨
    (fun input => inputProgram (boolInput input)) :=
  (implements_ofFreeM inputProgram).contramapInput boolInput


-- @@ L512-514 verbatim
example : (inputFreeMachine.dimap boolInput (· * 2)) ⊨
    (fun input => FreeM.map (· * 2) (inputProgram (boolInput input))) :=
  (implements_ofFreeM inputProgram).dimap boolInput (· * 2)


-- @@ L516-518 verbatim
/-- A second realization over `lossySource` pins nonidentity lens congruence. -/
def lossyProgram (input : Nat) : FreeM lossySource Nat :=
  FreeM.liftBind () fun answer => pure (Bool.rec input (input + 1) answer)


-- @@ L520-520 verbatim
def lossyFreeMachine : DynComputation lossySource Nat Nat := ofFreeM lossyProgram


-- @@ L522-523 verbatim
def lossyResumptionMachine : DynComputation lossySource Nat Nat :=
  ofResumption fun input => FreeM.toResumption (lossyProgram input)


-- @@ L525-527 verbatim
theorem lossyMachinesObsEq : ObsEq lossyFreeMachine lossyResumptionMachine :=
  ObsEq.of_implements (implements_ofFreeM lossyProgram)
    (implements_ofResumption lossyProgram)


-- @@ L529-532 verbatim
example : ObsEq
    (lossyFreeMachine.wrap lossyLens)
    (lossyResumptionMachine.wrap lossyLens) :=
  lossyMachinesObsEq.wrap lossyLens


-- @@ L534-534 verbatim
end PFunctor.DynSystem.DynComputation
