/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import PolyFun.PFunctor.PatternRunsOnMatter.Display


-- @@ L11-15 verbatim
/-!
Canaries for indexed M-types and state-free proof-relevant responder behavior.
Postcondition evidence depends on the actual answer, and continuation evidence
is checked after transport along the ordinary behavior-child equation.
-/


-- @@ L17-17 verbatim
@[expose] public section


-- @@ L19-22 verbatim
namespace PFunctor.ResponderBehaviorExample

/- Lean 4.33 compares assigned metavariable types at implicit transparency;
the behavior examples below unfold these constants there. -/

-- @@ L23-27 verbatim
attribute [local implicit_reducible] PFunctor.y PFunctor.monomial PFunctor.ihom
  PFunctor.DynSystem.out PFunctor.DynSystem.expose PFunctor.DynSystem.update
  PFunctor.M.terminalSystem PFunctor.Responder.terminal

-- Lean 4.33: the examples below unfold `Interface` at implicit transparency.

-- @@ L28-31 verbatim
@[implicit_reducible]
def Interface : PFunctor where
  A := Unit
  B := fun _ => Bool


-- @@ L33-35 verbatim
def query : Interface.A := ()

-- Lean 4.33: the examples below unfold `contract` at implicit transparency.

-- @@ L36-39 verbatim
@[implicit_reducible]
def contract : Display Interface where
  position _ := Bool
  direction _ expected answer := if expected = answer then Fin 2 else Fin 3


-- @@ L41-46 verbatim
def directionFromNat (expected answer : Bool) (value : Nat) :
    contract.direction () expected answer := by
  simp only [contract]
  split
  · exact ⟨value % 2, Nat.mod_lt _ (by decide)⟩
  · exact ⟨value % 3, Nat.mod_lt _ (by decide)⟩


-- @@ L48-53 verbatim
def directionVal (expected answer : Bool)
    (evidence : contract.direction () expected answer) : Nat := by
  change (if expected = answer then Fin 2 else Fin 3) at evidence
  split at evidence
  · exact evidence.val
  · exact evidence.val


-- @@ L55-56 verbatim
def responder : Responder Bool Interface :=
  Responder.mk' (fun state _ => state) (fun state _ => !state)


-- @@ L58-58 verbatim
def Invariant (state : Bool) := if state then Fin 2 else Fin 3


-- @@ L60-64 verbatim
def invariantFromNat (state : Bool) (value : Nat) : Invariant state := by
  simp only [Invariant]
  split
  · exact ⟨value % 2, Nat.mod_lt _ (by decide)⟩
  · exact ⟨value % 3, Nat.mod_lt _ (by decide)⟩


-- @@ L66-70 verbatim
def invariantVal (state : Bool) (witness : Invariant state) : Nat := by
  simp only [Invariant] at witness
  split at witness
  · exact witness.val
  · exact witness.val


-- @@ L72-80 verbatim
def obligation :
    (state : Bool) → Invariant state →
      (query : Unit) → (precondition : Bool) →
        contract.direction query precondition
            (responder.answer state query) ×
          Invariant (responder.next state query) :=
  fun state witness _ precondition =>
    ⟨directionFromNat precondition state (invariantVal state witness),
      invariantFromNat (!state) (invariantVal state witness + 1)⟩


-- @@ L82-84 verbatim
def displayed :
    Display.Coalgebra (Display.responder contract) responder.out Invariant :=
  (Display.responderCoalgebraEquiv contract responder Invariant).symm obligation


-- @@ L86-88 verbatim
def initialWitness : Invariant false := invariantFromNat false 1

-- Lean 4.33: the examples below unfold `behavior` at implicit transparency.

-- @@ L89-93 verbatim
@[implicit_reducible]
def behavior := responder.behavior false

-- Lean 4.33: the examples below unfold `toDisplayedBehavior` at implicit
-- transparency.

-- @@ L94-97 verbatim
@[implicit_reducible]
def toDisplayedBehavior :=
  Responder.toDisplayedBehavior contract responder Invariant displayed
    false initialWitness


-- @@ L99-101 verbatim
example : behavior.head.toFunB query PUnit.unit = false := by
  change responder.answer false query = false
  rfl


-- @@ L103-110 verbatim
example : directionVal false false
    (Responder.respondDisplayed contract toDisplayedBehavior query false).1 = 1 := by
  change directionVal false false
    (Responder.respondDisplayed contract
      (Responder.toDisplayedBehavior contract responder Invariant displayed
        false initialWitness) query false).1 = 1
  rw [Responder.respondDisplayed_toDisplayedBehavior_post]
  rfl


-- @@ L112-113 verbatim
/-! Changing only the supplied precondition selects the `Fin 3` branch.  This
would not typecheck if state-free behavior erased answer-dependent evidence. -/

-- @@ L114-121 verbatim
example : directionVal true false
    (Responder.respondDisplayed contract toDisplayedBehavior query true).1 = 1 := by
  change directionVal true false
    (Responder.respondDisplayed contract
      (Responder.toDisplayedBehavior contract responder Invariant displayed
        false initialWitness) query true).1 = 1
  rw [Responder.respondDisplayed_toDisplayedBehavior_post]
  rfl


-- @@ L123-137 verbatim
example :
    Display.M.transport (Responder.behavior_child responder false ())
        (Responder.respondDisplayed contract toDisplayedBehavior query false).2 =
      Responder.toDisplayedBehavior contract responder Invariant displayed
        (responder.next false query)
        ((Display.responderCoalgebraEquiv contract responder Invariant)
          displayed false initialWitness query false).2 := by
  change Display.M.transport
      (Responder.behavior_child responder false query)
      (Responder.respondDisplayed contract
        (Responder.toDisplayedBehavior contract responder Invariant displayed
          false initialWitness) query false).2 = _
  exact
    Responder.respondDisplayed_toDisplayedBehavior_next contract responder Invariant displayed
      false initialWitness query false


-- @@ L139-140 verbatim
def oneCall : Handler (FreeM Interface) Interface :=
  fun _ => FreeM.lift query


-- @@ L142-143 verbatim
def twoCalls : Handler (FreeM Interface) Interface :=
  fun _ => .liftBind query fun _ => FreeM.lift query


-- @@ L145-148 verbatim
def displayedOneCall : Display.Handler contract contract oneCall :=
  fun _ precondition =>
    ⟨precondition, fun answer evidence =>
      contract.leaf (contract.direction query precondition) answer evidence⟩


-- @@ L150-152 verbatim
def reindexedDisplayedBehavior :=
  Responder.reindexDisplayedBehavior contract contract oneCall displayedOneCall
    behavior toDisplayedBehavior


-- @@ L154-157 verbatim
example : Responder.reindexBehavior oneCall behavior =
    (Responder.reindexViaRunAgainst oneCall
      (Responder.terminal (P := Interface))).behavior behavior :=
  Responder.reindexBehavior_eq_runAgainst oneCall behavior


-- @@ L159-162 verbatim
def directDisplayedStep :=
  Responder.runFreeDisplayed contract (Responder.terminal (P := Interface))
    (Display.Coalgebra.terminal (Display.responder contract))
    (displayedOneCall query false) behavior toDisplayedBehavior


-- @@ L164-172 verbatim
def runAgainstDisplayedStep :=
  Responder.transportRunEvidence (contract.direction query false)
    (Display.M (Display.responder contract))
    (Responder.runAgainstResult_eq_runFree
      (Responder.terminal (P := Interface)) (oneCall query) behavior)
    (Responder.runAgainstDisplayed contract
      (Responder.terminal (P := Interface))
      (Display.Coalgebra.terminal (Display.responder contract))
      (displayedOneCall query false) behavior toDisplayedBehavior)


-- @@ L174-176 verbatim
/-! The direct displayed execution and the coinductive reindexed `respondDisplayed` side
are observed separately, so changing the semantic equation and implementation
in lockstep does not preserve both canaries. -/


-- @@ L178-184 verbatim
example : directionVal false false directDisplayedStep.1 = 1 := by
  change directionVal false false
    (Responder.respondDisplayed contract
      (Responder.toDisplayedBehavior contract responder Invariant displayed
        false initialWitness) query false).1 = 1
  rw [Responder.respondDisplayed_toDisplayedBehavior_post]
  rfl


-- @@ L186-199 verbatim
example : directionVal false false
    (Responder.respondDisplayed contract reindexedDisplayedBehavior query false).1 = 1 := by
  change directionVal false false
    (Responder.respondDisplayed contract
      (Responder.reindexDisplayedBehavior contract contract oneCall
        displayedOneCall behavior toDisplayedBehavior) query false).1 = 1
  rw [Responder.respondDisplayed_reindexDisplayedBehavior_post]
  exact show directionVal false false directDisplayedStep.1 = 1 from by
    change directionVal false false
      (Responder.respondDisplayed contract
        (Responder.toDisplayedBehavior contract responder Invariant displayed
          false initialWitness) query false).1 = 1
    rw [Responder.respondDisplayed_toDisplayedBehavior_post]
    rfl


-- @@ L201-214 verbatim
/-- The state-free proof-relevant postcondition is supplied by evaluated
Pattern Runs on Matter, not merely by the raw Xi synchronization tree. -/
example :
    (Responder.respondDisplayed contract reindexedDisplayedBehavior query false).1 =
      (Responder.transportRunEvidence (contract.direction query false)
        (Display.M (Display.responder contract))
        (Responder.runAgainstResult_eq_runFree
          (Responder.terminal (P := Interface)) (oneCall query) behavior)
        (Responder.runAgainstDisplayed contract
          (Responder.terminal (P := Interface))
          (Display.Coalgebra.terminal (Display.responder contract))
          (displayedOneCall query false) behavior toDisplayedBehavior)).1 :=
  Responder.respondDisplayed_reindexDisplayedBehavior_post_runAgainst contract contract
    oneCall displayedOneCall behavior toDisplayedBehavior query false


-- @@ L216-227 verbatim
example :
    Display.M.transport
        (Responder.behavior_child
          (Responder.reindex oneCall
            (Responder.terminal (P := Interface))) behavior query)
        (Responder.respondDisplayed contract reindexedDisplayedBehavior query false).2 =
      Responder.reindexDisplayedBehavior contract contract oneCall
        displayedOneCall
        ((Responder.terminal (P := Interface)).runFree
          (oneCall query) behavior).2 directDisplayedStep.2 := by
  exact Responder.respondDisplayed_reindexDisplayedBehavior_next contract contract
    oneCall displayedOneCall behavior toDisplayedBehavior query false


-- @@ L229-243 verbatim
/-- The evaluated Pattern-Runs-on-Matter continuation bridge is exercised
directly, rather than only through its `runFreeDisplayed` predecessor. -/
example :
    Display.M.transport
        (Responder.behavior_child
          (Responder.reindex oneCall
            (Responder.terminal (P := Interface))) behavior query)
        (Responder.respondDisplayed contract reindexedDisplayedBehavior query false).2 =
      Responder.reindexDisplayedBehavior contract contract oneCall
        displayedOneCall
        ((Responder.terminal (P := Interface)).runFree
          (oneCall query) behavior).2 runAgainstDisplayedStep.2 := by
  exact
    Responder.respondDisplayed_reindexDisplayedBehavior_next_runAgainst contract contract
      oneCall displayedOneCall behavior toDisplayedBehavior query false


-- @@ L245-252 verbatim
def firstRunAgainstContinuation :
    Display.M (Display.responder contract)
      (Responder.reindexBehavior oneCall
        ((Responder.terminal (P := Interface)).runFree
          (oneCall query) behavior).2) :=
  Responder.reindexDisplayedBehavior contract contract oneCall displayedOneCall
    ((Responder.terminal (P := Interface)).runFree
      (oneCall query) behavior).2 runAgainstDisplayedStep.2


-- @@ L254-271 verbatim
/-- After the evaluated-action bridge, the successor continuation still
exposes the answer-dependent evidence of its next state. -/
example : directionVal true true
    (Responder.respondDisplayed contract firstRunAgainstContinuation query true).1 = 0 := by
  have hstep : runAgainstDisplayedStep = directDisplayedStep :=
    Responder.runAgainstDisplayed_eq_runFreeDisplayed contract
      (Responder.terminal (P := Interface))
      (Display.Coalgebra.terminal (Display.responder contract))
      (displayedOneCall query false) behavior toDisplayedBehavior
  change directionVal true true
    (Responder.respondDisplayed contract
      (Responder.reindexDisplayedBehavior contract contract oneCall
        displayedOneCall
        ((Responder.terminal (P := Interface)).runFree
          (oneCall query) behavior).2 runAgainstDisplayedStep.2)
      query true).1 = 0
  rw [hstep]
  rfl


-- @@ L273-282 verbatim
def firstReindexedContinuation :
    Display.M (Display.responder contract)
      (Responder.reindexBehavior oneCall
        ((Responder.terminal (P := Interface)).runFree
          (oneCall query) behavior).2) :=
  Display.M.transport
    (Responder.behavior_child
      (Responder.reindex oneCall (Responder.terminal (P := Interface)))
      behavior query)
    (Responder.respondDisplayed contract reindexedDisplayedBehavior query false).2


-- @@ L284-286 verbatim
/-! The continuation produced by displayed reindexing is itself executed for a
second step. This catches a reindexer that returns a stale or copied original
continuation even when its one-step equation is changed in lockstep. -/

-- @@ L287-300 verbatim
example : directionVal true true
    (Responder.respondDisplayed contract firstReindexedContinuation query true).1 = 0 := by
  change directionVal true true
    (Responder.respondDisplayed contract
      (Display.M.transport
        (Responder.behavior_child
          (Responder.reindex oneCall
            (Responder.terminal (P := Interface))) behavior query)
        (Responder.respondDisplayed contract
          (Responder.reindexDisplayedBehavior contract contract oneCall
            displayedOneCall behavior toDisplayedBehavior) query false).2)
      query true).1 = 0
  rw [Responder.respondDisplayed_reindexDisplayedBehavior_next]
  rfl


-- @@ L302-305 verbatim
def firstDisplayedContinuation :
    Display.M (Display.responder contract) (responder.behavior true) :=
  Display.M.transport (Responder.behavior_child responder false query)
    (Responder.respondDisplayed contract toDisplayedBehavior query false).2


-- @@ L307-309 verbatim
/-! This unfolds the continuation returned by the first `respondDisplayed` call and then
observes its next answer-dependent postcondition. It is independent of the
one-step continuation equality above. -/

-- @@ L310-320 verbatim
example : directionVal true true
    (Responder.respondDisplayed contract firstDisplayedContinuation query true).1 = 0 := by
  change directionVal true true
    (Responder.respondDisplayed contract
      (Display.M.transport (Responder.behavior_child responder false query)
        (Responder.respondDisplayed contract
          (Responder.toDisplayedBehavior contract responder Invariant displayed
            false initialWitness) query false).2) query true).1 = 0
  rw [Responder.respondDisplayed_toDisplayedBehavior_next]
  rw [Responder.respondDisplayed_toDisplayedBehavior_post]
  rfl


-- @@ L322-325 verbatim
/-! Re-coinducing a displayed behavior from its own destructor gives a second
presentation of the same displayed tree.  The following two canaries exercise
the generic displayed and responder-observation bisimulation interfaces
directly; their child obligations reject a copied or stale continuation. -/


-- @@ L327-330 verbatim
def recoinducedDisplayedBehavior :
    Display.M (Display.responder contract) behavior :=
  Display.M.corec (Display.M (Display.responder contract))
    (fun _ displayed => Display.M.dest displayed) behavior toDisplayedBehavior


-- @@ L332-359 verbatim
/-- Direct producer canary for `Display.M.bisim`, using the original displayed
tree and the distinct corecursive presentation generated by its destructor. -/
example : toDisplayedBehavior = recoinducedDisplayedBehavior := by
  let step := fun
      (current : PFunctor.M (Interface ⊸ y))
      (displayed : Display.M (Display.responder contract) current) =>
    Display.M.dest displayed
  let Rel := fun
      (current : PFunctor.M (Interface ⊸ y))
      (left right : Display.M (Display.responder contract) current) =>
    ∃ displayed,
      left = displayed ∧
        right = Display.M.corec
          (Display.M (Display.responder contract)) step current displayed
  apply Display.M.bisim Rel
  · intro current left right related
    rcases related with ⟨source, leftEq, rightEq⟩
    subst left
    subst right
    refine ⟨source.head, source.child,
      (fun direction precondition =>
        Display.M.corec (Display.M (Display.responder contract)) step _
          (source.child direction precondition)), rfl, ?_, ?_⟩
    · rw [Display.M.dest_corec]
      rfl
    · intro direction precondition
      exact ⟨source.child direction precondition, rfl, rfl⟩
  · exact ⟨toDisplayedBehavior, rfl, rfl⟩


-- @@ L361-396 verbatim
/-- Direct producer canary for the responder-shaped bisimulation.  Equality of
the answer-dependent evidence and recursive selection of the matching child
are both exposed through `respondDisplayed`. -/
example : toDisplayedBehavior = recoinducedDisplayedBehavior := by
  let step := fun
      (current : PFunctor.M (Interface ⊸ y))
      (displayed : Display.M (Display.responder contract) current) =>
    Display.M.dest displayed
  let Rel := fun
      (current : PFunctor.M (Interface ⊸ y))
      (left right : Display.M (Display.responder contract) current) =>
    ∃ displayed,
      left = displayed ∧
        right = Display.M.corec
          (Display.M (Display.responder contract)) step current displayed
  apply Responder.respondDisplayed_bisim contract Rel
  · intro current left right related currentQuery precondition
    rcases related with ⟨source, leftEq, rightEq⟩
    subst left
    subst right
    have hDest := Display.M.dest_corec
      (Display.M (Display.responder contract)) step current source
    constructor
    · rw [Responder.respondDisplayed_post, Responder.respondDisplayed_post]
      have hHead := congrArg Sigma.fst hDest
      change
        (Display.M.corec (Display.M (Display.responder contract)) step
          current source).head = source.head at hHead
      exact congrFun (congrFun hHead.symm currentQuery) precondition
    · refine ⟨
        (Responder.respondDisplayed contract source currentQuery precondition).2,
        rfl, ?_⟩
      rw [Responder.respondDisplayed_next, Responder.respondDisplayed_next]
      exact congrArg
        (fun node => node.2 ⟨currentQuery, PUnit.unit⟩ precondition) hDest
  · exact ⟨toDisplayedBehavior, rfl, rfl⟩


-- @@ L398-401 verbatim
example :
    Responder.reindexBehavior oneCall (responder.behavior false) =
      (Responder.reindex oneCall responder).behavior false :=
  Responder.reindexBehavior_behavior oneCall responder false


-- @@ L403-407 verbatim
example :
    Responder.reindexBehavior oneCall
        (Responder.reindexBehavior oneCall behavior) =
      Responder.reindexBehavior (oneCall.comp oneCall) behavior :=
  Responder.reindexBehavior_comp oneCall oneCall behavior


-- @@ L409-410 verbatim
example : Responder.reindexBehavior (Handler.id Interface) behavior = behavior :=
  Responder.reindexBehavior_id behavior


-- @@ L412-417 verbatim
example :
    Display.M.transport (Responder.reindexBehavior_id behavior)
        (Responder.reindexDisplayedBehavior contract contract
          (Handler.id Interface) (Display.Handler.id contract)
          behavior toDisplayedBehavior) = toDisplayedBehavior :=
  Responder.reindexDisplayedBehavior_id contract behavior toDisplayedBehavior


-- @@ L419-429 verbatim
example :
    Display.M.transport
        (Responder.reindexBehavior_comp oneCall oneCall behavior)
        (Responder.reindexDisplayedBehavior contract contract oneCall
          displayedOneCall (Responder.reindexBehavior oneCall behavior)
          reindexedDisplayedBehavior) =
      Responder.reindexDisplayedBehavior contract contract
        (oneCall.comp oneCall) (displayedOneCall.comp displayedOneCall)
        behavior toDisplayedBehavior :=
  Responder.reindexDisplayedBehavior_comp contract contract contract
    oneCall displayedOneCall oneCall displayedOneCall behavior toDisplayedBehavior


-- @@ L431-435 verbatim
example :
    (Display.M.destEquiv (S := Display.responder contract)
      (tree := behavior)).symm
        (Display.M.dest toDisplayedBehavior) = toDisplayedBehavior :=
  Display.M.mk_dest toDisplayedBehavior


-- @@ L437-444 verbatim
example :
    (Display.M.transportEquiv (S := Display.responder contract)
      (show behavior = behavior from rfl)).symm
        (Display.M.transportEquiv (S := Display.responder contract)
          (show behavior = behavior from rfl) toDisplayedBehavior) =
      toDisplayedBehavior :=
  (Display.M.transportEquiv (S := Display.responder contract)
    (show behavior = behavior from rfl)).left_inv toDisplayedBehavior


-- @@ L446-448 verbatim
/-! Branch count is independently observable: one query returns the initial
answer, while the explicit two-query handler returns the answer after one
state transition. -/

-- @@ L449-457 verbatim
example :
    (Responder.reindexBehavior oneCall behavior).head.toFunB query PUnit.unit =
      false := by
  change
    (Responder.reindexBehavior oneCall (responder.behavior false)).head.toFunB
      query PUnit.unit = false
  rw [Responder.reindexBehavior_behavior oneCall responder false]
  change (Responder.reindex oneCall responder).answer false query = false
  rfl


-- @@ L459-460 verbatim
/-! A concrete indexed M-type alternates two distinguishable source indices.
The first child is forced into the `true` fiber and its child into `false`. -/


-- @@ L462-465 verbatim
def IndexedToggle : IPFunctor.Endo Bool where
  A _ := Bool
  B _ _ := Unit
  src _ target _ := target


-- @@ L467-469 verbatim
def indexedToggleStep (index : Bool) (nextIndex : Bool) :
    IndexedToggle.Obj (fun _ => Bool) index :=
  ⟨nextIndex, fun _ => !nextIndex⟩


-- @@ L471-472 verbatim
def indexedToggleTree : IPFunctor.IM IndexedToggle false :=
  IPFunctor.IM.corec indexedToggleStep false true


-- @@ L474-476 verbatim
def indexedToggleStepWrapped (index : Bool) (state : Bool × Unit) :
    IndexedToggle.Obj (fun _ => Bool × Unit) index :=
  ⟨state.1, fun _ => (!state.1, ())⟩


-- @@ L478-479 verbatim
def indexedToggleTreeWrapped : IPFunctor.IM IndexedToggle false :=
  IPFunctor.IM.corec indexedToggleStepWrapped false (true, ())


-- @@ L481-482 verbatim
def indexedToggleChild : IPFunctor.IM IndexedToggle true :=
  (IPFunctor.IM.dest indexedToggleTree).2 ()


-- @@ L484-485 verbatim
def indexedToggleGrandchild : IPFunctor.IM IndexedToggle false :=
  (IPFunctor.IM.dest indexedToggleChild).2 ()


-- @@ L487-492 verbatim
example : (IPFunctor.IM.dest indexedToggleTree).1 = true := by
  change
    (IPFunctor.IM.dest
      (IPFunctor.IM.corec indexedToggleStep false true)).1 = true
  rw [IPFunctor.IM.dest_corec]
  rfl


-- @@ L494-504 verbatim
example : (IPFunctor.IM.dest indexedToggleChild).1 = false := by
  change
    (IPFunctor.IM.dest
      ((IPFunctor.IM.dest
        (IPFunctor.IM.corec indexedToggleStep false true)).2 ())).1 = false
  rw [IPFunctor.IM.dest_corec]
  change
    (IPFunctor.IM.dest
      (IPFunctor.IM.corec indexedToggleStep true false)).1 = false
  rw [IPFunctor.IM.dest_corec]
  rfl


-- @@ L506-509 verbatim
example :
    (IPFunctor.IM.destEquiv (P := IndexedToggle) (i := false)).symm
        (IPFunctor.IM.dest indexedToggleTree) = indexedToggleTree :=
  IPFunctor.IM.mk_dest indexedToggleTree


-- @@ L511-516 verbatim
example :
    IPFunctor.IM.dest
        ((IPFunctor.IM.destEquiv (P := IndexedToggle) (i := false)).symm
          (IPFunctor.IM.dest indexedToggleTree)) =
      IPFunctor.IM.dest indexedToggleTree := by
  exact (IPFunctor.IM.destEquiv (P := IndexedToggle) (i := false)).apply_symm_apply _


-- @@ L518-520 verbatim
/-! The two presentations have different seed-state types and step functions;
their equality is obtained only by matching the indexed branch transition at
every unfolding. -/

-- @@ L521-540 verbatim
example : indexedToggleTree = indexedToggleTreeWrapped := by
  apply IPFunctor.IM.bisim
    (R := fun index left right =>
      ∃ next,
        left = IPFunctor.IM.corec indexedToggleStep index next ∧
        right = IPFunctor.IM.corec indexedToggleStepWrapped index (next, ()))
  · intro index left right h
    rcases h with ⟨next, rfl, rfl⟩
    refine
      ⟨next,
        (fun _ => IPFunctor.IM.corec indexedToggleStep _ (!next)),
        (fun _ => IPFunctor.IM.corec indexedToggleStepWrapped _ (!next, ())),
        ?_, ?_, ?_⟩
    · rw [IPFunctor.IM.dest_corec]
      rfl
    · rw [IPFunctor.IM.dest_corec]
      rfl
    · intro direction
      exact ⟨!next, rfl, rfl⟩
  · exact ⟨true, rfl, rfl⟩


-- @@ L542-552 verbatim
example :
    (Responder.reindexBehavior twoCalls behavior).head.toFunB
        query PUnit.unit = true := by
  change
    (Responder.reindexBehavior twoCalls
      (responder.behavior false)).head.toFunB query PUnit.unit = true
  rw [Responder.reindexBehavior_behavior
    twoCalls responder false]
  change
    (Responder.reindex twoCalls responder).answer false query = true
  rfl


-- @@ L554-556 verbatim
/-! Universe producer canaries: base positions/directions, display
positions/directions, indexed states, and coalgebra witnesses remain
independent. -/


-- @@ L558-558 verbatim
section Universes


-- @@ L560-560 verbatim
universe uI uA uA' uA'' uB uB' uB'' uC uD uC' uD' uC'' uD'' uX uS uF


-- @@ L562-567 verbatim
def indexedMProducer
    {I : Type uI} (P : IPFunctor.Endo I)
    (St : I → Type uX)
    (step : (i : I) → St i → P.Obj St i)
    (i : I) (state : St i) : IPFunctor.IM P i :=
  IPFunctor.IM.corec step i state


-- @@ L569-576 verbatim
def displayedMProducer
    {P : PFunctor.{uA, uB}}
    (S : Display.{uA, uB, uC, uD} P)
    (St : PFunctor.M P → Type uX)
    (step : (tree : PFunctor.M P) → St tree →
      S.Obj St (PFunctor.M.dest tree))
    (tree : PFunctor.M P) (state : St tree) : Display.M S tree :=
  Display.M.corec St step tree state


-- @@ L578-586 verbatim
def toDisplayedBehaviorProducer
    {P : PFunctor.{uA, uB}}
    (S : Display.{uA, uB, uC, uD} P)
    {State : Type uS} (R : Responder State P)
    (I : State → Type uF)
    (displayedR : Display.Coalgebra (Display.responder S) R.out I)
    (state : State) (witness : I state) :
    Display.M (Display.responder S) (R.behavior state) :=
  Responder.toDisplayedBehavior S R I displayedR state witness


-- @@ L588-593 verbatim
def reindexBehaviorProducer
    {P : PFunctor.{uA, uB}} {Q : PFunctor.{uA', uB'}}
    (f : Handler (FreeM Q) P)
    (behavior : PFunctor.M (Q ⊸ y.{uA', uB'})) :
    PFunctor.M (P ⊸ y.{uA, uB}) :=
  Responder.reindexBehavior f behavior


-- @@ L595-603 verbatim
def reindexDisplayedBehaviorProducer
    {P : PFunctor.{uA, uB}} {Q : PFunctor.{uA', uB'}}
    (S : Display.{uA, uB, uC, uD} P)
    (T : Display.{uA', uB', uC', uD'} Q)
    (f : Handler (FreeM Q) P) (df : Display.Handler S T f)
    (behavior : PFunctor.M (Q ⊸ y.{uA', uB'}))
    (displayedBehavior : Display.M (Display.responder T) behavior) :
    Display.M (Display.responder S) (Responder.reindexBehavior f behavior) :=
  Responder.reindexDisplayedBehavior S T f df behavior displayedBehavior


-- @@ L605-615 verbatim
/-- The final target response universe remains independent in ordinary
state-free reindexing composition. -/
theorem reindexBehaviorCompProducer
    {P : PFunctor.{uA, uB}} {Q : PFunctor.{uA', uB}}
    {R : PFunctor.{uA'', uB''}}
    (second : Handler (FreeM R) Q) (first : Handler (FreeM Q) P)
    (behavior : PFunctor.M (R ⊸ y.{uA'', uB''})) :
    Responder.reindexBehavior first
        (Responder.reindexBehavior second behavior) =
      Responder.reindexBehavior (second.comp first) behavior :=
  Responder.reindexBehavior_comp second first behavior


-- @@ L617-638 verbatim
/-- The displayed composition law has the same independent final-target
response universe as its base-handler and coalgebra composition laws. -/
theorem reindexDisplayedBehaviorCompProducer
    {P : PFunctor.{uA, uB}} {Q : PFunctor.{uA', uB}}
    {R : PFunctor.{uA'', uB''}}
    (S : Display.{uA, uB, uC, uD} P)
    (T : Display.{uA', uB, uC', uD'} Q)
    (U : Display.{uA'', uB'', uC'', uD''} R)
    (second : Handler (FreeM R) Q) (dsecond : Display.Handler T U second)
    (first : Handler (FreeM Q) P) (dfirst : Display.Handler S T first)
    (behavior : PFunctor.M (R ⊸ y.{uA'', uB''}))
    (displayedBehavior : Display.M (Display.responder U) behavior) :
    Display.M.transport
        (Responder.reindexBehavior_comp second first behavior)
        (Responder.reindexDisplayedBehavior S T first dfirst
          (Responder.reindexBehavior second behavior)
          (Responder.reindexDisplayedBehavior T U second dsecond
            behavior displayedBehavior)) =
      Responder.reindexDisplayedBehavior S U (second.comp first)
        (dsecond.comp dfirst) behavior displayedBehavior :=
  Responder.reindexDisplayedBehavior_comp S T U second dsecond first dfirst
    behavior displayedBehavior


-- @@ L640-640 verbatim
end Universes


-- @@ L642-642 verbatim
end PFunctor.ResponderBehaviorExample
