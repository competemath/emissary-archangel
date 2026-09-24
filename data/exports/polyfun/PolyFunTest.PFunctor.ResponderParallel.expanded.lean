/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import PolyFun.PFunctor.Display.Parallel.Free
public import PolyFun.PFunctor.Dynamical.Responder.Parallel.Compatibility


-- @@ L12-18 verbatim
/-!
# Regression tests for parallel responder semantics

The examples distinguish sum from one-or-both parallel composition, observe
state freezing in every branch, and exercise ordinary, proof-relevant, and
reindexed execution.
-/


-- @@ L20-20 verbatim
@[expose] public section


-- @@ L22-22 verbatim
namespace PFunctor.ResponderParallelCanary


-- @@ L24-24 verbatim
abbrev Left : PFunctor.{0, 0} := ⟨Bool, fun _ => Bool⟩


-- @@ L26-26 verbatim
abbrev Right : PFunctor.{0, 0} := ⟨PUnit, fun _ => Nat⟩


-- @@ L28-29 verbatim
def leftResponder : Responder Nat Left :=
  Responder.mk' (fun _ query => !query) (fun state _ => state + 1)


-- @@ L31-32 verbatim
def rightResponder : Responder Nat Right :=
  Responder.mk' (fun state _ => state) (fun state _ => state + 10)


-- @@ L34-35 verbatim
def leftProgram : FreeM Left Bool :=
  FreeM.liftBind true FreeM.pure


-- @@ L37-38 verbatim
def rightProgram : FreeM Right Nat :=
  FreeM.liftBind PUnit.unit FreeM.pure


-- @@ L40-41 verbatim
example : (Responder.sum leftResponder rightResponder).answer (0, 5) (.inl true) = false :=
  rfl


-- @@ L43-44 verbatim
example : (Responder.sum leftResponder rightResponder).next (0, 5) (.inl true) = (1, 5) :=
  rfl


-- @@ L46-47 verbatim
example : (Responder.sum leftResponder rightResponder).next (0, 5) (.inr PUnit.unit) = (0, 15) :=
  rfl


-- @@ L49-50 verbatim
example : (Responder.parallel leftResponder rightResponder).next (0, 5) (.left true) = (1, 5) :=
  rfl


-- @@ L52-55 verbatim
example :
    (Responder.parallel leftResponder rightResponder).next
      (0, 5) (.right PUnit.unit) = (0, 15) :=
  rfl


-- @@ L57-60 verbatim
example :
    (Responder.parallel leftResponder rightResponder).next
      (0, 5) (.both true PUnit.unit) = (1, 15) :=
  rfl


-- @@ L62-66 verbatim
example :
    (Responder.parallel leftResponder rightResponder).runFree
      (FreeM.parallel leftProgram rightProgram) (0, 5) =
        ((false, 5), (1, 15)) :=
  rfl


-- @@ L68-72 verbatim
example :
    (Responder.parallel leftResponder rightResponder).runFree
      (FreeM.parallel leftProgram (FreeM.pure 7)) (0, 5) =
        ((false, 7), (1, 5)) :=
  rfl


-- @@ L74-78 verbatim
example :
    (Responder.parallel leftResponder rightResponder).runFree
      (FreeM.parallel (FreeM.pure true) rightProgram) (0, 5) =
        ((true, 5), (0, 15)) :=
  rfl


-- @@ L80-84 verbatim
example : (Responder.terminal (P := Left ∥ Right)).answer
    (Responder.parallelBehavior
      (leftResponder.behavior 0) (rightResponder.behavior 5))
    (.both true PUnit.unit) = (false, 5) :=
  rfl


-- @@ L86-88 verbatim
def leftDisplay : Display Left where
  position _ := PUnit
  direction _ _ _ := PUnit


-- @@ L90-92 verbatim
def rightDisplay : Display Right where
  position _ := PUnit
  direction _ _ _ := PUnit


-- @@ L94-94 verbatim
def leftInvariant (_ : Nat) : Type := PUnit


-- @@ L96-96 verbatim
def rightInvariant (_ : Nat) : Type := PUnit


-- @@ L98-102 verbatim
def displayedLeftResponder :
    Display.Coalgebra (Display.responder leftDisplay)
      leftResponder.out leftInvariant :=
  (Display.responderCoalgebraEquiv leftDisplay leftResponder leftInvariant).symm
    fun _ _ _ _ => (PUnit.unit, PUnit.unit)


-- @@ L104-108 verbatim
def displayedRightResponder :
    Display.Coalgebra (Display.responder rightDisplay)
      rightResponder.out rightInvariant :=
  (Display.responderCoalgebraEquiv rightDisplay rightResponder rightInvariant).symm
    fun _ _ _ _ => (PUnit.unit, PUnit.unit)


-- @@ L110-113 verbatim
def displayedLeftProgram :
    FreeM.Displayed
      (leftDisplay.toDisplayedAlgebra (fun _ => PUnit)) leftProgram :=
  ⟨PUnit.unit, fun answer _ => leftDisplay.leaf _ answer PUnit.unit⟩


-- @@ L115-118 verbatim
def displayedRightProgram :
    FreeM.Displayed
      (rightDisplay.toDisplayedAlgebra (fun _ => PUnit)) rightProgram :=
  ⟨PUnit.unit, fun answer _ => rightDisplay.leaf _ answer PUnit.unit⟩


-- @@ L120-126 verbatim
def displayedParallelProgram :
    FreeM.Displayed
      ((Display.parallelSum leftDisplay rightDisplay).toDisplayedAlgebra
        (fun _ => PUnit × PUnit))
      (FreeM.parallel leftProgram rightProgram) :=
  FreeM.Displayed.parallel leftProgram rightProgram
    displayedLeftProgram displayedRightProgram


-- @@ L128-134 verbatim
def displayedParallelResponder :
    Display.Coalgebra
      (Display.responder (Display.parallelSum leftDisplay rightDisplay))
      (Responder.parallel leftResponder rightResponder).out
      (fun state => leftInvariant state.1 × rightInvariant state.2) :=
  Responder.parallelCoalgebra leftResponder rightResponder
    leftInvariant rightInvariant displayedLeftResponder displayedRightResponder


-- @@ L136-143 verbatim
example :
    Responder.runFreeDisplayed
      (Display.parallelSum leftDisplay rightDisplay)
      (Responder.parallel leftResponder rightResponder)
      displayedParallelResponder displayedParallelProgram
      (0, 5) (PUnit.unit, PUnit.unit) =
        ((PUnit.unit, PUnit.unit), (PUnit.unit, PUnit.unit)) :=
  rfl


-- @@ L145-145 verbatim
def leftIdentityHandler : Handler (FreeM Left) Left := Handler.id Left


-- @@ L147-147 verbatim
def rightIdentityHandler : Handler (FreeM Right) Right := Handler.id Right


-- @@ L149-156 verbatim
example :
    Responder.reindex
        (Handler.parallel leftIdentityHandler rightIdentityHandler)
        (Responder.parallel leftResponder rightResponder) =
      Responder.parallel
        (Responder.reindex leftIdentityHandler leftResponder)
        (Responder.reindex rightIdentityHandler rightResponder) :=
  Responder.reindex_parallel _ _ _ _


-- @@ L158-159 verbatim
/-! Nonidentity compatibility canaries distinguish both handler components,
the one-sided coproduct embedding, and responder-state handoff. -/


-- @@ L161-162 verbatim
def leftNegatingHandler : Handler (FreeM Left) Left := fun query =>
  FreeM.liftBind (!query) fun answer => FreeM.pure (!answer)


-- @@ L164-166 verbatim
def rightTwoCallHandler : Handler (FreeM Right) Right := fun _ =>
  FreeM.liftBind PUnit.unit fun first =>
    FreeM.liftBind PUnit.unit fun second => FreeM.pure (first + second)


-- @@ L168-171 verbatim
def reindexedParallel :=
  Responder.reindex
    (Handler.parallel leftNegatingHandler rightTwoCallHandler)
    (Responder.parallel leftResponder rightResponder)


-- @@ L173-173 verbatim
example : reindexedParallel.answer (0, 5) (.left true) = false := rfl

-- @@ L174-174 verbatim
example : reindexedParallel.next (0, 5) (.left true) = (1, 5) := rfl

-- @@ L175-175 verbatim
example : (show Nat from reindexedParallel.answer (0, 5) (.right PUnit.unit)) = 20 := rfl

-- @@ L176-176 verbatim
example : reindexedParallel.next (0, 5) (.right PUnit.unit) = (0, 25) := rfl

-- @@ L177-177 verbatim
example : reindexedParallel.answer (0, 5) (.both true PUnit.unit) = (false, 20) := rfl

-- @@ L178-178 verbatim
example : reindexedParallel.next (0, 5) (.both true PUnit.unit) = (1, 25) := rfl


-- @@ L180-182 verbatim
def parallelRestrictedToSum :=
  Responder.reindex (Handler.ofLens (Lens.sumToParallel Left Right))
    (Responder.parallel leftResponder rightResponder)


-- @@ L184-184 verbatim
example : parallelRestrictedToSum.answer (0, 5) (.inl true) = false := rfl

-- @@ L185-185 verbatim
example : parallelRestrictedToSum.next (0, 5) (.inl true) = (1, 5) := rfl

-- @@ L186-186 verbatim
example : (show Nat from parallelRestrictedToSum.answer (0, 5) (.inr PUnit.unit)) = 5 := rfl

-- @@ L187-187 verbatim
example : parallelRestrictedToSum.next (0, 5) (.inr PUnit.unit) = (0, 15) := rfl

-- @@ L188-189 verbatim
example : Responder.sum leftResponder rightResponder = parallelRestrictedToSum :=
  Responder.sum_eq_reindex_parallel leftResponder rightResponder


-- @@ L191-192 verbatim
/-! Nonconstant dependent contracts make every proof-relevant branch and
continuation observable. -/


-- @@ L194-196 verbatim
def dependentLeftDisplay : Display Left where
  position operation := if operation then Nat else Bool
  direction _ _ answer := if answer then Fin 2 else Fin 3


-- @@ L198-200 verbatim
def dependentRightDisplay : Display Right where
  position _ := String
  direction _ _ answer := Fin (answer + 1)


-- @@ L202-203 verbatim
def leftPost (answer : Bool) : if answer then Fin 2 else Fin 3 := by
  cases answer <;> exact ⟨0, Nat.zero_lt_succ _⟩


-- @@ L205-206 verbatim
def rightPost (answer : Nat) : Fin (answer + 1) :=
  ⟨0, Nat.zero_lt_succ _⟩


-- @@ L208-208 verbatim
def leftContractTrue : dependentLeftDisplay.position true := (5 : Nat)

-- @@ L209-209 verbatim
def leftContractFalse : dependentLeftDisplay.position false := true

-- @@ L210-210 verbatim
def rightContract : dependentRightDisplay.position PUnit.unit := "right"


-- @@ L212-212 verbatim
def dependentLeftInvariant (state : Nat) : Type := Fin (state + 2)

-- @@ L213-213 verbatim
def dependentRightInvariant (state : Nat) : Type := Fin (state + 2)


-- @@ L215-220 verbatim
def dependentLeftCoalgebra :
    Display.Coalgebra (Display.responder dependentLeftDisplay)
      leftResponder.out dependentLeftInvariant :=
  (Display.responderCoalgebraEquiv dependentLeftDisplay
    leftResponder dependentLeftInvariant).symm fun _ _ operation _ =>
      ⟨leftPost (!operation), ⟨0, Nat.zero_lt_succ _⟩⟩


-- @@ L222-227 verbatim
def dependentRightCoalgebra :
    Display.Coalgebra (Display.responder dependentRightDisplay)
      rightResponder.out dependentRightInvariant :=
  (Display.responderCoalgebraEquiv dependentRightDisplay
    rightResponder dependentRightInvariant).symm fun state _ _ _ =>
      ⟨rightPost state, ⟨0, Nat.zero_lt_succ _⟩⟩


-- @@ L229-229 verbatim
def leftWitness0 : dependentLeftInvariant 0 := ⟨1, by decide⟩

-- @@ L230-230 verbatim
def leftWitness1 : dependentLeftInvariant 1 := ⟨0, Nat.zero_lt_succ _⟩

-- @@ L231-231 verbatim
def rightWitness5 : dependentRightInvariant 5 := ⟨1, by decide⟩

-- @@ L232-232 verbatim
def rightWitness15 : dependentRightInvariant 15 := ⟨0, Nat.zero_lt_succ _⟩


-- @@ L234-237 verbatim
def dependentSumCoalgebra :=
  Responder.sumCoalgebra leftResponder rightResponder
    dependentLeftInvariant dependentRightInvariant
    dependentLeftCoalgebra dependentRightCoalgebra


-- @@ L239-242 verbatim
def dependentParallelCoalgebra :=
  Responder.parallelCoalgebra leftResponder rightResponder
    dependentLeftInvariant dependentRightInvariant
    dependentLeftCoalgebra dependentRightCoalgebra


-- @@ L244-252 verbatim
example :
    (Display.responderCoalgebraEquiv
      (Display.sum dependentLeftDisplay dependentRightDisplay)
      (Responder.sum leftResponder rightResponder)
      (fun state => dependentLeftInvariant state.1 ×
        dependentRightInvariant state.2))
      dependentSumCoalgebra (0, 5) (leftWitness0, rightWitness5)
      (.inl true) (ULift.up leftContractTrue) =
        (ULift.up (leftPost false), (leftWitness1, rightWitness5)) := rfl


-- @@ L254-262 verbatim
example :
    (Display.responderCoalgebraEquiv
      (Display.sum dependentLeftDisplay dependentRightDisplay)
      (Responder.sum leftResponder rightResponder)
      (fun state => dependentLeftInvariant state.1 ×
        dependentRightInvariant state.2))
      dependentSumCoalgebra (0, 5) (leftWitness0, rightWitness5)
      (.inr PUnit.unit) (ULift.up rightContract) =
        (ULift.up (rightPost 5), (leftWitness0, rightWitness15)) := rfl


-- @@ L264-272 verbatim
example :
    (Display.responderCoalgebraEquiv
      (Display.parallelSum dependentLeftDisplay dependentRightDisplay)
      (Responder.parallel leftResponder rightResponder)
      (fun state => dependentLeftInvariant state.1 ×
        dependentRightInvariant state.2))
      dependentParallelCoalgebra (0, 5) (leftWitness0, rightWitness5)
      (.left true) (ULift.up leftContractTrue) =
        (ULift.up (leftPost false), (leftWitness1, rightWitness5)) := rfl


-- @@ L274-282 verbatim
example :
    (Display.responderCoalgebraEquiv
      (Display.parallelSum dependentLeftDisplay dependentRightDisplay)
      (Responder.parallel leftResponder rightResponder)
      (fun state => dependentLeftInvariant state.1 ×
        dependentRightInvariant state.2))
      dependentParallelCoalgebra (0, 5) (leftWitness0, rightWitness5)
      (.right PUnit.unit) (ULift.up rightContract) =
        (ULift.up (rightPost 5), (leftWitness0, rightWitness15)) := rfl


-- @@ L284-292 verbatim
example :
    (Display.responderCoalgebraEquiv
      (Display.parallelSum dependentLeftDisplay dependentRightDisplay)
      (Responder.parallel leftResponder rightResponder)
      (fun state => dependentLeftInvariant state.1 ×
        dependentRightInvariant state.2))
      dependentParallelCoalgebra (0, 5) (leftWitness0, rightWitness5)
      (.both true PUnit.unit) (leftContractTrue, rightContract) =
        ((leftPost false, rightPost 5), (leftWitness1, rightWitness15)) := rfl


-- @@ L294-296 verbatim
def dependentLeftDisplayedBehavior :=
  Responder.toDisplayedBehavior dependentLeftDisplay leftResponder
    dependentLeftInvariant dependentLeftCoalgebra 0 leftWitness0


-- @@ L298-300 verbatim
def dependentRightDisplayedBehavior :=
  Responder.toDisplayedBehavior dependentRightDisplay rightResponder
    dependentRightInvariant dependentRightCoalgebra 5 rightWitness5


-- @@ L302-305 verbatim
def dependentSumDisplayedBehavior :=
  Responder.sumDisplayedBehavior dependentLeftDisplay dependentRightDisplay
    (leftResponder.behavior 0) dependentLeftDisplayedBehavior
    (rightResponder.behavior 5) dependentRightDisplayedBehavior


-- @@ L307-310 verbatim
def dependentParallelDisplayedBehavior :=
  Responder.parallelDisplayedBehavior dependentLeftDisplay dependentRightDisplay
    (leftResponder.behavior 0) dependentLeftDisplayedBehavior
    (rightResponder.behavior 5) dependentRightDisplayedBehavior


-- @@ L312-313 verbatim
example : dependentSumDisplayedBehavior.head (.inl true)
    (ULift.up leftContractTrue) = ULift.up (leftPost false) := rfl


-- @@ L315-316 verbatim
example : dependentSumDisplayedBehavior.head (.inr PUnit.unit)
    (ULift.up rightContract) = ULift.up (rightPost 5) := rfl


-- @@ L318-319 verbatim
example : dependentParallelDisplayedBehavior.head (.left true)
    (ULift.up leftContractTrue) = ULift.up (leftPost false) := rfl


-- @@ L321-322 verbatim
example : dependentParallelDisplayedBehavior.head (.right PUnit.unit)
    (ULift.up rightContract) = ULift.up (rightPost 5) := rfl


-- @@ L324-325 verbatim
example : dependentParallelDisplayedBehavior.head (.both true PUnit.unit)
    (leftContractTrue, rightContract) = (leftPost false, rightPost 5) := rfl


-- @@ L327-335 verbatim
example :
    (Responder.respondDisplayed
      (Display.parallelSum dependentLeftDisplay dependentRightDisplay)
      (Responder.respondDisplayed
        (Display.parallelSum dependentLeftDisplay dependentRightDisplay)
        dependentParallelDisplayedBehavior (.left true)
        (ULift.up leftContractTrue)).2
      (.right PUnit.unit) (ULift.up rightContract)).1 =
        ULift.up (rightPost 5) := rfl


-- @@ L337-345 verbatim
example :
    (Responder.respondDisplayed
      (Display.parallelSum dependentLeftDisplay dependentRightDisplay)
      (Responder.respondDisplayed
        (Display.parallelSum dependentLeftDisplay dependentRightDisplay)
        dependentParallelDisplayedBehavior (.right PUnit.unit)
        (ULift.up rightContract)).2
      (.right PUnit.unit) (ULift.up rightContract)).1 =
        ULift.up (rightPost 15) := rfl


-- @@ L347-355 verbatim
example :
    (Responder.respondDisplayed
      (Display.parallelSum dependentLeftDisplay dependentRightDisplay)
      (Responder.respondDisplayed
        (Display.parallelSum dependentLeftDisplay dependentRightDisplay)
        dependentParallelDisplayedBehavior (.both true PUnit.unit)
        (leftContractTrue, rightContract)).2
      (.right PUnit.unit) (ULift.up rightContract)).1 =
        ULift.up (rightPost 15) := rfl


-- @@ L357-357 verbatim
namespace UniverseCanary


-- @@ L359-359 verbatim
universe uA₁ uA₂ uB uS₁ uS₂ uC₁ uD₁ uC₂ uD₂ uI uJ uE uF


-- @@ L361-366 verbatim
def parallelResponder
    {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}}
    {State₁ : Type uS₁} {State₂ : Type uS₂} :
    Responder State₁ P → Responder State₂ Q →
      Responder (State₁ × State₂) (P ∥ Q) :=
  Responder.parallel


-- @@ L368-379 verbatim
def sumCoalgebra
    {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}}
    {S : Display.{uA₁, uB, uC₁, uD₁} P}
    {T : Display.{uA₂, uB, uC₂, uD₂} Q}
    {State₁ : Type uS₁} {State₂ : Type uS₂}
    (left : Responder State₁ P) (right : Responder State₂ Q)
    (I : State₁ → Type uI) (J : State₂ → Type uJ)
    (dLeft : Display.Coalgebra (Display.responder S) left.out I)
    (dRight : Display.Coalgebra (Display.responder T) right.out J) :
    Display.Coalgebra (Display.responder (Display.sum S T))
      (Responder.sum left right).out (fun state => I state.1 × J state.2) :=
  Responder.sumCoalgebra left right I J dLeft dRight


-- @@ L381-393 verbatim
def parallelCoalgebra
    {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}}
    {S : Display.{uA₁, uB, uC₁, uD₁} P}
    {T : Display.{uA₂, uB, uC₂, uD₂} Q}
    {State₁ : Type uS₁} {State₂ : Type uS₂}
    (left : Responder State₁ P) (right : Responder State₂ Q)
    (I : State₁ → Type uI) (J : State₂ → Type uJ)
    (dLeft : Display.Coalgebra (Display.responder S) left.out I)
    (dRight : Display.Coalgebra (Display.responder T) right.out J) :
    Display.Coalgebra (Display.responder (Display.parallelSum S T))
      (Responder.parallel left right).out
      (fun state => I state.1 × J state.2) :=
  Responder.parallelCoalgebra left right I J dLeft dRight


-- @@ L395-400 verbatim
def parallelBehavior
    {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}} :
    PFunctor.M (P ⊸ y.{uA₁, uB}) →
    PFunctor.M (Q ⊸ y.{uA₂, uB}) →
      PFunctor.M ((P ∥ Q) ⊸ y.{max uA₁ uA₂, uB}) :=
  Responder.parallelBehavior


-- @@ L402-412 verbatim
def parallelDisplayedBehavior
    {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}}
    (S : Display.{uA₁, uB, uC₁, uD₁} P)
    (T : Display.{uA₂, uB, uC₂, uD₂} Q)
    (left : PFunctor.M (P ⊸ y.{uA₁, uB}))
    (dLeft : Display.M (Display.responder S) left)
    (right : PFunctor.M (Q ⊸ y.{uA₂, uB}))
    (dRight : Display.M (Display.responder T) right) :
    Display.M (Display.responder (Display.parallelSum S T))
      (Responder.parallelBehavior left right) :=
  Responder.parallelDisplayedBehavior S T left dLeft right dRight


-- @@ L414-424 verbatim
def sumDisplayedBehavior
    {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}}
    (S : Display.{uA₁, uB, uC₁, uD₁} P)
    (T : Display.{uA₂, uB, uC₂, uD₂} Q)
    (left : PFunctor.M (P ⊸ y.{uA₁, uB}))
    (dLeft : Display.M (Display.responder S) left)
    (right : PFunctor.M (Q ⊸ y.{uA₂, uB}))
    (dRight : Display.M (Display.responder T) right) :
    Display.M (Display.responder (Display.sum S T))
      (Responder.sumBehavior left right) :=
  Responder.sumDisplayedBehavior S T left dLeft right dRight


-- @@ L426-439 verbatim
theorem runFreeParallel
    {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}}
    {State₁ : Type uS₁} {State₂ : Type uS₂}
    (left : Responder State₁ P) (right : Responder State₂ Q)
    (leftProgram : FreeM P (ULift.{uE} PUnit))
    (rightProgram : FreeM Q (ULift.{uF} PUnit))
    (leftState : State₁) (rightState : State₂) :
    (Responder.parallel left right).runFree
        (FreeM.parallel leftProgram rightProgram) (leftState, rightState) =
      let leftResult := left.runFree leftProgram leftState
      let rightResult := right.runFree rightProgram rightState
      ((leftResult.1, rightResult.1), (leftResult.2, rightResult.2)) :=
  Responder.runFree_parallel left right leftProgram rightProgram
    leftState rightState


-- @@ L441-441 verbatim
end UniverseCanary


-- @@ L443-443 verbatim
end PFunctor.ResponderParallelCanary
