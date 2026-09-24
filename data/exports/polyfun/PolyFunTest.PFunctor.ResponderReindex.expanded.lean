/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import PolyFun.PFunctor.PatternRunsOnMatter.Display


-- @@ L11-17 verbatim
/-!
# Responder reindexing worked examples

Worked examples for base and proof-relevant responder reindexing. Contract
evidence depends on both the supplied precondition and actual answer; invariant
evidence is state-indexed data and affects the next witness.
-/


-- @@ L19-19 verbatim
@[expose] public section


-- @@ L21-23 verbatim
namespace PFunctor.ResponderReindexExample

-- Lean 4.33: the examples below unfold `Interface` at implicit transparency.

-- @@ L24-29 verbatim
@[implicit_reducible]
def Interface : PFunctor where
  A := Unit
  B := fun _ => Bool

-- Lean 4.33: the examples below unfold `contract` at implicit transparency.

-- @@ L30-33 verbatim
@[implicit_reducible]
def contract : Display Interface where
  position _ := Bool
  direction _ expected answer := if expected = answer then Fin 2 else Fin 3


-- @@ L35-38 verbatim
def directionVal (expected answer : Bool)
    (evidence : contract.direction () expected answer) : Nat := by
  change (if expected = answer then Fin 2 else Fin 3) at evidence
  split at evidence <;> exact evidence.val


-- @@ L40-45 verbatim
def directionFromNat (expected answer : Bool) (value : Nat) :
    contract.direction () expected answer := by
  simp only [contract]
  split
  · exact ⟨value % 2, Nat.mod_lt _ (by decide)⟩
  · exact ⟨value % 3, Nat.mod_lt _ (by decide)⟩


-- @@ L47-48 verbatim
def target : Responder Bool Interface :=
  Responder.mk' (fun state _ => state) (fun state _ => !state)


-- @@ L50-50 verbatim
def Invariant (state : Bool) := if state then Fin 2 else Fin 3


-- @@ L52-54 verbatim
def invariantVal (state : Bool) (witness : Invariant state) : Nat := by
  simp only [Invariant] at witness
  split at witness <;> exact witness.val


-- @@ L56-60 verbatim
def invariantFromNat (state : Bool) (value : Nat) : Invariant state := by
  simp only [Invariant]
  split
  · exact ⟨value % 2, Nat.mod_lt _ (by decide)⟩
  · exact ⟨value % 3, Nat.mod_lt _ (by decide)⟩


-- @@ L62-72 verbatim
def targetObligation :
    (state : Bool) → Invariant state →
      (query : Unit) → (precondition : Bool) →
        contract.direction query precondition (target.answer state query) ×
          Invariant (target.next state query) :=
  fun state witness query precondition =>
    let post := directionFromNat precondition (target.answer state query)
      (invariantVal state witness)
    ⟨post, invariantFromNat (target.next state query)
      (invariantVal state witness + directionVal precondition
        (target.answer state query) post)⟩


-- @@ L74-77 verbatim
def displayedTarget :
    Display.Coalgebra (Display.responder contract) target.out Invariant :=
  (Display.responderCoalgebraEquiv contract target Invariant).symm
    targetObligation


-- @@ L79-84 verbatim
/-- Two target calls; both the returned answers and displayed evidence flow
into the source leaf. -/
def twoCalls : Handler (FreeM Interface) Interface :=
  fun _ => .liftBind () fun first =>
    .liftBind () fun second =>
      .pure (Bool.xor first second)


-- @@ L86-90 verbatim
/-- A concrete complete path through the encoded two-call program.  Its two
directions deliberately differ so that the backward component of
`Handler.toFreeLens` cannot silently swap or duplicate answers. -/
def twoCallsPath : FreeM.Path (FreeP.encode (twoCalls ())).1 :=
  ⟨false, ⟨true, ⟨⟩⟩⟩


-- @@ L92-97 verbatim
/-- The forward component of the structural handler/lens equivalence is the
unlabelled program shape. -/
example :
    (Handler.toFreeLens twoCalls).toFunA () =
      (FreeP.encode (twoCalls ())).1 :=
  rfl


-- @@ L99-103 verbatim
/-- The backward component reads the source result at the selected complete
path; here `false xor true` is observable. -/
example :
    (Handler.toFreeLens twoCalls).toFunB () twoCallsPath = true :=
  rfl


-- @@ L105-107 verbatim
/-- Decoding after encoding preserves a nontrivial handler extensionally. -/
example : Handler.ofFreeLens (Handler.toFreeLens twoCalls) = twoCalls :=
  Handler.freeLensEquiv.left_inv twoCalls


-- @@ L109-114 verbatim
/-- Encoding after decoding preserves a nontrivial lens extensionally. -/
example :
    Handler.toFreeLens
        (Handler.ofFreeLens (Handler.toFreeLens twoCalls)) =
      Handler.toFreeLens twoCalls :=
  Handler.freeLensEquiv.right_inv (Handler.toFreeLens twoCalls)


-- @@ L116-124 verbatim
def displayedTwoCalls : Display.Handler contract contract twoCalls :=
  fun _ sourcePrecondition =>
    ⟨sourcePrecondition, fun first firstEvidence =>
      ⟨first, fun second secondEvidence =>
        contract.leaf (contract.direction () sourcePrecondition)
          (Bool.xor first second)
          (directionFromNat sourcePrecondition (Bool.xor first second)
            (directionVal sourcePrecondition first firstEvidence +
              directionVal first second secondEvidence))⟩⟩


-- @@ L126-128 verbatim
/-- A separate nonidentity handler for composition-law canaries. -/
def negateCall : Handler (FreeM Interface) Interface :=
  fun _ => .liftBind () fun answer => .pure (!answer)


-- @@ L130-135 verbatim
def displayedNegateCall : Display.Handler contract contract negateCall :=
  fun _ sourcePrecondition =>
    ⟨sourcePrecondition, fun answer evidence =>
      contract.leaf (contract.direction () sourcePrecondition) (!answer)
        (directionFromNat sourcePrecondition (!answer)
          (directionVal sourcePrecondition answer evidence))⟩


-- @@ L137-138 verbatim
example : target.runFree (twoCalls ()) false = (true, false) :=
  rfl


-- @@ L140-140 verbatim
def source := Responder.reindex twoCalls target


-- @@ L142-145 verbatim
/-- G5's categorical reconstruction reaches the same responder, including
the nontrivial answer and returned state below. -/
example : Responder.reindexViaRunAgainst twoCalls target = source :=
  Responder.reindexViaRunAgainst_eq_reindex twoCalls target


-- @@ L147-150 verbatim
example : Responder.runAgainstResult target (twoCalls ()) false =
    (true, false) := by
  rw [Responder.runAgainstResult_eq_runFree]
  rfl


-- @@ L152-153 verbatim
example : source.answer false () = true :=
  rfl


-- @@ L155-156 verbatim
example : source.next false () = false :=
  rfl


-- @@ L158-159 verbatim
def initialWitness : Invariant false :=
  invariantFromNat false 1


-- @@ L161-163 verbatim
def displayedExecution :=
  Responder.runFreeDisplayed contract target displayedTarget
    (displayedTwoCalls () false) false initialWitness


-- @@ L165-167 verbatim
def patternDisplayedExecution :=
  Responder.runAgainstDisplayed contract target displayedTarget
    (displayedTwoCalls () false) false initialWitness


-- @@ L169-171 verbatim
def displayedSource :=
  Responder.reindexCoalgebra contract contract twoCalls displayedTwoCalls
    target displayedTarget


-- @@ L173-178 verbatim
def transportedCoalgebraExecution :=
  Responder.transportRunEvidence (contract.direction () false) Invariant
    (Responder.runAgainstResult_eq_runFree
      target (twoCalls ()) false).symm
    ((Display.responderCoalgebraEquiv contract source Invariant)
      displayedSource false initialWitness () false)


-- @@ L180-186 verbatim
/-- The state-presented displayed action is directly the transported
displayed responder-reindexing obligation, with nonconstant postcondition and
state-invariant evidence. -/
example : patternDisplayedExecution = transportedCoalgebraExecution :=
  Responder.runAgainstDisplayed_eq_reindexCoalgebra contract contract
    twoCalls displayedTwoCalls target displayedTarget false initialWitness
    () false


-- @@ L188-196 verbatim
/-- Both proof-relevant components survive transport through the G5
Pattern-Runs-on-Matter identification. -/
example :
    Responder.transportRunEvidence (contract.direction () false) Invariant
        (Responder.runAgainstResult_eq_runFree
          target (twoCalls ()) false)
        patternDisplayedExecution = displayedExecution :=
  Responder.runAgainstDisplayed_eq_runFreeDisplayed contract target
    displayedTarget (displayedTwoCalls () false) false initialWitness


-- @@ L198-200 verbatim
example : directionVal false (target.runFree (twoCalls ()) false).1
    displayedExecution.1 = 1 :=
  rfl


-- @@ L202-204 verbatim
example : invariantVal (target.runFree (twoCalls ()) false).2
    displayedExecution.2 = 0 :=
  rfl


-- @@ L206-216 verbatim
example : directionVal false (target.runFree (twoCalls ()) false).1
    (Responder.transportRunEvidence (contract.direction () false) Invariant
      (Responder.runAgainstResult_eq_runFree target (twoCalls ()) false)
      transportedCoalgebraExecution).1 = 1 := by
  rw [← show patternDisplayedExecution = transportedCoalgebraExecution from
    Responder.runAgainstDisplayed_eq_reindexCoalgebra contract contract
      twoCalls displayedTwoCalls target displayedTarget false initialWitness
      () false]
  unfold patternDisplayedExecution
  rw [Responder.runAgainstDisplayed_eq_runFreeDisplayed]
  rfl


-- @@ L218-228 verbatim
example : invariantVal (target.runFree (twoCalls ()) false).2
    (Responder.transportRunEvidence (contract.direction () false) Invariant
      (Responder.runAgainstResult_eq_runFree target (twoCalls ()) false)
      transportedCoalgebraExecution).2 = 0 := by
  rw [← show patternDisplayedExecution = transportedCoalgebraExecution from
    Responder.runAgainstDisplayed_eq_reindexCoalgebra contract contract
      twoCalls displayedTwoCalls target displayedTarget false initialWitness
      () false]
  unfold patternDisplayedExecution
  rw [Responder.runAgainstDisplayed_eq_runFreeDisplayed]
  rfl


-- @@ L230-233 verbatim
example : directionVal false (source.answer false ())
    ((Display.responderCoalgebraEquiv contract source Invariant)
      displayedSource false initialWitness () false).1 = 1 :=
  rfl


-- @@ L235-238 verbatim
example : invariantVal (source.next false ())
    ((Display.responderCoalgebraEquiv contract source Invariant)
      displayedSource false initialWitness () false).2 = 0 :=
  rfl


-- @@ L240-243 verbatim
example :
    Responder.reindex twoCalls (Responder.reindex negateCall target) =
      Responder.reindex (negateCall.comp twoCalls) target :=
  Responder.reindex_comp negateCall twoCalls target


-- @@ L245-252 verbatim
/-- The free-handler encoding uses the existing substitution fold for
categorical composition. -/
example :
    Handler.toFreeLens (negateCall.comp twoCalls) =
      FreeP.foldLens (FreeP.substMonoid Interface)
          (Handler.toFreeLens negateCall) ∘ₗ
        Handler.toFreeLens twoCalls :=
  Handler.toFreeLens_comp negateCall twoCalls


-- @@ L254-264 verbatim
/-- Proof-relevant displayed composition is associative only after transport
along the ordinary handler law; this canary uses nonconstant evidence. -/
example :
    Display.Handler.transport
        (Handler.comp_assoc twoCalls negateCall twoCalls)
        ((displayedTwoCalls.comp displayedNegateCall).comp
          displayedTwoCalls) =
      displayedTwoCalls.comp
        (displayedNegateCall.comp displayedTwoCalls) :=
  Display.Handler.comp_assoc displayedTwoCalls displayedNegateCall
    displayedTwoCalls


-- @@ L266-269 verbatim
/-! These committed observations make handler-composition order independently
falsifiable.  Starting from `false`, interpreting `twoCalls` through
`negateCall` returns `true`, while interpreting `negateCall` through
`twoCalls` returns `false`; both executions return to state `false`. -/


-- @@ L271-272 verbatim
example : target.runFree ((negateCall.comp twoCalls) ()) false = (true, false) :=
  rfl


-- @@ L274-275 verbatim
example : target.runFree ((twoCalls.comp negateCall) ()) false = (false, false) :=
  rfl


-- @@ L277-286 verbatim
example :
    (Display.responderCoalgebraEquiv contract
      (Responder.reindex (Handler.id Interface) target) Invariant
      (Responder.reindexCoalgebra contract contract (Handler.id Interface)
        (Display.Handler.id contract) target displayedTarget)
      false initialWitness () false) =
    (Display.responderCoalgebraEquiv contract target Invariant displayedTarget
      false initialWitness () false) :=
  Responder.reindexCoalgebra_id_obligation contract target displayedTarget
    false initialWitness () false


-- @@ L288-303 verbatim
/-- The transport-sensitive displayed execution theorem is exercised directly
on a two-node source program and a nonidentity reindexing handler. -/
example :
    Responder.transportRunEvidence (contract.direction () false) Invariant
        (Responder.runFree_reindex negateCall target (twoCalls ()) false)
        (Responder.runFreeDisplayed contract
          (Responder.reindex negateCall target)
          (Responder.reindexCoalgebra contract contract negateCall
            displayedNegateCall target displayedTarget)
          (displayedTwoCalls () false) false initialWitness) =
      Responder.runFreeDisplayed contract target displayedTarget
        (contract.liftM contract (twoCalls ()) (displayedTwoCalls () false)
          negateCall displayedNegateCall) false initialWitness :=
  Responder.runFreeDisplayed_reindex contract contract negateCall
    displayedNegateCall target displayedTarget (twoCalls ())
    (displayedTwoCalls () false) false initialWitness


-- @@ L305-308 verbatim
/-! Observe both proof-relevant components of the transported fusion result,
independently of the fusion theorem.  This catches implementations that erase
or mis-route postcondition or invariant data even if a theorem is changed in
lockstep with the implementation. -/


-- @@ L310-317 verbatim
def displayedFusionLeft :=
  Responder.transportRunEvidence (contract.direction () false) Invariant
      (Responder.runFree_reindex negateCall target (twoCalls ()) false)
      (Responder.runFreeDisplayed contract
        (Responder.reindex negateCall target)
        (Responder.reindexCoalgebra contract contract negateCall
          displayedNegateCall target displayedTarget)
        (displayedTwoCalls () false) false initialWitness)


-- @@ L319-322 verbatim
def displayedFusionRight :=
  Responder.runFreeDisplayed contract target displayedTarget
    (contract.liftM contract (twoCalls ()) (displayedTwoCalls () false)
      negateCall displayedNegateCall) false initialWitness


-- @@ L324-327 verbatim
example : directionVal false
    (target.runFree ((twoCalls ()).liftM negateCall) false).1
    displayedFusionLeft.1 = 1 :=
  rfl


-- @@ L329-332 verbatim
example : invariantVal
    (target.runFree ((twoCalls ()).liftM negateCall) false).2
    displayedFusionLeft.2 = 0 :=
  rfl


-- @@ L334-337 verbatim
example : directionVal false
    (target.runFree ((twoCalls ()).liftM negateCall) false).1
    displayedFusionRight.1 = 1 :=
  rfl


-- @@ L339-342 verbatim
example : invariantVal
    (target.runFree ((twoCalls ()).liftM negateCall) false).2
    displayedFusionRight.2 = 0 :=
  rfl


-- @@ L344-365 verbatim
/-- The displayed composition law is exercised with two nonidentity programs
and response-dependent evidence. -/
example :
    Responder.transportRunEvidence (contract.direction () false) Invariant
        (Responder.runFree_reindex negateCall target (twoCalls ()) false)
        ((Display.responderCoalgebraEquiv contract
          (Responder.reindex twoCalls (Responder.reindex negateCall target))
          Invariant)
          (Responder.reindexCoalgebra contract contract twoCalls
            displayedTwoCalls (Responder.reindex negateCall target)
            (Responder.reindexCoalgebra contract contract negateCall
              displayedNegateCall target displayedTarget))
          false initialWitness () false) =
      (Display.responderCoalgebraEquiv contract
        (Responder.reindex (negateCall.comp twoCalls) target) Invariant)
        (Responder.reindexCoalgebra contract contract
          (negateCall.comp twoCalls)
          (displayedNegateCall.comp displayedTwoCalls) target displayedTarget)
        false initialWitness () false :=
  Responder.reindexCoalgebra_comp_obligation contract contract contract
    twoCalls displayedTwoCalls negateCall displayedNegateCall target
    displayedTarget false initialWitness () false


-- @@ L367-367 verbatim
/-! Producer-level canaries preserve all compatible universe separation. -/


-- @@ L369-369 verbatim
universe uA uA' uA'' uA''' uB uB' uC uD uC' uD' uE uF uS uV


-- @@ L371-371 verbatim
section UniverseCanary


-- @@ L373-373 verbatim
variable {P : PFunctor.{uA, uB}} {Q : PFunctor.{uA', uB'}}

-- @@ L374-374 verbatim
variable {State : Type uS}


-- @@ L376-378 verbatim
def universeFreeLensEquiv :
    Handler (FreeM Q) P ≃ Lens P (FreeP Q) :=
  Handler.freeLensEquiv


-- @@ L380-385 verbatim
def universeDisplayHandlerTransport
    (S : Display.{uA, uB, uC, uD} P)
    (T : Display.{uA', uB', uC', uD'} Q)
    {f g : Handler (FreeM Q) P} (h : f = g)
    (df : Display.Handler S T f) : Display.Handler S T g :=
  Display.Handler.transport (S := S) (T := T) h df


-- @@ L387-393 verbatim
example
    (S : Display.{uA, uB, uC, uD} P)
    (T : Display.{uA', uB', uC', uD'} Q)
    {f : Handler (FreeM Q) P} (df : Display.Handler S T f) :
    Display.Handler.transport (Handler.comp_id f)
        (df.comp (Display.Handler.id S)) = df :=
  Display.Handler.comp_id (S := S) (T := T) df


-- @@ L395-410 verbatim
example
    {Middle : PFunctor.{uA', uB}} {Third : PFunctor.{uA'', uB}}
    {Target : PFunctor.{uA''', uB'}}
    (S : Display.{uA, uB, uC, uD} P)
    (T : Display.{uA', uB, uC', uD'} Middle)
    (U : Display.{uA'', uB, uE, uF} Third)
    (W : Display.{uA''', uB', uE, uF} Target)
    {f : Handler (FreeM Middle) P}
    {g : Handler (FreeM Third) Middle}
    {h : Handler (FreeM Target) Third}
    (df : Display.Handler S T f)
    (dg : Display.Handler T U g)
    (dh : Display.Handler U W h) :
    Display.Handler.transport (Handler.comp_assoc h g f)
        ((dh.comp dg).comp df) = dh.comp (dg.comp df) :=
  Display.Handler.comp_assoc (S := S) (T := T) (U := U) (W := W) df dg dh


-- @@ L412-416 verbatim
def universeHandlerCompFinal
    {Middle : PFunctor.{uA', uB}} {Target : PFunctor.{uA'', uB'}}
    (second : Handler (FreeM Target) Middle)
    (first : Handler (FreeM Middle) P) : Handler (FreeM Target) P :=
  second.comp first


-- @@ L418-427 verbatim
/-- `FreeM.liftM_comp` is an arbitrary-lawful-monad theorem, not merely a
composition theorem specialized to a second free monad. -/
theorem universeLiftMCompOption
    {Middle : PFunctor.{uA', uB}} {E : Type uB}
    (program : FreeM P E)
    (first : (a : P.A) → FreeM Middle (P.B a))
    (second : (a : Middle.A) → Option (Middle.B a)) :
    (program.liftM first).liftM second =
      program.liftM (fun a ↦ (first a).liftM second) :=
  FreeM.liftM_comp program first second


-- @@ L429-432 verbatim
def universeRunFree {E : Type uV}
    (R : Responder State Q) (program : FreeM Q E) (state : State) :
    E × State :=
  R.runFree program state


-- @@ L434-436 verbatim
def universeReindex (f : Handler (FreeM Q) P) (R : Responder State Q) :
    Responder State P :=
  Responder.reindex f R


-- @@ L438-448 verbatim
def universeRunFreeDisplayed
    (T : Display.{uA', uB', uC', uD'} Q)
    (R : Responder State Q)
    {I : State → Type uF}
    (displayedR : Display.Coalgebra (Display.responder T) R.out I)
    {E : Type uV} {F : E → Type uE}
    {program : FreeM Q E}
    (displayedProgram : FreeM.Displayed (T.toDisplayedAlgebra F) program)
    (state : State) (witness : I state) :
    F (R.runFree program state).1 × I (R.runFree program state).2 :=
  Responder.runFreeDisplayed T R displayedR displayedProgram state witness


-- @@ L450-458 verbatim
def universeReindexCoalgebra
    (S : Display.{uA, uB, uC, uD} P)
    (T : Display.{uA', uB', uC', uD'} Q)
    (f : Handler (FreeM Q) P) (df : Display.Handler S T f)
    (R : Responder State Q)
    {I : State → Type uF}
    (displayedR : Display.Coalgebra (Display.responder T) R.out I) :
    Display.Coalgebra (Display.responder S) (Responder.reindex f R).out I :=
  Responder.reindexCoalgebra S T f df R displayedR


-- @@ L460-475 verbatim
example
    {Middle : PFunctor.{uA', uB}} {Target : PFunctor.{uA'', uB'}}
    (S : Display.{uA, uB, uC, uD} P)
    (T : Display.{uA', uB, uC', uD'} Middle)
    (U : Display.{uA'', uB', uC', uD'} Target)
    (first : Handler (FreeM Middle) P)
    (dfirst : Display.Handler S T first)
    (second : Handler (FreeM Target) Middle)
    (dsecond : Display.Handler T U second)
    (R : Responder State Target)
    {I : State → Type uF}
    (displayedR : Display.Coalgebra (Display.responder U) R.out I)
    (state : State) (witness : I state)
    (query : P.A) (contract : S.position query) :=
  Responder.reindexCoalgebra_comp_obligation S T U first dfirst second
    dsecond R displayedR state witness query contract


-- @@ L477-480 verbatim
def universeRunAgainstProgramObj {E : Type uV}
    (R : Responder State Q) (program : FreeM Q E) (state : State) :
    (FreeP y.{uA', uB'}).Obj (E × State) :=
  Responder.runAgainstProgramObj R program state


-- @@ L482-491 verbatim
def universeRunAgainstDisplayed
    (T : Display.{uA', uB', uC', uD'} Q)
    (R : Responder State Q)
    {I : State → Type uF}
    (displayedR : Display.Coalgebra (Display.responder T) R.out I)
    {E : Type uV} {F : E → Type uE}
    {program : FreeM Q E}
    (displayedProgram : FreeM.Displayed (T.toDisplayedAlgebra F) program)
    (state : State) (witness : I state) :=
   Responder.runAgainstDisplayed T R displayedR displayedProgram state witness


-- @@ L493-493 verbatim
end UniverseCanary


-- @@ L495-495 verbatim
end PFunctor.ResponderReindexExample
