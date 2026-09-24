/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import PolyFun.PFunctor.PatternRunsOnMatter.Parallel
public import PolyFun.PFunctor.Wiring.Parallel


-- @@ L12-18 verbatim
/-!
# Regression tests for parallel wiring and reconstruction bridges

The concrete wiring examples observe that the two external sigma resources
remain distinct in all three one-or-both branches.  The generic theorem pins
the Pattern-Runs-on-Matter comparison at independent component universes.
-/


-- @@ L20-20 verbatim
@[expose] public section


-- @@ L22-22 verbatim
namespace PFunctor.ParallelBridgesCanary


-- @@ L24-24 verbatim
abbrev Step : PFunctor.{0, 0} := ⟨Bool, fun _ => PUnit⟩


-- @@ L26-26 verbatim
def Boxes := PEmpty


-- @@ L28-28 verbatim
def Arity (box : Boxes) : Type := nomatch box


-- @@ L30-30 verbatim
def Dom (box : Boxes) : Arity box → PFunctor := nomatch box


-- @@ L32-32 verbatim
def Cod (box : Boxes) : PFunctor := nomatch box


-- @@ L34-34 verbatim
def Inputs := PUnit


-- @@ L36-36 verbatim
def inputInterface (_ : Inputs) : PFunctor := Step


-- @@ L38-40 verbatim
def implementation (box : Boxes) : (operation : (Cod box).A) →
    FreeM (PFunctor.sigma (Dom box)) ((Cod box).B operation) :=
  nomatch box


-- @@ L42-43 verbatim
def inputWiring : Wiring Boxes Arity Dom Cod Inputs inputInterface Step :=
  .input PUnit.unit


-- @@ L45-51 verbatim
def rootOperation {E : Type} :
    FreeM (PFunctor.sigma inputInterface ∥
      PFunctor.sigma inputInterface) E →
      Option (ParallelChoice (PFunctor.sigma inputInterface).A
        (PFunctor.sigma inputInterface).A)
  | .pure _ => none
  | .liftBind operation _ => some operation


-- @@ L53-56 verbatim
example : rootOperation
    (Wiring.evalParallel implementation inputWiring inputWiring (.left false)) =
      some (.left ⟨PUnit.unit, false⟩) :=
  rfl


-- @@ L58-61 verbatim
example : rootOperation
    (Wiring.evalParallel implementation inputWiring inputWiring (.right true)) =
      some (.right ⟨PUnit.unit, true⟩) :=
  rfl


-- @@ L63-67 verbatim
example : rootOperation
    (Wiring.evalParallel implementation inputWiring inputWiring
      (.both false true)) =
      some (.both ⟨PUnit.unit, false⟩ ⟨PUnit.unit, true⟩) :=
  rfl


-- @@ L69-71 verbatim
abbrev unaryDisplay : Display Step where
  position _ := PUnit
  direction _ _ _ := PUnit


-- @@ L73-75 verbatim
def domDisplay (box : Boxes) :
    (port : Arity box) → Display (Dom box port) :=
  nomatch box


-- @@ L77-78 verbatim
def codDisplay (box : Boxes) : Display (Cod box) :=
  nomatch box


-- @@ L80-80 verbatim
def inputDisplay (_ : Inputs) : Display Step := unaryDisplay


-- @@ L82-85 verbatim
def displayedImplementation (box : Boxes) :
    Display.Handler (codDisplay box) (Display.sigma (domDisplay box))
      (implementation box) :=
  nomatch box


-- @@ L87-90 verbatim
def displayedInputWiring :
    Wiring.Displayed domDisplay codDisplay inputDisplay
      inputWiring unaryDisplay :=
  .input PUnit.unit


-- @@ L92-97 verbatim
example :
    (Wiring.evalDisplayedParallel domDisplay codDisplay inputDisplay
      implementation displayedImplementation displayedInputWiring
      displayedInputWiring (.both false true)
      (PUnit.unit, PUnit.unit)).1 = (PUnit.unit, PUnit.unit) :=
  rfl


-- @@ L99-99 verbatim
universe uA₁ uA₂ uB uS₁ uS₂


-- @@ L101-114 verbatim
theorem reindexViaRunAgainst_parallel
    {P R : PFunctor.{uA₁, uB}} {Q V : PFunctor.{uA₂, uB}}
    {LeftState : Type uS₁} {RightState : Type uS₂}
    (leftHandler : Handler (FreeM P) R)
    (rightHandler : Handler (FreeM Q) V)
    (left : Responder LeftState P) (right : Responder RightState Q) :
    Responder.reindexViaRunAgainst
        (Handler.parallel leftHandler rightHandler)
        (Responder.parallel left right) =
      Responder.parallel
        (Responder.reindexViaRunAgainst leftHandler left)
        (Responder.reindexViaRunAgainst rightHandler right) :=
  Responder.reindexViaRunAgainst_parallel
    leftHandler rightHandler left right


-- @@ L116-116 verbatim
end PFunctor.ParallelBridgesCanary
