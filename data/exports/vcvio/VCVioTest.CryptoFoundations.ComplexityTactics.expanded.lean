/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Realizability.Quantitative.Polynomial
public import VCVio.CryptoFoundations.Asymptotics.ComputationalComplexity
public meta import VCVio.CryptoFoundations.Asymptotics.ComplexityTactics


-- @@ L13-19 verbatim
/-!
# Complexity-tactic checks

Compile-time checks for strict `@[ppt_primitive]` validation and the bounded `ppt`, `ppt?`, and
`ppt using` lookup modes. The test backend has zero cost and size solely to provide small concrete
`PolyRealizer` values; the tactic never constructs those values itself.
-/


-- @@ L21-21 verbatim
@[expose] public section


-- @@ L23-23 verbatim
open PFunctor


-- @@ L25-25 verbatim
namespace OracleComp.Complexity.ComplexityTacticsTest


-- @@ L27-32 verbatim
/-- Qualitative carrier used only by the tactic smoke tests. -/
def stepClass : StepClass where
  Str _ := PUnit
  Hom _ _ _ := True
  id_mem _ := trivial
  comp_mem _ _ := trivial


-- @@ L34-36 verbatim
/-- The unique test representation of a type. -/
def representation (A : Type) : stepClass.Str A :=
  PUnit.unit


-- @@ L38-43 verbatim
/-- Zero-cost quantitative backend used to construct concrete test certificates. -/
def backend : QuantitativeStepClass stepClass where
  Realizer _ _ _ := PUnit
  size _ _ := 0
  cost _ _ := 0
  admissible _ := trivial


-- @@ L45-52 verbatim
/-- Every function has an explicit zero-cost polynomial realizer in the test backend. -/
def polyRealizer {A B : Type} (a : stepClass.Str A) (b : stepClass.Str B) (f : A → B) :
    backend.PolyRealizer a b f where
  code := PUnit.unit
  work := Complexity.FirstOrderPolynomial.const 0
  outputSize := Complexity.FirstOrderPolynomial.const 0
  work_le _ := le_rfl
  outputSize_le _ := le_rfl


-- @@ L54-54 verbatim
abbrev unitRepresentation : stepClass.Str Unit := representation Unit

-- @@ L55-55 verbatim
abbrev boolRepresentation : stepClass.Str Bool := representation Bool


-- @@ L57-60 verbatim
@[ppt_primitive]
def boolIdentityPrimitive :
    backend.PolyRealizer boolRepresentation boolRepresentation id :=
  polyRealizer boolRepresentation boolRepresentation id


-- @@ L62-65 verbatim
@[ppt_primitive]
def unitIdentityPrimitive :
    backend.PolyRealizer unitRepresentation unitRepresentation id :=
  polyRealizer unitRepresentation unitRepresentation id


-- @@ L67-68 verbatim
example : backend.PolyRealizer unitRepresentation unitRepresentation id := by
  ppt


-- @@ L70-72 verbatim
example (hypothesis : backend.PolyRealizer unitRepresentation unitRepresentation id) :
    backend.PolyRealizer unitRepresentation unitRepresentation id := by
  ppt


-- @@ L74-75 verbatim
example : backend.PolyRealizer unitRepresentation unitRepresentation id := by
  ppt using unitIdentityPrimitive


-- @@ L77-79 verbatim
#guard_msgs (drop info) in
example : backend.PolyRealizer unitRepresentation unitRepresentation id := by
  ppt?


-- @@ L81-87 verbatim
/--
error: @[ppt_primitive] expects a declaration ending in exactly one of:
-/
#guard_msgs (error, substring := true) in
@[ppt_primitive]
theorem rejectedTruthPrimitive : True :=
  trivial


-- @@ L89-94 verbatim
/--
error: ppt supports goals headed exactly by `PolyRealizer` or `IsOraclePPTBy`
-/
#guard_msgs (error, substring := true) in
example : True := by
  ppt


-- @@ L96-101 verbatim
/--
error: ppt found no exact local assumption
-/
#guard_msgs (error, substring := true) in
example : backend.PolyRealizer boolRepresentation boolRepresentation Bool.not := by
  ppt


-- @@ L103-108 verbatim
/--
error: ppt using failed to close the goal exactly
-/
#guard_msgs (error, substring := true) in
example : backend.PolyRealizer unitRepresentation unitRepresentation id := by
  ppt using boolIdentityPrimitive


-- @@ L110-110 verbatim
section OraclePPT


-- @@ L112-112 verbatim
universe u v w x


-- @@ L114-114 verbatim
open PFunctor.DynSystem.DynComputation


-- @@ L116-120 verbatim
variable {p : PFunctor.{u, u}} {C : StepClass.{u, v}}
  [C.HasProd] [C.HasSum] [C.HasOption] [DecidableEq p.A]
  {Q : QuantitativeStepClass.{u, v, w} C} {input output : Type u}
  {bd : Boundary C p input output} {label : Type x}
  {contract : OracleContract Q bd.interface label} {program : input → FreeM p output}


-- @@ L122-129 verbatim
/--
error: @[ppt_primitive] rejects
-/
#guard_msgs (error, substring := true) in
@[ppt_primitive]
def rejectedOraclePPTDefinition (hypothesis : IsOraclePPTBy Q bd contract program) :
    IsOraclePPTBy Q bd contract program :=
  hypothesis


-- @@ L131-134 verbatim
@[ppt_primitive]
theorem oraclePPTPrimitive (hypothesis : IsOraclePPTBy Q bd contract program) :
    IsOraclePPTBy Q bd contract program :=
  hypothesis


-- @@ L136-138 verbatim
example (hypothesis : IsOraclePPTBy Q bd contract program) :
    IsOraclePPTBy Q bd contract program := by
  ppt


-- @@ L140-142 verbatim
example (hypothesis : IsOraclePPTBy Q bd contract program) :
    IsOraclePPTBy Q bd contract program := by
  ppt using oraclePPTPrimitive hypothesis


-- @@ L144-144 verbatim
end OraclePPT


-- @@ L146-146 verbatim
end OracleComp.Complexity.ComplexityTacticsTest
