/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.CryptoFoundations.Asymptotics.OracleClosure


-- @@ L11-16 verbatim
/-!
# Dependent oracle-handler closure checks

These tests use distinct Boolean and ternary answer types to ensure handler substitution preserves
the dependent query index and its answer policy.
-/


-- @@ L18-18 verbatim
public section


-- @@ L20-20 verbatim
open PFunctor

-- @@ L21-21 verbatim
open PFunctor.DynSystem.DynComputation

-- @@ L22-22 verbatim
open OracleComp.Complexity


-- @@ L24-24 verbatim
universe u v w x y


-- @@ L26-26 verbatim
namespace OracleComp.Complexity


-- @@ L28-28 verbatim
/-! ## Genuinely dependent response canary -/


-- @@ L30-34 verbatim
/-- Two query positions whose response types are not definitionally equal. -/
inductive DependentQuery where
  | bit
  | trit
  deriving DecidableEq


-- @@ L36-39 verbatim
/-- A small dependent oracle: one position returns a bit and the other returns a ternary digit. -/
abbrev dependentSpec : OracleSpec DependentQuery
  | .bit => Bool
  | .trit => Fin 3


-- @@ L41-45 verbatim
/-- The answer policy also depends on the query position. Every bit is admitted, while ternary
answers are restricted to zero or one. -/
@[expose] def dependentAllows : ∀ position, dependentSpec position → Prop
  | .bit, _ => True
  | .trit, answer => answer.val ≤ 1


-- @@ L47-51 verbatim
/-- A coin-powered implementation whose result type varies with the outer query position. -/
@[expose] def dependentHandler : ∀ position, FreeM coinSpec.toPFunctor (dependentSpec position)
  | .bit => FreeM.liftBind () fun answer ↦ FreeM.pure answer
  | .trit => FreeM.liftBind () fun answer ↦
      FreeM.pure (if answer then (1 : Fin 3) else 0)


-- @@ L53-60 verbatim
/-- An adaptive outer program uses the Boolean reply to decide whether to request a `Fin 3`
reply. -/
@[expose] def dependentProgram : FreeM dependentSpec.toPFunctor ℕ :=
  FreeM.liftBind .bit fun answer ↦
    if answer then
      FreeM.liftBind .trit fun digit ↦ FreeM.pure digit.val
    else
      FreeM.pure 0


-- @@ L62-73 verbatim
/-- Both branches of the dependent handler meet their corresponding answer policy. -/
theorem dependentHandler_returnsAllowed (position : dependentSpec.Domain) :
    (dependentHandler position).LeavesSatisfyUnder (fun _ _ ↦ True)
      (dependentAllows position) := by
  cases position with
  | bit =>
      change ∀ _ : Bool, True → True
      simp
  | trit =>
      change ∀ answer : Bool, True → (if answer then (1 : Fin 3) else 0).val ≤ 1
      intro answer _
      cases answer <;> decide


-- @@ L75-89 verbatim
/-- The adaptive outer program returns only zero or one on every admitted typed-answer path. -/
theorem dependentProgram_returnsSmall :
  dependentProgram.LeavesSatisfyUnder dependentAllows (fun result ↦ result ≤ 1) := by
  unfold dependentProgram
  change ∀ answer : Bool, dependentAllows DependentQuery.bit answer →
    (if answer then FreeM.liftBind (P := dependentSpec.toPFunctor) DependentQuery.trit
        (fun digit ↦ FreeM.pure digit.val)
      else FreeM.pure 0).LeavesSatisfyUnder dependentAllows (fun result ↦ result ≤ 1)
  intro answer _
  cases answer with
  | false => simp
  | true =>
      simp only [if_true]
      intro digit hdigit
      simpa [dependentAllows] using hdigit


-- @@ L91-98 verbatim
/-- Typed handler substitution composes the variable-response policy without erasing the query
index or appealing to a probabilistic semantics. -/
theorem closeDependentHandler_returnsSmall :
    (closeHandler dependentHandler dependentProgram).LeavesSatisfyUnder
      (fun _ _ ↦ True) (fun result ↦ result ≤ 1) :=
  leavesSatisfyUnder_closeHandler dependentHandler dependentAllows (fun _ _ ↦ True)
    (fun result ↦ result ≤ 1) dependentHandler_returnsAllowed dependentProgram
      dependentProgram_returnsSmall


-- @@ L100-100 verbatim
section ProofBearingCanary


-- @@ L102-108 verbatim
variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  {outer : InterfaceBoundary C dependentSpec.toPFunctor}
  {inner : InterfaceBoundary C coinSpec.toPFunctor}
  {outerLabel : Type x} {innerLabel : Type y}
  {outerContract : OracleContract Q outer outerLabel}
  {innerContract : OracleContract Q inner innerLabel}


-- @@ L110-122 verbatim
/-- Even for a variable-response handler, a bare semantic conformance theorem does not fabricate
executable evidence: the constructor additionally consumes strict PPT of the one packed
dispatcher. -/
example
    (hppt : IsOraclePPTBy Q (handlerBoundary outer inner) innerContract
      (packHandler dependentHandler))
    (modelMap : innerContract.Model → outerContract.Model)
    (returnsAllowed : ∀ (innerModel : innerContract.Model)
      (position : dependentSpec.Domain),
      (dependentHandler position).LeavesSatisfyUnder innerModel.resourceModel.allows
        ((modelMap innerModel).resourceModel.allows position)) :
    Nonempty (HandlerCertificate outer inner outerContract innerContract dependentHandler) :=
  HandlerCertificate.nonempty_of_isOraclePPTBy hppt modelMap returnsAllowed


-- @@ L124-124 verbatim
end ProofBearingCanary


-- @@ L126-126 verbatim
end OracleComp.Complexity
