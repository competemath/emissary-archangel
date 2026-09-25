/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, VCVio Contributors
-/

module

public import VCVio.CryptoFoundations.Asymptotics.RankedRun
public import PolyFun.Realizability.Instances


-- @@ L12-18 verbatim
/-!
# Decisive canaries for VCVio's quantitative-complexity adapters

The synthetic zero-cost backend used here is only an API fixture. The tests pin VCVio's public
ranked-certificate and uniform-security-family facades, while the adaptive and parity examples
make the rank depend observably on an oracle answer and on the runtime input.
-/


-- @@ L20-20 verbatim
public section


-- @@ L22-22 verbatim
namespace OracleComp.Complexity.ComplexityAdaptersTest


-- @@ L24-24 verbatim
open PFunctor

-- @@ L25-25 verbatim
open PFunctor.DynSystem

-- @@ L26-26 verbatim
open PFunctor.DynSystem.DynComputation


-- @@ L28-28 verbatim
/-! ## Synthetic structural fixture -/


-- @@ L30-35 verbatim
@[expose]
def zeroBackend : QuantitativeStepClass.{0, 0, 0} StepClass.unconstrained.{0, 0} where
  Realizer _ _ _ := PUnit
  size _ _ := 0
  cost _ _ := 0
  admissible _ := True.intro


-- @@ L37-41 verbatim
instance : zeroBackend.HasCategory where
  identity _ := PUnit.unit
  compose _ _ := PUnit.unit
  composeOverhead _ _ _ := 0
  cost_compose_le _ _ _ := le_rfl


-- @@ L43-46 verbatim
instance : zeroBackend.HasProd where
  fst _ _ := PUnit.unit
  snd _ _ := PUnit.unit
  pair _ _ := PUnit.unit


-- @@ L48-51 verbatim
instance : zeroBackend.HasSum where
  inl _ _ := PUnit.unit
  inr _ _ := PUnit.unit
  elim _ _ := PUnit.unit


-- @@ L53-56 verbatim
instance : zeroBackend.HasOption where
  map _ := PUnit.unit
  none _ _ := PUnit.unit
  bindContext _ := PUnit.unit


-- @@ L58-59 verbatim
instance : zeroBackend.IsDistributive where
  distribute _ _ _ := PUnit.unit


-- @@ L61-61 verbatim
/-! ## Ranked strict PPT for one genuinely uniform security family -/


-- @@ L63-64 verbatim
@[expose]
def familySpec (_n : ℕ) : OracleSpec PUnit := fun _ ↦ PEmpty


-- @@ L66-67 verbatim
/-- The member input and output types vary with the security parameter. -/
abbrev familyValue (n : ℕ) := Fin (n + 1)


-- @@ L69-71 verbatim
def familyProgram (n : ℕ) (input : familyValue n) :
    OracleComp (familySpec n) (familyValue n) :=
  pure input


-- @@ L73-77 verbatim
abbrev familyBoundary : Boundary StepClass.unconstrained
    (OracleComp.SecurityFamily.Spec familySpec).toPFunctor
    (OracleComp.SecurityFamily.Input familyValue)
    (OracleComp.SecurityFamily.Output familyValue) :=
  Boundary.unconstrained _ _ _


-- @@ L79-86 verbatim
/-- One machine implements every member of the nonconstant family. -/
@[expose]
def familyRealization : QuantitativeRealization zeroBackend familyBoundary where
  machine := ofFn id
  state := PUnit.unit
  initCode := PUnit.unit
  headCode := PUnit.unit
  updateCode := PUnit.unit


-- @@ L88-93 verbatim
def familyResourceModel :
    OracleResourceModel zeroBackend familyBoundary.interface (fun _ ↦ ()) where
  allows := fun _ answer ↦ nomatch answer
  responseSize := fun _ _ ↦ 0
  responseSize_monotone := fun _ _ _ _ ↦ le_rfl
  responseSize_le := fun _ answer ↦ nomatch answer


-- @@ L95-98 verbatim
def familyContract : OracleContract zeroBackend familyBoundary.interface Unit where
  labelOf _ := ()
  admissible model := model = familyResourceModel
  model_nonempty := ⟨familyResourceModel, rfl⟩


-- @@ L100-102 verbatim
def familyOutputRecovery : zeroBackend.PolyOutputSizeRecovery familyBoundary where
  polynomial := .const 0
  output_le _ := le_rfl


-- @@ L104-119 verbatim
/-- Local ranked resource evidence for the packed immediate-return realization. -/
@[expose]
def familyResourcePotential : RankedRun.ResourcePotentialCertificate familyRealization
    familyResourceModel.allows (fun _ ↦ 0) where
  toRankedRunCertificate := {
    rank := fun _ ↦ 0
    returns_of_rank_zero := fun state _ ↦ ⟨state, rfl⟩
    decreases := fun _ direction ↦ nomatch direction
    progress := fun hview ↦ by
      rw [show familyRealization.machine.view _ = Sum.inl _ by rfl] at hview
      exact nomatch hview }
  potential := fun _ ↦ 0
  terminal_le _ := le_rfl
  query_le := fun _ direction _ ↦ nomatch direction
  init_le _ := le_rfl
  rank_init_le _ := le_rfl


-- @@ L121-136 verbatim
/-- One ranked certificate gives executable, semantic, and resource evidence for every member. -/
def familyRankedPPTCertificate : RankedPPTCertificate zeroBackend familyBoundary familyContract
    (fun input ↦ ((OracleComp.SecurityFamily.packProgram familyProgram) input).toFreeM) where
  realization := familyRealization
  implements := by
    change (ofFn id).Implements (fun input ↦ FreeM.pure input)
    intro input
    rw [denote_ofFn]
    simp
  outputRecovery := familyOutputRecovery
  polynomial := ResourcePolynomial.const 0
  resourcePotential model := by
    rcases model with ⟨model, hmodel⟩
    change model = familyResourceModel at hmodel
    subst model
    simpa only [ResourcePolynomial.eval_const] using familyResourcePotential


-- @@ L138-142 verbatim
/-- The ranked facade reaches VCVio's public strict-PPT predicate end to end. -/
theorem familyRanked_isOraclePPTBy :
    IsOraclePPTBy zeroBackend familyBoundary familyContract
      (fun input ↦ ((OracleComp.SecurityFamily.packProgram familyProgram) input).toFreeM) :=
  familyRankedPPTCertificate.isOraclePPTBy


-- @@ L144-148 verbatim
/-- Positive producer canary for the uniform packed-family public predicate. -/
theorem family_isOraclePPTBy :
    OracleComp.Complexity.SecurityFamily.IsOraclePPTBy zeroBackend familyBoundary
      familyContract familyProgram :=
  familyRankedPPTCertificate.isOraclePPTBy


-- @@ L150-150 verbatim
/-! ## Branch- and input-sensitive rank canaries -/


-- @@ L152-156 verbatim
inductive AdaptiveState where
  | first
  | second
  | done (result : Bool)
  deriving DecidableEq


-- @@ L158-161 verbatim
def adaptiveView : AdaptiveState → Bool ⊕ coinSpec.toPFunctor.Obj AdaptiveState
  | .first => Sum.inr ⟨(), fun answer ↦ if answer then .second else .done false⟩
  | .second => Sum.inr ⟨(), fun answer ↦ .done answer⟩
  | .done result => Sum.inl result


-- @@ L163-169 verbatim
@[expose]
def adaptiveMachine : DynComputation coinSpec.toPFunctor Unit Bool where
  State := AdaptiveState
  toDynSystem :=
    (fun state ↦ (Resumption.pack (adaptiveView state)).1) ⇆
      fun state ↦ (Resumption.pack (adaptiveView state)).2
  init := fun _ ↦ .first


-- @@ L171-175 verbatim
@[simp]
theorem adaptiveMachine_view_first : adaptiveMachine.view .first =
    Sum.inr ⟨(), fun answer ↦ if answer then .second else .done false⟩ := by
  change Resumption.unpack (Resumption.pack (adaptiveView .first)) = _
  exact Resumption.unpack_pack _


-- @@ L177-181 verbatim
@[simp]
theorem adaptiveMachine_view_second : adaptiveMachine.view .second =
    Sum.inr ⟨(), fun answer ↦ .done answer⟩ := by
  change Resumption.unpack (Resumption.pack (adaptiveView .second)) = _
  exact Resumption.unpack_pack _


-- @@ L183-187 verbatim
@[simp]
theorem adaptiveMachine_view_done (result : Bool) : adaptiveMachine.view (.done result) =
    Sum.inl result := by
  change Resumption.unpack (Resumption.pack (adaptiveView (.done result))) = _
  exact Resumption.unpack_pack _


-- @@ L189-192 verbatim
def adaptiveRemaining : AdaptiveState → ℕ
  | .first => 2
  | .second => 1
  | .done _ => 0


-- @@ L194-221 verbatim
theorem adaptiveRemaining_lt_of_view_query
    {state : AdaptiveState} {position : coinSpec.Domain}
    {next : coinSpec.Range position → AdaptiveState}
    (view_eq : adaptiveMachine.view state = Sum.inr ⟨position, next⟩)
    (direction : coinSpec.Range position) :
    adaptiveRemaining (next direction) < adaptiveRemaining state := by
  cases state with
  | first =>
      rw [adaptiveMachine_view_first] at view_eq
      have query_eq := Sum.inr.inj view_eq
      cases position
      have next_eq :
          (fun answer : Bool ↦ if answer then AdaptiveState.second else .done false) = next :=
        eq_of_heq (Sigma.ext_iff.mp query_eq).2
      cases next_eq
      cases direction <;> decide
  | second =>
      rw [adaptiveMachine_view_second] at view_eq
      have query_eq := Sum.inr.inj view_eq
      cases position
      have next_eq : (fun answer : Bool ↦ AdaptiveState.done answer) = next :=
        eq_of_heq (Sigma.ext_iff.mp query_eq).2
      cases next_eq
      change 0 < 1
      decide
  | done result =>
      rw [adaptiveMachine_view_done] at view_eq
      exact nomatch view_eq


-- @@ L223-224 verbatim
abbrev adaptiveBoundary : Boundary StepClass.unconstrained coinSpec.toPFunctor Unit Bool :=
  Boundary.unconstrained _ _ _


-- @@ L226-231 verbatim
def adaptiveRealization : QuantitativeRealization zeroBackend adaptiveBoundary where
  machine := adaptiveMachine
  state := PUnit.unit
  initCode := PUnit.unit
  headCode := PUnit.unit
  updateCode := PUnit.unit


-- @@ L233-243 verbatim
def adaptiveRanked : RankedRunCertificate adaptiveRealization (fun _ _ ↦ True) where
  rank := adaptiveRemaining
  returns_of_rank_zero := by
    intro state hzero
    cases state with
    | first => simp [adaptiveRemaining] at hzero
    | second => simp [adaptiveRemaining] at hzero
    | done result => exact ⟨result, adaptiveMachine_view_done result⟩
  decreases := fun view_eq direction _ ↦
    adaptiveRemaining_lt_of_view_query view_eq direction
  progress := fun _ ↦ ⟨false, trivial⟩


-- @@ L245-247 verbatim
/-- The two answers to the first query have observably different successor ranks. -/
example : adaptiveRanked.rank (.done false) = 0 ∧ adaptiveRanked.rank .second = 1 := by
  decide


-- @@ L249-252 verbatim
def parityView : (ℕ × Bool) → Bool ⊕ coinSpec.toPFunctor.Obj (ℕ × Bool)
  | (0, parity) => Sum.inl parity
  | (remaining + 1, parity) =>
      Sum.inr ⟨(), fun answer ↦ (remaining, Bool.xor parity answer)⟩


-- @@ L254-260 verbatim
@[expose]
def parityMachine : DynComputation coinSpec.toPFunctor ℕ Bool where
  State := ℕ × Bool
  toDynSystem :=
    (fun state ↦ (Resumption.pack (parityView state)).1) ⇆
      fun state ↦ (Resumption.pack (parityView state)).2
  init := fun queries ↦ (queries, false)


-- @@ L262-266 verbatim
@[simp]
theorem parityMachine_view_zero (parity : Bool) : parityMachine.view (0, parity) =
    Sum.inl parity := by
  change Resumption.unpack (Resumption.pack (parityView (0, parity))) = _
  exact Resumption.unpack_pack _


-- @@ L268-273 verbatim
@[simp]
theorem parityMachine_view_succ (remaining : ℕ) (parity : Bool) :
    parityMachine.view (remaining + 1, parity) =
      Sum.inr ⟨(), fun answer ↦ (remaining, Bool.xor parity answer)⟩ := by
  change Resumption.unpack (Resumption.pack (parityView (remaining + 1, parity))) = _
  exact Resumption.unpack_pack _


-- @@ L275-275 verbatim
def parityRemaining (state : ℕ × Bool) : ℕ := state.1


-- @@ L277-297 verbatim
theorem parityRemaining_lt_of_view_query
    {state : ℕ × Bool} {position : coinSpec.Domain}
    {next : coinSpec.Range position → ℕ × Bool}
    (view_eq : parityMachine.view state = Sum.inr ⟨position, next⟩)
    (direction : coinSpec.Range position) :
    parityRemaining (next direction) < parityRemaining state := by
  rcases state with ⟨remaining, parity⟩
  cases remaining with
  | zero =>
      rw [parityMachine_view_zero] at view_eq
      exact nomatch view_eq
  | succ remaining =>
      rw [parityMachine_view_succ] at view_eq
      have query_eq := Sum.inr.inj view_eq
      cases position
      have next_eq :
          (fun answer : Bool ↦ (remaining, Bool.xor parity answer)) = next :=
        eq_of_heq (Sigma.ext_iff.mp query_eq).2
      cases next_eq
      change remaining < remaining + 1
      omega


-- @@ L299-300 verbatim
abbrev parityBoundary : Boundary StepClass.unconstrained coinSpec.toPFunctor ℕ Bool :=
  Boundary.unconstrained _ _ _


-- @@ L302-307 verbatim
def parityRealization : QuantitativeRealization zeroBackend parityBoundary where
  machine := parityMachine
  state := PUnit.unit
  initCode := PUnit.unit
  headCode := PUnit.unit
  updateCode := PUnit.unit


-- @@ L309-318 verbatim
def parityRanked : RankedRunCertificate parityRealization (fun _ _ ↦ True) where
  rank := parityRemaining
  returns_of_rank_zero := by
    intro ⟨remaining, parity⟩ hzero
    change remaining = 0 at hzero
    subst remaining
    exact ⟨parity, parityMachine_view_zero parity⟩
  decreases := fun view_eq direction _ ↦
    parityRemaining_lt_of_view_query view_eq direction
  progress := fun _ ↦ ⟨false, trivial⟩


-- @@ L320-323 verbatim
/-- The initial rank is the runtime query-count input, rather than a fixed test constant. -/
example (queries : ℕ) :
    parityRanked.rank (parityRealization.machine.init queries) = queries :=
  rfl


-- @@ L325-325 verbatim
end OracleComp.Complexity.ComplexityAdaptersTest
