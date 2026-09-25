/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.OracleComp.Coinductive.SecurityFamily
public import PolyFun.Realizability.Quantitative.Resource


-- @@ L12-32 verbatim
/-!
# Strict polynomial time for syntactic oracle computations

This file gives VCVio's backend-relative, worst-case notion of polynomial time. It combines four
pieces which remain explicit in every statement:

1. one `DynComputation` implementing the whole input family;
2. Type-valued executable evidence for its `init`, `head`, and enabled `update?` maps;
3. exact resource accounting for every finite, typed query-answer prefix; and
4. second-order polynomial bounds in the encoded input size and oracle response-length functions.

The generic definition is deliberately named `IsOraclePPTBy`: a `QuantitativeStepClass` supplies an
operational backend, but only a backend-specific adequacy theorem can identify that cost with a
standard machine model. VCVio does not turn an arbitrary cost annotation into an unqualified
claim of PPT.

Random sampling is just another syntactic oracle interaction. Consequently the strict predicate
quantifies over every contract-conforming answer branch, including every coin outcome and branches
having probability zero under a later semantics. Expected polynomial time is a different
probabilistic notion and is not smuggled into this pathwise definition.
-/


-- @@ L34-34 verbatim
@[expose] public section


-- @@ L36-36 verbatim
universe u v w x y


-- @@ L38-38 verbatim
namespace OracleComp.Complexity


-- @@ L40-40 verbatim
open PFunctor

-- @@ L41-41 verbatim
open PFunctor.DynSystem.DynComputation


-- @@ L43-43 verbatim
/-! ## Generic quantitative-resource facade -/


-- @@ L45-46 verbatim
/-- VCVio's crypto-facing name for PolyFun's generic execution-cost polynomial. -/
abbrev ResourcePolynomial (label : Type x) := PFunctor.ExecutionCostPolynomial label


-- @@ L48-48 verbatim
namespace ResourcePolynomial


-- @@ L50-50 verbatim
abbrev ofFirstOrder := @PFunctor.ExecutionCostPolynomial.ofFirstOrder

-- @@ L51-53 verbatim
abbrev eval {label : Type x} (bound : ResourcePolynomial label)
    (length : label → ℕ → ℕ) (inputSize : ℕ) :=
  PFunctor.ExecutionCostPolynomial.eval bound length inputSize

-- @@ L54-54 verbatim
abbrev const := @PFunctor.ExecutionCostPolynomial.const

-- @@ L55-56 verbatim
abbrev add {label : Type x} (left right : ResourcePolynomial label) :=
  PFunctor.ExecutionCostPolynomial.add left right

-- @@ L57-59 verbatim
abbrev comp {label : Type x} (bound : ResourcePolynomial label)
    (inputBound : _root_.Complexity.SecondOrderPolynomial label) :=
  PFunctor.ExecutionCostPolynomial.comp bound inputBound

-- @@ L60-62 verbatim
abbrev reindex {label : Type x} {target : Type y} (bound : ResourcePolynomial label)
    (map : label → target) :=
  PFunctor.ExecutionCostPolynomial.reindex bound map

-- @@ L63-65 verbatim
abbrev subst {label : Type x} {target : Type y} (bound : ResourcePolynomial label)
    (replacement : label → _root_.Complexity.SecondOrderPolynomial target) :=
  PFunctor.ExecutionCostPolynomial.subst bound replacement

-- @@ L66-66 verbatim
abbrev eval_ofFirstOrder := @PFunctor.ExecutionCostPolynomial.eval_ofFirstOrder

-- @@ L67-67 verbatim
abbrev eval_const := @PFunctor.ExecutionCostPolynomial.eval_const

-- @@ L68-68 verbatim
abbrev eval_comp := @PFunctor.ExecutionCostPolynomial.eval_comp

-- @@ L69-69 verbatim
abbrev eval_reindex := @PFunctor.ExecutionCostPolynomial.eval_reindex

-- @@ L70-70 verbatim
abbrev eval_subst := @PFunctor.ExecutionCostPolynomial.eval_subst

-- @@ L71-71 verbatim
abbrev add_eval_le_eval_add := @PFunctor.ExecutionCostPolynomial.add_eval_le_eval_add

-- @@ L72-72 verbatim
abbrev eval_mono_input := @PFunctor.ExecutionCostPolynomial.eval_mono_input

-- @@ L73-73 verbatim
abbrev eval_mono_lengths := @PFunctor.ExecutionCostPolynomial.eval_mono_lengths


-- @@ L75-75 verbatim
end ResourcePolynomial


-- @@ L77-79 verbatim
/-- VCVio's oracle-facing name for PolyFun's response-size modulus symbols. -/
abbrev OracleModulus (label : Type x) :=
  PFunctor.DynSystem.DynComputation.ResponseModulus label


-- @@ L81-85 verbatim
/-- VCVio's oracle-facing view of PolyFun's admitted-response resource model. -/
abbrev OracleResourceModel {p : PFunctor.{u, u}} {C : StepClass.{u, v}}
    {label : Type x} (Q : QuantitativeStepClass.{u, v, w} C)
    (interface : InterfaceBoundary C p) (labelOf : p.A → label) :=
  PFunctor.DynSystem.DynComputation.ResponseResourceModel Q interface labelOf


-- @@ L87-91 verbatim
/-- VCVio's oracle-facing view of PolyFun's nonempty response-resource contract. -/
abbrev OracleContract {p : PFunctor.{u, u}} {C : StepClass.{u, v}}
    (Q : QuantitativeStepClass.{u, v, w} C) (interface : InterfaceBoundary C p)
    (label : Type x) :=
  PFunctor.DynSystem.DynComputation.ResponseResourceContract Q interface label


-- @@ L93-93 verbatim
namespace OracleResourceModel


-- @@ L95-95 verbatim
abbrev modulus := @PFunctor.DynSystem.DynComputation.ResponseResourceModel.modulus

-- @@ L96-97 verbatim
abbrev modulus_monotone :=
  @PFunctor.DynSystem.DynComputation.ResponseResourceModel.modulus_monotone


-- @@ L99-99 verbatim
end OracleResourceModel


-- @@ L101-101 verbatim
namespace OracleContract


-- @@ L103-106 verbatim
abbrev Model {p : PFunctor.{u, u}} {C : StepClass.{u, v}}
    {Q : QuantitativeStepClass.{u, v, w} C} {interface : InterfaceBoundary C p}
    {label : Type x} (contract : OracleContract Q interface label) :=
  PFunctor.DynSystem.DynComputation.ResponseResourceContract.Model contract


-- @@ L108-108 verbatim
namespace Model


-- @@ L110-112 verbatim
variable {p : PFunctor.{u, u}} {C : StepClass.{u, v}}
  {Q : QuantitativeStepClass.{u, v, w} C} {interface : InterfaceBoundary C p}
  {label : Type x} {contract : OracleContract Q interface label}


-- @@ L114-115 verbatim
abbrev resourceModel (model : contract.Model) :=
  PFunctor.DynSystem.DynComputation.ResponseResourceContract.Model.resourceModel model

-- @@ L116-117 verbatim
abbrev modulus (model : contract.Model) :=
  PFunctor.DynSystem.DynComputation.ResponseResourceContract.Model.modulus model

-- @@ L118-120 verbatim
theorem modulus_monotone (model : contract.Model) :
    _root_.Complexity.SecondOrderPolynomial.MonotoneLengths model.modulus :=
  PFunctor.DynSystem.DynComputation.ResponseResourceContract.Model.modulus_monotone model


-- @@ L122-122 verbatim
end Model


-- @@ L124-124 verbatim
end OracleContract


-- @@ L126-126 verbatim
/-! ## Backend-relative strict PPT -/


-- @@ L128-131 verbatim
variable {p : PFunctor.{u, u}} {C : StepClass.{u, v}}
  [C.HasProd] [C.HasSum] [C.HasOption] [DecidableEq p.A]
  {Q : QuantitativeStepClass.{u, v, w} C} {input output : Type u}
  {bd : Boundary C p input output} {label : Type x}


-- @@ L133-138 verbatim
/-- VCVio's strict-PPT witness is PolyFun's generic polynomial program witness, interpreted as a
cryptographic open-oracle certificate. -/
abbrev StrictPPTWitness
    (Q : QuantitativeStepClass.{u, v, w} C) (bd : Boundary C p input output)
    (contract : OracleContract Q bd.interface label) (program : input → FreeM p output) :=
  PFunctor.DynSystem.DynComputation.PolynomialProgramWitness Q bd contract program


-- @@ L140-144 verbatim
/-- VCVio's certified-pure facade over PolyFun's generic pure resource certificate. -/
abbrev PureCertificate
    (Q : QuantitativeStepClass.{u, v, w} C) (bd : Boundary C p input output)
    (function : input → output) :=
  PFunctor.DynSystem.DynComputation.PureResourceCertificate Q bd function


-- @@ L146-146 verbatim
namespace PureCertificate


-- @@ L148-149 verbatim
abbrev ofPolyRealizer :=
  @PFunctor.DynSystem.DynComputation.PureResourceCertificate.ofPolyRealizer

-- @@ L150-151 verbatim
abbrev realization :=
  @PFunctor.DynSystem.DynComputation.PureResourceCertificate.realization

-- @@ L152-153 verbatim
abbrev polynomial :=
  @PFunctor.DynSystem.DynComputation.PureResourceCertificate.polynomial

-- @@ L154-155 verbatim
abbrev implements :=
  @PFunctor.DynSystem.DynComputation.PureResourceCertificate.implements

-- @@ L156-157 verbatim
abbrev runsWithin :=
  @PFunctor.DynSystem.DynComputation.PureResourceCertificate.runsWithin


-- @@ L159-159 verbatim
variable {function : input → output}


-- @@ L161-166 verbatim
/-- Build the complete strict-PPT witness for an immediately returning program. -/
def strictPPTWitness (certificate : PureCertificate Q bd function)
    (contract : OracleContract Q bd.interface label) :
    StrictPPTWitness Q bd contract fun value ↦ FreeM.pure (function value) :=
  PFunctor.DynSystem.DynComputation.PureResourceCertificate.programWitness
    certificate contract


-- @@ L168-168 verbatim
end PureCertificate


-- @@ L170-174 verbatim
/-- Strict, worst-case oracle PPT relative to an explicit quantitative backend. -/
def IsOraclePPTBy (Q : QuantitativeStepClass.{u, v, w} C)
    (bd : Boundary C p input output) (contract : OracleContract Q bd.interface label)
    (program : input → FreeM p output) : Prop :=
  Nonempty (StrictPPTWitness Q bd contract program)


-- @@ L176-177 verbatim
/-- An explicit synonym emphasizing that the generic oracle predicate is strict and pathwise. -/
abbrev IsStrictPPTBy := @IsOraclePPTBy


-- @@ L179-184 verbatim
/-- An immediately returning function with explicit polynomial code is strict oracle PPT. -/
theorem PureCertificate.isOraclePPTBy {function : input → output}
    (certificate : PureCertificate Q bd function)
    (contract : OracleContract Q bd.interface label) :
    IsOraclePPTBy Q bd contract fun value ↦ FreeM.pure (function value) :=
  ⟨certificate.strictPPTWitness contract⟩


-- @@ L186-186 verbatim
namespace StrictPPTWitness


-- @@ L188-188 verbatim
variable {contract : OracleContract Q bd.interface label} {program : input → FreeM p output}


-- @@ L190-192 verbatim
/-- Preserve VCVio's direct polynomial projection over PolyFun's factored run certificate. -/
abbrev polynomial (witness : StrictPPTWitness Q bd contract program) :=
  witness.runBound.polynomial


-- @@ L194-199 verbatim
/-- Preserve VCVio's model-specialized pathwise bound accessor. -/
theorem runsWithin (witness : StrictPPTWitness Q bd contract program)
    (model : contract.Model) :
    witness.realization.RunsWithinUnder model.resourceModel.allows fun value ↦
      witness.polynomial.eval model.modulus (Q.size bd.input value) :=
  witness.runBound.runsWithin model


-- @@ L201-202 verbatim
abbrev outputSizePolynomial :=
  @PFunctor.DynSystem.DynComputation.PolynomialProgramWitness.outputSizePolynomial

-- @@ L203-204 verbatim
abbrev eval_outputSizePolynomial :=
  @PFunctor.DynSystem.DynComputation.PolynomialProgramWitness.eval_outputSizePolynomial

-- @@ L205-206 verbatim
abbrev returnedSize_le :=
  @PFunctor.DynSystem.DynComputation.PolynomialProgramWitness.returnedSize_le

-- @@ L207-210 verbatim
def congrProgram {program' : input → FreeM p output}
    (witness : StrictPPTWitness Q bd contract program) (hprogram : program = program') :
    StrictPPTWitness Q bd contract program' :=
  PFunctor.DynSystem.DynComputation.PolynomialProgramWitness.congrProgram witness hprogram


-- @@ L212-214 verbatim
theorem isQuantitativelyRealizableBy (witness : StrictPPTWitness Q bd contract program) :
    IsQuantitativelyRealizableBy Q bd program :=
  PFunctor.DynSystem.DynComputation.PolynomialProgramWitness.isQuantitativelyRealizableBy witness


-- @@ L216-220 verbatim
theorem isQuantitativelyRealizableWithinUnder
    (witness : StrictPPTWitness Q bd contract program) (model : contract.Model) :
    IsQuantitativelyRealizableWithinUnder Q bd model.resourceModel.allows program
      (fun value ↦ witness.polynomial.eval model.modulus (Q.size bd.input value)) :=
  ⟨witness.realization, witness.implements, witness.runsWithin model⟩


-- @@ L222-230 verbatim
theorem isTotalRollBound (witness : StrictPPTWitness Q bd contract program)
    (model : contract.Model)
    (hAllows : ∀ position answer, model.resourceModel.allows position answer)
    (value : input) :
    (program value).IsTotalRollBound
      (witness.polynomial.eval model.modulus (Q.size bd.input value)).queries := by
  simpa only [PolynomialRunBound.bound_apply] using
    PFunctor.DynSystem.DynComputation.PolynomialProgramWitness.isTotalRollBound
      witness model hAllows value


-- @@ L232-232 verbatim
end StrictPPTWitness


-- @@ L234-234 verbatim
namespace IsOraclePPTBy


-- @@ L236-236 verbatim
variable {contract : OracleContract Q bd.interface label} {program : input → FreeM p output}


-- @@ L238-243 verbatim
/-- Strict oracle PPT is invariant under equality of whole program families. -/
theorem congrProgram {program' : input → FreeM p output}
    (h : IsOraclePPTBy Q bd contract program) (hprogram : program = program') :
    IsOraclePPTBy Q bd contract program' := by
  obtain ⟨witness⟩ := h
  exact ⟨witness.congrProgram hprogram⟩


-- @@ L245-249 verbatim
/-- Strict PPT implies backend-relative quantitative realizability. -/
theorem isQuantitativelyRealizableBy (h : IsOraclePPTBy Q bd contract program) :
    IsQuantitativelyRealizableBy Q bd program := by
  obtain ⟨witness⟩ := h
  exact witness.isQuantitativelyRealizableBy


-- @@ L251-254 verbatim
/-- Strict PPT erases to qualitative realizability. -/
theorem isRealizableBy (h : IsOraclePPTBy Q bd contract program) :
    IsRealizableBy C bd program :=
  h.isQuantitativelyRealizableBy.isRealizableBy


-- @@ L256-256 verbatim
end IsOraclePPTBy

-- @@ L257-257 verbatim
/-! ## OracleComp and uniform-family facades -/


-- @@ L259-268 verbatim
/-- Strict oracle PPT for a VCVio `OracleComp` program, via its definitional `FreeM` syntax. -/
def OracleProgram.IsOraclePPTBy {index : Type u} {spec : OracleSpec.{u, u} index}
    {input output : Type u} {C : StepClass.{u, v}}
    [C.HasProd] [C.HasSum] [C.HasOption] [DecidableEq spec.Domain]
    (Q : QuantitativeStepClass.{u, v, w} C)
    (bd : Boundary C spec.toPFunctor input output)
    {label : Type x} (contract : OracleContract Q bd.interface label)
    (program : input → OracleComp spec output) : Prop :=
  OracleComp.Complexity.IsOraclePPTBy Q bd contract fun value ↦
    (program value).toFreeM


-- @@ L270-289 verbatim
/-- Canonical finite resource model for the explicit fair-coin interface.

The response envelope is the larger encoded tagged-answer size of the two Boolean outcomes. This
contract concerns only the open computation's answer lengths; efficient fair-bit generation is a
separate sampler/handler certificate. -/
def fairCoinResourceModel {C : StepClass}
    [C.HasProd] [C.HasSum] [C.HasOption]
    (Q : QuantitativeStepClass C)
    (interface : InterfaceBoundary C coinSpec.toPFunctor) :
    OracleResourceModel Q interface (fun _ ↦ PUnit.unit) where
  allows := fun _ _ ↦ True
  responseSize := fun _ _ ↦
    max (Q.size interface.idx ⟨PUnit.unit, false⟩)
      (Q.size interface.idx ⟨PUnit.unit, true⟩)
  responseSize_monotone := fun _ _ _ _ ↦ le_rfl
  responseSize_le := fun position answer _ ↦ by
    cases position
    cases answer
    · exact Nat.le_max_left _ _
    · exact Nat.le_max_right _ _


-- @@ L291-299 verbatim
/-- Both Boolean replies are admitted by the canonical fair-coin resource model. -/
@[simp]
theorem fairCoinResourceModel_allows {C : StepClass}
    [C.HasProd] [C.HasSum] [C.HasOption]
    (Q : QuantitativeStepClass C)
    (interface : InterfaceBoundary C coinSpec.toPFunctor)
    (position : coinSpec.Domain) (answer : coinSpec.Range position) :
    (fairCoinResourceModel Q interface).allows position answer :=
  trivial


-- @@ L301-309 verbatim
/-- Contract admitting exactly the canonical finite fair-coin resource model. -/
def fairCoinContract {C : StepClass}
    [C.HasProd] [C.HasSum] [C.HasOption]
    (Q : QuantitativeStepClass C)
    (interface : InterfaceBoundary C coinSpec.toPFunctor) :
    OracleContract Q interface Unit where
  labelOf _ := PUnit.unit
  admissible model := model = fairCoinResourceModel Q interface
  model_nonempty := ⟨fairCoinResourceModel Q interface, rfl⟩


-- @@ L311-320 verbatim
/-- A model compatible with `fairCoinContract` is the canonical fair-coin model. -/
@[simp]
theorem fairCoinContract_admissible_iff {C : StepClass}
    [C.HasProd] [C.HasSum] [C.HasOption]
    (Q : QuantitativeStepClass C)
    (interface : InterfaceBoundary C coinSpec.toPFunctor)
    (model : OracleResourceModel Q interface (fairCoinContract Q interface).labelOf) :
    (fairCoinContract Q interface).admissible model ↔
      model = fairCoinResourceModel Q interface :=
  Iff.rfl


-- @@ L322-328 verbatim
/-- The canonical resource model packaged with its fair-coin contract evidence. -/
def fairCoinModel {C : StepClass}
    [C.HasProd] [C.HasSum] [C.HasOption]
    (Q : QuantitativeStepClass C)
    (interface : InterfaceBoundary C coinSpec.toPFunctor) :
    (fairCoinContract Q interface).Model :=
  ⟨fairCoinResourceModel Q interface, rfl⟩


-- @@ L330-338 verbatim
/-- The fair-coin contract admits no resource model other than the canonical one. -/
theorem fairCoinModel_eq {C : StepClass}
    [C.HasProd] [C.HasSum] [C.HasOption]
    (Q : QuantitativeStepClass C)
    (interface : InterfaceBoundary C coinSpec.toPFunctor)
    (model : (fairCoinContract Q interface).Model) :
    model = fairCoinModel Q interface := by
  apply Subtype.ext
  exact model.2


-- @@ L340-350 verbatim
/-- Strict probabilistic polynomial time, specialized to the explicit fair-coin interface.

The backend and every boundary representation remain explicit, while the oracle contract is fixed
to `fairCoinContract`. Fairness belongs to VCVio's probability interpretation of `coinSpec`;
strict cost still quantifies over both Boolean answers. -/
def IsPPTBy {input output : Type} {C : StepClass}
    [C.HasProd] [C.HasSum] [C.HasOption]
    (Q : QuantitativeStepClass C)
    (bd : Boundary C coinSpec.toPFunctor input output)
    (program : input → OracleComp coinSpec output) : Prop :=
  OracleProgram.IsOraclePPTBy Q bd (fairCoinContract Q bd.interface) program


-- @@ L352-352 verbatim
/-! ## Security-family resource contracts -/


-- @@ L354-354 verbatim
namespace SecurityFamily


-- @@ L356-363 verbatim
/-- The raw dependent sum of parameter-indexed resource labels.

This is only a carrier construction, not a way for one finite second-order-polynomial expression
to select its current security parameter dynamically. A polynomial can mention only finitely many
concrete inhabitants of this sum. Uniform families should therefore normally classify queries by
a fixed global port-label type; use this carrier only when those finitely mentioned sigma labels
have an independently justified meaning. -/
abbrev ParameterizedLabel (label : ℕ → Type x) := (n : ℕ) × label n


-- @@ L365-368 verbatim
variable {index : ℕ → Type u} {spec : (n : ℕ) → OracleSpec.{u, u} (index n)}
  {C : StepClass.{u, v}} {Q : QuantitativeStepClass.{u, v, w} C}
  {interface : InterfaceBoundary C (OracleComp.SecurityFamily.Spec spec).toPFunctor}
  {label : Type x}


-- @@ L370-375 verbatim
/-- Pack a member-wise query classification into the sigma interface used by
`SecurityFamily.packProgram`. The result type is one global resource-label space, so one uniform
second-order polynomial can refer to its symbols. -/
def packedLabelOf (labelOf : ∀ n, (spec n).Domain → label) :
    (OracleComp.SecurityFamily.Spec spec).Domain → label
  | ⟨n, position⟩ => labelOf n position


-- @@ L377-381 verbatim
@[simp]
theorem packedLabelOf_apply (labelOf : ∀ n, (spec n).Domain → label)
    (n : ℕ) (position : (spec n).Domain) :
    packedLabelOf labelOf ⟨n, position⟩ = labelOf n position :=
  rfl


-- @@ L383-402 verbatim
/-- A resource model presented member-by-member before packing a security family.

This is only an ergonomic view of `OracleResourceModel`: executable costs and encoded sizes still
come from the explicit quantitative backend `Q` and the pinned packed interface boundary. No
machine model, encoding, or complexity library is definitionally selected here. -/
structure ResourceModel
    (Q : QuantitativeStepClass.{u, v, w} C)
    (interface : InterfaceBoundary C (OracleComp.SecurityFamily.Spec spec).toPFunctor)
    (labelOf : ∀ n, (spec n).Domain → label) where
  /-- Replies admitted for each parameter and typed query position. -/
  allows : ∀ n (position : (spec n).Domain), (spec n).Range position → Prop
  /-- Tagged-response size envelope for each global interface label. -/
  responseSize : label → ℕ → ℕ
  /-- Every response-size envelope is monotone in encoded query size. -/
  responseSize_monotone : ∀ interface, Monotone (responseSize interface)
  /-- Every admitted typed reply fits its packed tagged-response envelope. -/
  responseSize_le : ∀ n (position : (spec n).Domain) (answer : (spec n).Range position),
    allows n position answer →
      Q.size interface.idx ⟨⟨n, position⟩, answer⟩ ≤
        responseSize (labelOf n position) (Q.size interface.pos ⟨n, position⟩)


-- @@ L404-404 verbatim
namespace ResourceModel


-- @@ L406-406 verbatim
variable {labelOf : ∀ n, (spec n).Domain → label}


-- @@ L408-415 verbatim
/-- Pack a family resource model into the backend-neutral core contract layer. -/
def pack (model : ResourceModel Q interface labelOf) :
    OracleResourceModel Q interface (packedLabelOf labelOf) where
  allows := fun ⟨n, position⟩ answer ↦ model.allows n position answer
  responseSize := model.responseSize
  responseSize_monotone := model.responseSize_monotone
  responseSize_le := fun ⟨n, position⟩ answer hanswer ↦
    model.responseSize_le n position answer hanswer


-- @@ L417-424 verbatim
/-- Present a packed resource model member-by-member. -/
def unpack (model : OracleResourceModel Q interface (packedLabelOf labelOf)) :
    ResourceModel Q interface labelOf where
  allows := fun n position answer ↦ model.allows ⟨n, position⟩ answer
  responseSize := model.responseSize
  responseSize_monotone := model.responseSize_monotone
  responseSize_le := fun n position answer hanswer ↦
    model.responseSize_le ⟨n, position⟩ answer hanswer


-- @@ L426-430 verbatim
@[simp]
theorem unpack_pack (model : ResourceModel Q interface labelOf) :
    unpack model.pack = model := by
  cases model
  rfl


-- @@ L432-436 verbatim
@[simp]
theorem pack_unpack (model : OracleResourceModel Q interface (packedLabelOf labelOf)) :
    pack (unpack model) = model := by
  cases model
  rfl


-- @@ L438-444 verbatim
/-- Family and packed presentations of a resource model are equivalent data. -/
def equiv : ResourceModel Q interface labelOf ≃
    OracleResourceModel Q interface (packedLabelOf labelOf) where
  toFun := pack
  invFun := unpack
  left_inv := unpack_pack
  right_inv := pack_unpack


-- @@ L446-446 verbatim
end ResourceModel


-- @@ L448-461 verbatim
/-- A contract stated over the members of a security family.

Packing this structure produces an ordinary `OracleContract`, so all strict-PPT definitions remain
parametric in the quantitative backend and consume the same small core interface. -/
structure ResourceContract
    (Q : QuantitativeStepClass.{u, v, w} C)
    (interface : InterfaceBoundary C (OracleComp.SecurityFamily.Spec spec).toPFunctor)
    (label : Type x) where
  /-- Interface label of each member's query positions. -/
  labelOf : ∀ n, (spec n).Domain → label
  /-- Resource environments admitted by this family contract. -/
  admissible : ResourceModel Q interface labelOf → Prop
  /-- The family contract admits at least one global finite resource envelope. -/
  model_nonempty : ∃ model, admissible model


-- @@ L463-463 verbatim
namespace ResourceContract


-- @@ L465-465 verbatim
variable (contract : ResourceContract Q interface label)


-- @@ L467-473 verbatim
/-- Pack a family contract into the core oracle-contract layer. -/
def pack : OracleContract Q interface label where
  labelOf := packedLabelOf contract.labelOf
  admissible model := contract.admissible (ResourceModel.unpack model)
  model_nonempty := by
    obtain ⟨model, hmodel⟩ := contract.model_nonempty
    exact ⟨model.pack, by simpa using hmodel⟩


-- @@ L475-477 verbatim
/-- A resource environment compatible with a family contract. -/
abbrev Model := { model : ResourceModel Q interface contract.labelOf //
  contract.admissible model }


-- @@ L479-479 verbatim
namespace Model


-- @@ L481-481 verbatim
variable {contract : ResourceContract Q interface label}


-- @@ L483-486 verbatim
/-- Forget that a family resource environment satisfies its contract. -/
abbrev resourceModel (model : contract.Model) :
    ResourceModel Q interface contract.labelOf :=
  model.1


-- @@ L488-493 verbatim
/-- Pack a compatible family model for use by the core strict-PPT witness. -/
def pack (model : contract.Model) : contract.pack.Model :=
  ⟨model.resourceModel.pack, by
    change contract.admissible (ResourceModel.unpack model.resourceModel.pack)
    rw [ResourceModel.unpack_pack]
    exact model.2⟩


-- @@ L495-497 verbatim
/-- Recover the family presentation of a compatible packed model. -/
def unpack (model : contract.pack.Model) : contract.Model :=
  ⟨ResourceModel.unpack model.1, model.2⟩


-- @@ L499-502 verbatim
@[simp]
theorem unpack_pack (model : contract.Model) : unpack model.pack = model := by
  apply Subtype.ext
  exact ResourceModel.unpack_pack model.resourceModel


-- @@ L504-507 verbatim
@[simp]
theorem pack_unpack (model : contract.pack.Model) : pack (unpack model) = model := by
  apply Subtype.ext
  exact ResourceModel.pack_unpack model.1


-- @@ L509-509 verbatim
end Model


-- @@ L511-511 verbatim
end ResourceContract


-- @@ L513-513 verbatim
end SecurityFamily


-- @@ L515-529 verbatim
/-- Strict PPT for a security-indexed family means strict PPT of its one packed program.

This requires one shared realization and one shared polynomial across all security parameters. It
is strictly stronger than choosing unrelated witnesses pointwise. -/
def SecurityFamily.IsOraclePPTBy
    {index : ℕ → Type u} {spec : (n : ℕ) → OracleSpec.{u, u} (index n)}
    {input output : ℕ → Type u} {C : StepClass.{u, v}}
    [C.HasProd] [C.HasSum] [C.HasOption]
    [DecidableEq (SecurityFamily.Spec spec).Domain]
    (Q : QuantitativeStepClass.{u, v, w} C)
    (bd : Boundary C (SecurityFamily.Spec spec).toPFunctor
      (SecurityFamily.Input input) (SecurityFamily.Output output))
    {label : Type x} (contract : OracleContract Q bd.interface label)
    (program : (n : ℕ) → input n → OracleComp (spec n) (output n)) : Prop :=
  OracleProgram.IsOraclePPTBy Q bd contract (SecurityFamily.packProgram program)


-- @@ L531-545 verbatim
/-- Uniform strict oracle PPT using a member-by-member family resource contract.

This is an ergonomic adapter to `SecurityFamily.IsOraclePPTBy`; it does not change the trusted
complexity predicate or select a concrete backend. -/
def SecurityFamily.IsOraclePPTByContract
    {index : ℕ → Type u} {spec : (n : ℕ) → OracleSpec.{u, u} (index n)}
    {input output : ℕ → Type u} {C : StepClass.{u, v}}
    [C.HasProd] [C.HasSum] [C.HasOption]
    [DecidableEq (SecurityFamily.Spec spec).Domain]
    (Q : QuantitativeStepClass.{u, v, w} C)
    (bd : Boundary C (SecurityFamily.Spec spec).toPFunctor
      (SecurityFamily.Input input) (SecurityFamily.Output output))
    {label : Type x} (contract : SecurityFamily.ResourceContract Q bd.interface label)
    (program : (n : ℕ) → input n → OracleComp (spec n) (output n)) : Prop :=
  SecurityFamily.IsOraclePPTBy Q bd contract.pack program


-- @@ L547-548 verbatim
/-- An explicit synonym emphasizing strict pathwise bounds for a packed oracle family. -/
abbrev SecurityFamily.IsStrictPPTBy := @SecurityFamily.IsOraclePPTBy


-- @@ L550-565 verbatim
/-- Uniform strict oracle PPT for a packed security family whose only syntactic interaction is a
fair coin.

The explicit contract must additionally control how the packed security parameter contributes to
the boundary's encoded query and tagged-answer sizes. Deriving that contract requires a
quantitative encoding-growth certificate and cannot be done from an arbitrary `Boundary` alone. -/
def SecurityFamily.IsCoinPPTByUnder
    {input output : ℕ → Type} {C : StepClass}
    [C.HasProd] [C.HasSum] [C.HasOption]
    [DecidableEq (SecurityFamily.Spec (fun _ : ℕ ↦ coinSpec)).Domain]
    (Q : QuantitativeStepClass C)
    (bd : Boundary C (SecurityFamily.Spec (fun _ : ℕ ↦ coinSpec)).toPFunctor
      (SecurityFamily.Input input) (SecurityFamily.Output output))
    {label : Type x} (contract : OracleContract Q bd.interface label)
    (program : (n : ℕ) → input n → OracleComp coinSpec (output n)) : Prop :=
  SecurityFamily.IsOraclePPTBy Q bd contract program


-- @@ L567-567 verbatim
end OracleComp.Complexity
