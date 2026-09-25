import Clean.Circuit.Basic
import Clean.Circuit.Subcircuit
import Clean.Circuit.Theorems


-- @@ L5-6 verbatim
variable {F : Type} [FiniteField F]
  {Input Mid Output : TypeMap} [ProvableType Input] [ProvableType Mid] [ProvableType Output]


-- @@ L8-8 verbatim
namespace FormalCircuit

-- @@ L9-10 verbatim
instance (circuit : FormalCircuit F Input Output) : ElaboratedCircuit F Input Output circuit.main :=
  circuit.elaborated


-- @@ L12-48 expanded
/-- Concatenate two FormalCircuits into a single FormalCircuit.

This combinator requires:
- A compatibility proof that the first circuit's spec implies the second circuit's assumptions
- A proof that circuit1's output is independent of the offset (h_output_stable)

The composite circuit:
- Has the assumptions of the first circuit
- Has a spec stating that there exists an intermediate value such that both component specs hold
-/
def concat (circuit1 : FormalCircuit F Input Mid) (circuit2 : FormalCircuit F Mid Output)
    (h_compat :
      ∀ input mid, circuit1.Assumptions input → circuit1.Spec input mid → circuit2.Assumptions mid)
    (h_localLength_stable : ∀ mid mid', circuit2.localLength mid = circuit2.localLength mid') :
    FormalCircuit F Input Output
    where
  main := (circuit1 · >>= circuit2)
  elaborated :=
    .fromExplicit
        (by (
            try unfold_explicit_circuits_head
            try dsimp only
            apply ExplicitCircuits.fromSingle
            intro a
            ( try intros
              repeat
                ( try intros
                  first
                  | infer_explicit_head
                  | cases_match_discr
                  | apply ExplicitCircuit.from_bind
                  | apply ExplicitCircuit.from_map
                  | apply ExplicitCircuit.from_pure
                  | infer_instance
                  try infer_instance)
              done))) <|
      by
      constructor
      · intro a n m
        change
          circuit1.localLength a + circuit2.localLength (circuit1.output a n) =
            circuit1.localLength a + circuit2.localLength (circuit1.output a m)
        rw [h_localLength_stable]
      · intro a a' n m
        change
          circuit1.channelsWithGuarantees ++ circuit2.channelsWithGuarantees =
            circuit1.channelsWithGuarantees ++ circuit2.channelsWithGuarantees
        rfl
  channelsWithRequirements := circuit1.channelsWithRequirements ++ circuit2.channelsWithRequirements
  Assumptions := circuit1.Assumptions
  Spec input output := ∃ mid, circuit1.Spec input mid ∧ circuit2.Spec mid output
  soundness := by
    simp only [circuit_norm]
    aesop
  completeness := by
    simp only [circuit_norm]
    aesop


-- @@ L50-53 verbatim
@[circuit_norm]
lemma concat_assumptions (c1 : FormalCircuit F Input Mid) (c2 : FormalCircuit F Mid Output) p0 p1 :
    (c1.concat c2 p0 p1).Assumptions = c1.Assumptions := by
  simp only [concat]


-- @@ L55-60 verbatim
@[circuit_norm]
lemma concat_localLength (c1 : FormalCircuit F Input Mid) (c2 : FormalCircuit F Mid Output) p0 p1 inp :
  (c1.concat c2 p0 p1).localLength inp =
    c1.localLength inp + c2.localLength (c1.output inp 0) := by
  change c1.localLength inp + c2.localLength (c1.output inp 0) = _
  rfl


-- @@ L62-67 verbatim
@[circuit_norm]
lemma concat_localLength' (c1 : FormalCircuit F Input Mid) (c2 : FormalCircuit F Mid Output) p0 p1 inp :
  ElaboratedCircuit.localLength (c1.concat c2 p0 p1).main inp =
    c1.localLength inp + c2.localLength (c1.output inp 0) := by
  change c1.localLength inp + c2.localLength (c1.output inp 0) = _
  rfl


-- @@ L69-73 verbatim
@[circuit_norm]
lemma concat_channelsWithGuarantees (c1 : FormalCircuit F Input Mid) (c2 : FormalCircuit F Mid Output) p0 p1 :
    (c1.concat c2 p0 p1).channelsWithGuarantees = c1.channelsWithGuarantees ++ c2.channelsWithGuarantees := by
  change c1.channelsWithGuarantees ++ c2.channelsWithGuarantees = _
  rfl


-- @@ L75-80 verbatim
@[circuit_norm]
lemma concat_channelsWithGuarantees' (c1 : FormalCircuit F Input Mid) (c2 : FormalCircuit F Mid Output) p0 p1 :
    ElaboratedCircuit.channelsWithGuarantees (c1.concat c2 p0 p1).main =
      c1.channelsWithGuarantees ++ c2.channelsWithGuarantees := by
  change c1.channelsWithGuarantees ++ c2.channelsWithGuarantees = _
  rfl


-- @@ L82-117 verbatim
/--
Weaken the specification of a FormalCircuit.

This combinator takes a FormalCircuit with a strong specification and produces
a new FormalCircuit with a weaker specification. This is useful when:
- You have a circuit that proves more than you need
- You want to compose circuits where the specs don't match exactly
- You need to adapt a specific circuit to a more general interface

The requirements are:
- The assumptions remain the same
- The stronger spec and the assumption imply the weaker spec
-/
def weakenSpec (circuit : FormalCircuit F Input Output)
    (WeakerSpec : Input F → Output F → Prop)
    (h_spec_implication : ∀ input output,
      circuit.Assumptions input →
      circuit.Spec input output →
      WeakerSpec input output) :
    FormalCircuit F Input Output where
  main := circuit.main
  elaborated := circuit.elaborated
  channelsWithRequirements := circuit.channelsWithRequirements
  requirementsChannelsLawful := circuit.requirementsChannelsLawful
  Assumptions := circuit.Assumptions
  Spec := WeakerSpec
  soundness := by
    intro offset env input_var input h_eval h_assumptions h_holds
    -- Use the original circuit's soundness
    have h_strong_spec := circuit.soundness offset env input_var input h_eval h_assumptions h_holds
    -- Apply the implication to get the weaker spec
    exact ⟨h_spec_implication input _ h_assumptions h_strong_spec.1, h_strong_spec.2⟩
  completeness := by
    -- Completeness is preserved since we use the same elaborated circuit
    -- and the same assumptions
    exact circuit.completeness


-- @@ L119-122 verbatim
@[circuit_norm] lemma weakenSpec_assumptions
    (c : FormalCircuit F Input Output) (WeakerSpec : Input F → Output F → Prop) h_spec_implication :
    (c.weakenSpec WeakerSpec h_spec_implication).Assumptions = c.Assumptions := by
  simp only [weakenSpec]


-- @@ L124-128 verbatim
@[circuit_norm] lemma weakenSpec_localLength
    (c : FormalCircuit F Input Output) (WeakerSpec : Input F → Output F → Prop) h_spec_implication
    (input : Var Input F) :
    (c.weakenSpec WeakerSpec h_spec_implication).localLength input = c.localLength input := by
  rfl


-- @@ L130-134 verbatim
@[circuit_norm] lemma weakenSpec_localLength'
    (c : FormalCircuit F Input Output) (WeakerSpec : Input F → Output F → Prop) h_spec_implication
    (input : Var Input F) :
    ElaboratedCircuit.localLength (c.weakenSpec WeakerSpec h_spec_implication).main input = c.localLength input := by
  rfl


-- @@ L136-140 verbatim
@[circuit_norm] lemma weakenSpec_output
    (c : FormalCircuit F Input Output) (WeakerSpec : Input F → Output F → Prop) h_spec_implication
    (input : Var Input F) (offset : Nat) :
    (c.weakenSpec WeakerSpec h_spec_implication).output input offset = c.output input offset := by
  rfl


-- @@ L142-146 verbatim
@[circuit_norm] lemma weakenSpec_output'
    (c : FormalCircuit F Input Output) (WeakerSpec : Input F → Output F → Prop) h_spec_implication
    (input : Var Input F) (offset : Nat) :
    ElaboratedCircuit.output (c.weakenSpec WeakerSpec h_spec_implication).main input offset = c.output input offset := by
  rfl


-- @@ L148-150 verbatim
@[circuit_norm] lemma weakenSpec_channelsWithGuarantees
    (c : FormalCircuit F Input Output) (WeakerSpec : Input F → Output F → Prop) h_spec_implication :
    (c.weakenSpec WeakerSpec h_spec_implication).channelsWithGuarantees = c.channelsWithGuarantees := rfl


-- @@ L152-154 verbatim
@[circuit_norm] lemma weakenSpec_channelsWithGuarantees'
    (c : FormalCircuit F Input Output) (WeakerSpec : Input F → Output F → Prop) h_spec_implication :
    ElaboratedCircuit.channelsWithGuarantees (c.weakenSpec WeakerSpec h_spec_implication).main = c.channelsWithGuarantees := rfl


-- @@ L156-159 verbatim
@[circuit_norm] lemma weakenSpec_channelsWithRequirements
    (c : FormalCircuit F Input Output) (WeakerSpec : Input F → Output F → Prop) h_spec_implication :
    (c.weakenSpec WeakerSpec h_spec_implication).channelsWithRequirements = c.channelsWithRequirements := by
  simp only [weakenSpec]

-- @@ L160-160 verbatim
end FormalCircuit


-- @@ L162-162 verbatim
namespace GeneralFormalCircuit

-- @@ L163-183 verbatim
/--
Weaken the specification of a GeneralFormalCircuit.
-/
def weakenSpec (circuit : GeneralFormalCircuit F Input Output)
    (WeakerSpec : Input F → Output F → ProverData F → Prop)
    (h_spec_implication : ∀ input output data,
      circuit.Spec input output data → WeakerSpec input output data) :
    GeneralFormalCircuit F Input Output where
  main := circuit.main
  elaborated := circuit.elaborated
  channelsWithRequirements := circuit.channelsWithRequirements
  requirementsChannelsLawful := circuit.requirementsChannelsLawful
  Assumptions := circuit.Assumptions
  Spec := WeakerSpec
  ProverAssumptions := circuit.ProverAssumptions
  ProverSpec := circuit.ProverSpec
  soundness := by
    intro offset env input_var input h_eval h_assumptions h_holds
    have h_strong_spec := circuit.soundness offset env input_var input h_eval h_assumptions h_holds
    exact ⟨ h_spec_implication input _ _ h_strong_spec.1, h_strong_spec.2 ⟩
  completeness := circuit.completeness


-- @@ L185-190 verbatim
@[circuit_norm]
lemma weakenSpec_assumptions (c : GeneralFormalCircuit F Input Output)
    (WeakerSpec : Input F → Output F → ProverData F → Prop)
    h_spec_implication :
    (c.weakenSpec WeakerSpec h_spec_implication).Assumptions = c.Assumptions := by
  simp only [GeneralFormalCircuit.weakenSpec]

-- @@ L191-191 verbatim
end GeneralFormalCircuit
