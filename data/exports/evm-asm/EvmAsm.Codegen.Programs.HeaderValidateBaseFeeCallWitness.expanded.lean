/-
  EvmAsm.Codegen.Programs.HeaderValidateBaseFeeCallWitness

  A constructive non-vacuity witness for the H+132 call to
  `header_validate_base_fee`.

  `validate_header_base_fee_call_spec_within` takes its `hcallee` premise in
  the `baseEntryRest` vocabulary.  A positive-control search shows that no
  theorem anywhere concludes in that vocabulary, so the premise has no
  producer on main.  This file deliberately proves the other half only:
  the complete call-frame assertion `(.x1 ↦ᵣ BaseRet) ** baseEntryRest …`
  at the H+132 caller instantiation is jointly inhabitable at a concrete,
  non-degenerate point.  The two frame slots live at real stack addresses and
  the saved `x8` holds a nonzero register value, so the witness is not an
  `emp` artefact.  It does not claim that a whole-routine `baseCalleePost`
  machine triple exists, nor that this is the only caller.
-/

import EvmAsm.Codegen.Programs.HeaderValidateExcessBlobGasSpec
import EvmAsm.Rv64.MemSat


-- @@ L22-22 verbatim
namespace EvmAsm.Codegen.ValidateHeaderGasCorrespondence


-- @@ L24-24 verbatim
open EvmAsm EvmAsm.Rv64 EvmAsm.Rv64.SAsm


-- @@ L26-26 verbatim
/-! ## Concrete non-degenerate call-site values -/


-- @@ L28-28 verbatim
private def witnessSp0 : Word := 0x10000

-- @@ L29-29 verbatim
private def witnessNewSp : Word := witnessSp0 + signExtend12 (-16 : BitVec 12)

-- @@ L30-30 verbatim
private def witnessThisPtr : Word := 0x20000

-- @@ L31-31 verbatim
private def witnessParentPtr : Word := 0x30000

-- @@ L32-32 verbatim
private def witnessGasLimit : Word := 120000000

-- @@ L33-33 verbatim
private def witnessGasUsed : Word := 50000000

-- @@ L34-35 verbatim
private def witnessVals : Reg → Word :=
  fun r => if r = .x8 then 0x404 else 0


-- @@ L37-37 verbatim
/-! ## One resource key per separating-conjunction atom -/


-- @@ L39-42 verbatim
private structure WitnessMem where
  a : Word
  v : Word
  valid : isValidDwordAccess a = true


-- @@ L44-48 verbatim
private inductive WitnessAtom where
  | reg (r : Reg) (v : Word)
  | regOwn (r : Reg)
  | mem (m : WitnessMem)
  | memOwn (m : WitnessMem)


-- @@ L50-54 verbatim
private def witnessAtomAssertion : WitnessAtom → Assertion
  | .reg r v => r ↦ᵣ v
  | .regOwn r => regOwn r
  | .mem m => m.a ↦ₘ m.v
  | .memOwn m => memOwn m.a


-- @@ L56-60 verbatim
private def witnessAtomHeap : WitnessAtom → PartialState
  | .reg r v => PartialState.singletonReg r v
  | .regOwn r => PartialState.singletonReg r 0
  | .mem m => PartialState.singletonMem m.a m.v
  | .memOwn m => PartialState.singletonMem m.a 0


-- @@ L62-65 verbatim
private inductive WitnessResource where
  | reg (r : Reg)
  | mem (a : Word)
  deriving DecidableEq


-- @@ L67-71 verbatim
private def witnessAtomResource : WitnessAtom → WitnessResource
  | .reg r _ => .reg r
  | .regOwn r => .reg r
  | .mem m => .mem m.a
  | .memOwn m => .mem m.a


-- @@ L73-85 verbatim
private theorem witness_reg_reg_disjoint {r1 r2 : Reg} {v1 v2 : Word}
    (hne : r1 ≠ r2) :
    (PartialState.singletonReg r1 v1).Disjoint
      (PartialState.singletonReg r2 v2) := by
  refine ⟨?_, fun _ => Or.inl rfl, fun _ => Or.inl rfl,
    Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl⟩
  intro r
  by_cases h : r = r1
  · subst r
    right
    simp [PartialState.singletonReg, hne]
  · left
    simp [PartialState.singletonReg, h]


-- @@ L87-99 verbatim
private theorem witness_mem_mem_disjoint {a1 a2 : Word} {v1 v2 : Word}
    (hne : a1 ≠ a2) :
    (PartialState.singletonMem a1 v1).Disjoint
      (PartialState.singletonMem a2 v2) := by
  refine ⟨fun _ => Or.inl rfl, ?_, fun _ => Or.inl rfl,
    Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl⟩
  intro a
  by_cases h : a = a1
  · subst a
    right
    simp [PartialState.singletonMem, hne]
  · left
    simp [PartialState.singletonMem, h]


-- @@ L101-105 verbatim
private theorem witness_reg_mem_disjoint {r : Reg} {a : Word} {v w : Word} :
    (PartialState.singletonReg r v).Disjoint
      (PartialState.singletonMem a w) := by
  exact ⟨fun _ => Or.inr rfl, fun _ => Or.inl rfl, fun _ => Or.inl rfl,
    Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl⟩


-- @@ L107-110 verbatim
private theorem witness_mem_reg_disjoint {r : Reg} {a : Word} {v w : Word} :
    (PartialState.singletonMem a v).Disjoint
      (PartialState.singletonReg r w) :=
  witness_reg_mem_disjoint.symm


-- @@ L112-139 verbatim
private theorem witnessAtomHeap_disjoint_of_resource_ne {x y : WitnessAtom}
    (h : witnessAtomResource x ≠ witnessAtomResource y) :
    (witnessAtomHeap x).Disjoint (witnessAtomHeap y) := by
  cases x <;> cases y
  · apply witness_reg_reg_disjoint
    simpa [witnessAtomResource] using h
  · apply witness_reg_reg_disjoint
    simpa [witnessAtomResource] using h
  · exact witness_reg_mem_disjoint
  · exact witness_reg_mem_disjoint
  · apply witness_reg_reg_disjoint
    simpa [witnessAtomResource] using h
  · apply witness_reg_reg_disjoint
    simpa [witnessAtomResource] using h
  · exact witness_reg_mem_disjoint
  · exact witness_reg_mem_disjoint
  · exact witness_mem_reg_disjoint
  · exact witness_mem_reg_disjoint
  · apply witness_mem_mem_disjoint
    simpa [witnessAtomResource] using h
  · apply witness_mem_mem_disjoint
    simpa [witnessAtomResource] using h
  · exact witness_mem_reg_disjoint
  · exact witness_mem_reg_disjoint
  · apply witness_mem_mem_disjoint
    simpa [witnessAtomResource] using h
  · apply witness_mem_mem_disjoint
    simpa [witnessAtomResource] using h


-- @@ L141-144 verbatim
/-! The atom list mirrors `(.x1 ↦ᵣ BaseRet) ** baseEntryRest …` exactly:
the linking `x1` register first, then the caller stack pointer, the two
`baseFrame` slots as owned cells, the saved `x8` value, the four argument
registers, the seven owned scratch registers, and `x0`. -/


-- @@ L146-164 verbatim
private def witnessAtoms : List WitnessAtom :=
  [ .reg .x1 BaseRet
  , .reg .x2 witnessSp0
  , .memOwn ⟨witnessNewSp, 0, by decide⟩
  , .memOwn ⟨witnessNewSp + 8, 0, by decide⟩
  , .reg .x8 (witnessVals .x8)
  , .reg .x10 (witnessThisPtr + 96)
  , .reg .x11 witnessGasLimit
  , .reg .x12 witnessGasUsed
  , .reg .x13 (witnessParentPtr + 96)
  , .regOwn .x5
  , .regOwn .x6
  , .regOwn .x7
  , .regOwn .x28
  , .regOwn .x29
  , .regOwn .x30
  , .regOwn .x31
  , .reg .x0 0
  ]


-- @@ L166-171 verbatim
private theorem witnessAtoms_resource_pairwise :
    witnessAtoms.Pairwise
      (fun x y => witnessAtomResource x ≠ witnessAtomResource y) := by
  unfold witnessAtoms witnessAtomResource witnessSp0 witnessNewSp
    witnessThisPtr witnessParentPtr witnessGasLimit witnessGasUsed witnessVals
  decide


-- @@ L173-174 verbatim
private def witnessHeap : PartialState :=
  witnessAtoms.foldr (fun x acc => (witnessAtomHeap x).union acc) PartialState.empty


-- @@ L176-188 verbatim
private theorem witnessAtoms_hsat :
    (witnessAtoms.foldr (fun x acc => witnessAtomAssertion x ** acc) empAssertion)
      witnessHeap := by
  apply sepConj_foldr_satisfiable witnessAtomAssertion witnessAtomHeap witnessAtoms
  · intro x hx
    cases x with
    | reg r v => exact rfl
    | regOwn r => exact ⟨0, rfl⟩
    | mem m => exact ⟨rfl, m.valid⟩
    | memOwn m => exact ⟨0, rfl, m.valid⟩
  · exact List.Pairwise.imp
      (fun {_ _} h => witnessAtomHeap_disjoint_of_resource_ne h)
      witnessAtoms_resource_pairwise


-- @@ L190-203 verbatim
private theorem witness_assertion_inhabited :
    ∃ h : PartialState,
      ((.x1 ↦ᵣ BaseRet) **
        baseEntryRest witnessSp0 witnessVals
          (witnessThisPtr + 96) witnessGasLimit witnessGasUsed
          (witnessParentPtr + 96) empAssertion) h := by
  refine ⟨witnessHeap, ?_⟩
  have hsat := witnessAtoms_hsat
  simp [witnessAtomAssertion, witnessAtomHeap, witnessHeap, witnessAtoms,
    witnessSp0, witnessNewSp, witnessThisPtr, witnessParentPtr, witnessGasLimit,
    witnessGasUsed, witnessVals, baseEntryRest, baseFrame, baseSavedFrame,
    regsAt, frameSlotsOwn, regOwns, signExtend12,
    sepConj_emp_right', sepConj_assoc'] at hsat ⊢
  xperm_hyp hsat


-- @@ L205-226 verbatim
/-- The whole H+132 `hcallee` premise is jointly inhabited at a
non-degenerate point.  The `baseEntryRest` vocabulary has no producer on
main (positive-control search), so this is the other half of the
inhabitance question: the call-frame assertion itself is satisfiable, and
only the missing whole-routine `baseCalleePost` machine triple separates
`hcallee` from being dischargeable. -/
theorem header_validate_base_fee_call_pre_non_degenerate_inhabited :
    ∃ h : PartialState,
      witnessThisPtr ≠ witnessParentPtr ∧
      witnessGasLimit ≠ 0 ∧
      witnessGasUsed ≠ 0 ∧
      witnessGasLimit ≠ witnessGasUsed ∧
      ((.x1 ↦ᵣ BaseRet) **
        baseEntryRest witnessSp0 witnessVals
          (witnessThisPtr + 96) witnessGasLimit witnessGasUsed
          (witnessParentPtr + 96) empAssertion) h := by
  obtain ⟨h, hh⟩ := witness_assertion_inhabited
  refine ⟨h, ?_, ?_, ?_, ?_, hh⟩
  · decide
  · decide
  · decide
  · decide


-- @@ L228-228 verbatim
#print axioms header_validate_base_fee_call_pre_non_degenerate_inhabited


-- @@ L230-230 verbatim
end EvmAsm.Codegen.ValidateHeaderGasCorrespondence