/-
  Concrete entry-state witness for `amsterdam_blob_gas_price_u256`.

  The witness uses excess_blob_gas = 0, but that is not a short-circuit: the
  nonzero Taylor constant drives the local recurrence and final division.
-/
import EvmAsm.Codegen.Programs.Header
import EvmAsm.Codegen.Programs.U256
import EvmAsm.Codegen.Programs.U256DivU64BeSAsm
import EvmAsm.Codegen.Proofs.U256BeFlatTriples
import EvmAsm.Codegen.Proofs.U256IsZeroSpec
import EvmAsm.Rv64.SAsm.AbiFrame
import EvmAsm.Rv64.SAsm.FnFlat
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.Word
import EvmAsm.Stateless.SpecRef.TaylorExponential


-- @@ L18-18 verbatim
namespace EvmAsm.Codegen.AmsterdamBlobGasPriceU256Sat


-- @@ L20-20 verbatim
open EvmAsm.Rv64

-- @@ L21-21 verbatim
open EvmAsm.Rv64.SAsm

-- @@ L22-22 verbatim
open EvmAsm.Codegen

-- @@ L23-23 verbatim
open EvmAsm.Stateless.SpecRef


-- @@ L25-25 verbatim
abbrev B : Word := (GuestAddrs.amsterdam_blob_gas_price_u256 : Word)

-- @@ L26-26 verbatim
def CR : CodeReq := CodeReq.ofProg B amsterdamBlobGasPriceU256_prog


-- @@ L28-29 verbatim
/-! The replacement is self-contained: its restoring multiply/divide loops are
    local, so the whole linked requirement is exactly the Amsterdam body. -/

-- @@ L30-30 verbatim
def fullCR : CodeReq := CR


-- @@ L32-32 verbatim
def sampleSp0 : Word := (0xa0050000 : Word)

-- @@ L33-33 verbatim
def sampleRet : Word := (0x8000af00 : Word)

-- @@ L34-34 verbatim
def sampleOutPtr : Word := (0xa0010100 : Word)

-- @@ L35-35 verbatim
def sampleNewSp : Word := sampleSp0 + signExtend12 (-208 : BitVec 12)

-- @@ L36-36 verbatim
def sampleStackA : Word := sampleNewSp + (64 : Word)

-- @@ L37-37 verbatim
def sampleStackB : Word := sampleNewSp + (112 : Word)

-- @@ L38-38 verbatim
def sampleStackC : Word := sampleNewSp + (160 : Word)


-- @@ L40-42 verbatim
def sampleFrame : FrameDesc :=
  [(.x1, 0), (.x8, 8), (.x9, 16), (.x18, 24), (.x19, 32), (.x20, 40),
   (.x21, 48), (.x22, 56)]


-- @@ L44-53 verbatim
def sampleSaved : Reg → Word
  | .x1 => sampleRet
  | .x8 => (0x101 : Word)
  | .x9 => (0x202 : Word)
  | .x18 => (0x303 : Word)
  | .x19 => (0x404 : Word)
  | .x20 => (0x505 : Word)
  | .x21 => (0x606 : Word)
  | .x22 => (0x707 : Word)
  | _ => 0


-- @@ L55-55 verbatim
def zero32 : List (BitVec 8) := List.replicate 32 0

-- @@ L56-56 verbatim
def zero48 : List (BitVec 8) := List.replicate 48 0


-- @@ L58-69 verbatim
/-- The whole-routine ABI precondition at a concrete, non-overlapping layout. -/
def entryPre : Assertion :=
  ((.x2 : Reg) ↦ᵣ sampleSp0) **
  regsAt sampleFrame (sampleSaved) **
  ((.x10 : Reg) ↦ᵣ (0 : Word)) **
  ((.x11 : Reg) ↦ᵣ sampleOutPtr) **
  frameSlotsOwn sampleFrame sampleNewSp **
  regOwns [.x5, .x6, .x7, .x28, .x29, .x30, .x31] **
  bytesRegion sampleStackA zero48 **
  bytesRegion sampleStackB zero48 **
  bytesRegion sampleStackC zero48 **
  bytesRegion sampleOutPtr zero32


-- @@ L71-78 verbatim
theorem sample_layout :
    sampleSp0 = (0xa0050000 : Word) ∧
    sampleNewSp = (0xa004ff30 : Word) ∧
    sampleStackA = (0xa004ff70 : Word) ∧
    sampleStackB = (0xa004ffa0 : Word) ∧
    sampleStackC = (0xa004ffd0 : Word) := by
  unfold sampleSp0 sampleNewSp sampleStackA sampleStackB sampleStackC
  decide


-- @@ L80-83 verbatim
theorem sample_return_even :
    (sampleRet &&& ~~~(1 : Word)) = sampleRet := by
  unfold sampleRet
  decide


-- @@ L85-87 verbatim
/-! The zero-input path's branch predicates.  The constant loaded by the
    routine is 0xb24b3f = 11684671, so zero input still takes the local
    recurrence and final division. -/


-- @@ L89-89 verbatim
def taylorConstant : Word := (11684671 : Word)


-- @@ L91-94 verbatim
/-! This machine-facing witness consumes the exact bounded model rather than
    merely importing it: the two boundary lemmas below are the arithmetic
    contract for the 384-bit recurrence implemented by the local loops in
    `amsterdamBlobGasPriceU256_prog`. -/

-- @@ L95-95 verbatim
def taylorModelResult (excess : Nat) : Option Nat := taylorExp384 excess


-- @@ L97-100 verbatim
theorem taylorModelResult_10D :
    taylorModelResult (10 * taylorDenominator) =
      some (taylorExpNat 1 (10 * taylorDenominator) taylorDenominator) := by
  simpa [taylorModelResult] using taylorExp384_some_witness_10D


-- @@ L102-107 verbatim
theorem taylorModelResult_boundary_none :
    taylorModelResult 2073394371 = none := by
  have h_num : 2073394371 < taylorWord64Bound := by decide
  have h_ge := taylorExp384_none_witness_measured.1
  simpa [taylorModelResult] using
    (taylorExp384_none_iff_ge 2073394371 h_num).2 h_ge


-- @@ L109-111 verbatim
theorem sample_constant_nonzero : taylorConstant ≠ 0 := by
  unfold taylorConstant
  decide


-- @@ L113-115 verbatim
theorem sample_divisor_positive : 0 < taylorConstant.toNat := by
  unfold taylorConstant
  decide


-- @@ L117-119 verbatim
theorem sample_divisor_bound : taylorConstant.toNat ≤ 2 ^ 56 := by
  unfold taylorConstant
  decide


-- @@ L121-126 verbatim
theorem sample_zero_path_no_overflow :
    (0 : Word) * taylorConstant = 0 ∧
    taylorConstant * (1 : Word) = taylorConstant ∧
    (taylorConstant.toNat * 1) < 2 ^ 64 := by
  unfold taylorConstant
  decide


-- @@ L128-131 verbatim
private theorem add_ofNat_add (base : Word) (i j : Nat) :
    (base + BitVec.ofNat 64 i) + BitVec.ofNat 64 j =
      base + BitVec.ofNat 64 (i + j) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]


-- @@ L133-141 verbatim
theorem zero32_region_expands (base : Word) :
    bytesRegion base zero32 =
      ((base ↦ₘ (0 : Word)) **
        ((base + 8 ↦ₘ (0 : Word)) **
          ((base + 16 ↦ₘ (0 : Word)) **
            (base + 24 ↦ₘ (0 : Word))))) := by
  funext h
  simp [bytesRegion, bytesRegionAux, zero32, packBytes, getByteAt,
    packDword, add_ofNat_add, sepConj_emp_right']


-- @@ L143-153 verbatim
theorem zero48_region_expands (base : Word) :
    bytesRegion base zero48 =
      ((base ↦ₘ (0 : Word)) **
        ((base + 8 ↦ₘ (0 : Word)) **
          ((base + 16 ↦ₘ (0 : Word)) **
            ((base + 24 ↦ₘ (0 : Word)) **
              ((base + 32 ↦ₘ (0 : Word)) **
                (base + 40 ↦ₘ (0 : Word))))))) := by
  funext h
  simp [bytesRegion, bytesRegionAux, zero48, packBytes, getByteAt,
    packDword, add_ofNat_add, sepConj_emp_right']


-- @@ L155-155 verbatim
/-! ## A concrete separating heap for the whole entry pre -/


-- @@ L157-160 verbatim
private inductive Resource where
  | reg (r : Reg)
  | mem (a : Word)
  deriving DecidableEq


-- @@ L162-167 verbatim
private inductive Atom where
  | regVal (r : Reg) (v : Word)
  | regOwn (r : Reg)
  | memVal (a : Word) (v : Word) (valid : isValidDwordAccess a = true)
  | memOwn (a : Word) (valid : isValidDwordAccess a = true)
  deriving DecidableEq


-- @@ L169-173 verbatim
private def atomResource : Atom → Resource
  | .regVal r _ => .reg r
  | .regOwn r => .reg r
  | .memVal a _ _ => .mem a
  | .memOwn a _ => .mem a


-- @@ L175-179 verbatim
private def atomAssertion : Atom → Assertion
  | .regVal r v => r ↦ᵣ v
  | .regOwn r => regOwn r
  | .memVal a v _ => a ↦ₘ v
  | .memOwn a _ => memOwn a


-- @@ L181-185 verbatim
private def atomHeap : Atom → PartialState
  | .regVal r v => PartialState.singletonReg r v
  | .regOwn r => PartialState.singletonReg r 0
  | .memVal a v _ => PartialState.singletonMem a v
  | .memOwn a _ => PartialState.singletonMem a 0


-- @@ L187-199 verbatim
private theorem singletonReg_disjoint {r1 r2 : Reg} {v1 v2 : Word}
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


-- @@ L201-213 verbatim
private theorem singletonMem_disjoint {a1 a2 : Word} {v1 v2 : Word}
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


-- @@ L215-219 verbatim
private theorem singletonReg_mem_disjoint {r : Reg} {a : Word} {v w : Word} :
    (PartialState.singletonReg r v).Disjoint
      (PartialState.singletonMem a w) := by
  exact ⟨fun _ => Or.inr rfl, fun _ => Or.inl rfl, fun _ => Or.inl rfl,
    Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl⟩


-- @@ L221-224 verbatim
private theorem singletonMem_reg_disjoint {r : Reg} {a : Word} {v w : Word} :
    (PartialState.singletonMem a v).Disjoint
      (PartialState.singletonReg r w) :=
  singletonReg_mem_disjoint.symm


-- @@ L226-253 verbatim
private theorem atomHeap_disjoint_of_resource_ne {x y : Atom}
    (h : atomResource x ≠ atomResource y) :
    (atomHeap x).Disjoint (atomHeap y) := by
  cases x <;> cases y
  · apply singletonReg_disjoint
    simpa [atomResource] using h
  · apply singletonReg_disjoint
    simpa [atomResource] using h
  · exact singletonReg_mem_disjoint
  · exact singletonReg_mem_disjoint
  · apply singletonReg_disjoint
    simpa [atomResource] using h
  · apply singletonReg_disjoint
    simpa [atomResource] using h
  · exact singletonReg_mem_disjoint
  · exact singletonReg_mem_disjoint
  · exact singletonMem_reg_disjoint
  · exact singletonMem_reg_disjoint
  · apply singletonMem_disjoint
    simpa [atomResource] using h
  · apply singletonMem_disjoint
    simpa [atomResource] using h
  · exact singletonMem_reg_disjoint
  · exact singletonMem_reg_disjoint
  · apply singletonMem_disjoint
    simpa [atomResource] using h
  · apply singletonMem_disjoint
    simpa [atomResource] using h


-- @@ L255-298 verbatim
private def atoms : List Atom :=
  [ .regVal .x2 sampleSp0,
    .regVal .x1 (sampleSaved .x1),
    .regVal .x8 (sampleSaved .x8),
    .regVal .x9 (sampleSaved .x9),
    .regVal .x18 (sampleSaved .x18),
    .regVal .x19 (sampleSaved .x19),
    .regVal .x20 (sampleSaved .x20),
    .regVal .x21 (sampleSaved .x21),
    .regVal .x22 (sampleSaved .x22),
    .regVal .x10 0,
    .regVal .x11 sampleOutPtr,
    .memOwn (sampleNewSp + 0) (by decide),
    .memOwn (sampleNewSp + 8) (by decide),
    .memOwn (sampleNewSp + 16) (by decide),
    .memOwn (sampleNewSp + 24) (by decide),
    .memOwn (sampleNewSp + 32) (by decide),
    .memOwn (sampleNewSp + 40) (by decide),
    .memOwn (sampleNewSp + 48) (by decide),
    .memOwn (sampleNewSp + 56) (by decide),
    .regOwn .x5, .regOwn .x6, .regOwn .x7,
    .regOwn .x28, .regOwn .x29, .regOwn .x30, .regOwn .x31,
    .memVal sampleStackA 0 (by decide),
    .memVal (sampleStackA + 8) 0 (by decide),
    .memVal (sampleStackA + 16) 0 (by decide),
    .memVal (sampleStackA + 24) 0 (by decide),
    .memVal (sampleStackA + 32) 0 (by decide),
    .memVal (sampleStackA + 40) 0 (by decide),
    .memVal sampleStackB 0 (by decide),
    .memVal (sampleStackB + 8) 0 (by decide),
    .memVal (sampleStackB + 16) 0 (by decide),
    .memVal (sampleStackB + 24) 0 (by decide),
    .memVal (sampleStackB + 32) 0 (by decide),
    .memVal (sampleStackB + 40) 0 (by decide),
    .memVal sampleStackC 0 (by decide),
    .memVal (sampleStackC + 8) 0 (by decide),
    .memVal (sampleStackC + 16) 0 (by decide),
    .memVal (sampleStackC + 24) 0 (by decide),
    .memVal (sampleStackC + 32) 0 (by decide),
    .memVal (sampleStackC + 40) 0 (by decide),
    .memVal sampleOutPtr 0 (by decide),
    .memVal (sampleOutPtr + 8) 0 (by decide),
    .memVal (sampleOutPtr + 16) 0 (by decide),
    .memVal (sampleOutPtr + 24) 0 (by decide) ]


-- @@ L300-301 verbatim
private def atomsAssert : Assertion :=
  atoms.foldr (fun x acc => atomAssertion x ** acc) empAssertion


-- @@ L303-304 verbatim
private def atomsHeap : PartialState :=
  atoms.foldr (fun x acc => (atomHeap x).union acc) PartialState.empty


-- @@ L306-310 verbatim
private theorem atoms_pairwise :
    atoms.Pairwise (fun x y => atomResource x ≠ atomResource y) := by
  unfold atoms atomResource sampleSp0 sampleOutPtr sampleNewSp
    sampleStackA sampleStackB sampleStackC sampleSaved
  decide


-- @@ L312-321 verbatim
private theorem atoms_hsat : atomsAssert atomsHeap := by
  apply sepConj_foldr_satisfiable atomAssertion atomHeap atoms
  · intro x hx
    cases x with
    | regVal r v => exact rfl
    | regOwn r => exact ⟨0, rfl⟩
    | memVal a v hvalid => exact ⟨rfl, hvalid⟩
    | memOwn a hvalid => exact ⟨0, rfl, hvalid⟩
  · exact List.Pairwise.imp
      (fun {_ _} h => atomHeap_disjoint_of_resource_ne h) atoms_pairwise


-- @@ L323-333 verbatim
private theorem entryPre_eq_atomsAssert : entryPre = atomsAssert := by
  unfold entryPre
  rw [zero48_region_expands sampleStackA,
    zero48_region_expands sampleStackB,
    zero48_region_expands sampleStackC,
    zero32_region_expands sampleOutPtr]
  unfold atomsAssert atoms atomAssertion
  simp [sampleFrame, sampleSaved, frameSlotsOwn, regsAt, regOwns,
    sampleNewSp, sampleStackA, sampleStackB, sampleStackC,
    sepConj_emp_right', add_ofNat_add, signExtend12]
  simp only [sepConj_assoc']


-- @@ L335-345 verbatim
def sampleState : MachineState where
  regs := fun r =>
    match atomsHeap.regs r with
    | some v => v
    | none => (0 : Word)
  mem := fun a =>
    match atomsHeap.mem a with
    | some v => v
    | none => (0 : Word)
  code := CR
  pc := B


-- @@ L347-347 verbatim
def fullState : MachineState := sampleState


-- @@ L349-351 verbatim
private theorem atomsHeap_x0 : atomsHeap.regs .x0 = none := by
  unfold atomsHeap atoms atomHeap
  decide


-- @@ L353-356 verbatim
private theorem sampleState_getReg (r : Reg) (hr : r ≠ .x0) :
    sampleState.getReg r =
      (match atomsHeap.regs r with | some v => v | none => (0 : Word)) := by
  cases r <;> simp_all [sampleState, MachineState.getReg]


-- @@ L358-361 verbatim
private theorem sampleState_getMem (a : Word) :
    sampleState.getMem a =
      (match atomsHeap.mem a with | some v => v | none => (0 : Word)) := by
  rfl


-- @@ L363-365 verbatim
private theorem atomHeap_code_none (x : Atom) (a : Word) :
    (atomHeap x).code a = none := by
  cases x <;> rfl


-- @@ L367-376 verbatim
private theorem atomsHeap_code_none (a : Word) : atomsHeap.code a = none := by
  unfold atomsHeap
  induction atoms with
  | nil => rfl
  | cons x xs ih =>
    change (match (atomHeap x).code a with
      | some v => some v
      | none => (xs.foldr (fun y acc => (atomHeap y).union acc)
          PartialState.empty).code a) = none
    rw [atomHeap_code_none x a, ih]


-- @@ L378-388 verbatim
private theorem atomsHeap_pc_none : atomsHeap.pc = none := by
  unfold atomsHeap
  induction atoms with
  | nil => rfl
  | cons x xs ih =>
    have hx : (atomHeap x).pc = none := by cases x <;> rfl
    change (match (atomHeap x).pc with
      | some v => some v
      | none => (xs.foldr (fun y acc => (atomHeap y).union acc)
          PartialState.empty).pc) = none
    rw [hx, ih]


-- @@ L390-409 verbatim
private theorem atomsHeap_compatible :
    atomsHeap.CompatibleWith sampleState := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r v h
    by_cases hr : r = .x0
    · subst r
      rw [atomsHeap_x0] at h
      cases h
    · rw [sampleState_getReg r hr, h]
  · intro a v h
    rw [sampleState_getMem a, h]
  · intro a i h
    rw [atomsHeap_code_none a] at h
    cases h
  · intro v h
    rw [atomsHeap_pc_none] at h
    cases h
  · intro v h; cases h
  · intro v h; cases h
  · intro v h; cases h


-- @@ L411-413 verbatim
private theorem fullState_getReg (r : Reg) :
    fullState.getReg r = sampleState.getReg r := by
  rfl


-- @@ L415-417 verbatim
private theorem fullState_getMem (a : Word) :
    fullState.getMem a = sampleState.getMem a := by
  rfl


-- @@ L419-438 verbatim
private theorem atomsHeap_compatible_full :
    atomsHeap.CompatibleWith fullState := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r v h
    by_cases hr : r = .x0
    · subst r
      rw [atomsHeap_x0] at h
      cases h
    · rw [fullState_getReg, sampleState_getReg r hr, h]
  · intro a v h
    rw [fullState_getMem, sampleState_getMem a, h]
  · intro a i h
    rw [atomsHeap_code_none a] at h
    cases h
  · intro v h
    rw [atomsHeap_pc_none] at h
    cases h
  · intro v h; cases h
  · intro v h; cases h
  · intro v h; cases h


-- @@ L440-449 verbatim
theorem entryState_exists :
    sampleState.pc = B ∧
    CR.SatisfiedBy sampleState ∧
    entryPre.holdsFor sampleState := by
  refine ⟨rfl, ?_, ?_⟩
  · intro a i h
    simpa only [sampleState] using h
  · refine ⟨atomsHeap, atomsHeap_compatible, ?_⟩
    rw [entryPre_eq_atomsAssert]
    exact atoms_hsat


-- @@ L451-453 verbatim
/-! The second name is retained for callers that used the old probe API; since
    the replacement has no external JALs, `fullCR` is definitionally the same
    local requirement as `CR`. -/

-- @@ L454-465 verbatim
theorem full_entryState_exists :
    fullState.pc = B ∧
    fullCR.SatisfiedBy fullState ∧
    entryPre.holdsFor fullState := by
  refine ⟨rfl, ?_, ?_⟩
  · intro a i h
    unfold fullCR at h
    simpa only [fullState, sampleState] using h
  · refine ⟨atomsHeap, ?_, ?_⟩
    · exact atomsHeap_compatible_full
    · rw [entryPre_eq_atomsAssert]
      exact atoms_hsat


-- @@ L467-467 verbatim
end EvmAsm.Codegen.AmsterdamBlobGasPriceU256Sat
