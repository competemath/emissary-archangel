/-
  Anti-vacuity witnesses for the #12457 shared-list call seam.

  The first theorem inhabits the rewritten premise at the empty child window.
  The second carries a genuine nested list, a nonzero cursor, and caller frame
  values.  Its only hypothesis is the positive validator family that the
  mutual induction supplies; the theorem deliberately does not manufacture
  that family as a standalone axiom.
-/

import EvmAsm.Codegen.Programs.RlpWalkNextStrictFuelMachine
import EvmAsm.Rv64.SAsm.AbiFrame


-- @@ L14-14 verbatim
namespace EvmAsm.Codegen.RlpWalkNextStrictFuel


-- @@ L16-16 verbatim
open EvmAsm.Rv64 EvmAsm.Rv64.RLP EvmAsm.EL.RLP

-- @@ L17-17 verbatim
open EvmAsm.Rv64.Tactics


-- @@ L19-19 verbatim
def antiVacuityBytes : List (BitVec 8) := [0xc0]

-- @@ L20-20 verbatim
def antiVacuityBase : Word := BitVec.ofNat 64 INPUT_MEM_START

-- @@ L21-21 verbatim
def antiVacuityFloor : Nat := 0

-- @@ L22-22 verbatim
def antiVacuityCursor : Nat := 0

-- @@ L23-23 verbatim
def antiVacuityEnd : Nat := 1

-- @@ L24-24 verbatim
def antiVacuityPayloadStart : Nat := 1

-- @@ L25-25 verbatim
def antiVacuityPayloadEnd : Nat := 1

-- @@ L26-27 verbatim
def antiVacuityParentFuel : Nat :=
  cycleFuel antiVacuityCursor antiVacuityEnd

-- @@ L28-28 verbatim
def antiVacuitySp : Word := 0x1000

-- @@ L29-29 verbatim
def antiVacuitySpV : Word := 0x0fe0

-- @@ L30-30 verbatim
def antiVacuityRa : Word := 0x2000

-- @@ L31-31 verbatim
def antiVacuityExit : Word := antiVacuityRa &&& ~~~(1 : Word)

-- @@ L32-33 verbatim
def antiVacuityEndPtr : Word :=
  antiVacuityBase + BitVec.ofNat 64 antiVacuityEnd

-- @@ L34-34 verbatim
def antiVacuityPfx : Word := 0xc0

-- @@ L35-36 verbatim
def antiVacuityListBase : Word :=
  antiVacuityBase + BitVec.ofNat 64 antiVacuityCursor

-- @@ L37-37 verbatim
def antiVacuityDepth : Word := 0

-- @@ L38-38 verbatim
def antiVacuityP : Assertion := empAssertion


-- @@ L40-100 verbatim
theorem shared_list_boundary_inhabited :
    Nonempty (SharedListArmInputs antiVacuityBytes antiVacuityBase
      antiVacuityFloor antiVacuityParentFuel antiVacuityCursor antiVacuityEnd
      antiVacuitySpV antiVacuitySp antiVacuityRa antiVacuityExit antiVacuityEndPtr
      antiVacuityPfx antiVacuityListBase antiVacuityDepth
      0 0 0 0 0 0 0 0 antiVacuityP) := by
  let hsel : SharedListSelection antiVacuityBytes antiVacuityParentFuel
      antiVacuityCursor antiVacuityEnd := {
    payloadStart := antiVacuityPayloadStart
    payloadEnd := antiVacuityPayloadEnd
    hparent := by rfl
    hcursor := by decide
    hpayload := by decide
    hpayloadEnd := by decide
    houter := by decide
    hvalidate := by
      exact validateFuel_empty_window_inhabited antiVacuityBytes rfl (by decide)
    hlongHeader := by
      intro pfx hpfx hlong
      rcases hpfx with ⟨hcursor, hpfx⟩
      have hpfx' : pfx = (0xc0 : Word) := by
        simpa [antiVacuityBytes] using hpfx
      subst pfx
      have hshort : BitVec.ult (0xc0 : Word) (248 : Word) := by decide
      exact False.elim (hlong hshort)
  }
  have hprefix : sharedPrefixByteAt antiVacuityBytes antiVacuityCursor
      antiVacuityPfx := by
    refine ⟨by decide, ?_⟩
    rfl
  have hchild0 : validateMachineIndexedFamily antiVacuityBytes
      antiVacuityBase antiVacuityFloor antiVacuitySpV
      (RlpWalkNextStrictTie.S + 160)
      ((RlpWalkNextStrictTie.S + 160) &&& ~~~(1 : Word))
      validateCR antiVacuityP 0 := by
    exact validate_machine_indexed_family_zero
  have hvalid : ∀ off, off < antiVacuityEnd →
      isValidByteAccess
        (antiVacuityBase + BitVec.ofNat 64 off) = true := by
    intro off hoff
    have hoff1 : off < 1 := by simpa [antiVacuityEnd] using hoff
    have hoff0 : off = 0 := by omega
    subst off
    decide
  refine ⟨{
    selector := hsel
    hprefix := hprefix
    hlistPrefix := by decide
    hdepth := by decide
    hsp := by decide
    hlistBase := by rfl
    hendPtr := by rfl
    hbase_aligned := by decide
    hover := by decide
    hnowrap := by decide
    hvalid := hvalid
    hP := by exact pcFree_emp
    hchild := by
      dsimp [hsel, antiVacuityPayloadStart, antiVacuityPayloadEnd]
      exact hchild0
  }⟩


-- @@ L102-102 verbatim
def discriminatingBytes : List (BitVec 8) := [0xc2, 0xc1, 0x00]

-- @@ L103-103 verbatim
def discriminatingBase : Word := BitVec.ofNat 64 INPUT_MEM_START

-- @@ L104-104 verbatim
def discriminatingFloor : Nat := 0

-- @@ L105-105 verbatim
def discriminatingCursor : Nat := 1

-- @@ L106-106 verbatim
def discriminatingEnd : Nat := 3

-- @@ L107-107 verbatim
def discriminatingPayloadStart : Nat := 2

-- @@ L108-108 verbatim
def discriminatingPayloadEnd : Nat := 3

-- @@ L109-110 verbatim
def discriminatingParentFuel : Nat :=
  cycleFuel discriminatingCursor discriminatingEnd

-- @@ L111-111 verbatim
def discriminatingSp : Word := 0x7000

-- @@ L112-112 verbatim
def discriminatingSpV : Word := 0x6fe0

-- @@ L113-113 verbatim
def discriminatingRa : Word := 0x9000

-- @@ L114-114 verbatim
def discriminatingExit : Word := discriminatingRa &&& ~~~(1 : Word)

-- @@ L115-116 verbatim
def discriminatingEndPtr : Word :=
  discriminatingBase + BitVec.ofNat 64 discriminatingEnd

-- @@ L117-117 verbatim
def discriminatingPfx : Word := 0xc1

-- @@ L118-119 verbatim
def discriminatingListBase : Word :=
  discriminatingBase + BitVec.ofNat 64 discriminatingCursor

-- @@ L120-120 verbatim
def discriminatingDepth : Word := 1

-- @@ L121-121 verbatim
def discriminatingP : Assertion := empAssertion


-- @@ L123-188 verbatim
theorem shared_list_discriminating_inhabited
    (hchild : validateMachineIndexedFamily discriminatingBytes
      discriminatingBase discriminatingFloor discriminatingSpV
      (RlpWalkNextStrictTie.S + 160)
      ((RlpWalkNextStrictTie.S + 160) &&& ~~~(1 : Word))
      validateCR discriminatingP
      (cycleFuel discriminatingPayloadStart discriminatingPayloadEnd)) :
    Nonempty (SharedListArmInputs discriminatingBytes discriminatingBase
      discriminatingFloor discriminatingParentFuel discriminatingCursor
      discriminatingEnd discriminatingSpV discriminatingSp discriminatingRa discriminatingExit
      discriminatingEndPtr discriminatingPfx discriminatingListBase
      discriminatingDepth 0 0 0 0 0 0 0 0
      discriminatingP) := by
  have hnested := nested_list_exact_fit_inhabited
  dsimp at hnested
  rcases hnested with ⟨_houterShared, _hinnerShared, _houterValidate,
    hinnerValidate, _hdone, _hdecode⟩
  let hsel : SharedListSelection discriminatingBytes
      discriminatingParentFuel discriminatingCursor discriminatingEnd := {
    payloadStart := discriminatingPayloadStart
    payloadEnd := discriminatingPayloadEnd
    hparent := by rfl
    hcursor := by decide
    hpayload := by decide
    hpayloadEnd := by decide
    houter := by decide
    hvalidate := by
      simpa [discriminatingBytes, discriminatingPayloadStart,
        discriminatingPayloadEnd] using hinnerValidate
    hlongHeader := by
      intro pfx hpfx hlong
      rcases hpfx with ⟨hcursor, hpfx⟩
      have hpfx' : pfx = (0xc1 : Word) := by
        simpa [discriminatingBytes, discriminatingCursor] using hpfx
      subst pfx
      have hshort : BitVec.ult (0xc1 : Word) (248 : Word) := by decide
      exact False.elim (hlong hshort)
  }
  have hprefix : sharedPrefixByteAt discriminatingBytes discriminatingCursor
      discriminatingPfx := by
    refine ⟨by decide, ?_⟩
    rfl
  have hvalid : ∀ off, off < discriminatingEnd →
      isValidByteAccess
        (discriminatingBase + BitVec.ofNat 64 off) = true := by
    intro off hoff
    have hoff3 : off < 3 := by simpa [discriminatingEnd] using hoff
    have hoff_cases : off = 0 ∨ off = 1 ∨ off = 2 := by omega
    rcases hoff_cases with rfl | rfl | rfl <;> decide
  refine ⟨{
    selector := hsel
    hprefix := hprefix
    hlistPrefix := by decide
    hdepth := by decide
    hsp := by decide
    hlistBase := by rfl
    hendPtr := by rfl
    hbase_aligned := by decide
    hover := by decide
    hnowrap := by decide
    hvalid := hvalid
    hP := by exact pcFree_emp
    hchild := by
      dsimp [hsel, discriminatingPayloadStart, discriminatingPayloadEnd]
      exact hchild
  }⟩


-- @@ L190-190 verbatim
def longHeaderBytes : List (BitVec 8) := [0xf8, 0x01]

-- @@ L191-191 verbatim
def longHeaderBase : Word := BitVec.ofNat 64 INPUT_MEM_START

-- @@ L192-192 verbatim
def longHeaderFloor : Nat := 0

-- @@ L193-193 verbatim
def longHeaderCursor : Nat := 0

-- @@ L194-194 verbatim
def longHeaderEnd : Nat := 2

-- @@ L195-195 verbatim
def longHeaderPayloadStart : Nat := 2

-- @@ L196-196 verbatim
def longHeaderPayloadEnd : Nat := 2

-- @@ L197-198 verbatim
def longHeaderParentFuel : Nat :=
  cycleFuel longHeaderCursor longHeaderEnd

-- @@ L199-199 verbatim
def longHeaderSp : Word := 0x7100

-- @@ L200-200 verbatim
def longHeaderSpV : Word := 0x70e0

-- @@ L201-201 verbatim
def longHeaderRa : Word := 0x9100

-- @@ L202-202 verbatim
def longHeaderExit : Word := longHeaderRa &&& ~~~(1 : Word)

-- @@ L203-204 verbatim
def longHeaderEndPtr : Word :=
  longHeaderBase + BitVec.ofNat 64 longHeaderEnd

-- @@ L205-205 verbatim
def longHeaderPfx : Word := 0xf8

-- @@ L206-207 verbatim
def longHeaderListBase : Word :=
  longHeaderBase + BitVec.ofNat 64 longHeaderCursor

-- @@ L208-208 verbatim
def longHeaderDepth : Word := 1

-- @@ L209-209 verbatim
def longHeaderP : Assertion := empAssertion


-- @@ L211-214 verbatim
/-! The long-header witness is deliberately separate from the short and nested
    witnesses above.  It exercises the new selector result: the one-byte
    length-of-length is decoded, the computed payload start is `2`, and the
    core header-fit fact is `0 + 1 < 2`. -/

-- @@ L215-273 verbatim
theorem shared_list_long_header_inhabited :
    Nonempty (SharedListArmInputs longHeaderBytes longHeaderBase
      longHeaderFloor longHeaderParentFuel longHeaderCursor longHeaderEnd
      longHeaderSpV longHeaderSp longHeaderRa longHeaderExit longHeaderEndPtr
      longHeaderPfx longHeaderListBase longHeaderDepth
      0 0 0 0 0 0 0 0 longHeaderP) := by
  have hchild : validateMachineIndexedFamily longHeaderBytes longHeaderBase
      longHeaderFloor longHeaderSpV
      (RlpWalkNextStrictTie.S + 160)
      ((RlpWalkNextStrictTie.S + 160) &&& ~~~(1 : Word))
      validateCR longHeaderP 0 := by
    exact validate_machine_indexed_family_zero
  let hsel : SharedListSelection longHeaderBytes longHeaderParentFuel
      longHeaderCursor longHeaderEnd := {
    payloadStart := longHeaderPayloadStart
    payloadEnd := longHeaderPayloadEnd
    hparent := by rfl
    hcursor := by decide
    hpayload := by decide
    hpayloadEnd := by decide
    houter := by decide
    hvalidate := by
      exact validateFuel_empty_window_inhabited longHeaderBytes rfl (by decide)
    hlongHeader := by
      intro pfx hpfx hlong
      rcases hpfx with ⟨hcursor, hpfx⟩
      have hpfx' : pfx = (0xf8 : Word) := by
        simpa [longHeaderBytes, longHeaderCursor] using hpfx
      rw [hpfx']
      exact ⟨1, by decide, by decide, by decide, by decide⟩
  }
  have hprefix : sharedPrefixByteAt longHeaderBytes longHeaderCursor
      longHeaderPfx := by
    refine ⟨by decide, ?_⟩
    rfl
  have hvalid : ∀ off, off < longHeaderEnd →
      isValidByteAccess
        (longHeaderBase + BitVec.ofNat 64 off) = true := by
    intro off hoff
    have hoff2 : off < 2 := by simpa [longHeaderEnd] using hoff
    have hoff_cases : off = 0 ∨ off = 1 := by omega
    rcases hoff_cases with rfl | rfl <;> decide
  refine ⟨{
    selector := hsel
    hprefix := hprefix
    hlistPrefix := by decide
    hdepth := by decide
    hsp := by decide
    hlistBase := by rfl
    hendPtr := by rfl
    hbase_aligned := by decide
    hover := by decide
    hnowrap := by decide
    hvalid := hvalid
    hP := by exact pcFree_emp
    hchild := by
      dsimp [hsel, longHeaderPayloadStart, longHeaderPayloadEnd]
      exact hchild
  }⟩


-- @@ L275-280 verbatim
/-! ## Frame-repair witness

The frame repair is checked against an actual machine state rather than only
with `P = empAssertion`.  The witness owns the three Shared-frame cells and a
separate `x9` register through `P`, so the strengthened knot pre is inhabited
without reusing any resource. -/


-- @@ L282-282 verbatim
def frameRepairBytes : List (BitVec 8) := []

-- @@ L283-283 verbatim
def frameRepairBase : Word := BitVec.ofNat 64 INPUT_MEM_START

-- @@ L284-284 verbatim
def frameRepairSp : Word := 0x40000200

-- @@ L285-285 verbatim
def frameRepairRa : Word := 0x2000

-- @@ L286-286 verbatim
def frameRepairX1 : Word := 0x2004

-- @@ L287-287 verbatim
def frameRepairP : Assertion := regIs .x9 1


-- @@ L289-293 verbatim
private inductive FrameRepairResource where
  | reg (r : Reg)
  | mem (a : Word)
  | pure
  deriving DecidableEq


-- @@ L295-301 verbatim
private inductive FrameRepairAtom where
  | regVal (r : Reg) (v : Word)
  | regOwn (r : Reg)
  | memVal (a : Word) (v : Word) (valid : isValidDwordAccess a = true)
  | memOwn (a : Word) (valid : isValidDwordAccess a = true)
  | fuel
  deriving DecidableEq


-- @@ L303-308 verbatim
private def frameRepairAtomResource : FrameRepairAtom → FrameRepairResource
  | .regVal r _ => .reg r
  | .regOwn r => .reg r
  | .memVal a _ _ => .mem a
  | .memOwn a _ => .mem a
  | .fuel => .pure


-- @@ L310-315 verbatim
private def frameRepairAtomAssertion : FrameRepairAtom → Assertion
  | .regVal r v => regIs r v
  | .regOwn r => regOwn r
  | .memVal a v _ => memIs a v
  | .memOwn a _ => memOwn a
  | .fuel => ⌜ValidateFuel frameRepairBytes 0 0 0⌝


-- @@ L317-322 verbatim
private def frameRepairAtomHeap : FrameRepairAtom → PartialState
  | .regVal r v => PartialState.singletonReg r v
  | .regOwn r => PartialState.singletonReg r 0
  | .memVal a v _ => PartialState.singletonMem a v
  | .memOwn a _ => PartialState.singletonMem a 0
  | .fuel => PartialState.empty


-- @@ L324-336 verbatim
private theorem frameRepair_singletonReg_disjoint
    {r1 r2 : Reg} {v1 v2 : Word} (hne : r1 ≠ r2) :
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


-- @@ L338-350 verbatim
private theorem frameRepair_singletonMem_disjoint
    {a1 a2 : Word} {v1 v2 : Word} (hne : a1 ≠ a2) :
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


-- @@ L352-357 verbatim
private theorem frameRepair_singletonReg_mem_disjoint
    {r : Reg} {a : Word} {v w : Word} :
    (PartialState.singletonReg r v).Disjoint
      (PartialState.singletonMem a w) := by
  exact ⟨fun _ => Or.inr rfl, fun _ => Or.inl rfl, fun _ => Or.inl rfl,
    Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl⟩


-- @@ L359-363 verbatim
private theorem frameRepair_singletonMem_reg_disjoint
    {r : Reg} {a : Word} {v w : Word} :
    (PartialState.singletonMem a v).Disjoint
      (PartialState.singletonReg r w) :=
  frameRepair_singletonReg_mem_disjoint.symm


-- @@ L365-403 verbatim
private theorem frameRepair_atomHeap_disjoint_of_resource_ne
    {x y : FrameRepairAtom}
    (h : frameRepairAtomResource x ≠ frameRepairAtomResource y) :
    (frameRepairAtomHeap x).Disjoint (frameRepairAtomHeap y) := by
  cases x <;> cases y
  · apply frameRepair_singletonReg_disjoint
    simpa [frameRepairAtomResource] using h
  · apply frameRepair_singletonReg_disjoint
    simpa [frameRepairAtomResource] using h
  · exact frameRepair_singletonReg_mem_disjoint
  · exact frameRepair_singletonReg_mem_disjoint
  · exact PartialState.Disjoint_empty_right
  · apply frameRepair_singletonReg_disjoint
    simpa [frameRepairAtomResource] using h
  · apply frameRepair_singletonReg_disjoint
    simpa [frameRepairAtomResource] using h
  · exact frameRepair_singletonReg_mem_disjoint
  · exact frameRepair_singletonReg_mem_disjoint
  · exact PartialState.Disjoint_empty_right
  · exact frameRepair_singletonMem_reg_disjoint
  · exact frameRepair_singletonMem_reg_disjoint
  · apply frameRepair_singletonMem_disjoint
    simpa [frameRepairAtomResource] using h
  · apply frameRepair_singletonMem_disjoint
    simpa [frameRepairAtomResource] using h
  · exact PartialState.Disjoint_empty_right
  · exact frameRepair_singletonMem_reg_disjoint
  · exact frameRepair_singletonMem_reg_disjoint
  · apply frameRepair_singletonMem_disjoint
    simpa [frameRepairAtomResource] using h
  · apply frameRepair_singletonMem_disjoint
    simpa [frameRepairAtomResource] using h
  · exact PartialState.Disjoint_empty_right
  · exact PartialState.Disjoint_empty_left
  · exact PartialState.Disjoint_empty_left
  · exact PartialState.Disjoint_empty_left
  · exact PartialState.Disjoint_empty_left
  · exfalso
    exact h rfl


-- @@ L405-420 verbatim
private def frameRepairAtoms : List FrameRepairAtom :=
  [ .regVal .x1 frameRepairX1
  , .regVal .x2 frameRepairSp
  , .regVal .x10 frameRepairBase
  , .regVal .x5 frameRepairBase
  , .regVal .x11 frameRepairBase
  , .memVal frameRepairSp frameRepairRa (by decide)
  , .memVal (frameRepairSp + 8) frameRepairBase (by decide)
  , .memVal (frameRepairSp + 16) frameRepairBase (by decide)
  , .regVal .x0 0
  , .regOwn .x12
  , .memOwn (frameRepairSp - BitVec.ofNat 64 64) (by decide)
  , .memOwn (frameRepairSp - BitVec.ofNat 64 56) (by decide)
  , .memOwn (frameRepairSp - BitVec.ofNat 64 48) (by decide)
  , .fuel
  , .regVal .x9 1 ]


-- @@ L422-424 verbatim
private def frameRepairAtomsAssert : Assertion :=
  frameRepairAtoms.foldr (fun x acc => frameRepairAtomAssertion x ** acc)
    empAssertion


-- @@ L426-428 verbatim
private def frameRepairAtomsHeap : PartialState :=
  frameRepairAtoms.foldr (fun x acc => (frameRepairAtomHeap x).union acc)
    PartialState.empty


-- @@ L430-434 verbatim
private theorem frameRepairAtoms_pairwise :
    frameRepairAtoms.Pairwise
      (fun x y => frameRepairAtomResource x ≠ frameRepairAtomResource y) := by
  unfold frameRepairAtoms frameRepairAtomResource
  decide


-- @@ L436-453 verbatim
private theorem frameRepairAtoms_hsat :
    frameRepairAtomsAssert frameRepairAtomsHeap := by
  apply EvmAsm.Rv64.SAsm.sepConj_foldr_satisfiable
    frameRepairAtomAssertion frameRepairAtomHeap frameRepairAtoms
  · intro x hx
    cases x with
    | regVal r v => exact rfl
    | regOwn r => exact ⟨0, rfl⟩
    | memVal a v hvalid => exact ⟨rfl, hvalid⟩
    | memOwn a hvalid => exact ⟨0, rfl, hvalid⟩
    | fuel =>
      exact ⟨rfl, by
        simpa [frameRepairBytes, cycleFuel, remainingBytes] using
          (ValidateFuel.empty (bytes := frameRepairBytes)
            (cursor := 0) (endOff := 0) ⟨rfl, by decide⟩)⟩
  · exact List.Pairwise.imp
      (fun {_ _} h => frameRepair_atomHeap_disjoint_of_resource_ne h)
      frameRepairAtoms_pairwise


-- @@ L455-462 verbatim
private theorem frameRepair_pre_eq_atomsAssert :
    validateKnotBodyPre frameRepairBytes frameRepairBase
      0 0 0 frameRepairSp frameRepairRa frameRepairX1 frameRepairP =
      frameRepairAtomsAssert := by
  unfold validateKnotBodyPre validateKnotSharedFrame frameRepairAtomsAssert
    frameRepairAtoms frameRepairAtomAssertion frameRepairP
  simp [frameRepairBytes, bytesRegion_nil, sepConj_emp_left',
    sepConj_emp_right', sepConj_assoc']


-- @@ L464-473 verbatim
def frameRepairState : MachineState where
  regs := fun r =>
    match frameRepairAtomsHeap.regs r with
    | some v => v
    | none => 0
  mem := fun a =>
    match frameRepairAtomsHeap.mem a with
    | some v => v
    | none => 0
  pc := validateEntry + 36


-- @@ L475-478 verbatim
private theorem frameRepairAtomsHeap_x0 :
    frameRepairAtomsHeap.regs .x0 = some 0 := by
  unfold frameRepairAtomsHeap frameRepairAtoms frameRepairAtomHeap
  decide


-- @@ L480-483 verbatim
private theorem frameRepairState_getReg (r : Reg) (hr : r ≠ .x0) :
    frameRepairState.getReg r =
      (match frameRepairAtomsHeap.regs r with | some v => v | none => 0) := by
  cases r <;> simp_all [frameRepairState, MachineState.getReg]


-- @@ L485-488 verbatim
private theorem frameRepairState_getMem (a : Word) :
    frameRepairState.getMem a =
      (match frameRepairAtomsHeap.mem a with | some v => v | none => 0) := by
  rfl


-- @@ L490-494 verbatim
private theorem frameRepairAtomsHeap_code_none (a : Word) :
    frameRepairAtomsHeap.code a = none := by
  simp [frameRepairAtomsHeap, frameRepairAtoms, frameRepairAtomHeap,
    PartialState.union, PartialState.singletonReg, PartialState.singletonMem,
    PartialState.empty]


-- @@ L496-500 verbatim
private theorem frameRepairAtomsHeap_pc_none :
    frameRepairAtomsHeap.pc = none := by
  simp [frameRepairAtomsHeap, frameRepairAtoms, frameRepairAtomHeap,
    PartialState.union, PartialState.singletonReg, PartialState.singletonMem,
    PartialState.empty]


-- @@ L502-525 verbatim
private theorem frameRepairAtomsHeap_compat :
    frameRepairAtomsHeap.CompatibleWith frameRepairState := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r v h
    by_cases hr : r = .x0
    · subst r
      rw [frameRepairAtomsHeap_x0] at h
      simp only [Option.some.injEq] at h
      simpa [frameRepairState, MachineState.getReg] using h
    · rw [frameRepairState_getReg r hr, h]
  · intro a v h
    rw [frameRepairState_getMem a, h]
  · intro a i h
    rw [frameRepairAtomsHeap_code_none a] at h
    cases h
  · intro v h
    rw [frameRepairAtomsHeap_pc_none] at h
    cases h
  · intro v h
    cases h
  · intro v h
    cases h
  · intro v h
    cases h


-- @@ L527-533 verbatim
private theorem frameRepair_pre_holdsFor :
    (validateKnotBodyPre frameRepairBytes frameRepairBase
      0 0 0 frameRepairSp frameRepairRa frameRepairX1 frameRepairP).holdsFor
      frameRepairState := by
  rw [frameRepair_pre_eq_atomsAssert]
  exact ⟨frameRepairAtomsHeap, frameRepairAtomsHeap_compat,
    frameRepairAtoms_hsat⟩


-- @@ L535-546 verbatim
theorem validate_knot_body_pre_non_degenerate_inhabited :
    frameRepairP ≠ empAssertion ∧
      (validateKnotBodyPre frameRepairBytes frameRepairBase
        0 0 0 frameRepairSp frameRepairRa frameRepairX1 frameRepairP).holdsFor
        frameRepairState := by
  refine ⟨?_, frameRepair_pre_holdsFor⟩
  intro hEq
  have := congrArg (fun P => P (PartialState.singletonReg .x9 1)) hEq
  have hbad : PartialState.singletonReg .x9 1 = PartialState.empty := by
    exact this.mp rfl
  have hreg := congrArg (fun h => h.regs .x9) hbad
  simp [PartialState.singletonReg, PartialState.empty] at hreg


-- @@ L548-554 verbatim
/-! The code-side fields are inhabited jointly with the repaired assertion
    witness.  The empty continuation is deliberate here: it makes the
    disjointness obligation a structural fact, while `bodyCode` still contains
    the concrete V+36 `JAL` and the full nested requirement.  This is only a
    witness for the repaired static premises, not a `ValidateKnotBodyContract`
    proof; the latter still has to provide the machine triple in its `proof`
    field. -/

-- @@ L555-580 verbatim
theorem validate_knot_body_repaired_premises_inhabited_empty_continuation :
    frameRepairP ≠ empAssertion ∧
      (validateKnotBodyPre frameRepairBytes frameRepairBase
        0 0 0 frameRepairSp frameRepairRa frameRepairX1 frameRepairP).holdsFor
        frameRepairState ∧
      (∃ continuationCode bodyCode wholeCode : CodeReq,
        bodyCode = validateKnotBodyCode continuationCode ∧
        (validateKnotCallCode.union nestedCR).Disjoint continuationCode ∧
        (∀ a i, bodyCode a = some i → wholeCode a = some i) ∧
        (∃ a i, bodyCode a = some i)) := by
  refine ⟨?_, frameRepair_pre_holdsFor, ?_⟩
  · intro hEq
    have h := congrArg (fun P => P (PartialState.singletonReg .x9 1)) hEq
    have hbad : PartialState.singletonReg .x9 1 = PartialState.empty := by
      exact h.mp rfl
    have hreg := congrArg (fun h => h.regs .x9) hbad
    simp [PartialState.singletonReg, PartialState.empty] at hreg
  · refine ⟨CodeReq.empty, validateKnotBodyCode CodeReq.empty,
      validateKnotBodyCode CodeReq.empty, rfl,
      CodeReq.Disjoint.empty_right _, ?_, ?_⟩
    · intro a i h
      exact h
    · refine ⟨validateEntry + 36,
        .JAL .x1 (jalOff rlpWalkNextNestedOfflineAddr
          (GuestAddrs.rlp_validate_payload + 36)), ?_⟩
      decide


-- @@ L582-582 verbatim
end EvmAsm.Codegen.RlpWalkNextStrictFuel
