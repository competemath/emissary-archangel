/-
  EvmAsm.Rv64.SAsm.Sym

  The pure block engine for SAsm: forward symbolic execution of straight-line
  instruction blocks over the exposed register file.

  `aluSem` classifies each supported instruction as a destination register, a
  source list, and a result function of the register valuation, mirroring
  `execInstrBr` exactly.  `execInstrRF`/`execBlock` run that classification
  over a `RegFile`; `instrOk`/`blockOk` are the decidable supported-subset and
  exposure checks whose failure the VC generator surfaces as a labeled goal.

  Supported subset (docs/sasm-design.md §3.4): ALU reg/reg and reg/imm ops,
  constants (LI/LUI/MV/NOP), ADDIW, and the RV64M multiply/divide family.
  Memory, branches, jumps, and system instructions are not block leaves:
  branches/jumps are synthesized by the flattener, and memory ops arrive with
  region support (M5).
-/

module

public import EvmAsm.Rv64.Execution
public import EvmAsm.Rv64.ByteOps
public import EvmAsm.Rv64.MemRegionWriteWide
public import EvmAsm.Rv64.SAsm.RegFile


-- @@ L27-27 verbatim
@[expose] public section


-- @@ L29-29 verbatim
namespace EvmAsm.Rv64

-- @@ L30-34 verbatim
namespace SAsm

-- ============================================================================
-- Read-only byte regions (docs/sasm-design.md §3.3)
-- ============================================================================


-- @@ L36-41 verbatim
/-- A read-only byte buffer owned by an SAsm function: `bytes` live at the
    dword-aligned `base`.  The degenerate `Region.empty` is the default for
    functions that touch no memory. -/
structure Region where
  base : Word
  bytes : List (BitVec 8)


-- @@ L43-44 verbatim
/-- The no-memory region (its assertion is `empAssertion`). -/
def Region.empty : Region := ⟨0, []⟩


-- @@ L46-49 verbatim
/-- Read the byte at an absolute address (junk when out of range; the block
    VCs rule that out). -/
def Region.byteAt (reg : Region) (addr : Word) : BitVec 8 :=
  reg.bytes.getD (addr - reg.base).toNat 0


-- @@ L51-53 verbatim
/-- Read the little-endian 16-bit halfword at a 2-aligned absolute address. -/
def Region.half16At (reg : Region) (addr : Word) : BitVec 16 :=
  reg.byteAt (addr + 1) ++ reg.byteAt addr


-- @@ L55-58 verbatim
/-- Read the little-endian 32-bit word at a 4-aligned absolute address. -/
def Region.word32At (reg : Region) (addr : Word) : BitVec 32 :=
  reg.byteAt (addr + 3) ++ reg.byteAt (addr + 2)
    ++ reg.byteAt (addr + 1) ++ reg.byteAt addr


-- @@ L60-62 verbatim
/-- Read the dword (as its packed cell) at an 8-aligned absolute address. -/
def Region.dwordAt (reg : Region) (addr : Word) : Word :=
  packBytes ((reg.bytes.drop (addr - reg.base).toNat).take 8)


-- @@ L64-68 verbatim
/-- Address side condition of an `n`-byte load: the index is `n`-aligned
    within the region and the whole access fits. -/
def Region.loadOk (reg : Region) (addr : Word) (n : Nat) : Prop :=
  n ∣ (addr - reg.base).toNat
    ∧ (addr - reg.base).toNat + n ≤ reg.bytes.length


-- @@ L70-76 verbatim
/-- Region well-formedness: dword-aligned base, no address wrap, and every
    byte within the machine's valid memory range.  Decidable for concrete
    regions (`decide`); `omega`/`bv_omega` for symbolic ones. -/
def Region.wf (reg : Region) : Prop :=
  reg.base.toNat % 8 = 0 ∧
  reg.base.toNat + reg.bytes.length < 2 ^ 64 ∧
  ∀ k, k < reg.bytes.length → isValidMemAddr (reg.base + BitVec.ofNat 64 k) = true


-- @@ L78-80 verbatim
instance (reg : Region) : Decidable reg.wf := by
  unfold Region.wf
  infer_instance


-- @@ L82-86 verbatim
theorem Region.empty_wf : Region.empty.wf := by decide

-- ============================================================================
-- Writable byte regions (docs/sasm-design.md §3.3, M5b-2)
-- ============================================================================


-- @@ L88-95 verbatim
/-- A writable byte region owned by an SAsm function: `len` bytes at the
    dword-aligned `base`.  Unlike the read-only `Region`, the *contents* are
    part of the symbolic state (`Reach`), not of the region descriptor.  The
    degenerate `RwRegion.empty` is the default for functions that write no
    memory. -/
structure RwRegion where
  base : Word
  len : Nat


-- @@ L97-98 verbatim
/-- The no-writable-memory region. -/
def RwRegion.empty : RwRegion := ⟨0, 0⟩


-- @@ L100-105 verbatim
/-- Writable-region well-formedness: dword-aligned base, no address wrap,
    every byte within the machine's valid memory range. -/
def RwRegion.wf (rw : RwRegion) : Prop :=
  rw.base.toNat % 8 = 0 ∧
  rw.base.toNat + rw.len < 2 ^ 64 ∧
  ∀ k, k < rw.len → isValidMemAddr (rw.base + BitVec.ofNat 64 k) = true


-- @@ L107-109 verbatim
instance (rw : RwRegion) : Decidable rw.wf := by
  unfold RwRegion.wf
  infer_instance


-- @@ L111-111 verbatim
theorem RwRegion.empty_wf : RwRegion.empty.wf := by decide


-- @@ L113-118 verbatim
/-- Whether an `n`-byte access at `addr` falls entirely inside the writable
    region (current contents `ws`).  This is the load-routing condition: such
    accesses read the symbolic contents, everything else reads the read-only
    region. -/
def inRw (rwBase : Word) (ws : List (BitVec 8)) (addr : Word) (n : Nat) : Prop :=
  (addr - rwBase).toNat + n ≤ ws.length


-- @@ L120-123 verbatim
instance (rwBase : Word) (ws : List (BitVec 8)) (addr : Word) (n : Nat) :
    Decidable (inRw rwBase ws addr n) := by
  unfold inRw
  infer_instance


-- @@ L125-130 verbatim
/-- Classification of a supported straight-line instruction: destination,
    sources, and result as a function of the register valuation. -/
structure AluOp where
  rd : Reg
  srcs : List Reg
  f : (Reg → Word) → Word


-- @@ L132-182 verbatim
/-- Classify an instruction.  The result functions mirror `execInstrBr`
    case-for-case; `none` means the instruction is not a supported SAsm
    block leaf. -/
def aluSem : Instr → Option AluOp
  -- ALU register-register
  | .ADD  rd rs1 rs2 => some ⟨rd, [rs1, rs2], fun g => g rs1 + g rs2⟩
  | .SUB  rd rs1 rs2 => some ⟨rd, [rs1, rs2], fun g => g rs1 - g rs2⟩
  | .SLL  rd rs1 rs2 => some ⟨rd, [rs1, rs2], fun g => g rs1 <<< ((g rs2).toNat % 64)⟩
  | .SRL  rd rs1 rs2 => some ⟨rd, [rs1, rs2], fun g => g rs1 >>> ((g rs2).toNat % 64)⟩
  | .SRA  rd rs1 rs2 => some ⟨rd, [rs1, rs2],
      fun g => BitVec.sshiftRight (g rs1) ((g rs2).toNat % 64)⟩
  | .AND  rd rs1 rs2 => some ⟨rd, [rs1, rs2], fun g => g rs1 &&& g rs2⟩
  | .OR   rd rs1 rs2 => some ⟨rd, [rs1, rs2], fun g => g rs1 ||| g rs2⟩
  | .XOR  rd rs1 rs2 => some ⟨rd, [rs1, rs2], fun g => g rs1 ^^^ g rs2⟩
  | .SLT  rd rs1 rs2 => some ⟨rd, [rs1, rs2],
      fun g => if BitVec.slt (g rs1) (g rs2) then 1 else 0⟩
  | .SLTU rd rs1 rs2 => some ⟨rd, [rs1, rs2],
      fun g => if BitVec.ult (g rs1) (g rs2) then 1 else 0⟩
  -- ALU immediate
  | .ADDI  rd rs1 imm => some ⟨rd, [rs1], fun g => g rs1 + signExtend12 imm⟩
  | .ANDI  rd rs1 imm => some ⟨rd, [rs1], fun g => g rs1 &&& signExtend12 imm⟩
  | .ORI   rd rs1 imm => some ⟨rd, [rs1], fun g => g rs1 ||| signExtend12 imm⟩
  | .XORI  rd rs1 imm => some ⟨rd, [rs1], fun g => g rs1 ^^^ signExtend12 imm⟩
  | .SLTI  rd rs1 imm => some ⟨rd, [rs1],
      fun g => if BitVec.slt (g rs1) (signExtend12 imm) then 1 else 0⟩
  | .SLTIU rd rs1 imm => some ⟨rd, [rs1],
      fun g => if BitVec.ult (g rs1) (signExtend12 imm) then 1 else 0⟩
  | .SLLI  rd rs1 shamt => some ⟨rd, [rs1], fun g => g rs1 <<< shamt.toNat⟩
  | .SRLI  rd rs1 shamt => some ⟨rd, [rs1], fun g => g rs1 >>> shamt.toNat⟩
  | .SRAI  rd rs1 shamt => some ⟨rd, [rs1],
      fun g => BitVec.sshiftRight (g rs1) shamt.toNat⟩
  -- Upper immediate / constants / pseudo
  | .LUI rd imm => some ⟨rd, [],
      fun _ => ((imm.zeroExtend 32 <<< 12 : BitVec 32).signExtend 64)⟩
  | .MV  rd rs  => some ⟨rd, [rs], fun g => g rs⟩
  | .LI  rd imm => some ⟨rd, [], fun _ => imm⟩
  | .NOP        => some ⟨.x0, [], fun _ => 0⟩
  -- *W
  | .ADDIW rd rs1 imm => some ⟨rd, [rs1],
      fun g => (((g rs1).truncate 32 + (signExtend12 imm).truncate 32 : BitVec 32).signExtend 64)⟩
  -- RV64M
  | .MUL    rd rs1 rs2 => some ⟨rd, [rs1, rs2], fun g => g rs1 * g rs2⟩
  | .MULH   rd rs1 rs2 => some ⟨rd, [rs1, rs2], fun g => rv64_mulh (g rs1) (g rs2)⟩
  | .MULHSU rd rs1 rs2 => some ⟨rd, [rs1, rs2], fun g => rv64_mulhsu (g rs1) (g rs2)⟩
  | .MULHU  rd rs1 rs2 => some ⟨rd, [rs1, rs2], fun g => rv64_mulhu (g rs1) (g rs2)⟩
  | .DIV    rd rs1 rs2 => some ⟨rd, [rs1, rs2], fun g => rv64_div (g rs1) (g rs2)⟩
  | .DIVU   rd rs1 rs2 => some ⟨rd, [rs1, rs2], fun g => rv64_divu (g rs1) (g rs2)⟩
  | .REM    rd rs1 rs2 => some ⟨rd, [rs1, rs2], fun g => rv64_rem (g rs1) (g rs2)⟩
  | .REMU   rd rs1 rs2 => some ⟨rd, [rs1, rs2], fun g => rv64_remu (g rs1) (g rs2)⟩
  -- Everything else (memory, control flow, system) is not a block leaf.
  | _ => none


-- @@ L184-192 verbatim
/-- Classification of a load from the function's read-only region:
    destination, address register, immediate offset, access width in bytes,
    and the loaded (extended) word as a function of region and address. -/
structure LoadOp where
  rd : Reg
  rs1 : Reg
  ofs : BitVec 12
  nbytes : Nat
  val : Region → Word → Word


-- @@ L194-203 verbatim
/-- Classify a load.  Bytes, halfwords, 32-bit words, and dwords. -/
def loadSem : Instr → Option LoadOp
  | .LBU rd rs1 ofs => some ⟨rd, rs1, ofs, 1, fun reg a => (reg.byteAt a).zeroExtend 64⟩
  | .LB  rd rs1 ofs => some ⟨rd, rs1, ofs, 1, fun reg a => (reg.byteAt a).signExtend 64⟩
  | .LHU rd rs1 ofs => some ⟨rd, rs1, ofs, 2, fun reg a => (reg.half16At a).zeroExtend 64⟩
  | .LH  rd rs1 ofs => some ⟨rd, rs1, ofs, 2, fun reg a => (reg.half16At a).signExtend 64⟩
  | .LW  rd rs1 ofs => some ⟨rd, rs1, ofs, 4, fun reg a => (reg.word32At a).signExtend 64⟩
  | .LWU rd rs1 ofs => some ⟨rd, rs1, ofs, 4, fun reg a => (reg.word32At a).zeroExtend 64⟩
  | .LD  rd rs1 ofs => some ⟨rd, rs1, ofs, 8, fun reg a => reg.dwordAt a⟩
  | _ => none


-- @@ L205-213 verbatim
/-- Classification of a store to the function's writable region: address
    register, data register, immediate offset, access width in bytes, and
    the little-endian payload as a function of the stored word. -/
structure StoreOp where
  rs1 : Reg
  rs2 : Reg
  ofs : BitVec 12
  nbytes : Nat
  payload : Word → List (BitVec 8)


-- @@ L215-221 verbatim
/-- Classify a store.  Bytes, halfwords, 32-bit words, and dwords. -/
def storeSem : Instr → Option StoreOp
  | .SB rs1 rs2 ofs => some ⟨rs1, rs2, ofs, 1, fun v => [v.truncate 8]⟩
  | .SH rs1 rs2 ofs => some ⟨rs1, rs2, ofs, 2, fun v => halfwordBytes (v.truncate 16)⟩
  | .SW rs1 rs2 ofs => some ⟨rs1, rs2, ofs, 4, fun v => word32Bytes (v.truncate 32)⟩
  | .SD rs1 rs2 ofs => some ⟨rs1, rs2, ofs, 8, fun v => dwordBytes v⟩
  | _ => none


-- @@ L223-227 verbatim
/-- Every supported store moves at least one byte. -/
theorem storeSem_nbytes_pos {i : Instr} {st : StoreOp} (h : storeSem i = some st) :
    0 < st.nbytes := by
  cases i <;> simp only [storeSem, reduceCtorEq] at h <;>
    (injection h with h; subst h; simp)


-- @@ L229-234 verbatim
/-- The payload has exactly the classified width. -/
theorem storeSem_payload_length {i : Instr} {st : StoreOp}
    (h : storeSem i = some st) (v : Word) :
    (st.payload v).length = st.nbytes := by
  cases i <;> simp only [storeSem, reduceCtorEq] at h <;>
    (injection h with h; subst h; rfl)


-- @@ L236-258 verbatim
/-- Symbolic execution of one instruction over the register file and the
    writable region's contents `ws`.  A load whose access falls entirely
    inside the writable region reads the symbolic contents; every other load
    reads the read-only region `ro`.  Unsupported instructions are the
    identity; they are ruled out by `instrOk`, which the VC generator
    enforces. -/
def execInstrRF (ro : Region) (rwBase : Word) (rf : RegFile)
    (ws : List (BitVec 8)) (i : Instr) : RegFile × List (BitVec 8) :=
  match aluSem i with
  | some op => (rf.set op.rd (op.f rf.get), ws)
  | none =>
    match loadSem i with
    | some l =>
        let a := rf.get l.rs1 + signExtend12 l.ofs
        ((if inRw rwBase ws a l.nbytes
          then rf.set l.rd (l.val ⟨rwBase, ws⟩ a)
          else rf.set l.rd (l.val ro a)), ws)
    | none =>
      match storeSem i with
      | some st =>
          let a := rf.get st.rs1 + signExtend12 st.ofs
          (rf, setBytes ws (a - rwBase).toNat (st.payload (rf.get st.rs2)))
      | none => (rf, ws)


-- @@ L260-278 verbatim
/-- Supported-and-exposed check for a block leaf instruction: the instruction
    is in the supported subset, writes an exposed register (or x0), and reads
    only exposed registers (or x0). -/
def instrOk (i : Instr) : Bool :=
  match aluSem i with
  | some op =>
      (Reg.isExposed op.rd || op.rd == .x0)
        && op.srcs.all (fun r => Reg.isExposed r || r == .x0)
  | none =>
    match loadSem i with
    | some l =>
        (Reg.isExposed l.rd || l.rd == .x0)
          && (Reg.isExposed l.rs1 || l.rs1 == .x0)
    | none =>
      match storeSem i with
      | some st =>
          (Reg.isExposed st.rs1 || st.rs1 == .x0)
            && (Reg.isExposed st.rs2 || st.rs2 == .x0)
      | none => false


-- @@ L280-286 verbatim
/-- Forward symbolic execution of a straight-line block. -/
def execBlock (ro : Region) (rwBase : Word) (rf : RegFile)
    (ws : List (BitVec 8)) : List Instr → RegFile × List (BitVec 8)
  | [] => (rf, ws)
  | i :: is =>
      execBlock ro rwBase (execInstrRF ro rwBase rf ws i).1
        (execInstrRF ro rwBase rf ws i).2 is


-- @@ L288-290 verbatim
/-- Every instruction of the block is a supported, exposure-respecting leaf. -/
def blockOk (instrs : List Instr) : Bool :=
  instrs.all instrOk


-- @@ L292-313 verbatim
/-- Address side conditions of a block's loads, threaded through the
    symbolic execution: a load routed to the writable region must be aligned
    (it fits by the routing condition); every other load indexes into the
    read-only region. -/
def blockVCs (ro : Region) (rwBase : Word) (rf : RegFile)
    (ws : List (BitVec 8)) : List Instr → Prop
  | [] => True
  | i :: is =>
      (match loadSem i with
       | some l =>
           let a := rf.get l.rs1 + signExtend12 l.ofs
           if inRw rwBase ws a l.nbytes
           then (Region.mk rwBase ws).loadOk a l.nbytes
           else ro.loadOk a l.nbytes
       | none =>
         match storeSem i with
         | some st =>
             let a := rf.get st.rs1 + signExtend12 st.ofs
             inRw rwBase ws a st.nbytes ∧ st.nbytes ∣ (a - rwBase).toNat
         | none => True)
      ∧ blockVCs ro rwBase (execInstrRF ro rwBase rf ws i).1
          (execInstrRF ro rwBase rf ws i).2 is


-- @@ L315-318 verbatim
/-- Whether a block contains any memory access (decides whether a `.mem`
    VC is emitted at all). -/
def hasLoad (instrs : List Instr) : Bool :=
  instrs.any (fun i => (loadSem i).isSome || (storeSem i).isSome)


-- @@ L320-334 verbatim
/-- Blocks without memory accesses have no memory side conditions. -/
theorem blockVCs_of_not_hasLoad (ro : Region) (rwBase : Word) (rf : RegFile)
    (ws : List (BitVec 8)) (instrs : List Instr) (h : hasLoad instrs = false) :
    blockVCs ro rwBase rf ws instrs := by
  induction instrs generalizing rf ws with
  | nil => trivial
  | cons i is ih =>
      simp only [hasLoad, List.any_cons, Bool.or_eq_false_iff] at h
      refine ⟨?_, ih _ _ (by simp [hasLoad, h.2])⟩
      cases hl : loadSem i with
      | none =>
          cases hst : storeSem i with
          | none => trivial
          | some st => simp [hl, hst] at h
      | some l => simp [hl] at h


-- @@ L336-340 verbatim
/-- Every supported load moves at least one byte. -/
theorem loadSem_nbytes_pos {i : Instr} {l : LoadOp} (h : loadSem i = some l) :
    0 < l.nbytes := by
  cases i <;> simp only [loadSem, reduceCtorEq] at h <;>
    (injection h with h; subst h; simp)


-- @@ L342-347 verbatim
/-- With no writable bytes, nothing routes to the writable region. -/
theorem not_inRw_nil {rwBase a : Word} {n : Nat} (hn : 0 < n) :
    ¬ inRw rwBase [] a n := by
  unfold inRw
  simp only [List.length_nil, Nat.le_zero]
  omega


-- @@ L349-354 verbatim
/-- Routing `if` over an empty writable region collapses to the read-only
    branch (`hn` is discharged by `decide` for the engine's literal widths). -/
@[simp] theorem ite_inRw_nil {α : Sort u} (rwBase a : Word) {n : Nat}
    (hn : 0 < n) (X Y : α) :
    (if inRw rwBase [] a n then X else Y) = Y :=
  if_neg (not_inRw_nil hn)


-- @@ L356-383 verbatim
/-- With no writable bytes, one engine step reads the read-only region:
    the `ws = []` reduction demos and read-only ports rewrite with. -/
@[simp] theorem execInstrRF_nil (ro : Region) (rwBase : Word) (rf : RegFile)
    (i : Instr) :
    execInstrRF ro rwBase rf [] i
      = (match aluSem i with
         | some op => (rf.set op.rd (op.f rf.get), [])
         | none =>
           match loadSem i with
           | some l =>
               (rf.set l.rd (l.val ro (rf.get l.rs1 + signExtend12 l.ofs)), [])
           | none => (rf, [])) := by
  unfold execInstrRF
  cases haluSem : aluSem i with
  | some op => rfl
  | none =>
      cases hload : loadSem i with
      | some l =>
          dsimp only
          rw [if_neg (not_inRw_nil (loadSem_nbytes_pos hload))]
      | none =>
          cases hst : storeSem i with
          | some st =>
              dsimp only
              rw [show setBytes [] ((rf.get st.rs1 + signExtend12 st.ofs)
                    - rwBase).toNat (st.payload (rf.get st.rs2))
                  = [] from setBytes_nil_left ..]
          | none => rfl


-- @@ L385-396 verbatim
/-- One instruction preserves the writable region's size. -/
@[simp] theorem execInstrRF_ws_length (ro : Region) (rwBase : Word)
    (rf : RegFile) (ws : List (BitVec 8)) (i : Instr) :
    (execInstrRF ro rwBase rf ws i).2.length = ws.length := by
  unfold execInstrRF
  split
  · rfl
  · split
    · rfl
    · split
      · exact length_setBytes ..
      · rfl


-- @@ L398-406 verbatim
/-- A block preserves the writable region's size. -/
@[simp] theorem execBlock_ws_length (ro : Region) (rwBase : Word)
    (rf : RegFile) (ws : List (BitVec 8)) (instrs : List Instr) :
    (execBlock ro rwBase rf ws instrs).2.length = ws.length := by
  induction instrs generalizing rf ws with
  | nil => rfl
  | cons i is ih =>
      show (execBlock ro rwBase _ _ is).2.length = _
      rw [ih, execInstrRF_ws_length]


-- @@ L408-410 verbatim
@[simp] theorem execBlock_nil (ro : Region) (rwBase : Word) (rf : RegFile)
    (ws : List (BitVec 8)) :
    execBlock ro rwBase rf ws [] = (rf, ws) := rfl


-- @@ L412-428 verbatim
@[simp] theorem execBlock_cons (ro : Region) (rwBase : Word) (rf : RegFile)
    (ws : List (BitVec 8)) (i : Instr) (is : List Instr) :
    execBlock ro rwBase rf ws (i :: is)
      = execBlock ro rwBase (execInstrRF ro rwBase rf ws i).1
          (execInstrRF ro rwBase rf ws i).2 is := rfl

-- ============================================================================
-- Engine-step projections (multi-access focus blocks)
--
-- `blockVCs`/`execBlock` thread the register file through each prior
-- `execInstrRF`; for loads that term is an unreduced routing `if`, so a
-- later access's address expression contains the whole previous load
-- verbatim.  These projections let `simp only`/`rw` normalize
-- "instruction doesn't write `r`" and "instruction doesn't touch the
-- window" WITHOUT unfolding `execInstrRF` or resolving the routing `if`s.
-- Recipe: docs/sasm-howto.md ("Multi-dword focus blocks").
-- ============================================================================


-- @@ L430-450 verbatim
/-- One engine step leaves every register other than the classified
    destination unchanged — including for loads, where the result is a
    routing `if` (both branches set the same `rd`, so the read commutes
    past the `if` without deciding it). -/
theorem execInstrRF_get_ne (ro : Region) (rwBase : Word) (rf : RegFile)
    (ws : List (BitVec 8)) (i : Instr) (r : Reg)
    (halu : ∀ op, aluSem i = some op → r ≠ op.rd)
    (hload : ∀ l, loadSem i = some l → r ≠ l.rd) :
    (execInstrRF ro rwBase rf ws i).1.get r = rf.get r := by
  unfold execInstrRF
  cases ha : aluSem i with
  | some op => exact RegFile.get_set_ne _ _ _ _ (halu op ha)
  | none =>
    cases hl : loadSem i with
    | some l =>
        dsimp only
        split <;> exact RegFile.get_set_ne _ _ _ _ (hload l hl)
    | none =>
        cases hst : storeSem i with
        | some st => rfl
        | none => rfl


-- @@ L452-459 verbatim
/-- Load-step register projection, in directly-`rw`-able per-constructor
    form: an `LD` into `rd` preserves every other register. -/
theorem execInstrRF_ld_get_ne (ro : Region) (rwBase : Word) (rf : RegFile)
    (ws : List (BitVec 8)) (rd rs1 : Reg) (ofs : BitVec 12) (r : Reg)
    (h : r ≠ rd) :
    (execInstrRF ro rwBase rf ws (.LD rd rs1 ofs)).1.get r = rf.get r :=
  execInstrRF_get_ne ro rwBase rf ws _ r (fun op hop => nomatch hop)
    (fun l hl => by injection hl with hl; subst hl; exact h)


-- @@ L461-466 verbatim
/-- A load step never changes the writable window. -/
@[simp] theorem execInstrRF_ld_snd (ro : Region) (rwBase : Word)
    (rf : RegFile) (ws : List (BitVec 8)) (rd rs1 : Reg) (ofs : BitVec 12) :
    (execInstrRF ro rwBase rf ws (.LD rd rs1 ofs)).2 = ws := by
  unfold execInstrRF
  dsimp only [aluSem, loadSem]


-- @@ L468-471 verbatim
/-- A store step never changes the register file. -/
@[simp] theorem execInstrRF_sd_fst (ro : Region) (rwBase : Word)
    (rf : RegFile) (ws : List (BitVec 8)) (rs1 rs2 : Reg) (ofs : BitVec 12) :
    (execInstrRF ro rwBase rf ws (.SD rs1 rs2 ofs)).1 = rf := rfl


-- @@ L473-480 verbatim
/-- A store step splices its payload into the window at the classified
    index (stated so `.mem`/engine proofs can rewrite without unfolding
    `execInstrRF`). -/
theorem execInstrRF_sd_snd (ro : Region) (rwBase : Word) (rf : RegFile)
    (ws : List (BitVec 8)) (rs1 rs2 : Reg) (ofs : BitVec 12) :
    (execInstrRF ro rwBase rf ws (.SD rs1 rs2 ofs)).2
      = setBytes ws ((rf.get rs1 + signExtend12 ofs) - rwBase).toNat
          (dwordBytes (rf.get rs2)) := rfl


-- @@ L482-506 verbatim
/-- **The dword-load step, fully resolved**: an `LD` whose address lands
    `k` bytes into the window, where the window's dword at `k` is `v`,
    is exactly `rf.set rd v` with the window untouched.  Chain this once
    per load (with `execBlock_cons`) to run a multi-load block through
    the engine in one `rw` each — no routing `if`s survive.  The `haddr`
    side condition is `bv_omega` after reducing the `signExtend12`
    literal (`show signExtend12 (8 : BitVec 12) = (8 : Word) from by
    decide`); `hslice` is `List.drop`/`take` algebra on the window. -/
theorem execInstrRF_ld_dword (ro : Region) (rwBase : Word) (rf : RegFile)
    (ws : List (BitVec 8)) (rd rs1 : Reg) (ofs : BitVec 12) (k : Nat)
    (v : Word)
    (haddr : ((rf.get rs1 + signExtend12 ofs) - rwBase).toNat = k)
    (hfit : k + 8 ≤ ws.length)
    (hslice : packBytes ((ws.drop k).take 8) = v) :
    execInstrRF ro rwBase rf ws (.LD rd rs1 ofs) = (rf.set rd v, ws) := by
  unfold execInstrRF
  dsimp only [aluSem, loadSem]
  rw [if_pos (show inRw rwBase ws (rf.get rs1 + signExtend12 ofs) 8 from by
    unfold inRw
    rw [haddr]
    omega)]
  unfold Region.dwordAt
  rw [show ((rf.get rs1 + signExtend12 ofs)
      - (⟨rwBase, ws⟩ : Region).base).toNat = k from haddr,
    hslice]


-- @@ L508-526 verbatim
/-- **The byte-load step, fully resolved**: an `LBU` whose address lands
    `k` bytes into the window is exactly `rf.set rd` of the (zero-extended)
    `k`-th window byte, window untouched.  Byte accesses have no alignment
    side condition — only `hfit`. -/
theorem execInstrRF_lbu_byte (ro : Region) (rwBase : Word) (rf : RegFile)
    (ws : List (BitVec 8)) (rd rs1 : Reg) (ofs : BitVec 12) (k : Nat)
    (haddr : ((rf.get rs1 + signExtend12 ofs) - rwBase).toNat = k)
    (hfit : k + 1 ≤ ws.length) :
    execInstrRF ro rwBase rf ws (.LBU rd rs1 ofs)
      = (rf.set rd ((ws.getD k 0).zeroExtend 64), ws) := by
  unfold execInstrRF
  dsimp only [aluSem, loadSem]
  rw [if_pos (show inRw rwBase ws (rf.get rs1 + signExtend12 ofs) 1 from by
    unfold inRw
    rw [haddr]
    omega)]
  unfold Region.byteAt
  rw [show ((rf.get rs1 + signExtend12 ofs)
      - (⟨rwBase, ws⟩ : Region).base).toNat = k from haddr]


-- @@ L528-539 verbatim
/-- **The byte-store step, fully resolved**: an `SB` whose address lands
    `k` bytes into the window splices the (truncated) source byte at `k`
    and leaves the registers alone.  With `setBytes_singleton`
    (MultiDword.lean) the window becomes a plain `List.set`. -/
theorem execInstrRF_sb_byte (ro : Region) (rwBase : Word) (rf : RegFile)
    (ws : List (BitVec 8)) (rs1 rs2 : Reg) (ofs : BitVec 12) (k : Nat)
    (haddr : ((rf.get rs1 + signExtend12 ofs) - rwBase).toNat = k) :
    execInstrRF ro rwBase rf ws (.SB rs1 rs2 ofs)
      = (rf, setBytes ws k [(rf.get rs2).truncate 8]) := by
  rw [show execInstrRF ro rwBase rf ws (.SB rs1 rs2 ofs)
      = (rf, setBytes ws ((rf.get rs1 + signExtend12 ofs) - rwBase).toNat
          [(rf.get rs2).truncate 8]) from rfl, haddr]


-- @@ L541-544 verbatim
/-- A byte-store step never changes the register file. -/
@[simp] theorem execInstrRF_sb_fst (ro : Region) (rwBase : Word)
    (rf : RegFile) (ws : List (BitVec 8)) (rs1 rs2 : Reg) (ofs : BitVec 12) :
    (execInstrRF ro rwBase rf ws (.SB rs1 rs2 ofs)).1 = rf := rfl


-- @@ L546-552 verbatim
/-- A byte-store step splices its (truncated) byte at the classified
    index. -/
theorem execInstrRF_sb_snd (ro : Region) (rwBase : Word) (rf : RegFile)
    (ws : List (BitVec 8)) (rs1 rs2 : Reg) (ofs : BitVec 12) :
    (execInstrRF ro rwBase rf ws (.SB rs1 rs2 ofs)).2
      = setBytes ws ((rf.get rs1 + signExtend12 ofs) - rwBase).toNat
          [(rf.get rs2).truncate 8] := rfl


-- @@ L554-564 verbatim
/-- **The dword-store step, fully resolved**: an `SD` whose address lands
    `k` bytes into the window splices `dwordBytes (rf.get rs2)` at `k`
    and leaves the registers alone. -/
theorem execInstrRF_sd_dword (ro : Region) (rwBase : Word) (rf : RegFile)
    (ws : List (BitVec 8)) (rs1 rs2 : Reg) (ofs : BitVec 12) (k : Nat)
    (haddr : ((rf.get rs1 + signExtend12 ofs) - rwBase).toNat = k) :
    execInstrRF ro rwBase rf ws (.SD rs1 rs2 ofs)
      = (rf, setBytes ws k (dwordBytes (rf.get rs2))) := by
  rw [show execInstrRF ro rwBase rf ws (.SD rs1 rs2 ofs)
      = (rf, setBytes ws ((rf.get rs1 + signExtend12 ofs) - rwBase).toNat
          (dwordBytes (rf.get rs2))) from rfl, haddr]


-- @@ L566-566 verbatim
end SAsm

-- @@ L567-567 verbatim
end EvmAsm.Rv64
