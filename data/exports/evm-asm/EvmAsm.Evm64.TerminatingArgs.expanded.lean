/-
  EvmAsm.Evm64.TerminatingArgs

  Pure stack-argument records for frame-terminating opcodes (GH #113).

  Mirrors the LogArgs / CallArgs pattern: a `Kind` classifier covering
  STOP, RETURN, REVERT, INVALID, and SELFDESTRUCT, together with a
  `TerminatingArgs` structure capturing the (offset, size) pair that
  RETURN and REVERT pop off the stack to describe the returned memory
  slice.

  This file is intentionally pure / RISC-V-free: it gives downstream
  spec/program files (under #113) a stable surface to refer to before
  the assembly-level handlers land.
-/

module

public import EvmAsm.Evm64.EvmWord


-- @@ L21-21 verbatim
@[expose] public section


-- @@ L23-23 verbatim
namespace EvmAsm.Evm64


-- @@ L25-25 verbatim
namespace TerminatingArgs


-- @@ L27-33 verbatim
/-- Memory slice described by an EVM offset and byte size.  Mirrors
    `LogArgs.MemoryRange` and `CallArgs.MemoryRange` so call sites can
    share helpers in the future without coercing between record types. -/
structure MemoryRange where
  offset : EvmWord
  size : EvmWord
  deriving Repr


-- @@ L35-42 verbatim
/-- Frame-terminating opcode classifier. -/
inductive Kind where
  | stop
  | return_
  | revert
  | invalid
  | selfdestruct
  deriving DecidableEq, Repr


-- @@ L44-46 verbatim
/-- The frame-terminating opcode kinds covered by GH #113. -/
def allKinds : List Kind :=
  [.stop, .return_, .revert, .invalid, .selfdestruct]


-- @@ L48-54 verbatim
/-- Stack arguments for RETURN/REVERT: a memory range describing the
returned/reverted byte slice. STOP / INVALID / SELFDESTRUCT carry no
relevant memory range here (SELFDESTRUCT pops a beneficiary address,
modeled separately). -/
structure Args where
  data : MemoryRange
  deriving Repr


-- @@ L56-63 verbatim
/-- RETURN/REVERT pop two stack words (offset, size); STOP / INVALID
pop none; SELFDESTRUCT pops one (the beneficiary address). -/
def stackArgumentCount : Kind → Nat
  | .stop => 0
  | .return_ => 2
  | .revert => 2
  | .invalid => 0
  | .selfdestruct => 1


-- @@ L65-71 verbatim
/-- Whether the opcode reads a memory slice off the stack. -/
def hasMemoryRange : Kind → Bool
  | .stop => false
  | .return_ => true
  | .revert => true
  | .invalid => false
  | .selfdestruct => false


-- @@ L73-81 verbatim
/-- Whether the opcode signals a successful (non-error) termination.
RETURN and STOP succeed; REVERT and INVALID fail; SELFDESTRUCT succeeds
with respect to frame status. -/
def isSuccess : Kind → Bool
  | .stop => true
  | .return_ => true
  | .revert => false
  | .invalid => false
  | .selfdestruct => true


-- @@ L83-91 verbatim
/-- Whether the opcode reverts in-frame state changes. Only REVERT
preserves the caller's pre-call state; INVALID also rolls back but
additionally consumes all gas. -/
def reverts : Kind → Bool
  | .stop => false
  | .return_ => false
  | .revert => true
  | .invalid => true
  | .selfdestruct => false


-- @@ L93-95 verbatim
/-- Convenience builder used by RETURN/REVERT consumers. -/
def returnArgs (offset size : EvmWord) : Args :=
  { data := { offset := offset, size := size } }


-- @@ L97-99 verbatim
/-- Convenience builder used by RETURN/REVERT consumers (REVERT alias). -/
def revertArgs (offset size : EvmWord) : Args :=
  { data := { offset := offset, size := size } }


-- @@ L101-103 verbatim
/-- The data memory range projected from a terminating-args record. -/
def dataRange (args : Args) : MemoryRange :=
  args.data


-- @@ L105-106 verbatim
theorem stackArgumentCountStop :
    stackArgumentCount .stop = 0 := rfl


-- @@ L108-109 verbatim
theorem stackArgumentCountReturn :
    stackArgumentCount .return_ = 2 := rfl


-- @@ L111-112 verbatim
theorem stackArgumentCountRevert :
    stackArgumentCount .revert = 2 := rfl


-- @@ L114-115 verbatim
theorem stackArgumentCountInvalid :
    stackArgumentCount .invalid = 0 := rfl


-- @@ L117-118 verbatim
theorem stackArgumentCountSelfdestruct :
    stackArgumentCount .selfdestruct = 1 := rfl


-- @@ L120-122 verbatim
theorem allKinds_nodup :
    allKinds.Nodup := by
  decide


-- @@ L124-126 verbatim
theorem mem_allKinds (kind : Kind) :
    kind ∈ allKinds := by
  cases kind <;> decide


-- @@ L128-129 verbatim
theorem allKinds_stackArgumentCounts :
    allKinds.map stackArgumentCount = [0, 2, 2, 0, 1] := rfl


-- @@ L131-132 verbatim
theorem allKinds_hasMemoryRanges :
    allKinds.map hasMemoryRange = [false, true, true, false, false] := rfl


-- @@ L134-135 verbatim
theorem allKinds_isSuccesses :
    allKinds.map isSuccess = [true, true, false, false, true] := rfl


-- @@ L137-138 verbatim
theorem allKinds_reverts :
    allKinds.map reverts = [false, false, true, true, false] := rfl


-- @@ L140-141 verbatim
theorem hasMemoryRangeReturn :
    hasMemoryRange .return_ = true := rfl


-- @@ L143-144 verbatim
theorem hasMemoryRangeRevert :
    hasMemoryRange .revert = true := rfl


-- @@ L146-147 verbatim
theorem hasMemoryRangeStop :
    hasMemoryRange .stop = false := rfl


-- @@ L149-150 verbatim
theorem hasMemoryRangeInvalid :
    hasMemoryRange .invalid = false := rfl


-- @@ L152-153 verbatim
theorem hasMemoryRangeSelfdestruct :
    hasMemoryRange .selfdestruct = false := rfl


-- @@ L155-156 verbatim
theorem returnArgs_offset (offset size : EvmWord) :
    (returnArgs offset size).data.offset = offset := rfl


-- @@ L158-159 verbatim
theorem returnArgs_size (offset size : EvmWord) :
    (returnArgs offset size).data.size = size := rfl


-- @@ L161-162 verbatim
theorem revertArgs_offset (offset size : EvmWord) :
    (revertArgs offset size).data.offset = offset := rfl


-- @@ L164-165 verbatim
theorem revertArgs_size (offset size : EvmWord) :
    (revertArgs offset size).data.size = size := rfl


-- @@ L167-169 verbatim
theorem stackArgumentCount_eq_two_of_hasMemoryRange (kind : Kind) :
    hasMemoryRange kind = true → stackArgumentCount kind = 2 := by
  cases kind <;> simp [hasMemoryRange, stackArgumentCount]


-- @@ L171-173 verbatim
theorem hasMemoryRange_of_stackArgumentCount_eq_two (kind : Kind) :
    stackArgumentCount kind = 2 → hasMemoryRange kind = true := by
  cases kind <;> simp [hasMemoryRange, stackArgumentCount]


-- @@ L175-178 verbatim
theorem hasMemoryRange_iff_stackArgumentCount_eq_two (kind : Kind) :
    hasMemoryRange kind = true ↔ stackArgumentCount kind = 2 :=
  ⟨stackArgumentCount_eq_two_of_hasMemoryRange kind,
    hasMemoryRange_of_stackArgumentCount_eq_two kind⟩


-- @@ L180-182 verbatim
theorem reverts_imp_not_isSuccess (kind : Kind) :
    reverts kind = true → isSuccess kind = false := by
  cases kind <;> simp [reverts, isSuccess]


-- @@ L184-192 verbatim
/-- Whether the opcode signals a failed (non-success) termination. The
boolean dual of `isSuccess`: REVERT and INVALID fail; STOP, RETURN, and
SELFDESTRUCT succeed. -/
def failed : Kind → Bool
  | .stop => false
  | .return_ => false
  | .revert => true
  | .invalid => true
  | .selfdestruct => false


-- @@ L194-194 verbatim
@[simp] theorem failed_stop : failed .stop = false := rfl

-- @@ L195-195 verbatim
@[simp] theorem failed_return : failed .return_ = false := rfl

-- @@ L196-196 verbatim
@[simp] theorem failed_revert : failed .revert = true := rfl

-- @@ L197-197 verbatim
@[simp] theorem failed_invalid : failed .invalid = true := rfl

-- @@ L198-198 verbatim
@[simp] theorem failed_selfdestruct : failed .selfdestruct = false := rfl


-- @@ L200-202 verbatim
theorem failed_eq_not_isSuccess (kind : Kind) :
    failed kind = !isSuccess kind := by
  cases kind <;> rfl


-- @@ L204-205 verbatim
theorem allKinds_failed :
    allKinds.map failed = [false, false, true, true, false] := rfl


-- @@ L207-209 verbatim
theorem isSuccess_eq_not_failed (kind : Kind) :
    isSuccess kind = !failed kind := by
  cases kind <;> rfl


-- @@ L211-213 verbatim
theorem reverts_imp_failed (kind : Kind) :
    reverts kind = true → failed kind = true := by
  cases kind <;> simp [reverts, failed]


-- @@ L215-216 verbatim
theorem dataRange_offset (offset size : EvmWord) :
    (dataRange { data := { offset := offset, size := size } }).offset = offset := rfl


-- @@ L218-219 verbatim
theorem dataRange_size (offset size : EvmWord) :
    (dataRange { data := { offset := offset, size := size } }).size = size := rfl


-- @@ L221-221 verbatim
end TerminatingArgs


-- @@ L223-223 verbatim
end EvmAsm.Evm64
