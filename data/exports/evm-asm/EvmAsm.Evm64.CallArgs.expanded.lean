/-
  EvmAsm.Evm64.CallArgs

  Pure stack-argument records for CALL-family opcodes (GH #114).
-/

module

public import EvmAsm.Evm64.EvmWord


-- @@ L11-11 verbatim
@[expose] public section


-- @@ L13-13 verbatim
namespace EvmAsm.Evm64


-- @@ L15-15 verbatim
namespace CallArgs


-- @@ L17-21 verbatim
/-- Memory slice described by an EVM offset and byte size. -/
structure MemoryRange where
  offset : EvmWord
  size : EvmWord
  deriving Repr


-- @@ L23-30 verbatim
/-- CALL stack arguments: gas, target, value, input range, and output range. -/
structure Call where
  gas : EvmWord
  to : EvmWord
  value : EvmWord
  input : MemoryRange
  output : MemoryRange
  deriving Repr


-- @@ L32-38 verbatim
/-- STATICCALL stack arguments: no value transfer argument. -/
structure StaticCall where
  gas : EvmWord
  to : EvmWord
  input : MemoryRange
  output : MemoryRange
  deriving Repr


-- @@ L40-46 verbatim
/-- DELEGATECALL stack arguments: caller/value context is inherited. -/
structure DelegateCall where
  gas : EvmWord
  to : EvmWord
  input : MemoryRange
  output : MemoryRange
  deriving Repr


-- @@ L48-53 verbatim
/-- Opcode family classifier for stack argument decoding. -/
inductive Kind where
  | call
  | staticcall
  | delegatecall
  deriving DecidableEq, Repr


-- @@ L55-57 verbatim
/-- The CALL-family opcode kinds covered by GH #114. -/
def allKinds : List Kind :=
  [.call, .staticcall, .delegatecall]


-- @@ L59-62 verbatim
def argumentCount : Kind → Nat
  | .call => 7
  | .staticcall => 6
  | .delegatecall => 6


-- @@ L64-64 verbatim
def resultCount (_kind : Kind) : Nat := 1


-- @@ L66-66 verbatim
def memoryRangeCount (_kind : Kind) : Nat := 2


-- @@ L68-71 verbatim
def hasValueArgument : Kind → Bool
  | .call => true
  | .staticcall => false
  | .delegatecall => false


-- @@ L73-76 verbatim
def isStatic : Kind → Bool
  | .call => false
  | .staticcall => true
  | .delegatecall => false


-- @@ L78-81 verbatim
def preservesCallerContext : Kind → Bool
  | .call => false
  | .staticcall => false
  | .delegatecall => true


-- @@ L83-84 verbatim
theorem callArgumentCount :
    argumentCount .call = 7 := rfl


-- @@ L86-87 verbatim
theorem staticcallArgumentCount :
    argumentCount .staticcall = 6 := rfl


-- @@ L89-90 verbatim
theorem delegatecallArgumentCount :
    argumentCount .delegatecall = 6 := rfl


-- @@ L92-94 verbatim
theorem allKinds_nodup :
    allKinds.Nodup := by
  decide


-- @@ L96-98 verbatim
theorem mem_allKinds (kind : Kind) :
    kind ∈ allKinds := by
  cases kind <;> decide


-- @@ L100-101 verbatim
theorem allKinds_argumentCounts :
    allKinds.map argumentCount = [7, 6, 6] := rfl


-- @@ L103-104 verbatim
theorem allKinds_resultCounts :
    allKinds.map resultCount = [1, 1, 1] := rfl


-- @@ L106-107 verbatim
theorem allKinds_memoryRangeCounts :
    allKinds.map memoryRangeCount = [2, 2, 2] := rfl


-- @@ L109-110 verbatim
theorem resultCount_eq_one (kind : Kind) :
    resultCount kind = 1 := rfl


-- @@ L112-113 verbatim
theorem memoryRangeCount_eq_two (kind : Kind) :
    memoryRangeCount kind = 2 := rfl


-- @@ L115-117 verbatim
theorem argumentCount_eq_six_plus_value (kind : Kind) :
    argumentCount kind = 6 + if hasValueArgument kind then 1 else 0 := by
  cases kind <;> rfl


-- @@ L119-120 verbatim
theorem callHasValue :
    hasValueArgument .call = true := rfl


-- @@ L122-123 verbatim
theorem staticcallHasNoValue :
    hasValueArgument .staticcall = false := rfl


-- @@ L125-126 verbatim
theorem delegatecallHasNoValue :
    hasValueArgument .delegatecall = false := rfl


-- @@ L128-129 verbatim
theorem staticcallIsStatic :
    isStatic .staticcall = true := rfl


-- @@ L131-132 verbatim
theorem delegatecallPreservesCallerContext :
    preservesCallerContext .delegatecall = true := rfl


-- @@ L134-141 verbatim
/-! ### Classifier ↔ Kind iffs and pairwise mutual exclusions

Cross-predicate lemmas for the three Kind classifiers
(`hasValueArgument`, `isStatic`, `preservesCallerContext`). Each Kind is
characterised by exactly one of the predicates being `true`; the iffs make
that explicit and the pairwise exclusion lemmas let downstream proofs avoid
re-`cases`-ing on `Kind`. Mirrors the cross-predicate slice on
`TerminatingArgs` (see `EvmAsm.Evm64.TerminatingArgs`). -/


-- @@ L143-145 verbatim
theorem hasValueArgument_iff_call (kind : Kind) :
    hasValueArgument kind = true ↔ kind = .call := by
  cases kind <;> decide


-- @@ L147-149 verbatim
theorem isStatic_iff_staticcall (kind : Kind) :
    isStatic kind = true ↔ kind = .staticcall := by
  cases kind <;> decide


-- @@ L151-153 verbatim
theorem preservesCallerContext_iff_delegatecall (kind : Kind) :
    preservesCallerContext kind = true ↔ kind = .delegatecall := by
  cases kind <;> decide


-- @@ L155-157 verbatim
theorem not_hasValueArgument_iff_not_call (kind : Kind) :
    hasValueArgument kind = false ↔ kind ≠ .call := by
  cases kind <;> decide


-- @@ L159-161 verbatim
theorem not_isStatic_iff_not_staticcall (kind : Kind) :
    isStatic kind = false ↔ kind ≠ .staticcall := by
  cases kind <;> decide


-- @@ L163-165 verbatim
theorem not_preservesCallerContext_iff_not_delegatecall (kind : Kind) :
    preservesCallerContext kind = false ↔ kind ≠ .delegatecall := by
  cases kind <;> decide


-- @@ L167-169 verbatim
theorem argumentCount_eq_seven_iff_call (kind : Kind) :
    argumentCount kind = 7 ↔ kind = .call := by
  cases kind <;> decide


-- @@ L171-173 verbatim
theorem argumentCount_eq_six_iff_not_call (kind : Kind) :
    argumentCount kind = 6 ↔ kind ≠ .call := by
  cases kind <;> decide


-- @@ L175-177 verbatim
theorem hasValueArgument_not_isStatic (kind : Kind)
    (h : hasValueArgument kind = true) : isStatic kind = false := by
  cases kind <;> simp_all (config := { decide := true })


-- @@ L179-181 verbatim
theorem hasValueArgument_not_preservesCallerContext (kind : Kind)
    (h : hasValueArgument kind = true) : preservesCallerContext kind = false := by
  cases kind <;> simp_all (config := { decide := true })


-- @@ L183-185 verbatim
theorem isStatic_not_hasValueArgument (kind : Kind)
    (h : isStatic kind = true) : hasValueArgument kind = false := by
  cases kind <;> simp_all (config := { decide := true })


-- @@ L187-189 verbatim
theorem isStatic_not_preservesCallerContext (kind : Kind)
    (h : isStatic kind = true) : preservesCallerContext kind = false := by
  cases kind <;> simp_all (config := { decide := true })


-- @@ L191-193 verbatim
theorem preservesCallerContext_not_hasValueArgument (kind : Kind)
    (h : preservesCallerContext kind = true) : hasValueArgument kind = false := by
  cases kind <;> simp_all (config := { decide := true })


-- @@ L195-197 verbatim
theorem preservesCallerContext_not_isStatic (kind : Kind)
    (h : preservesCallerContext kind = true) : isStatic kind = false := by
  cases kind <;> simp_all (config := { decide := true })


-- @@ L199-199 verbatim
end CallArgs


-- @@ L201-201 verbatim
end EvmAsm.Evm64
