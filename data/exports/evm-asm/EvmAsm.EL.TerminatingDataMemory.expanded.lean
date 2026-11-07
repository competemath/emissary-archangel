/-
  EvmAsm.EL.TerminatingDataMemory

  Bridge from RETURN/REVERT stack arguments to returned memory bytes (GH #113).
-/

module

public import EvmAsm.EL.TerminatingArgsBridge


-- @@ L11-11 verbatim
@[expose] public section


-- @@ L13-13 verbatim
namespace EvmAsm.EL


-- @@ L15-15 verbatim
namespace TerminatingDataMemory


-- @@ L17-17 verbatim
abbrev TerminatingArgs := TerminatingArgsBridge.TerminatingArgs

-- @@ L18-18 verbatim
abbrev TerminatingKind := TerminatingArgsBridge.TerminatingKind

-- @@ L19-19 verbatim
abbrev MemoryReader := Nat → Byte


-- @@ L21-23 verbatim
/-- First memory byte consumed as RETURN/REVERT output data. -/
def dataStart (args : TerminatingArgs) : Nat :=
  (TerminatingArgsBridge.dataRange args).offset.toNat


-- @@ L25-27 verbatim
/-- Number of memory bytes consumed as RETURN/REVERT output data. -/
def dataSize (args : TerminatingArgs) : Nat :=
  (TerminatingArgsBridge.dataRange args).size.toNat


-- @@ L29-32 verbatim
/-- RETURN/REVERT data bytes loaded from a pure memory-reader function. -/
def terminatingDataFromMemory
    (readByte : MemoryReader) (args : TerminatingArgs) : List Byte :=
  (List.range (dataSize args)).map (fun i => readByte (dataStart args + i))


-- @@ L34-35 verbatim
theorem dataStart_eq (args : TerminatingArgs) :
    dataStart args = (TerminatingArgsBridge.dataRange args).offset.toNat := rfl


-- @@ L37-38 verbatim
theorem dataSize_eq (args : TerminatingArgs) :
    dataSize args = (TerminatingArgsBridge.dataRange args).size.toNat := rfl


-- @@ L40-43 verbatim
@[simp] theorem terminatingDataFromMemory_length
    (readByte : MemoryReader) (args : TerminatingArgs) :
    (terminatingDataFromMemory readByte args).length = dataSize args := by
  simp [terminatingDataFromMemory]


-- @@ L45-51 verbatim
theorem terminatingDataFromMemory_get
    {readByte : MemoryReader} {args : TerminatingArgs} {i : Nat}
    (h : i < dataSize args) :
    (terminatingDataFromMemory readByte args)[i]'(by
      simpa [terminatingDataFromMemory_length] using h) =
      readByte (dataStart args + i) := by
  simp [terminatingDataFromMemory, List.getElem_map, List.getElem_range]


-- @@ L53-56 verbatim
@[simp] theorem terminatingDataFromMemory_zero_size
    (readByte : MemoryReader) (rangeOffset : EvmAsm.Evm64.EvmWord) :
    terminatingDataFromMemory readByte
        (EvmAsm.Evm64.TerminatingArgs.returnArgs rangeOffset 0) = [] := rfl


-- @@ L58-61 verbatim
@[simp] theorem terminatingDataFromMemory_revert_zero_size
    (readByte : MemoryReader) (rangeOffset : EvmAsm.Evm64.EvmWord) :
    terminatingDataFromMemory readByte
        (EvmAsm.Evm64.TerminatingArgs.revertArgs rangeOffset 0) = [] := rfl


-- @@ L63-63 verbatim
end TerminatingDataMemory


-- @@ L65-65 verbatim
end EvmAsm.EL
