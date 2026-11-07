/-
  EvmAsm.EL.KeccakInputBridge

  Bridge from EVM KECCAK256 stack arguments to the executable memory input
  consumed by the zkVM accelerator (GH #111).
-/

module

public import EvmAsm.EL.WorldState
public import EvmAsm.Evm64.KeccakArgs


-- @@ L13-13 verbatim
@[expose] public section


-- @@ L15-15 verbatim
namespace EvmAsm.EL


-- @@ L17-17 verbatim
namespace KeccakInputBridge


-- @@ L19-19 verbatim
abbrev KeccakArgs := EvmAsm.Evm64.KeccakArgs.Args


-- @@ L21-22 verbatim
/-- A byte-addressed executable memory reader. -/
abbrev MemoryReader := Nat → Byte


-- @@ L24-27 verbatim
/-- Input payload passed to the `zkvm_keccak256(data, len, output)` accelerator. -/
structure AcceleratorInput where
  bytes : List Byte
  deriving Repr


-- @@ L29-34 verbatim
/--
Executable-spec `memory_read_bytes(memory, start, size)` shape: read exactly
`size` bytes starting at `start`.
-/
def memoryReadBytes (memory : MemoryReader) (start size : Nat) : List Byte :=
  (List.range size).map (fun i => memory (start + i))


-- @@ L36-40 verbatim
/-- Distinctive token: KeccakInputBridge.keccakInputBytesFromMemory #111. -/
def keccakInputBytesFromMemory (memory : MemoryReader) (args : KeccakArgs) : List Byte :=
  memoryReadBytes memory
    (EvmAsm.Evm64.KeccakArgs.inputOffsetNat args)
    (EvmAsm.Evm64.KeccakArgs.inputSizeNat args)


-- @@ L42-44 verbatim
/-- Accelerator-call input assembled from KECCAK stack arguments and memory. -/
def acceleratorInputFromArgs (memory : MemoryReader) (args : KeccakArgs) : AcceleratorInput :=
  { bytes := keccakInputBytesFromMemory memory args }


-- @@ L46-48 verbatim
theorem memoryReadBytes_length (memory : MemoryReader) (start size : Nat) :
    (memoryReadBytes memory start size).length = size := by
  simp [memoryReadBytes]


-- @@ L50-53 verbatim
theorem memoryReadBytes_get?
    (memory : MemoryReader) (start size i : Nat) (h_i : i < size) :
    (memoryReadBytes memory start size)[i]? = some (memory (start + i)) := by
  simp [memoryReadBytes, h_i]


-- @@ L55-56 verbatim
@[simp] theorem memoryReadBytes_zero (memory : MemoryReader) (start : Nat) :
    memoryReadBytes memory start 0 = [] := rfl


-- @@ L58-61 verbatim
theorem keccakInputBytesFromMemory_length (memory : MemoryReader) (args : KeccakArgs) :
    (keccakInputBytesFromMemory memory args).length =
      EvmAsm.Evm64.KeccakArgs.inputSizeNat args := by
  simp [keccakInputBytesFromMemory, memoryReadBytes_length]


-- @@ L63-68 verbatim
theorem keccakInputBytesFromMemory_get?
    (memory : MemoryReader) (args : KeccakArgs) (i : Nat)
    (h_i : i < EvmAsm.Evm64.KeccakArgs.inputSizeNat args) :
    (keccakInputBytesFromMemory memory args)[i]? =
      some (memory (EvmAsm.Evm64.KeccakArgs.inputOffsetNat args + i)) := by
  simp [keccakInputBytesFromMemory, memoryReadBytes_get?, h_i]


-- @@ L70-73 verbatim
@[simp] theorem keccakInputBytesFromMemory_zero_size
    (memory : MemoryReader) (offset : EvmAsm.Evm64.EvmWord) :
    keccakInputBytesFromMemory memory (EvmAsm.Evm64.KeccakArgs.keccakArgs offset 0) = [] := by
  rfl


-- @@ L75-77 verbatim
theorem acceleratorInputFromArgs_bytes (memory : MemoryReader) (args : KeccakArgs) :
    (acceleratorInputFromArgs memory args).bytes =
      keccakInputBytesFromMemory memory args := rfl


-- @@ L79-82 verbatim
theorem acceleratorInputFromArgs_length (memory : MemoryReader) (args : KeccakArgs) :
    (acceleratorInputFromArgs memory args).bytes.length =
      EvmAsm.Evm64.KeccakArgs.inputSizeNat args := by
  simp [acceleratorInputFromArgs, keccakInputBytesFromMemory_length]


-- @@ L84-84 verbatim
end KeccakInputBridge


-- @@ L86-86 verbatim
end EvmAsm.EL
