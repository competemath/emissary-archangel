/-
  EvmAsm.EL.ModexpInputBridge

  Bridge from executable memory to the input payload consumed by the
  `zkvm_modexp` accelerator (precompile 0x05).

  The C interface is

      zkvm_status zkvm_modexp(const uint8_t* base, size_t base_len,
                              const uint8_t* exp, size_t exp_len,
                              const uint8_t* modulus, size_t mod_len,
                              uint8_t* output);

  so the input payload is three independent variable-width byte buffers,
  each read from a contiguous range of executable memory.
-/

module

public import EvmAsm.EL.KeccakInputBridge


-- @@ L22-22 verbatim
@[expose] public section


-- @@ L24-24 verbatim
namespace EvmAsm.EL


-- @@ L26-26 verbatim
namespace ModexpInputBridge


-- @@ L28-29 verbatim
/-- A byte-addressed executable memory reader. -/
abbrev MemoryReader := KeccakInputBridge.MemoryReader


-- @@ L31-38 verbatim
/-- Input payload passed to `zkvm_modexp(base, base_len, exp, exp_len,
modulus, mod_len, output)`. The output buffer is part of the result
bridge; the request only carries the three input buffers. -/
structure AcceleratorInput where
  base    : List Byte
  exp     : List Byte
  modulus : List Byte
  deriving Repr


-- @@ L40-43 verbatim
/-- Executable-spec `memory_read_bytes(memory, start, size)` shape: read
exactly `size` bytes starting at `start`. -/
def memoryReadBytes (memory : MemoryReader) (start size : Nat) : List Byte :=
  KeccakInputBridge.memoryReadBytes memory start size


-- @@ L45-48 verbatim
/-- Distinctive token: ModexpInputBridge.modexpInputBytesFromMemory. -/
def modexpInputBytesFromMemory
    (memory : MemoryReader) (start size : Nat) : List Byte :=
  memoryReadBytes memory start size


-- @@ L50-58 verbatim
/-- Accelerator-call input assembled from three independent byte buffers
read from executable memory. -/
def acceleratorInputFromMemory
    (memory : MemoryReader)
    (baseStart baseLen expStart expLen modStart modLen : Nat) :
    AcceleratorInput :=
  { base    := modexpInputBytesFromMemory memory baseStart baseLen
    exp     := modexpInputBytesFromMemory memory expStart  expLen
    modulus := modexpInputBytesFromMemory memory modStart  modLen }


-- @@ L60-62 verbatim
theorem memoryReadBytes_length (memory : MemoryReader) (start size : Nat) :
    (memoryReadBytes memory start size).length = size := by
  simp [memoryReadBytes, KeccakInputBridge.memoryReadBytes_length]


-- @@ L64-67 verbatim
theorem memoryReadBytes_get?
    (memory : MemoryReader) (start size i : Nat) (h_i : i < size) :
    (memoryReadBytes memory start size)[i]? = some (memory (start + i)) := by
  simp [memoryReadBytes, KeccakInputBridge.memoryReadBytes_get?, h_i]


-- @@ L69-70 verbatim
@[simp] theorem memoryReadBytes_zero (memory : MemoryReader) (start : Nat) :
    memoryReadBytes memory start 0 = [] := rfl


-- @@ L72-75 verbatim
theorem modexpInputBytesFromMemory_length
    (memory : MemoryReader) (start size : Nat) :
    (modexpInputBytesFromMemory memory start size).length = size := by
  simp [modexpInputBytesFromMemory, memoryReadBytes_length]


-- @@ L77-81 verbatim
theorem modexpInputBytesFromMemory_get?
    (memory : MemoryReader) (start size i : Nat) (h_i : i < size) :
    (modexpInputBytesFromMemory memory start size)[i]? =
      some (memory (start + i)) := by
  simp [modexpInputBytesFromMemory, memoryReadBytes_get?, h_i]


-- @@ L83-85 verbatim
@[simp] theorem modexpInputBytesFromMemory_zero_size
    (memory : MemoryReader) (start : Nat) :
    modexpInputBytesFromMemory memory start 0 = [] := rfl


-- @@ L87-92 verbatim
theorem acceleratorInputFromMemory_base
    (memory : MemoryReader)
    (baseStart baseLen expStart expLen modStart modLen : Nat) :
    (acceleratorInputFromMemory memory
        baseStart baseLen expStart expLen modStart modLen).base =
      modexpInputBytesFromMemory memory baseStart baseLen := rfl


-- @@ L94-99 verbatim
theorem acceleratorInputFromMemory_exp
    (memory : MemoryReader)
    (baseStart baseLen expStart expLen modStart modLen : Nat) :
    (acceleratorInputFromMemory memory
        baseStart baseLen expStart expLen modStart modLen).exp =
      modexpInputBytesFromMemory memory expStart expLen := rfl


-- @@ L101-106 verbatim
theorem acceleratorInputFromMemory_modulus
    (memory : MemoryReader)
    (baseStart baseLen expStart expLen modStart modLen : Nat) :
    (acceleratorInputFromMemory memory
        baseStart baseLen expStart expLen modStart modLen).modulus =
      modexpInputBytesFromMemory memory modStart modLen := rfl


-- @@ L108-114 verbatim
theorem acceleratorInputFromMemory_base_length
    (memory : MemoryReader)
    (baseStart baseLen expStart expLen modStart modLen : Nat) :
    (acceleratorInputFromMemory memory
        baseStart baseLen expStart expLen modStart modLen).base.length =
      baseLen := by
  simp [acceleratorInputFromMemory, modexpInputBytesFromMemory_length]


-- @@ L116-122 verbatim
theorem acceleratorInputFromMemory_exp_length
    (memory : MemoryReader)
    (baseStart baseLen expStart expLen modStart modLen : Nat) :
    (acceleratorInputFromMemory memory
        baseStart baseLen expStart expLen modStart modLen).exp.length =
      expLen := by
  simp [acceleratorInputFromMemory, modexpInputBytesFromMemory_length]


-- @@ L124-130 verbatim
theorem acceleratorInputFromMemory_modulus_length
    (memory : MemoryReader)
    (baseStart baseLen expStart expLen modStart modLen : Nat) :
    (acceleratorInputFromMemory memory
        baseStart baseLen expStart expLen modStart modLen).modulus.length =
      modLen := by
  simp [acceleratorInputFromMemory, modexpInputBytesFromMemory_length]


-- @@ L132-132 verbatim
end ModexpInputBridge


-- @@ L134-134 verbatim
end EvmAsm.EL
