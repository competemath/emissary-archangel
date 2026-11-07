/-
  EvmAsm.EL.ModexpResultBridge

  Bridge from the zkVM `zkvm_modexp` accelerator output to the executable
  precompile-result surface (precompile 0x05).

  The accelerator writes exactly `mod_len` bytes to the output buffer.
  The EVM precompile 0x05 returns those bytes verbatim as the result data;
  callers that want a big-endian `EvmWord` projection (e.g. when the result
  is consumed via MLOAD or pushed to the stack) get it via
  `wordFromBigEndianBytes`, which yields `0` on the empty buffer and
  zero-extends short buffers naturally (consistent with
  `Ripemd160ResultBridge.wordFromBigEndianBytes`).
-/

module

public import EvmAsm.EL.KeccakResultBridge
public import EvmAsm.Evm64.Accelerators.Status


-- @@ L21-21 verbatim
@[expose] public section


-- @@ L23-23 verbatim
namespace EvmAsm.EL


-- @@ L25-25 verbatim
namespace ModexpResultBridge


-- @@ L27-27 verbatim
abbrev EvmWord := EvmAsm.Evm64.EvmWord

-- @@ L28-28 verbatim
abbrev ZkvmStatus := EvmAsm.Accelerators.ZkvmStatus


-- @@ L30-35 verbatim
/-- Variable-width output payload for `zkvm_modexp`. The buffer length is
exactly `mod_len`; the bytes are the big-endian-encoded value of
`(base ^ exp) % modulus`. -/
structure AcceleratorOutput where
  bytes : List Byte
  deriving Repr


-- @@ L37-40 verbatim
/-- Full ECALL result: status code plus output buffer contents. -/
structure AcceleratorResult where
  status : ZkvmStatus
  output : AcceleratorOutput


-- @@ L42-45 verbatim
/-- Big-endian byte conversion matching executable-spec `U256.from_be_bytes`,
shared with the Keccak/SHA256/RIPEMD160 result bridges. -/
def wordFromBigEndianBytes (bytes : List Byte) : EvmWord :=
  KeccakResultBridge.wordFromBigEndianBytes bytes


-- @@ L47-57 verbatim
/-- `EvmWord` projection of the accelerator output buffer.

For `bytes.length ≤ 32` the high `(32 - bytes.length)` bytes of the
resulting `EvmWord` are zero, matching the EVM convention of
left-padding short MODEXP results when they are pushed onto the stack.
For longer buffers the encoding follows `RLP.Nat.fromBytesBE` and
truncates modulo `2^256` via `BitVec.ofNat`.

Distinctive token: ModexpResultBridge.stackWordFromAcceleratorOutput. -/
def stackWordFromAcceleratorOutput (output : AcceleratorOutput) : EvmWord :=
  wordFromBigEndianBytes output.bytes


-- @@ L59-60 verbatim
@[simp] theorem wordFromBigEndianBytes_nil :
    wordFromBigEndianBytes [] = 0 := rfl


-- @@ L62-66 verbatim
theorem wordFromBigEndianBytes_cons (byte : Byte) (tail : List Byte) :
    wordFromBigEndianBytes (byte :: tail) =
      BitVec.ofNat 256
        (byte.toNat * 256 ^ tail.length + EvmAsm.EL.RLP.Nat.fromBytesBE tail) := by
  rfl


-- @@ L68-70 verbatim
theorem stackWordFromAcceleratorOutput_eq (output : AcceleratorOutput) :
    stackWordFromAcceleratorOutput output =
      wordFromBigEndianBytes output.bytes := rfl


-- @@ L72-75 verbatim
theorem stackWordFromAcceleratorOutput_nil
    (output : AcceleratorOutput) (h : output.bytes = []) :
    stackWordFromAcceleratorOutput output = 0 := by
  simp [stackWordFromAcceleratorOutput, h]


-- @@ L77-78 verbatim
theorem acceleratorOutput_bytes_length (output : AcceleratorOutput) :
    output.bytes.length = output.bytes.length := rfl


-- @@ L80-81 verbatim
theorem acceleratorResult_status (result : AcceleratorResult) :
    result.status = result.status := rfl


-- @@ L83-84 verbatim
theorem acceleratorResult_output (result : AcceleratorResult) :
    result.output = result.output := rfl


-- @@ L86-86 verbatim
end ModexpResultBridge


-- @@ L88-88 verbatim
end EvmAsm.EL
