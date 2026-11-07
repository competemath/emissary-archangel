/-
  EvmAsm.EL.Secp256r1VerifyResultBridge

  Bridge from the `zkvm_secp256r1_verify` accelerator output to the executable
  precompile-result surface.
-/

module

public import EvmAsm.Evm64.Accelerators.Status


-- @@ L12-12 verbatim
@[expose] public section


-- @@ L14-14 verbatim
namespace EvmAsm.EL


-- @@ L16-16 verbatim
namespace Secp256r1VerifyResultBridge


-- @@ L18-18 verbatim
abbrev ZkvmStatus := EvmAsm.Accelerators.ZkvmStatus


-- @@ L20-23 verbatim
/-- Accelerator output payload for `zkvm_secp256r1_verify`. -/
structure AcceleratorOutput where
  verified : Bool
  deriving Repr


-- @@ L25-28 verbatim
/-- Full ECALL result: status code plus output buffer contents. -/
structure AcceleratorResult where
  status : ZkvmStatus
  output : AcceleratorOutput


-- @@ L30-32 verbatim
/-- EVM precompile success word for a true signature verification. -/
def successWordFromVerified (verified : Bool) : BitVec 256 :=
  if verified then 1 else 0


-- @@ L34-35 verbatim
theorem successWordFromVerified_true :
    successWordFromVerified true = 1 := rfl


-- @@ L37-38 verbatim
theorem successWordFromVerified_false :
    successWordFromVerified false = 0 := rfl


-- @@ L40-41 verbatim
theorem acceleratorResult_status (result : AcceleratorResult) :
    result.status = result.status := rfl


-- @@ L43-44 verbatim
theorem acceleratorResult_output (result : AcceleratorResult) :
    result.output = result.output := rfl


-- @@ L46-47 verbatim
theorem acceleratorOutput_successWord (output : AcceleratorOutput) :
    successWordFromVerified output.verified = if output.verified then 1 else 0 := rfl


-- @@ L49-49 verbatim
end Secp256r1VerifyResultBridge


-- @@ L51-51 verbatim
end EvmAsm.EL
