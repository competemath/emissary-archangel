/-
  EvmAsm.Evm64.Xor.Program

  256-bit EVM XOR program definition.
-/

module

public import EvmAsm.Rv64.Program


-- @@ L11-11 verbatim
@[expose] public section


-- @@ L13-13 verbatim
namespace EvmAsm.Evm64


-- @@ L15-15 verbatim
open EvmAsm.Rv64


-- @@ L17-23 verbatim
/-- 256-bit EVM XOR. -/
def evm_xor : Program :=
  LD .x7 .x12 0 ;; LD .x6 .x12 32 ;; single (.XOR .x7 .x7 .x6) ;; SD .x12 .x7 32 ;;
  LD .x7 .x12 8 ;; LD .x6 .x12 40 ;; single (.XOR .x7 .x7 .x6) ;; SD .x12 .x7 40 ;;
  LD .x7 .x12 16 ;; LD .x6 .x12 48 ;; single (.XOR .x7 .x7 .x6) ;; SD .x12 .x7 48 ;;
  LD .x7 .x12 24 ;; LD .x6 .x12 56 ;; single (.XOR .x7 .x7 .x6) ;; SD .x12 .x7 56 ;;
  ADDI .x12 .x12 32


-- @@ L25-25 verbatim
end EvmAsm.Evm64
