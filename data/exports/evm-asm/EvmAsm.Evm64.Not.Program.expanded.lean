/-
  EvmAsm.Evm64.Not.Program

  256-bit EVM NOT program definition.
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
/-- 256-bit EVM NOT: unary (pop 1, push 1, sp unchanged).
    For each limb: load, XOR with -1 (complement), store back. -/
def evm_not : Program :=
  LD .x7 .x12 0 ;; XORI .x7 .x7 (-1) ;; SD .x12 .x7 0 ;;
  LD .x7 .x12 8 ;; XORI .x7 .x7 (-1) ;; SD .x12 .x7 8 ;;
  LD .x7 .x12 16 ;; XORI .x7 .x7 (-1) ;; SD .x12 .x7 16 ;;
  LD .x7 .x12 24 ;; XORI .x7 .x7 (-1) ;; SD .x12 .x7 24


-- @@ L25-25 verbatim
end EvmAsm.Evm64
