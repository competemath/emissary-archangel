/-
  EvmAsm.Evm64.Push0.Program

  256-bit EVM PUSH0: push 0 onto stack, sp -= 32.
  5 instructions (ADDI + 4 × SD x0).
-/

module

public import EvmAsm.Rv64.Program
public import EvmAsm.Rv64.SepLogic


-- @@ L13-13 verbatim
@[expose] public section


-- @@ L15-15 verbatim
namespace EvmAsm.Evm64


-- @@ L17-17 verbatim
open EvmAsm.Rv64


-- @@ L19-21 verbatim
def evm_push0 : Program :=
  ADDI .x12 .x12 (-32) ;;
  SD .x12 .x0 0 ;; SD .x12 .x0 8 ;; SD .x12 .x0 16 ;; SD .x12 .x0 24


-- @@ L23-24 verbatim
abbrev evm_push0_code (base : Word) : CodeReq :=
  CodeReq.ofProg base evm_push0


-- @@ L26-26 verbatim
end EvmAsm.Evm64
