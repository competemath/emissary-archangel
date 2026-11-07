/-
  EvmAsm.Evm64.Pop.Program

  256-bit EVM POP: discard top of stack, sp += 32.
  1 instruction (ADDI x12 x12 32).
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


-- @@ L19-19 verbatim
def evm_pop : Program := ADDI .x12 .x12 32


-- @@ L21-22 verbatim
abbrev evm_pop_code (base : Word) : CodeReq :=
  CodeReq.ofProg base evm_pop


-- @@ L24-24 verbatim
end EvmAsm.Evm64
