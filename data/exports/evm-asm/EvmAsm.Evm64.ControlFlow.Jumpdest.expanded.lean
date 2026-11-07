/-
  EvmAsm.Evm64.ControlFlow.Jumpdest

  Program and stack-level specification for the EVM `JUMPDEST` opcode (0x5b).

  JUMPDEST is a position marker: executing it has NO machine-state effect —
  it pops nothing, pushes nothing, and touches no memory. Its two real roles
  live elsewhere, each already handled:
  * its gas charge (JUMPDEST_GAS = 1) is charged by the dispatcher's
    per-opcode gas loop, like every opcode's static cost;
  * its role as a *valid jump target* is enforced by the JUMP/JUMPI handlers
    (the taken path loads `code[dest]` and the handler tail routes any
    non-0x5b byte to `.exit_invalid`).

  The verified program is therefore the EMPTY program, and the witness triple
  is the zero-step identity: the EVM stack (and everything else, by the frame
  rule) is unchanged. This is the opcode's full effect, stated honestly —
  there is nothing else to prove at the handler level.
-/

module

public import EvmAsm.Rv64.Program
public import EvmAsm.Rv64.CPSSpec
public import EvmAsm.Evm64.Stack


-- @@ L27-27 verbatim
@[expose] public section


-- @@ L29-29 verbatim
namespace EvmAsm.Evm64

-- @@ L30-30 verbatim
namespace ControlFlow


-- @@ L32-32 verbatim
open EvmAsm.Rv64


-- @@ L34-37 verbatim
/-- The `JUMPDEST` program: the empty instruction list. Executing a JUMPDEST
    does nothing at the machine level (the dispatcher tail advances the EVM
    PC past it, exactly as for every 1-byte opcode). -/
def evm_jumpdest : Program := []


-- @@ L39-41 verbatim
/-- `CodeReq` for `evm_jumpdest` at `base` — definitionally `CodeReq.empty`. -/
abbrev evm_jumpdest_code (base : Word) : CodeReq :=
  CodeReq.ofProg base evm_jumpdest


-- @@ L43-43 verbatim
theorem evm_jumpdest_length : evm_jumpdest.length = 0 := rfl


-- @@ L45-54 verbatim
/-- JUMPDEST stack spec: pops nothing, pushes nothing, zero steps — the EVM
    stack is unchanged (and by the frame rule so is everything else). The
    unconditional top-level triple witnessing JUMPDEST `.proven`. -/
theorem evm_jumpdest_stack_spec_within
    (nsp base : Word) (stack : List EvmWord) :
    let code := evm_jumpdest_code base
    cpsTripleWithin 0 base base code
      ((.x12 ↦ᵣ nsp) ** evmStackIs nsp stack)
      ((.x12 ↦ᵣ nsp) ** evmStackIs nsp stack) :=
  cpsTripleWithin_refl (fun _ h => h)


-- @@ L56-56 verbatim
end ControlFlow

-- @@ L57-57 verbatim
end EvmAsm.Evm64
