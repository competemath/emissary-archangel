/-
  EvmAsm.Evm64.Pop.Spec

  256-bit EVM POP specs.
-/

module

public import EvmAsm.Evm64.Pop.Program
public import EvmAsm.Evm64.Stack
public import EvmAsm.Rv64.SyscallSpecs
public import EvmAsm.Rv64.Tactics.RunBlock


-- @@ L14-14 verbatim
public section


-- @@ L16-16 verbatim
open EvmAsm.Rv64.Tactics


-- @@ L18-18 verbatim
namespace EvmAsm.Evm64


-- @@ L20-20 verbatim
open EvmAsm.Rv64


-- @@ L22-30 verbatim
/-- POP: advances stack pointer by 32 bytes (discards top 256-bit element).
    1 instruction = 4 bytes. -/
theorem evm_pop_spec_within (sp base : Word) :
    cpsTripleWithin 1 base (base + 4) (evm_pop_code base)
      (.x12 ↦ᵣ sp)
      (.x12 ↦ᵣ (sp + 32)) := by
  have h := addi_spec_gen_same_within .x12 sp 32 base (by nofun)
  simp only [signExtend12_32] at h
  runBlock h



-- @@ L33-42 verbatim
/-- POP stack spec: discards top element, rest untouched. -/
theorem evm_pop_stack_spec_within (sp base : Word)
    (a : EvmWord) (rest : List EvmWord) :
    cpsTripleWithin 1 base (base + 4) (evm_pop_code base)
      ((.x12 ↦ᵣ sp) ** evmWordIs sp a ** evmStackIs (sp + 32) rest)
      ((.x12 ↦ᵣ (sp + 32)) ** evmWordIs sp a ** evmStackIs (sp + 32) rest) :=
  cpsTripleWithin_frameR
    (evmWordIs sp a ** evmStackIs (sp + 32) rest)
    (pcFree_sepConj pcFree_evmWordIs pcFree_evmStackIs)
    (evm_pop_spec_within sp base)


-- @@ L44-44 verbatim
end EvmAsm.Evm64
