/-
  Byte-identical SAsm specification of `copy_word_gas`.
-/

import EvmAsm.Codegen.Programs.DynamicOpcodeGas
import EvmAsm.Rv64.SAsm.Tactic


-- @@ L8-8 verbatim
namespace EvmAsm.Codegen


-- @@ L10-10 verbatim
open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Rv64.SAsm.Stmt


-- @@ L12-12 verbatim
namespace CopyWordGasSAsm


-- @@ L14-16 verbatim
/-- RV64 semantics of the Amsterdam per-word copy-gas component.  Arithmetic
    intentionally wraps at 64 bits, exactly like the emitted guest code. -/
def copyWordGas (size : Word) : Word := ((size + 31) >>> 5) * 3


-- @@ L18-28 verbatim
def copyWordGasFn (size : Word) : Fn where
  name := "copyWordGas"
  region := Region.empty
  rw := RwRegion.empty
  pre := fun rf _ A => rf.get .x10 = size ∧ A = empAssertion
  post := fun rf _ A => rf.get .x10 = copyWordGas size ∧ A = empAssertion
  body := .block "copyWordGas"
    [ .ADDI .x5 .x10 (31 : BitVec 12),
      .SRLI .x5 .x5 (5 : BitVec 6),
      .LI .x6 (3 : Word),
      .MUL .x10 .x5 .x6 ]


-- @@ L30-36 verbatim
theorem copyWordGas_byte_tie :
    (copyWordGasFn 0).body.flatten 0 ++
      [Instr.JALR .x0 .x1 (0 : BitVec 12)] = copyWordGas_prog := by
  rfl

#guard (copyWordGasFn 0).body.flatten 0 =
  (copyWordGasFn 0).body.flatten 0x80000000


-- @@ L38-48 verbatim
theorem copyWordGasFn_spec (size base : Word) :
    (copyWordGasFn size).Spec base := by
  vcgen
  case copyWordGas.post =>
    rintro rf ws A ⟨rf0, ws0, hlen, ⟨hx10, hA⟩, rfl, rfl⟩
    simp only [copyWordGasFn, copyWordGas, execBlock_cons, execBlock_nil,
      execInstrRF, aluSem, RegFile.get_set_self, RegFile.get_set_ne,
      ne_eq, reduceCtorEq, not_false_eq_true, hx10]
    constructor
    · congr 1
    · exact hA



-- @@ L51-51 verbatim
end CopyWordGasSAsm

-- @@ L52-52 verbatim
end EvmAsm.Codegen
