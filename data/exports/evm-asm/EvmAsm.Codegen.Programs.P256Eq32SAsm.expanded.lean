/-
  EvmAsm.Codegen.Programs.P256Eq32SAsm

  Verified SAsm drop-in for `p256_eq32`: reuse the proved 32-byte byte-scan
  body from `secf_eq32`, with the P-256 label/program wrapper.
-/

import EvmAsm.Codegen.Programs.Secp256k1FieldEq32SAsm


-- @@ L10-10 verbatim
namespace EvmAsm.Codegen


-- @@ L12-12 verbatim
open EvmAsm.Rv64

-- @@ L13-13 verbatim
open EvmAsm.Rv64.SAsm


-- @@ L15-15 verbatim
namespace P256Eq32SAsm


-- @@ L17-20 verbatim
/-- The `p256_eq32` body is the same 32-byte byte equality scan as
    `secf_eq32`: inputs at `a0`/`a1`, result in `a0`. -/
def p256Eq32Body (ptr1 ptr2 : Word) (bs1 bs2 : List (BitVec 8)) : Stmt :=
  Secp256k1FieldEq32SAsm.secfEq32Body ptr1 ptr2 bs1 bs2


-- @@ L22-38 verbatim
/-- Verified `Fn`: `x10 := 1` iff the two 32-byte buffers are byte-identical. -/
def p256Eq32Fn (ptr1 ptr2 : Word) (bs1 bs2 : List (BitVec 8)) : Fn where
  name := "p256Eq32"
  region := ⟨ptr1, bs1⟩
  pre := fun rf _ A =>
    rf.get .x10 = ptr1 ∧ rf.get .x11 = ptr2 ∧
    bs1.length = 32 ∧ bs2.length = 32 ∧
    ptr1.toNat + 32 < 2 ^ 64 ∧ ptr2.toNat + 32 < 2 ^ 64 ∧
    (ptr1.toNat + 32 ≤ ptr2.toNat ∨ ptr2.toNat + 32 ≤ ptr1.toNat) ∧
    A = bytesRegion ptr2 bs2
  post := fun rf _ A =>
    (rf.get .x10 =
      if Secp256k1FieldEq32SAsm.firstDiff bs1 bs2 32 = 32 then (1 : Word) else (0 : Word)) ∧
    bs1.length = 32 ∧ bs2.length = 32 ∧
    ptr1.toNat + 32 < 2 ^ 64 ∧ ptr2.toNat + 32 < 2 ^ 64 ∧
    A = bytesRegion ptr2 bs2
  body := p256Eq32Body ptr1 ptr2 bs1 bs2


-- @@ L40-42 verbatim
/-- Re-emitted drop-in: verified single-exit body plus `ret`. -/
def p256Eq32_prog : Program :=
  (p256Eq32Body 0 0 [] []).flatten 0 ++ [Instr.JALR .x0 .x1 (0 : BitVec 12)]


-- @@ L44-45 verbatim
def p256Eq32Function : String :=
  "p256_eq32:\n" ++ emitProgram p256Eq32_prog


-- @@ L47-48 verbatim
theorem p256Eq32Function_eq_prog :
    p256Eq32Function = "p256_eq32:\n" ++ emitProgram p256Eq32_prog := rfl


-- @@ L50-50 verbatim
#guard p256Eq32Function.startsWith "p256_eq32:\n"

-- @@ L51-51 verbatim
#guard p256Eq32_prog.length = 15

-- @@ L52-53 verbatim
#guard (p256Eq32Body 0 0 [] []).flatten 0 =
  (p256Eq32Body 0 0 [] []).flatten 0x80000000


-- @@ L55-60 verbatim
theorem p256Eq32Fn_spec (ptr1 ptr2 : Word) (bs1 bs2 : List (BitVec 8))
    (hwf1 : (Region.mk ptr1 bs1).wf) (hwf2 : (Region.mk ptr2 bs2).wf) (base : Word) :
    (p256Eq32Fn ptr1 ptr2 bs1 bs2).Spec base := by
  -- `Fn.Spec` ignores the `name` field, so the two `Fn` literals have
  -- definitionally equal specs; `exact` closes that at default transparency.
  exact Secp256k1FieldEq32SAsm.secfEq32Fn_spec ptr1 ptr2 bs1 bs2 hwf1 hwf2 base



-- @@ L63-63 verbatim
end P256Eq32SAsm

-- @@ L64-64 verbatim
end EvmAsm.Codegen
