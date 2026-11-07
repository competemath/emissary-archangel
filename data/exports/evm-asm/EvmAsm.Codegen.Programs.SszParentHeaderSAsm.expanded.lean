/-
  EvmAsm.Codegen.Programs.SszParentHeaderSAsm

  Verified SAsm port for `eph_u32le`.
-/

import EvmAsm.Codegen.Programs.SszParentHeader
import EvmAsm.Codegen.Programs.SgLoadU32leSAsm


-- @@ L10-10 verbatim
namespace EvmAsm.Codegen


-- @@ L12-12 verbatim
open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Rv64.SAsm.Stmt


-- @@ L14-14 verbatim
namespace SszParentHeaderSAsm


-- @@ L16-16 verbatim
open SgLoadU32leSAsm


-- @@ L18-24 verbatim
/-- Verified port of `eph_u32le`: `a0 := leU32 (bytes at a0) 0`. -/
def ephU32leFn (p : Word) (bs : List (BitVec 8)) : Fn where
  name := "ephU32le"
  region := ⟨p, bs⟩
  pre := fun rf _ _ => rf.get .x10 = p ∧ 4 ≤ bs.length
  post := fun rf _ _ => rf.get .x10 = leU32 bs 0
  body := sgLoadU32leBody


-- @@ L26-28 verbatim
theorem ephU32le_byte_tie :
    (ephU32leFn 0 []).body.flatten 0
      ++ [Instr.JALR .x0 .x1 (0 : BitVec 12)] = ephU32le_prog := rfl


-- @@ L30-30 verbatim
#guard ((ephU32leFn 0 []).body.flatten 0).length = 11


-- @@ L32-38 verbatim
theorem ephU32leFn_spec (p : Word) (bs : List (BitVec 8))
    (hwf : (Region.mk p bs).wf) (base : Word) :
    (ephU32leFn p bs).Spec base := by
  -- The two `Fn` records differ only in `name`, which `Fn.Spec` does not read,
  -- so the statements are definitionally equal; `exact` closes at default
  -- transparency (since v4.31 `simpa … using` closes only at reducible).
  exact sgLoadU32leFn_spec p bs hwf base


-- @@ L40-40 verbatim
end SszParentHeaderSAsm


-- @@ L42-42 verbatim
end EvmAsm.Codegen
