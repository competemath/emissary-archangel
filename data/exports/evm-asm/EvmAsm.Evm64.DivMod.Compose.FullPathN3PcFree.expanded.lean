module

public import EvmAsm.Evm64.DivMod.Compose.FullPathN3LoopUnified


-- @@ L5-5 verbatim
public section


-- @@ L7-7 verbatim
namespace EvmAsm.Evm64


-- @@ L9-9 verbatim
open EvmAsm.Rv64


-- @@ L11-16 verbatim
theorem fullDivN3ScratchNoX1_pcFree (bltu_1 bltu_0 : Bool)
    (sp base a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratch_un0 : Word) :
    (fullDivN3ScratchNoX1 bltu_1 bltu_0 sp base
      a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratch_un0).pcFree := by
  delta fullDivN3ScratchNoX1
  pcFree


-- @@ L18-24 verbatim
instance pcFreeInst_fullDivN3ScratchNoX1 (bltu_1 bltu_0 : Bool)
    (sp base a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratch_un0 : Word) :
    Assertion.PCFree
      (fullDivN3ScratchNoX1 bltu_1 bltu_0 sp base
        a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratch_un0) :=
  ⟨fullDivN3ScratchNoX1_pcFree bltu_1 bltu_0 sp base
    a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratch_un0⟩


-- @@ L26-31 verbatim
theorem fullDivN3FrameNoX1_pcFree (bltu_1 bltu_0 : Bool)
    (sp base a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratch_un0 : Word) :
    (fullDivN3FrameNoX1 bltu_1 bltu_0 sp base
      a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratch_un0).pcFree := by
  delta fullDivN3FrameNoX1
  pcFree


-- @@ L33-39 verbatim
instance pcFreeInst_fullDivN3FrameNoX1 (bltu_1 bltu_0 : Bool)
    (sp base a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratch_un0 : Word) :
    Assertion.PCFree
      (fullDivN3FrameNoX1 bltu_1 bltu_0 sp base
        a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratch_un0) :=
  ⟨fullDivN3FrameNoX1_pcFree bltu_1 bltu_0 sp base
    a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratch_un0⟩


-- @@ L41-46 verbatim
theorem fullDivN3UnifiedPostNoX1_pcFree (bltu_1 bltu_0 : Bool)
    (sp base a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratch_un0 : Word) :
    (fullDivN3UnifiedPostNoX1 bltu_1 bltu_0 sp base
      a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratch_un0).pcFree := by
  delta fullDivN3UnifiedPostNoX1
  pcFree


-- @@ L48-54 verbatim
instance pcFreeInst_fullDivN3UnifiedPostNoX1 (bltu_1 bltu_0 : Bool)
    (sp base a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratch_un0 : Word) :
    Assertion.PCFree
      (fullDivN3UnifiedPostNoX1 bltu_1 bltu_0 sp base
        a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratch_un0) :=
  ⟨fullDivN3UnifiedPostNoX1_pcFree bltu_1 bltu_0 sp base
    a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratch_un0⟩


-- @@ L56-56 verbatim
end EvmAsm.Evm64
