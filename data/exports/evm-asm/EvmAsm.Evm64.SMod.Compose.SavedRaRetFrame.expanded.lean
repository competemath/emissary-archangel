/-
  EvmAsm.Evm64.SMod.Compose.SavedRaRetFrame

  Frame split for exposing the saved return address before the final SMOD
  return instruction.
-/

module

public import EvmAsm.Evm64.SMod.Compose.ModCallResultSignFixPost
public import EvmAsm.Rv64.Tactics.XSimp


-- @@ L13-13 verbatim
@[expose] public section


-- @@ L15-15 verbatim
namespace EvmAsm.Evm64.SMod.Compose


-- @@ L17-17 verbatim
open EvmAsm.Rv64.Tactics


-- @@ L19-30 verbatim
/-- Frame remaining after exposing `x18` for the saved-RA return.
    x9 is `regOwn` since the callable body modifies it (divisorSign is consumed). -/
@[irreducible]
def smodSavedRaRetFrame
    (sp base dividendTop : Word) (dividendAbsWord : EvmWord) :
    EvmAsm.Rv64.Assertion :=
  let dividendSign := smodAbsSign dividendTop
  (.x1 ↦ᵣ ((base + modCallOff) + 4)) **
    EvmAsm.Rv64.regOwn .x9 ** (.x8 ↦ᵣ dividendSign) **
    EvmAsm.Rv64.regOwn .x2 ** EvmAsm.Rv64.regOwn .x5 **
    EvmAsm.Rv64.regOwn .x6 ** evmWordIs sp dividendAbsWord **
    EvmAsm.Evm64.divScratchOwnCallNoX1 sp


-- @@ L32-42 verbatim
theorem smodSavedRaRetFrame_unfold
    {sp base dividendTop : Word} {dividendAbsWord : EvmWord} :
    smodSavedRaRetFrame sp base dividendTop dividendAbsWord =
      (let dividendSign := smodAbsSign dividendTop
       (.x1 ↦ᵣ ((base + modCallOff) + 4)) **
         EvmAsm.Rv64.regOwn .x9 ** (.x8 ↦ᵣ dividendSign) **
         EvmAsm.Rv64.regOwn .x2 ** EvmAsm.Rv64.regOwn .x5 **
         EvmAsm.Rv64.regOwn .x6 ** evmWordIs sp dividendAbsWord **
         EvmAsm.Evm64.divScratchOwnCallNoX1 sp) := by
  delta smodSavedRaRetFrame
  rfl


-- @@ L44-51 verbatim
theorem smodSavedRaRetFrame_pcFree
    {sp base dividendTop : Word} {dividendAbsWord : EvmWord} :
    (smodSavedRaRetFrame sp base dividendTop dividendAbsWord).pcFree := by
  rw [smodSavedRaRetFrame_unfold,
    EvmAsm.Evm64.divScratchOwnCallNoX1_unfold,
    EvmAsm.Evm64.divScratchOwn_unfold]
  dsimp only
  pcFree


-- @@ L53-57 verbatim
instance pcFreeInst_smodSavedRaRetFrame
    (sp base dividendTop : Word) (dividendAbsWord : EvmWord) :
    EvmAsm.Rv64.Assertion.PCFree
      (smodSavedRaRetFrame sp base dividendTop dividendAbsWord) :=
  ⟨smodSavedRaRetFrame_pcFree⟩


-- @@ L59-67 verbatim
/-- Expose the saved return address atom from the SMOD result-sign-fix frame,
    leaving the rest as an explicit return frame. -/
theorem smodModCallResultSignFixFrame_to_savedRaRet
    {vRa sp base dividendTop : Word} {dividendAbsWord : EvmWord} :
    smodModCallResultSignFixFrame vRa sp base dividendTop dividendAbsWord =
      ((.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12))) **
       smodSavedRaRetFrame sp base dividendTop dividendAbsWord) := by
  rw [smodModCallResultSignFixFrame_unfold, smodSavedRaRetFrame_unfold]
  xperm


-- @@ L69-69 verbatim
end EvmAsm.Evm64.SMod.Compose
