/-
  EvmAsm.Evm64.SDiv.Compose.BzeroFrames

  Named frames used after the SDIV zero-divisor unsigned-DIV callable
  returns.
-/

module

public import EvmAsm.Evm64.DivMod.Compose.Base
public import EvmAsm.Evm64.SDiv.Compose.BaseOffsets
public import EvmAsm.Evm64.Stack


-- @@ L14-14 verbatim
@[expose] public section


-- @@ L16-16 verbatim
namespace EvmAsm.Evm64.SDiv.Compose


-- @@ L18-18 verbatim
open EvmAsm.Rv64.Tactics


-- @@ L20-29 verbatim
/-- Frame left around the result-sign-fix precondition after the SDIV prefix
    and zero-divisor unsigned-DIV callable have run. -/
@[irreducible]
def saveRaDivCallBzeroResultSignFixFrame
    (vRa sp base divisorSign : Word) (dividendAbsWord : EvmWord) : EvmAsm.Rv64.Assertion :=
  EvmAsm.Rv64.regOwn .x2 ** EvmAsm.Rv64.regOwn .x5 ** EvmAsm.Rv64.regOwn .x6 **
  evmWordIs sp dividendAbsWord ** EvmAsm.Evm64.divScratchOwnCallNoX1 sp **
  (.x1 ↦ᵣ ((base + divCallOff) + 4)) **
  (.x9 ↦ᵣ divisorSign) **
  (.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)))


-- @@ L31-40 verbatim
theorem saveRaDivCallBzeroResultSignFixFrame_unfold
    {vRa sp base divisorSign : Word} {dividendAbsWord : EvmWord} :
    saveRaDivCallBzeroResultSignFixFrame vRa sp base divisorSign dividendAbsWord =
      (EvmAsm.Rv64.regOwn .x2 ** EvmAsm.Rv64.regOwn .x5 ** EvmAsm.Rv64.regOwn .x6 **
       evmWordIs sp dividendAbsWord ** EvmAsm.Evm64.divScratchOwnCallNoX1 sp **
       (.x1 ↦ᵣ ((base + divCallOff) + 4)) **
       (.x9 ↦ᵣ divisorSign) **
       (.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)))) := by
  delta saveRaDivCallBzeroResultSignFixFrame
  rfl


-- @@ L42-49 verbatim
/-- Frame remaining after exposing `x18` for the saved-RA return. -/
@[irreducible]
def saveRaDivCallBzeroSavedRaRetFrame
    (sp base divisorSign : Word) (dividendAbsWord : EvmWord) : EvmAsm.Rv64.Assertion :=
  EvmAsm.Rv64.regOwn .x2 ** EvmAsm.Rv64.regOwn .x5 ** EvmAsm.Rv64.regOwn .x6 **
  evmWordIs sp dividendAbsWord ** EvmAsm.Evm64.divScratchOwnCallNoX1 sp **
  (.x1 ↦ᵣ ((base + divCallOff) + 4)) **
  (.x9 ↦ᵣ divisorSign)


-- @@ L51-59 verbatim
theorem saveRaDivCallBzeroSavedRaRetFrame_unfold
    {sp base divisorSign : Word} {dividendAbsWord : EvmWord} :
    saveRaDivCallBzeroSavedRaRetFrame sp base divisorSign dividendAbsWord =
      (EvmAsm.Rv64.regOwn .x2 ** EvmAsm.Rv64.regOwn .x5 ** EvmAsm.Rv64.regOwn .x6 **
       evmWordIs sp dividendAbsWord ** EvmAsm.Evm64.divScratchOwnCallNoX1 sp **
       (.x1 ↦ᵣ ((base + divCallOff) + 4)) **
       (.x9 ↦ᵣ divisorSign)) := by
  delta saveRaDivCallBzeroSavedRaRetFrame
  rfl


-- @@ L61-70 verbatim
/-- Expose the saved return address atom from the bzero result-sign-fix
    frame, leaving the rest as an explicit return frame. -/
theorem saveRaDivCallBzeroResultSignFixFrame_to_savedRaRet
    {vRa sp base divisorSign : Word} {dividendAbsWord : EvmWord} :
    saveRaDivCallBzeroResultSignFixFrame vRa sp base divisorSign dividendAbsWord =
      ((.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12))) **
       saveRaDivCallBzeroSavedRaRetFrame sp base divisorSign dividendAbsWord) := by
  rw [saveRaDivCallBzeroResultSignFixFrame_unfold,
    saveRaDivCallBzeroSavedRaRetFrame_unfold]
  xperm


-- @@ L72-81 verbatim
/-- Exact-path result-sign-fix frame. It intentionally omits `x9`: nonzero
    unsigned DIV uses `x9` as its loop counter, so SDIV cannot retain the
    divisor sign there across the callable. -/
@[irreducible]
def saveRaDivCallResultSignFixFrameNoX9
    (vRa sp base : Word) (dividendAbsWord : EvmWord) : EvmAsm.Rv64.Assertion :=
  EvmAsm.Rv64.regOwn .x2 ** EvmAsm.Rv64.regOwn .x5 ** EvmAsm.Rv64.regOwn .x6 **
  evmWordIs sp dividendAbsWord ** EvmAsm.Evm64.divScratchOwnCallNoX1 sp **
  (.x1 ↦ᵣ ((base + divCallOff) + 4)) **
  (.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)))


-- @@ L83-91 verbatim
theorem saveRaDivCallResultSignFixFrameNoX9_unfold
    {vRa sp base : Word} {dividendAbsWord : EvmWord} :
    saveRaDivCallResultSignFixFrameNoX9 vRa sp base dividendAbsWord =
      (EvmAsm.Rv64.regOwn .x2 ** EvmAsm.Rv64.regOwn .x5 ** EvmAsm.Rv64.regOwn .x6 **
       evmWordIs sp dividendAbsWord ** EvmAsm.Evm64.divScratchOwnCallNoX1 sp **
       (.x1 ↦ᵣ ((base + divCallOff) + 4)) **
       (.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)))) := by
  delta saveRaDivCallResultSignFixFrameNoX9
  rfl


-- @@ L93-100 verbatim
/-- Exact-path saved-RA return frame after exposing `x18`; intentionally omits
    `x9` for the same reason as `saveRaDivCallResultSignFixFrameNoX9`. -/
@[irreducible]
def saveRaDivCallSavedRaRetFrameNoX9
    (sp base : Word) (dividendAbsWord : EvmWord) : EvmAsm.Rv64.Assertion :=
  EvmAsm.Rv64.regOwn .x2 ** EvmAsm.Rv64.regOwn .x5 ** EvmAsm.Rv64.regOwn .x6 **
  evmWordIs sp dividendAbsWord ** EvmAsm.Evm64.divScratchOwnCallNoX1 sp **
  (.x1 ↦ᵣ ((base + divCallOff) + 4))


-- @@ L102-109 verbatim
theorem saveRaDivCallSavedRaRetFrameNoX9_unfold
    {sp base : Word} {dividendAbsWord : EvmWord} :
    saveRaDivCallSavedRaRetFrameNoX9 sp base dividendAbsWord =
      (EvmAsm.Rv64.regOwn .x2 ** EvmAsm.Rv64.regOwn .x5 ** EvmAsm.Rv64.regOwn .x6 **
       evmWordIs sp dividendAbsWord ** EvmAsm.Evm64.divScratchOwnCallNoX1 sp **
       (.x1 ↦ᵣ ((base + divCallOff) + 4))) := by
  delta saveRaDivCallSavedRaRetFrameNoX9
  rfl


-- @@ L111-118 verbatim
theorem saveRaDivCallResultSignFixFrameNoX9_to_savedRaRet
    {vRa sp base : Word} {dividendAbsWord : EvmWord} :
    saveRaDivCallResultSignFixFrameNoX9 vRa sp base dividendAbsWord =
      ((.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12))) **
       saveRaDivCallSavedRaRetFrameNoX9 sp base dividendAbsWord) := by
  rw [saveRaDivCallResultSignFixFrameNoX9_unfold,
    saveRaDivCallSavedRaRetFrameNoX9_unfold]
  xperm


-- @@ L120-120 verbatim
end EvmAsm.Evm64.SDiv.Compose
