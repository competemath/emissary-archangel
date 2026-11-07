/-
  EvmAsm.Evm64.SDiv.Compose.BaseOffsets

  Shared byte offsets for the concrete SDIV wrapper layout.
-/

module


-- @@ L9-9 verbatim
@[expose] public section

-- @@ L10-10 verbatim
namespace EvmAsm.Evm64.SDiv.Compose


-- @@ L12-13 verbatim
/-- Byte offset of the saved-`ra` prologue inside `evm_sdiv_wrapper`. -/
def saveRaOff : Nat := 0


-- @@ L15-16 verbatim
/-- Byte offset of the dividend sign probe inside `evm_sdiv_wrapper`. -/
def dividendSignOff : Nat := 4


-- @@ L18-19 verbatim
/-- Byte offset of the divisor sign probe inside `evm_sdiv_wrapper`. -/
def divisorSignOff : Nat := 12


-- @@ L21-22 verbatim
/-- Byte offset of the in-place dividend absolute-value block. -/
def dividendAbsOff : Nat := 20


-- @@ L24-25 verbatim
/-- Byte offset of the in-place divisor absolute-value block. -/
def divisorAbsOff : Nat := 104


-- @@ L27-28 verbatim
/-- Byte offset of the sign-xor instruction selecting result negation. -/
def signXorOff : Nat := 188


-- @@ L30-31 verbatim
/-- Byte offset of the near call into `evm_div_callable`. -/
def divCallOff : Nat := 192


-- @@ L33-34 verbatim
/-- Byte offset of the in-place quotient sign-fixup block. -/
def resultSignFixOff : Nat := 196


-- @@ L36-37 verbatim
/-- Byte offset of the saved-`ra` return instruction. -/
def savedRaRetOff : Nat := 280


-- @@ L39-41 verbatim
/-- Byte offset at the end of the SDIV wrapper. The appended unsigned
    divider callable starts here. -/
def wrapperEndOff : Nat := 284


-- @@ L43-57 verbatim
/-- Bundled byte offsets for the concrete SDIV wrapper layout. -/
theorem sdiv_wrapper_block_byte_offsets :
    saveRaOff = 0 ∧
    dividendSignOff = 4 ∧
    divisorSignOff = 12 ∧
    dividendAbsOff = 20 ∧
    divisorAbsOff = 104 ∧
    signXorOff = 188 ∧
    divCallOff = 192 ∧
    resultSignFixOff = 196 ∧
    savedRaRetOff = 280 ∧
    wrapperEndOff = 284 := by
  unfold saveRaOff dividendSignOff divisorSignOff dividendAbsOff divisorAbsOff
    signXorOff divCallOff resultSignFixOff savedRaRetOff wrapperEndOff
  decide


-- @@ L59-72 verbatim
/-- Successive fall-through byte offsets for the concrete SDIV wrapper. -/
theorem sdiv_wrapper_fallthrough_offsets :
    saveRaOff + 4 = dividendSignOff ∧
    dividendSignOff + 8 = divisorSignOff ∧
    divisorSignOff + 8 = dividendAbsOff ∧
    dividendAbsOff + 84 = divisorAbsOff ∧
    divisorAbsOff + 84 = signXorOff ∧
    signXorOff + 4 = divCallOff ∧
    divCallOff + 4 = resultSignFixOff ∧
    resultSignFixOff + 84 = savedRaRetOff ∧
    savedRaRetOff + 4 = wrapperEndOff := by
  unfold saveRaOff dividendSignOff divisorSignOff dividendAbsOff divisorAbsOff
    signXorOff divCallOff resultSignFixOff savedRaRetOff wrapperEndOff
  decide


-- @@ L74-74 verbatim
end EvmAsm.Evm64.SDiv.Compose
