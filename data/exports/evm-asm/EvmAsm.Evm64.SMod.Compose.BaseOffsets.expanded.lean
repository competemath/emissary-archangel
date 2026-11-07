/-
  EvmAsm.Evm64.SMod.Compose.BaseOffsets

  Shared byte offsets for the concrete SMOD wrapper layout.
-/

module


-- @@ L9-9 verbatim
@[expose] public section

-- @@ L10-10 verbatim
namespace EvmAsm.Evm64.SMod.Compose


-- @@ L12-13 verbatim
/-- Byte offset of the saved-`ra` prologue inside `evm_smod_wrapper`. -/
def saveRaOff : Nat := 0


-- @@ L15-16 verbatim
/-- Byte offset of the dividend sign probe inside `evm_smod_wrapper`. -/
def dividendSignOff : Nat := 4


-- @@ L18-19 verbatim
/-- Byte offset of the dividend-sign preservation instruction. -/
def preserveDividendSignOff : Nat := 12


-- @@ L21-22 verbatim
/-- Byte offset of the divisor sign probe inside `evm_smod_wrapper`. -/
def divisorSignOff : Nat := 16


-- @@ L24-25 verbatim
/-- Byte offset of the in-place dividend absolute-value block. -/
def dividendAbsOff : Nat := 24


-- @@ L27-28 verbatim
/-- Byte offset of the in-place divisor absolute-value block. -/
def divisorAbsOff : Nat := 108


-- @@ L30-31 verbatim
/-- Byte offset of the near call into `evm_mod_callable`. -/
def modCallOff : Nat := 192


-- @@ L33-34 verbatim
/-- Byte offset of the in-place remainder sign-fixup block. -/
def resultSignFixOff : Nat := 196


-- @@ L36-37 verbatim
/-- Byte offset of the saved-`ra` return instruction. -/
def savedRaRetOff : Nat := 280


-- @@ L39-41 verbatim
/-- Byte offset at the end of the SMOD wrapper. The appended unsigned
    modulo callable starts here. -/
def wrapperEndOff : Nat := 284


-- @@ L43-57 verbatim
/-- Bundled byte offsets for the concrete SMOD wrapper layout. -/
theorem smod_wrapper_block_byte_offsets :
    saveRaOff = 0 ∧
    dividendSignOff = 4 ∧
    preserveDividendSignOff = 12 ∧
    divisorSignOff = 16 ∧
    dividendAbsOff = 24 ∧
    divisorAbsOff = 108 ∧
    modCallOff = 192 ∧
    resultSignFixOff = 196 ∧
    savedRaRetOff = 280 ∧
    wrapperEndOff = 284 := by
  unfold saveRaOff dividendSignOff preserveDividendSignOff divisorSignOff dividendAbsOff
    divisorAbsOff modCallOff resultSignFixOff savedRaRetOff wrapperEndOff
  decide


-- @@ L59-72 verbatim
/-- Successive fall-through byte offsets for the concrete SMOD wrapper. -/
theorem smod_wrapper_fallthrough_offsets :
    saveRaOff + 4 = dividendSignOff ∧
    dividendSignOff + 8 = preserveDividendSignOff ∧
    preserveDividendSignOff + 4 = divisorSignOff ∧
    divisorSignOff + 8 = dividendAbsOff ∧
    dividendAbsOff + 84 = divisorAbsOff ∧
    divisorAbsOff + 84 = modCallOff ∧
    modCallOff + 4 = resultSignFixOff ∧
    resultSignFixOff + 84 = savedRaRetOff ∧
    savedRaRetOff + 4 = wrapperEndOff := by
  unfold saveRaOff dividendSignOff preserveDividendSignOff divisorSignOff dividendAbsOff
    divisorAbsOff modCallOff resultSignFixOff savedRaRetOff wrapperEndOff
  decide


-- @@ L74-74 verbatim
end EvmAsm.Evm64.SMod.Compose
