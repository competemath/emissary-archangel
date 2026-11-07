import EvmAsm.Codegen.Programs.HeaderValidateExcessBlobGasSpec


-- @@ L3-3 verbatim
namespace EvmAsm.Codegen.ValidateHeaderGasCorrespondence


-- @@ L5-9 verbatim
/-- `hslack : listLen + 9 ≤ bytes.length` at the `H+176` call site instantiates to
    `headerLen + 9 ≤ headerLen` (see issue #13234), which is false for every `headerLen`. -/
theorem extra_data_hslack_unsat : ∀ (headerLen : Nat), ¬ (headerLen + 9 ≤ headerLen) := by
  intro headerLen
  omega


-- @@ L11-11 verbatim
end EvmAsm.Codegen.ValidateHeaderGasCorrespondence
