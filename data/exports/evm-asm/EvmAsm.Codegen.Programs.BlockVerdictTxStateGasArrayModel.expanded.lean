/-
  Shared pure intrinsic-state-gas fact for the surviving
  `tx_intrinsic_state_gas` leaf proof. The retired array replay formerly
  consumed this fact alongside a separate EIP-7702 reconstruction; the live
  inline AccountState path now owns that transaction-boundary accounting.
-/

module

public import EvmAsm.Stateless.SpecRef.Gas
public import EvmAsm.Stateless.SpecRef.Transactions


-- @@ L13-13 verbatim
@[expose] public section


-- @@ L15-15 verbatim
namespace EvmAsm.Codegen.BlockVerdictTxStateGasArrayModel


-- @@ L17-17 verbatim
open EvmAsm.Stateless.SpecRef


-- @@ L19-19 verbatim
/-! ## Constants (re-export for callers) -/


-- @@ L21-22 verbatim
/-- `StateGasCosts.AUTH_BASE` — net-new delegation indicator write. -/
abbrev authBase : Nat := StateGasCosts.AUTH_BASE


-- @@ L24-25 verbatim
/-- `StateGasCosts.NEW_ACCOUNT` — authority leaf materialization. -/
abbrev newAccount : Nat := StateGasCosts.NEW_ACCOUNT


-- @@ L27-27 verbatim
/-! ## Intrinsic state gas (post EIP-2780) -/


-- @@ L29-35 verbatim
/-- Success-path pure intrinsic state gas for an encoded tx.

    Matches SpecRef `calculate_intrinsic_cost(...).state = 0` and the guest
    `tx_intrinsic_state_gas` body (accumulator 0 → `eip8037_tx_state_gas`).
    Parse failures are *not* modeled here — the array prog surfaces them as
    status a0 ∈ {1,2,3} without a success claim on `out[]`. -/
def pureIntrinsicStateGasSuccess : Nat := 0


-- @@ L37-40 verbatim
theorem pureIntrinsicStateGasSuccess_eq_specRef
    (tx : Transaction) (sender : Address) :
    (calculate_intrinsic_cost tx sender).state = pureIntrinsicStateGasSuccess := by
  simp [calculate_intrinsic_cost, pureIntrinsicStateGasSuccess]


-- @@ L42-42 verbatim
end EvmAsm.Codegen.BlockVerdictTxStateGasArrayModel
