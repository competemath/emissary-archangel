/-
  EvmAsm.Evm64.StorageGas

  Pure cold/warm storage access gas helpers for issue #119.
-/

module

public import EvmAsm.Evm64.EvmWord
public import EvmAsm.Evm64.GasCost


-- @@ L12-12 verbatim
@[expose] public section


-- @@ L14-14 verbatim
namespace EvmAsm.Evm64

-- @@ L15-15 verbatim
namespace StorageGas


-- @@ L17-21 verbatim
/-- EIP-2929 storage access status before an SLOAD/SSTORE key access. -/
inductive StorageAccessStatus where
  | cold
  | warm
  deriving DecidableEq, Repr


-- @@ L23-25 verbatim
/-- Current Amsterdam cold SLOAD/storage-key access cost
    (`GasCosts.COLD_STORAGE_ACCESS`). -/
def coldSloadCost : Nat := 3000


-- @@ L27-28 verbatim
/-- Current Amsterdam warm storage read/access cost (`GasCosts.WARM_ACCESS`). -/
def warmStorageReadCost : Nat := 100


-- @@ L30-33 verbatim
/-- Dynamic gas charged for the storage-key access itself. -/
def storageAccessCost : StorageAccessStatus → Nat
  | .cold => coldSloadCost
  | .warm => warmStorageReadCost


-- @@ L35-37 verbatim
/-- Dynamic SLOAD cost is exactly the cold/warm storage-key access cost. -/
def sloadDynamicCost (status : StorageAccessStatus) : Nat :=
  storageAccessCost status


-- @@ L39-40 verbatim
/-- Warm SSTORE no-op cost: writing the same value charges a warm storage read. -/
def sstoreNoopCost : Nat := warmStorageReadCost


-- @@ L42-51 verbatim
/-- Warm SSTORE cost when a zero slot is set to a nonzero value.

The regular component is `GasCosts.STORAGE_WRITE` from
`execution-specs/src/ethereum/forks/amsterdam/vm/gas.py:73-75`; the state
component is `StateGasCosts.STORAGE_SET` from
`execution-specs/src/ethereum/forks/amsterdam/vm/gas.py:40-46`, namely 64
state bytes at 1,530 gas per byte. -/
def sstoreSetCost : GasCost :=
  { regular := 10000
    state := 64 * 1530 }


-- @@ L53-54 verbatim
/-- Warm SSTORE cost when a nonzero slot is written to a different value. -/
def sstoreResetCost : Nat := 10000


-- @@ L56-59 verbatim
/-- EIP-2929 cold-key surcharge for SSTORE. Warm keys have no surcharge. -/
def sstoreColdSurcharge : StorageAccessStatus → Nat
  | .cold => coldSloadCost
  | .warm => 0


-- @@ L61-68 verbatim
/-- Warm-key SSTORE write cost, before any cold-key surcharge or refund logic. -/
def sstoreWriteCost (current new : EvmWord) : Nat :=
  if new = current then
    sstoreNoopCost
  else if current = 0 then
    sstoreSetCost.regular
  else
    sstoreResetCost


-- @@ L70-72 verbatim
/-- Dynamic SSTORE cost surface: cold-key surcharge plus warm write cost. -/
def sstoreDynamicCost (status : StorageAccessStatus) (current new : EvmWord) : Nat :=
  sstoreColdSurcharge status + sstoreWriteCost current new


-- @@ L74-76 verbatim
/-- After any storage-key access, that key is warm for the rest of the transaction. -/
def warmAfterAccess (_status : StorageAccessStatus) : StorageAccessStatus :=
  .warm


-- @@ L78-79 verbatim
@[simp] theorem storageAccessCost_cold :
    storageAccessCost .cold = coldSloadCost := rfl


-- @@ L81-82 verbatim
@[simp] theorem storageAccessCost_warm :
    storageAccessCost .warm = warmStorageReadCost := rfl


-- @@ L84-85 verbatim
@[simp] theorem sloadDynamicCost_cold :
    sloadDynamicCost .cold = coldSloadCost := rfl


-- @@ L87-88 verbatim
@[simp] theorem sloadDynamicCost_warm :
    sloadDynamicCost .warm = warmStorageReadCost := rfl


-- @@ L90-91 verbatim
@[simp] theorem sstoreColdSurcharge_cold :
    sstoreColdSurcharge .cold = coldSloadCost := rfl


-- @@ L93-94 verbatim
@[simp] theorem sstoreColdSurcharge_warm :
    sstoreColdSurcharge .warm = 0 := rfl


-- @@ L96-98 verbatim
theorem sstoreWriteCost_noop (current : EvmWord) :
    sstoreWriteCost current current = sstoreNoopCost := by
  simp [sstoreWriteCost]


-- @@ L100-105 verbatim
theorem sstoreWriteCost_set {new : EvmWord} (h_new : new ≠ 0) :
    sstoreWriteCost 0 new = sstoreSetCost.regular := by
  unfold sstoreWriteCost
  split
  · contradiction
  · simp


-- @@ L107-113 verbatim
theorem sstoreWriteCost_reset {current new : EvmWord}
    (h_current : current ≠ 0) (h_ne : new ≠ current) :
    sstoreWriteCost current new = sstoreResetCost := by
  unfold sstoreWriteCost
  split
  · contradiction
  · rfl


-- @@ L115-117 verbatim
theorem sstoreDynamicCost_warm (current new : EvmWord) :
    sstoreDynamicCost .warm current new = sstoreWriteCost current new := by
  simp [sstoreDynamicCost]


-- @@ L119-121 verbatim
theorem sstoreDynamicCost_cold (current new : EvmWord) :
    sstoreDynamicCost .cold current new =
      coldSloadCost + sstoreWriteCost current new := rfl


-- @@ L123-124 verbatim
@[simp] theorem warmAfterAccess_cold :
    warmAfterAccess .cold = .warm := rfl


-- @@ L126-127 verbatim
@[simp] theorem warmAfterAccess_warm :
    warmAfterAccess .warm = .warm := rfl


-- @@ L129-131 verbatim
@[simp] theorem warmAfterAccess_eq_warm (status : StorageAccessStatus) :
    warmAfterAccess status = .warm := by
  cases status <;> rfl


-- @@ L133-134 verbatim
theorem storageAccessCost_cold_eq :
    storageAccessCost .cold = 3000 := rfl


-- @@ L136-137 verbatim
theorem storageAccessCost_warm_eq :
    storageAccessCost .warm = 100 := rfl


-- @@ L139-140 verbatim
theorem sloadDynamicCost_cold_eq :
    sloadDynamicCost .cold = 3000 := rfl


-- @@ L142-143 verbatim
theorem sloadDynamicCost_warm_eq :
    sloadDynamicCost .warm = 100 := rfl


-- @@ L145-146 verbatim
theorem sstoreNoopCost_eq :
    sstoreNoopCost = 100 := rfl


-- @@ L148-150 verbatim
theorem sstoreSetCost_components :
    sstoreSetCost.regular = 10000 ∧ sstoreSetCost.state = 97920 := by
  constructor <;> rfl


-- @@ L152-153 verbatim
theorem sstoreResetCost_eq :
    sstoreResetCost = 10000 := rfl


-- @@ L155-155 verbatim
end StorageGas

-- @@ L156-156 verbatim
end EvmAsm.Evm64
