/-
  EvmAsm.Evm64.StorageAccess

  Pure storage access-list helpers for issue #119.
-/

module

public import EvmAsm.Evm64.Environment
public import EvmAsm.Evm64.StorageGas


-- @@ L12-12 verbatim
@[expose] public section


-- @@ L14-14 verbatim
namespace EvmAsm.Evm64

-- @@ L15-15 verbatim
namespace StorageAccess


-- @@ L17-21 verbatim
/-- Storage key touched by EIP-2929 cold/warm accounting. -/
structure StorageAccessKey where
  address : Address
  slot : EvmWord
  deriving DecidableEq, Repr


-- @@ L23-24 verbatim
/-- Pure access-list model for storage keys already warmed in this transaction. -/
abbrev StorageAccessList := List StorageAccessKey


-- @@ L26-28 verbatim
/-- Whether a storage key is already warm. -/
def isWarm (accesses : StorageAccessList) (key : StorageAccessKey) : Bool :=
  accesses.contains key


-- @@ L30-32 verbatim
/-- Add a storage key to the warm set for subsequent accesses. -/
def warmKey (accesses : StorageAccessList) (key : StorageAccessKey) : StorageAccessList :=
  if isWarm accesses key then accesses else key :: accesses


-- @@ L34-37 verbatim
/-- Cold/warm status for the next access to `key`. -/
def accessStatus (accesses : StorageAccessList) (key : StorageAccessKey) :
    StorageGas.StorageAccessStatus :=
  if isWarm accesses key then .warm else .cold


-- @@ L39-40 verbatim
@[simp] theorem isWarm_nil (key : StorageAccessKey) :
    isWarm [] key = false := rfl


-- @@ L42-44 verbatim
@[simp] theorem isWarm_cons_self (key : StorageAccessKey) (accesses : StorageAccessList) :
    isWarm (key :: accesses) key = true := by
  simp [isWarm]


-- @@ L46-48 verbatim
theorem warmKey_warms (accesses : StorageAccessList) (key : StorageAccessKey) :
    isWarm (warmKey accesses key) key = true := by
  cases h_warm : isWarm accesses key <;> simp [warmKey, h_warm]


-- @@ L50-53 verbatim
theorem warmKey_of_warm {accesses : StorageAccessList} {key : StorageAccessKey}
    (h_warm : isWarm accesses key = true) :
    warmKey accesses key = accesses := by
  simp [warmKey, h_warm]


-- @@ L55-58 verbatim
theorem accessStatus_of_warm {accesses : StorageAccessList} {key : StorageAccessKey}
    (h_warm : isWarm accesses key = true) :
    accessStatus accesses key = .warm := by
  simp [accessStatus, h_warm]


-- @@ L60-63 verbatim
theorem accessStatus_of_cold {accesses : StorageAccessList} {key : StorageAccessKey}
    (h_cold : isWarm accesses key = false) :
    accessStatus accesses key = .cold := by
  simp [accessStatus, h_cold]


-- @@ L65-67 verbatim
@[simp] theorem accessStatus_nil (key : StorageAccessKey) :
    accessStatus [] key = .cold := by
  simp [accessStatus, isWarm]


-- @@ L69-71 verbatim
theorem accessStatus_after_warmKey (accesses : StorageAccessList) (key : StorageAccessKey) :
    accessStatus (warmKey accesses key) key = .warm := by
  exact accessStatus_of_warm (warmKey_warms accesses key)


-- @@ L73-75 verbatim
/-- Dynamic SLOAD gas for a key under the current access list. -/
def sloadDynamicCostForKey (accesses : StorageAccessList) (key : StorageAccessKey) : Nat :=
  StorageGas.sloadDynamicCost (accessStatus accesses key)


-- @@ L77-80 verbatim
theorem sloadDynamicCostForKey_of_warm {accesses : StorageAccessList} {key : StorageAccessKey}
    (h_warm : isWarm accesses key = true) :
    sloadDynamicCostForKey accesses key = StorageGas.warmStorageReadCost := by
  simp [sloadDynamicCostForKey, accessStatus_of_warm h_warm]


-- @@ L82-85 verbatim
theorem sloadDynamicCostForKey_of_cold {accesses : StorageAccessList} {key : StorageAccessKey}
    (h_cold : isWarm accesses key = false) :
    sloadDynamicCostForKey accesses key = StorageGas.coldSloadCost := by
  simp [sloadDynamicCostForKey, accessStatus_of_cold h_cold]


-- @@ L87-89 verbatim
@[simp] theorem sloadDynamicCostForKey_nil (key : StorageAccessKey) :
    sloadDynamicCostForKey [] key = StorageGas.coldSloadCost := by
  simp [sloadDynamicCostForKey]


-- @@ L91-95 verbatim
theorem sloadDynamicCostForKey_after_warmKey
    (accesses : StorageAccessList) (key : StorageAccessKey) :
    sloadDynamicCostForKey (warmKey accesses key) key =
      StorageGas.warmStorageReadCost := by
  simp [sloadDynamicCostForKey, accessStatus_after_warmKey]


-- @@ L97-100 verbatim
/-- Dynamic SSTORE gas for a key under the current access list. -/
def sstoreDynamicCostForKey
    (accesses : StorageAccessList) (key : StorageAccessKey) (current new : EvmWord) : Nat :=
  StorageGas.sstoreDynamicCost (accessStatus accesses key) current new


-- @@ L102-108 verbatim
theorem sstoreDynamicCostForKey_of_warm
    {accesses : StorageAccessList} {key : StorageAccessKey} {current new : EvmWord}
    (h_warm : isWarm accesses key = true) :
    sstoreDynamicCostForKey accesses key current new =
      StorageGas.sstoreWriteCost current new := by
  simp [sstoreDynamicCostForKey, accessStatus_of_warm h_warm,
    StorageGas.sstoreDynamicCost_warm]


-- @@ L110-116 verbatim
theorem sstoreDynamicCostForKey_of_cold
    {accesses : StorageAccessList} {key : StorageAccessKey} {current new : EvmWord}
    (h_cold : isWarm accesses key = false) :
    sstoreDynamicCostForKey accesses key current new =
      StorageGas.coldSloadCost + StorageGas.sstoreWriteCost current new := by
  simp [sstoreDynamicCostForKey, accessStatus_of_cold h_cold,
    StorageGas.sstoreDynamicCost_cold]


-- @@ L118-122 verbatim
@[simp] theorem sstoreDynamicCostForKey_nil
    (key : StorageAccessKey) (current new : EvmWord) :
    sstoreDynamicCostForKey [] key current new =
      StorageGas.coldSloadCost + StorageGas.sstoreWriteCost current new := by
  simp [sstoreDynamicCostForKey, StorageGas.sstoreDynamicCost_cold]


-- @@ L124-129 verbatim
theorem sstoreDynamicCostForKey_after_warmKey
    (accesses : StorageAccessList) (key : StorageAccessKey) (current new : EvmWord) :
    sstoreDynamicCostForKey (warmKey accesses key) key current new =
      StorageGas.sstoreWriteCost current new := by
  simp [sstoreDynamicCostForKey, accessStatus_after_warmKey,
    StorageGas.sstoreDynamicCost_warm]


-- @@ L131-131 verbatim
end StorageAccess

-- @@ L132-132 verbatim
end EvmAsm.Evm64
