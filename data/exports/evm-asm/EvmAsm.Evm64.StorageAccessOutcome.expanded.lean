/-
  EvmAsm.Evm64.StorageAccessOutcome

  Pure SLOAD/SSTORE access outcomes for issue #119.
-/

module

public import EvmAsm.Evm64.StorageAccess


-- @@ L11-11 verbatim
@[expose] public section


-- @@ L13-13 verbatim
namespace EvmAsm.Evm64

-- @@ L14-14 verbatim
namespace StorageAccessOutcome


-- @@ L16-21 verbatim
/-- Dynamic gas and warm-list state produced by one storage-key access. -/
structure Outcome where
  status : StorageGas.StorageAccessStatus
  cost : Nat
  accesses : StorageAccess.StorageAccessList
  deriving Repr


-- @@ L23-28 verbatim
def sloadOutcome
    (accesses : StorageAccess.StorageAccessList) (key : StorageAccess.StorageAccessKey) :
    Outcome :=
  { status := StorageAccess.accessStatus accesses key
    cost := StorageAccess.sloadDynamicCostForKey accesses key
    accesses := StorageAccess.warmKey accesses key }


-- @@ L30-36 verbatim
def sstoreOutcome
    (accesses : StorageAccess.StorageAccessList) (key : StorageAccess.StorageAccessKey)
    (current new : EvmWord) :
    Outcome :=
  { status := StorageAccess.accessStatus accesses key
    cost := StorageAccess.sstoreDynamicCostForKey accesses key current new
    accesses := StorageAccess.warmKey accesses key }


-- @@ L38-40 verbatim
theorem sloadOutcome_status
    (accesses : StorageAccess.StorageAccessList) (key : StorageAccess.StorageAccessKey) :
    (sloadOutcome accesses key).status = StorageAccess.accessStatus accesses key := rfl


-- @@ L42-45 verbatim
theorem sloadOutcome_cost
    (accesses : StorageAccess.StorageAccessList) (key : StorageAccess.StorageAccessKey) :
    (sloadOutcome accesses key).cost =
      StorageAccess.sloadDynamicCostForKey accesses key := rfl


-- @@ L47-50 verbatim
theorem sloadOutcome_warms
    (accesses : StorageAccess.StorageAccessList) (key : StorageAccess.StorageAccessKey) :
    StorageAccess.isWarm (sloadOutcome accesses key).accesses key = true := by
  exact StorageAccess.warmKey_warms accesses key


-- @@ L52-55 verbatim
theorem sstoreOutcome_status
    (accesses : StorageAccess.StorageAccessList) (key : StorageAccess.StorageAccessKey)
    (current new : EvmWord) :
    (sstoreOutcome accesses key current new).status = StorageAccess.accessStatus accesses key := rfl


-- @@ L57-61 verbatim
theorem sstoreOutcome_cost
    (accesses : StorageAccess.StorageAccessList) (key : StorageAccess.StorageAccessKey)
    (current new : EvmWord) :
    (sstoreOutcome accesses key current new).cost =
      StorageAccess.sstoreDynamicCostForKey accesses key current new := rfl


-- @@ L63-67 verbatim
theorem sstoreOutcome_warms
    (accesses : StorageAccess.StorageAccessList) (key : StorageAccess.StorageAccessKey)
    (current new : EvmWord) :
    StorageAccess.isWarm (sstoreOutcome accesses key current new).accesses key = true := by
  exact StorageAccess.warmKey_warms accesses key


-- @@ L69-71 verbatim
theorem sloadOutcome_nil_cost (key : StorageAccess.StorageAccessKey) :
    (sloadOutcome [] key).cost = StorageGas.coldSloadCost := by
  simp [sloadOutcome]


-- @@ L73-77 verbatim
theorem sstoreOutcome_nil_cost
    (key : StorageAccess.StorageAccessKey) (current new : EvmWord) :
    (sstoreOutcome [] key current new).cost =
      StorageGas.coldSloadCost + StorageGas.sstoreWriteCost current new := by
  simp [sstoreOutcome]


-- @@ L79-79 verbatim
end StorageAccessOutcome

-- @@ L80-80 verbatim
end EvmAsm.Evm64
