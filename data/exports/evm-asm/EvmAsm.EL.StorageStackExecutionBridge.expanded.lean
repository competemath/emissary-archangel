/-
  EvmAsm.EL.StorageStackExecutionBridge

  Pure stack-to-ECALL execution bridge for SLOAD/SSTORE (GH #110).
-/

module

public import EvmAsm.Evm64.StorageAccess
public import EvmAsm.Evm64.StorageArgs


-- @@ L12-12 verbatim
@[expose] public section


-- @@ L14-14 verbatim
namespace EvmAsm.EL


-- @@ L16-16 verbatim
namespace StorageStackExecutionBridge


-- @@ L18-18 verbatim
abbrev EvmWord := EvmAsm.Evm64.EvmWord

-- @@ L19-19 verbatim
abbrev StorageKind := EvmAsm.Evm64.StorageArgs.Kind

-- @@ L20-20 verbatim
abbrev StorageAccessList := EvmAsm.Evm64.StorageAccess.StorageAccessList


-- @@ L22-24 verbatim
/-- Runtime state visible to the pure storage stack bridge. -/
structure StorageStackState where
  stack : List EvmWord


-- @@ L26-35 verbatim
def stackRestAfterStorage? (kind : StorageKind) :
    List EvmWord -> Option (List EvmWord)
  | _slot :: rest =>
      match kind with
      | .sload => some rest
      | .sstore =>
          match rest with
          | _value :: rest => some rest
          | _ => none
  | _ => none


-- @@ L37-39 verbatim
theorem stackRestAfterStorage?_sload
    (slot : EvmWord) (rest : List EvmWord) :
    stackRestAfterStorage? .sload (slot :: rest) = some rest := rfl


-- @@ L41-43 verbatim
theorem stackRestAfterStorage?_sstore
    (slot value : EvmWord) (rest : List EvmWord) :
    stackRestAfterStorage? .sstore (slot :: value :: rest) = some rest := rfl


-- @@ L45-46 verbatim
@[simp] theorem stackRestAfterStorage?_nil (kind : StorageKind) :
    stackRestAfterStorage? kind [] = none := rfl


-- @@ L48-49 verbatim
theorem stackRestAfterStorage?_sload_none_of_empty :
    stackRestAfterStorage? .sload [] = none := rfl


-- @@ L51-52 verbatim
theorem stackRestAfterStorage?_sstore_none_of_empty :
    stackRestAfterStorage? .sstore [] = none := rfl


-- @@ L54-56 verbatim
theorem stackRestAfterStorage?_sstore_none_of_one
    (slot : EvmWord) :
    stackRestAfterStorage? .sstore [slot] = none := rfl


-- @@ L58-58 verbatim
end StorageStackExecutionBridge


-- @@ L60-60 verbatim
end EvmAsm.EL
