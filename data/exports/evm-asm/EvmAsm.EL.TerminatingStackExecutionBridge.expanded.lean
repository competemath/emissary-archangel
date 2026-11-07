/-
  EvmAsm.EL.TerminatingStackExecutionBridge

  Pure stack-to-result bridge for terminating opcodes (GH #113).
-/

module

public import EvmAsm.Evm64.TerminatingArgsStackDecode
public import EvmAsm.EL.TerminatingDataMemory


-- @@ L12-12 verbatim
@[expose] public section


-- @@ L14-14 verbatim
namespace EvmAsm.EL


-- @@ L16-16 verbatim
namespace TerminatingStackExecutionBridge


-- @@ L18-18 verbatim
abbrev EvmWord := EvmAsm.Evm64.EvmWord

-- @@ L19-19 verbatim
abbrev TerminatingKind := EvmAsm.Evm64.TerminatingArgs.Kind

-- @@ L20-20 verbatim
abbrev TerminatingArgs := EvmAsm.Evm64.TerminatingArgs.Args

-- @@ L21-21 verbatim
abbrev MemoryReader := TerminatingDataMemory.MemoryReader


-- @@ L23-25 verbatim
/-- Runtime state visible to the pure terminating-opcode stack bridge. -/
structure TerminatingStackState where
  stack : List EvmWord


-- @@ L27-34 verbatim
def stackRestAfterTerminating? :
    TerminatingKind -> List EvmWord -> Option (List EvmWord)
  | .stop, stack => some stack
  | .return_, _offset :: _size :: rest => some rest
  | .revert, _offset :: _size :: rest => some rest
  | .invalid, stack => some stack
  | .selfdestruct, _beneficiary :: rest => some rest
  | _, _ => none


-- @@ L36-45 verbatim
def argsFromStack? : TerminatingKind -> List EvmWord -> Option TerminatingArgs
  | .stop, _ => some (EvmAsm.Evm64.TerminatingArgs.returnArgs 0 0)
  | .return_, stack =>
      EvmAsm.Evm64.TerminatingArgsStackDecode.decodeReturnStack? stack
  | .revert, stack =>
      EvmAsm.Evm64.TerminatingArgsStackDecode.decodeRevertStack? stack
  | .invalid, _ => some (EvmAsm.Evm64.TerminatingArgs.returnArgs 0 0)
  | .selfdestruct, stack =>
      (EvmAsm.Evm64.TerminatingArgsStackDecode.decodeSelfdestructStack? stack).map
        (fun _beneficiary => EvmAsm.Evm64.TerminatingArgs.returnArgs 0 0)


-- @@ L47-48 verbatim
theorem stackRestAfterTerminating?_stop (stack : List EvmWord) :
    stackRestAfterTerminating? .stop stack = some stack := rfl


-- @@ L50-53 verbatim
theorem stackRestAfterTerminating?_return
    (offset size : EvmWord) (rest : List EvmWord) :
    stackRestAfterTerminating? .return_ (offset :: size :: rest) =
      some rest := rfl


-- @@ L55-58 verbatim
theorem stackRestAfterTerminating?_revert
    (offset size : EvmWord) (rest : List EvmWord) :
    stackRestAfterTerminating? .revert (offset :: size :: rest) =
      some rest := rfl


-- @@ L60-61 verbatim
theorem stackRestAfterTerminating?_invalid (stack : List EvmWord) :
    stackRestAfterTerminating? .invalid stack = some stack := rfl


-- @@ L63-66 verbatim
theorem stackRestAfterTerminating?_selfdestruct
    (beneficiary : EvmWord) (rest : List EvmWord) :
    stackRestAfterTerminating? .selfdestruct (beneficiary :: rest) =
      some rest := rfl


-- @@ L68-69 verbatim
theorem stackRestAfterTerminating?_return_none_of_empty :
    stackRestAfterTerminating? .return_ [] = none := rfl


-- @@ L71-73 verbatim
theorem stackRestAfterTerminating?_return_none_of_one
    (offset : EvmWord) :
    stackRestAfterTerminating? .return_ [offset] = none := rfl


-- @@ L75-76 verbatim
theorem stackRestAfterTerminating?_revert_none_of_empty :
    stackRestAfterTerminating? .revert [] = none := rfl


-- @@ L78-80 verbatim
theorem stackRestAfterTerminating?_revert_none_of_one
    (offset : EvmWord) :
    stackRestAfterTerminating? .revert [offset] = none := rfl


-- @@ L82-83 verbatim
theorem stackRestAfterTerminating?_selfdestruct_none_of_empty :
    stackRestAfterTerminating? .selfdestruct [] = none := rfl


-- @@ L85-88 verbatim
theorem argsFromStack?_return
    (offset size : EvmWord) (rest : List EvmWord) :
    argsFromStack? .return_ (offset :: size :: rest) =
      some (EvmAsm.Evm64.TerminatingArgs.returnArgs offset size) := rfl


-- @@ L90-93 verbatim
theorem argsFromStack?_revert
    (offset size : EvmWord) (rest : List EvmWord) :
    argsFromStack? .revert (offset :: size :: rest) =
      some (EvmAsm.Evm64.TerminatingArgs.revertArgs offset size) := rfl


-- @@ L95-98 verbatim
theorem argsFromStack?_selfdestruct
    (beneficiary : EvmWord) (rest : List EvmWord) :
    argsFromStack? .selfdestruct (beneficiary :: rest) =
      some (EvmAsm.Evm64.TerminatingArgs.returnArgs 0 0) := rfl


-- @@ L100-101 verbatim
theorem argsFromStack?_return_none_of_empty :
    argsFromStack? .return_ [] = none := rfl


-- @@ L103-105 verbatim
theorem argsFromStack?_return_none_of_one
    (offset : EvmWord) :
    argsFromStack? .return_ [offset] = none := rfl


-- @@ L107-108 verbatim
theorem argsFromStack?_revert_none_of_empty :
    argsFromStack? .revert [] = none := rfl


-- @@ L110-112 verbatim
theorem argsFromStack?_revert_none_of_one
    (offset : EvmWord) :
    argsFromStack? .revert [offset] = none := rfl


-- @@ L114-115 verbatim
theorem argsFromStack?_selfdestruct_none_of_empty :
    argsFromStack? .selfdestruct [] = none := rfl


-- @@ L117-122 verbatim
def resultStatusForKind : TerminatingKind -> CallStatus
  | .stop => .success
  | .return_ => .success
  | .revert => .revert
  | .invalid => .failure
  | .selfdestruct => .success


-- @@ L124-132 verbatim
def resultOutputForKind
    (kind : TerminatingKind) (readByte : MemoryReader) (args : TerminatingArgs) :
    List Byte :=
  match kind with
  | .stop => []
  | .return_ => TerminatingDataMemory.terminatingDataFromMemory readByte args
  | .revert => TerminatingDataMemory.terminatingDataFromMemory readByte args
  | .invalid => []
  | .selfdestruct => []


-- @@ L134-134 verbatim
end TerminatingStackExecutionBridge


-- @@ L136-136 verbatim
end EvmAsm.EL
