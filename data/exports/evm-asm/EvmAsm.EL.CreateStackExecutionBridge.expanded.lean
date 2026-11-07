/-
  EvmAsm.EL.CreateStackExecutionBridge

  Pure stack-to-execution bridge for CREATE and CREATE2 (GH #115).
-/

module

public import EvmAsm.Evm64.CreateArgsStackDecode
public import EvmAsm.EL.CreateInitcodeBridge
public import EvmAsm.EL.CreateResultBridge


-- @@ L13-13 verbatim
@[expose] public section


-- @@ L15-15 verbatim
namespace EvmAsm.EL


-- @@ L17-17 verbatim
namespace CreateStackExecutionBridge


-- @@ L19-19 verbatim
abbrev EvmWord := EvmAsm.Evm64.EvmWord

-- @@ L20-20 verbatim
abbrev CreateKind := EvmAsm.Evm64.CreateArgs.Kind

-- @@ L21-21 verbatim
abbrev Decoded := EvmAsm.Evm64.CreateArgsStackDecode.Decoded

-- @@ L22-22 verbatim
abbrev MemoryReader := CreateInitcodeBridge.MemoryReader


-- @@ L24-26 verbatim
/-- Runtime state visible to the pure CREATE stack bridge. -/
structure CreateStackState where
  stack : List EvmWord


-- @@ L28-36 verbatim
def stackRestAfterCreate? (kind : CreateKind) : List EvmWord -> Option (List EvmWord)
  | _value :: _offset :: _size :: rest =>
      match kind with
      | .create => some rest
      | .create2 =>
          match rest with
          | _salt :: rest => some rest
          | _ => none
  | _ => none


-- @@ L38-44 verbatim
def requestFromDecoded
    (creator : Address) (readByte : MemoryReader) (gas : EvmWord) :
    Decoded -> CreateRequest
  | .create args =>
      CreateInitcodeBridge.createRequestFromMemory creator readByte gas args
  | .create2 args =>
      CreateInitcodeBridge.create2RequestFromMemory creator readByte gas args


-- @@ L46-50 verbatim
def requestFromStack? (kind : CreateKind) (creator : Address)
    (readByte : MemoryReader) (gas : EvmWord) (stack : List EvmWord) :
    Option CreateRequest :=
  (EvmAsm.Evm64.CreateArgsStackDecode.decodeCreateStack? kind stack).map
    (requestFromDecoded creator readByte gas)


-- @@ L52-55 verbatim
theorem stackRestAfterCreate?_create
    (value offset size : EvmWord) (rest : List EvmWord) :
    stackRestAfterCreate? .create (value :: offset :: size :: rest) =
      some rest := rfl


-- @@ L57-60 verbatim
theorem stackRestAfterCreate?_create2
    (value offset size salt : EvmWord) (rest : List EvmWord) :
    stackRestAfterCreate? .create2 (value :: offset :: size :: salt :: rest) =
      some rest := rfl


-- @@ L62-63 verbatim
@[simp] theorem stackRestAfterCreate?_nil (kind : CreateKind) :
    stackRestAfterCreate? kind [] = none := rfl


-- @@ L65-67 verbatim
@[simp] theorem stackRestAfterCreate?_singleton
    (kind : CreateKind) (value : EvmWord) :
    stackRestAfterCreate? kind [value] = none := rfl


-- @@ L69-70 verbatim
theorem stackRestAfterCreate?_create_none_of_empty :
    stackRestAfterCreate? .create [] = none := rfl


-- @@ L72-74 verbatim
theorem stackRestAfterCreate?_create_none_of_one
    (value : EvmWord) :
    stackRestAfterCreate? .create [value] = none := rfl


-- @@ L76-78 verbatim
theorem stackRestAfterCreate?_create_none_of_two
    (value offset : EvmWord) :
    stackRestAfterCreate? .create [value, offset] = none := rfl


-- @@ L80-81 verbatim
theorem stackRestAfterCreate?_create2_none_of_empty :
    stackRestAfterCreate? .create2 [] = none := rfl


-- @@ L83-85 verbatim
theorem stackRestAfterCreate?_create2_none_of_one
    (value : EvmWord) :
    stackRestAfterCreate? .create2 [value] = none := rfl


-- @@ L87-89 verbatim
theorem stackRestAfterCreate?_create2_none_of_two
    (value offset : EvmWord) :
    stackRestAfterCreate? .create2 [value, offset] = none := rfl


-- @@ L91-93 verbatim
theorem stackRestAfterCreate?_create2_none_of_three
    (value offset size : EvmWord) :
    stackRestAfterCreate? .create2 [value, offset, size] = none := rfl


-- @@ L95-102 verbatim
theorem requestFromStack?_create
    (creator : Address) (readByte : MemoryReader) (gas : EvmWord)
    (value offset size : EvmWord) (rest : List EvmWord) :
    requestFromStack? .create creator readByte gas
        (value :: offset :: size :: rest) =
      some
        (CreateInitcodeBridge.createRequestFromMemory creator readByte gas
          (EvmAsm.Evm64.CreateArgsStackDecode.mkCreate value offset size)) := rfl


-- @@ L104-104 verbatim
end CreateStackExecutionBridge


-- @@ L106-106 verbatim
end EvmAsm.EL
