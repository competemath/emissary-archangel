/-
  EvmAsm.EL.MessageCall

  Pure message-call frame and result surface for GH #121.
-/

module

public import EvmAsm.EL.WorldState


-- @@ L11-11 verbatim
@[expose] public section


-- @@ L13-13 verbatim
namespace EvmAsm.EL


-- @@ L15-20 verbatim
/-- CALL-family variants modeled by the first message-call layer. -/
inductive CallKind where
  | call
  | staticcall
  | delegatecall
  deriving DecidableEq, Repr


-- @@ L22-22 verbatim
namespace CallKind


-- @@ L24-28 verbatim
/-- Whether the call kind transfers value from caller to callee. -/
def transfersValue : CallKind → Bool
  | call => true
  | staticcall => false
  | delegatecall => false


-- @@ L30-34 verbatim
/-- Whether the callee is allowed to write state in this call mode. -/
def mayWriteState : CallKind → Bool
  | call => true
  | staticcall => false
  | delegatecall => true


-- @@ L36-40 verbatim
/-- Whether execution preserves the caller/value context from the parent frame. -/
def preservesCallerContext : CallKind → Bool
  | call => false
  | staticcall => false
  | delegatecall => true


-- @@ L42-42 verbatim
theorem transfersValue_call : transfersValue call = true := rfl

-- @@ L43-43 verbatim
theorem transfersValue_staticcall : transfersValue staticcall = false := rfl

-- @@ L44-44 verbatim
theorem transfersValue_delegatecall : transfersValue delegatecall = false := rfl


-- @@ L46-46 verbatim
theorem mayWriteState_staticcall : mayWriteState staticcall = false := rfl

-- @@ L47-47 verbatim
theorem preservesCallerContext_delegatecall : preservesCallerContext delegatecall = true := rfl


-- @@ L49-49 verbatim
end CallKind


-- @@ L51-61 verbatim
/-- Pure input frame for one message-call execution. -/
structure CallFrame where
  kind : CallKind
  caller : Address
  callee : Address
  apparentValue : Word256
  transferredValue : Word256
  input : List Byte
  gas : Nat
  isStatic : Bool
  deriving Repr


-- @@ L63-63 verbatim
namespace CallFrame


-- @@ L65-76 verbatim
/-- CALL frame: value is both apparent to the callee and transferred. -/
def forCall
    (caller callee : Address) (value : Word256) (input : List Byte) (gas : Nat)
    (isStatic : Bool) : CallFrame :=
  { kind := .call
    caller := caller
    callee := callee
    apparentValue := value
    transferredValue := value
    input := input
    gas := gas
    isStatic := isStatic }


-- @@ L78-88 verbatim
/-- STATICCALL frame: no value transfer and state writes are forbidden. -/
def forStaticCall
    (caller callee : Address) (input : List Byte) (gas : Nat) : CallFrame :=
  { kind := .staticcall
    caller := caller
    callee := callee
    apparentValue := 0
    transferredValue := 0
    input := input
    gas := gas
    isStatic := true }


-- @@ L90-101 verbatim
/-- DELEGATECALL frame: caller/value context is preserved and no value is transferred. -/
def forDelegateCall
    (caller callee : Address) (apparentValue : Word256) (input : List Byte) (gas : Nat)
    (isStatic : Bool) : CallFrame :=
  { kind := .delegatecall
    caller := caller
    callee := callee
    apparentValue := apparentValue
    transferredValue := 0
    input := input
    gas := gas
    isStatic := isStatic }


-- @@ L103-106 verbatim
theorem transferredValue_forCall
    (caller callee : Address) (value : Word256) (input : List Byte) (gas : Nat)
    (isStatic : Bool) :
    (forCall caller callee value input gas isStatic).transferredValue = value := rfl


-- @@ L108-110 verbatim
theorem transferredValue_forStaticCall
    (caller callee : Address) (input : List Byte) (gas : Nat) :
    (forStaticCall caller callee input gas).transferredValue = 0 := rfl


-- @@ L112-115 verbatim
theorem transferredValue_forDelegateCall
    (caller callee : Address) (apparentValue : Word256) (input : List Byte) (gas : Nat)
    (isStatic : Bool) :
    (forDelegateCall caller callee apparentValue input gas isStatic).transferredValue = 0 := rfl


-- @@ L117-119 verbatim
theorem isStatic_forStaticCall
    (caller callee : Address) (input : List Byte) (gas : Nat) :
    (forStaticCall caller callee input gas).isStatic = true := rfl


-- @@ L121-124 verbatim
theorem kind_forDelegateCall
    (caller callee : Address) (apparentValue : Word256) (input : List Byte) (gas : Nat)
    (isStatic : Bool) :
    (forDelegateCall caller callee apparentValue input gas isStatic).kind = .delegatecall := rfl


-- @@ L126-126 verbatim
end CallFrame


-- @@ L128-133 verbatim
/-- Coarse result status for one message-call execution. -/
inductive CallStatus where
  | success
  | revert
  | failure
  deriving DecidableEq, Repr


-- @@ L135-135 verbatim
namespace CallResult


-- @@ L137-137 verbatim
end CallResult


-- @@ L139-139 verbatim
end EvmAsm.EL
