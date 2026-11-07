/-
  EvmAsm.EL.Create

  Pure contract-creation request surface for GH #115.
-/

module

public import EvmAsm.EL.WorldState


-- @@ L11-11 verbatim
@[expose] public section


-- @@ L13-13 verbatim
namespace EvmAsm.EL


-- @@ L15-19 verbatim
/-- CREATE-family opcode variant. -/
inductive CreateKind where
  | create
  | create2
  deriving DecidableEq, Repr


-- @@ L21-21 verbatim
namespace CreateKind


-- @@ L23-25 verbatim
def usesSalt : CreateKind → Bool
  | create => false
  | create2 => true


-- @@ L27-27 verbatim
theorem usesSalt_create : usesSalt create = false := rfl

-- @@ L28-28 verbatim
theorem usesSalt_create2 : usesSalt create2 = true := rfl


-- @@ L30-30 verbatim
end CreateKind


-- @@ L32-40 verbatim
/-- Pure input request for a CREATE or CREATE2 operation. -/
structure CreateRequest where
  kind : CreateKind
  creator : Address
  value : Word256
  initcode : List Byte
  gas : Nat
  salt? : Option Word256
  deriving Repr


-- @@ L42-42 verbatim
namespace CreateRequest


-- @@ L44-52 verbatim
def forCreate
    (creator : Address) (value : Word256) (initcode : List Byte) (gas : Nat) :
    CreateRequest :=
  { kind := .create
    creator := creator
    value := value
    initcode := initcode
    gas := gas
    salt? := none }


-- @@ L54-62 verbatim
def forCreate2
    (creator : Address) (value : Word256) (initcode : List Byte) (gas : Nat)
    (salt : Word256) : CreateRequest :=
  { kind := .create2
    creator := creator
    value := value
    initcode := initcode
    gas := gas
    salt? := some salt }


-- @@ L64-65 verbatim
def isCreate2 (request : CreateRequest) : Prop :=
  request.kind = .create2


-- @@ L67-68 verbatim
def hasSalt (request : CreateRequest) : Prop :=
  request.salt?.isSome


-- @@ L70-72 verbatim
theorem kind_forCreate
    (creator : Address) (value : Word256) (initcode : List Byte) (gas : Nat) :
    (forCreate creator value initcode gas).kind = .create := rfl


-- @@ L74-77 verbatim
theorem kind_forCreate2
    (creator : Address) (value : Word256) (initcode : List Byte) (gas : Nat)
    (salt : Word256) :
    (forCreate2 creator value initcode gas salt).kind = .create2 := rfl


-- @@ L79-81 verbatim
theorem salt?_forCreate
    (creator : Address) (value : Word256) (initcode : List Byte) (gas : Nat) :
    (forCreate creator value initcode gas).salt? = none := rfl


-- @@ L83-86 verbatim
theorem salt?_forCreate2
    (creator : Address) (value : Word256) (initcode : List Byte) (gas : Nat)
    (salt : Word256) :
    (forCreate2 creator value initcode gas salt).salt? = some salt := rfl


-- @@ L88-93 verbatim
theorem hasSalt_forCreate2
    (creator : Address) (value : Word256) (initcode : List Byte) (gas : Nat)
    (salt : Word256) :
    (forCreate2 creator value initcode gas salt).hasSalt := by
  unfold hasSalt
  rfl


-- @@ L95-98 verbatim
theorem not_hasSalt_forCreate
    (creator : Address) (value : Word256) (initcode : List Byte) (gas : Nat) :
    ¬ (forCreate creator value initcode gas).hasSalt := by
  simp [hasSalt, forCreate]


-- @@ L100-103 verbatim
theorem isCreate2_forCreate2
    (creator : Address) (value : Word256) (initcode : List Byte) (gas : Nat)
    (salt : Word256) :
    (forCreate2 creator value initcode gas salt).isCreate2 := rfl


-- @@ L105-108 verbatim
theorem not_isCreate2_forCreate
    (creator : Address) (value : Word256) (initcode : List Byte) (gas : Nat) :
    ¬ (forCreate creator value initcode gas).isCreate2 := by
  simp [isCreate2, forCreate]


-- @@ L110-110 verbatim
end CreateRequest


-- @@ L112-117 verbatim
/-- Coarse result status for CREATE and CREATE2. -/
inductive CreateStatus where
  | deployed
  | reverted
  | failed
  deriving DecidableEq, Repr


-- @@ L119-119 verbatim
namespace CreateResult


-- @@ L121-121 verbatim
end CreateResult


-- @@ L123-123 verbatim
end EvmAsm.EL
