/-
  EvmAsm.EL.CreateArgsBridge

  Bridge from EVM CREATE-family stack arguments to EL creation requests
  (GH #115).
-/

module

public import EvmAsm.EL.Create
public import EvmAsm.Evm64.CreateArgs


-- @@ L13-13 verbatim
@[expose] public section


-- @@ L15-15 verbatim
namespace EvmAsm.EL


-- @@ L17-17 verbatim
namespace CreateArgsBridge


-- @@ L19-19 verbatim
abbrev InitcodeRange := EvmAsm.Evm64.CreateArgs.InitcodeRange

-- @@ L20-20 verbatim
abbrev CreateArgs := EvmAsm.Evm64.CreateArgs.Create

-- @@ L21-21 verbatim
abbrev Create2Args := EvmAsm.Evm64.CreateArgs.Create2


-- @@ L23-24 verbatim
def gasNat (gas : EvmAsm.Evm64.EvmWord) : Nat :=
  gas.toNat


-- @@ L26-27 verbatim
def createInitcodeRange (args : CreateArgs) : InitcodeRange :=
  args.initcode


-- @@ L29-30 verbatim
def create2InitcodeRange (args : Create2Args) : InitcodeRange :=
  args.initcode


-- @@ L32-37 verbatim
/-- CREATE stack arguments become an EL creation request once the initcode
    memory slice has been loaded into bytes. -/
def createRequest
    (creator : Address) (initcode : List Byte) (gas : EvmAsm.Evm64.EvmWord)
    (args : CreateArgs) : CreateRequest :=
  CreateRequest.forCreate creator args.value initcode (gasNat gas)


-- @@ L39-44 verbatim
/-- CREATE2 stack arguments become an EL creation request once the initcode
    memory slice has been loaded into bytes. -/
def create2Request
    (creator : Address) (initcode : List Byte) (gas : EvmAsm.Evm64.EvmWord)
    (args : Create2Args) : CreateRequest :=
  CreateRequest.forCreate2 creator args.value initcode (gasNat gas) args.salt


-- @@ L46-49 verbatim
theorem createRequestKind
    (creator : Address) (initcode : List Byte) (gas : EvmAsm.Evm64.EvmWord)
    (args : CreateArgs) :
    (createRequest creator initcode gas args).kind = .create := rfl


-- @@ L51-54 verbatim
theorem create2RequestKind
    (creator : Address) (initcode : List Byte) (gas : EvmAsm.Evm64.EvmWord)
    (args : Create2Args) :
    (create2Request creator initcode gas args).kind = .create2 := rfl


-- @@ L56-59 verbatim
theorem createRequestValue
    (creator : Address) (initcode : List Byte) (gas : EvmAsm.Evm64.EvmWord)
    (args : CreateArgs) :
    (createRequest creator initcode gas args).value = args.value := rfl


-- @@ L61-64 verbatim
theorem create2RequestValue
    (creator : Address) (initcode : List Byte) (gas : EvmAsm.Evm64.EvmWord)
    (args : Create2Args) :
    (create2Request creator initcode gas args).value = args.value := rfl


-- @@ L66-69 verbatim
theorem createRequestInitcode
    (creator : Address) (initcode : List Byte) (gas : EvmAsm.Evm64.EvmWord)
    (args : CreateArgs) :
    (createRequest creator initcode gas args).initcode = initcode := rfl


-- @@ L71-74 verbatim
theorem create2RequestInitcode
    (creator : Address) (initcode : List Byte) (gas : EvmAsm.Evm64.EvmWord)
    (args : Create2Args) :
    (create2Request creator initcode gas args).initcode = initcode := rfl


-- @@ L76-79 verbatim
theorem createRequestGas
    (creator : Address) (initcode : List Byte) (gas : EvmAsm.Evm64.EvmWord)
    (args : CreateArgs) :
    (createRequest creator initcode gas args).gas = gasNat gas := rfl


-- @@ L81-84 verbatim
theorem create2RequestGas
    (creator : Address) (initcode : List Byte) (gas : EvmAsm.Evm64.EvmWord)
    (args : Create2Args) :
    (create2Request creator initcode gas args).gas = gasNat gas := rfl


-- @@ L86-89 verbatim
theorem createRequestSalt?
    (creator : Address) (initcode : List Byte) (gas : EvmAsm.Evm64.EvmWord)
    (args : CreateArgs) :
    (createRequest creator initcode gas args).salt? = none := rfl


-- @@ L91-94 verbatim
theorem create2RequestSalt?
    (creator : Address) (initcode : List Byte) (gas : EvmAsm.Evm64.EvmWord)
    (args : Create2Args) :
    (create2Request creator initcode gas args).salt? = some args.salt := rfl


-- @@ L96-102 verbatim
theorem createInitcodeRange_eq
    (args : CreateArgs) :
    createInitcodeRange args =
      { offset := args.initcode.offset, size := args.initcode.size } := by
  obtain ⟨value, initcode⟩ := args
  cases initcode
  rfl


-- @@ L104-110 verbatim
theorem create2InitcodeRange_eq
    (args : Create2Args) :
    create2InitcodeRange args =
      { offset := args.initcode.offset, size := args.initcode.size } := by
  obtain ⟨value, initcode, salt⟩ := args
  cases initcode
  rfl


-- @@ L112-112 verbatim
end CreateArgsBridge


-- @@ L114-114 verbatim
end EvmAsm.EL
