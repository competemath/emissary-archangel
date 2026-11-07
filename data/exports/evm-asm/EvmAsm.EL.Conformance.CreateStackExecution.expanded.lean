/-
  EvmAsm.EL.Conformance.CreateStackExecution

  Lean-side conformance vector for the CREATE stack execution bridge
  (GH #115 / GH #125).
-/

module

public import EvmAsm.EL.Conformance
public import EvmAsm.EL.CreateStackExecutionBridge


-- @@ L13-13 verbatim
@[expose] public section


-- @@ L15-15 verbatim
namespace EvmAsm.EL

-- @@ L16-16 verbatim
namespace Conformance

-- @@ L17-17 verbatim
namespace CreateStackExecution


-- @@ L19-19 verbatim
abbrev Byte := EvmAsm.EL.Byte

-- @@ L20-20 verbatim
abbrev EvmWord := EvmAsm.Evm64.EvmWord

-- @@ L21-21 verbatim
abbrev CreateKind := EvmAsm.Evm64.CreateArgs.Kind

-- @@ L22-23 verbatim
abbrev CreateStackState :=
  EvmAsm.EL.CreateStackExecutionBridge.CreateStackState


-- @@ L25-26 verbatim
deriving instance DecidableEq for
  EvmAsm.EL.CreateStackExecutionBridge.CreateStackState


-- @@ L28-33 verbatim
structure CreateStackInput where
  kind : CreateKind
  creator : Address
  memory : List Byte
  gas : EvmWord
  stackState : CreateStackState


-- @@ L35-36 verbatim
def readByteAt (memory : List Byte) (addr : Nat) : Byte :=
  memory.getD addr 0


-- @@ L38-38 verbatim
def deployedAddress : Address := 0x1234

-- @@ L39-39 verbatim
def create2DeployedAddress : Address := 0x5678


-- @@ L41-50 verbatim
def createStackVector : TestVector CreateStackInput CreateStackState :=
  { id := "create-stack-execution"
    input :=
      { kind := .create
        creator := 0xabcd
        memory := [(0xaa : Byte), 0xbb, 0xcc]
        gas := 321
        stackState := { stack := [(7 : EvmWord), 1, 2, 99] } }
    expected :=
      .value { stack := [(deployedAddress.zeroExtend 256 : EvmWord), 99] } }


-- @@ L52-63 verbatim
/-- CREATE2 consumes its salt operand and pushes the deployed address.
    Distinctive token: create2StackConformanceVector #115 #125. -/
def create2StackConformanceVector : TestVector CreateStackInput CreateStackState :=
  { id := "create2-stack-execution"
    input :=
      { kind := .create2
        creator := 0xabcd
        memory := [(0xaa : Byte), 0xbb, 0xcc]
        gas := 654
        stackState := { stack := [(11 : EvmWord), 1, 2, 0x55, 88] } }
    expected :=
      .value { stack := [(create2DeployedAddress.zeroExtend 256 : EvmWord), 88] } }


-- @@ L65-70 verbatim
/-- CREATE stack conformance inputs as reusable test vectors.
    Distinctive token:
    CreateStackExecutionConformance.createStackConformanceTestVectors #115 #125. -/
def createStackConformanceTestVectors :
    List (TestVector CreateStackInput CreateStackState) :=
  [createStackVector, create2StackConformanceVector]


-- @@ L72-73 verbatim
def createStackConformanceVectorIds : List String :=
  createStackConformanceTestVectors.map TestVector.id


-- @@ L75-76 verbatim
theorem createStackConformanceTestVectors_length :
    createStackConformanceTestVectors.length = 2 := rfl


-- @@ L78-80 verbatim
theorem createStackConformanceVectorIds_eq :
    createStackConformanceVectorIds =
      ["create-stack-execution", "create2-stack-execution"] := rfl


-- @@ L82-83 verbatim
theorem createStackConformanceVectorIds_length :
    createStackConformanceVectorIds.length = 2 := rfl


-- @@ L85-87 verbatim
theorem createStackConformanceVectorIds_nodup :
    createStackConformanceVectorIds.Nodup := by
  decide


-- @@ L89-89 verbatim
end CreateStackExecution

-- @@ L90-90 verbatim
end Conformance

-- @@ L91-91 verbatim
end EvmAsm.EL
