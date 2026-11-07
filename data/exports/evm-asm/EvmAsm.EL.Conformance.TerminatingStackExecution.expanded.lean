/-
  EvmAsm.EL.Conformance.TerminatingStackExecution

  Lean-side conformance vector for the terminating-opcode stack execution bridge
  (GH #113 / GH #125).
-/

module

public import EvmAsm.EL.Conformance
public import EvmAsm.EL.TerminatingStackExecutionBridge


-- @@ L13-13 verbatim
@[expose] public section


-- @@ L15-15 verbatim
namespace EvmAsm.EL

-- @@ L16-16 verbatim
namespace Conformance

-- @@ L17-17 verbatim
namespace TerminatingStackExecution


-- @@ L19-19 verbatim
abbrev Byte := EvmAsm.EL.Byte

-- @@ L20-20 verbatim
abbrev EvmWord := EvmAsm.Evm64.EvmWord

-- @@ L21-21 verbatim
abbrev TerminatingKind := EvmAsm.Evm64.TerminatingArgs.Kind

-- @@ L22-23 verbatim
abbrev TerminatingStackState :=
  EvmAsm.EL.TerminatingStackExecutionBridge.TerminatingStackState


-- @@ L25-30 verbatim
structure TerminatingVisibleResult where
  status : CallStatus
  output : List Byte
  gasRemaining : Nat
  stack : List EvmWord
  deriving DecidableEq, Repr


-- @@ L32-36 verbatim
structure TerminatingStackInput where
  kind : TerminatingKind
  memory : List Byte
  gasRemaining : Nat
  stackState : TerminatingStackState


-- @@ L38-39 verbatim
def readByteAt (memory : List Byte) (addr : Nat) : Byte :=
  memory.getD addr 0


-- @@ L41-54 verbatim
def terminatingReturnVector :
    TestVector TerminatingStackInput TerminatingVisibleResult :=
  { id := "terminating-stack-return"
    input :=
      { kind := .return_
        memory := [(0xaa : Byte), 0xbb, 0xcc]
        gasRemaining := 123
        stackState := { stack := [(1 : EvmWord), 2, 99] } }
    expected :=
      .value
        { status := .success
          output := [(0xbb : Byte), 0xcc]
          gasRemaining := 123
          stack := [(99 : EvmWord)] } }


-- @@ L56-71 verbatim
/-- REVERT threads memory data through while exposing reverted status.
    Distinctive token: terminatingRevertStackConformanceVector #113 #125. -/
def terminatingRevertStackConformanceVector :
    TestVector TerminatingStackInput TerminatingVisibleResult :=
  { id := "terminating-stack-revert"
    input :=
      { kind := .revert
        memory := [(0xaa : Byte), 0xbb, 0xcc]
        gasRemaining := 45
        stackState := { stack := [(1 : EvmWord), 2, 77] } }
    expected :=
      .value
        { status := .revert
          output := [(0xbb : Byte), 0xcc]
          gasRemaining := 45
          stack := [(77 : EvmWord)] } }


-- @@ L73-78 verbatim
/-- Terminating stack conformance inputs as reusable test vectors.
    Distinctive token:
    TerminatingStackExecutionConformance.terminatingStackConformanceTestVectors #113 #125. -/
def terminatingStackConformanceTestVectors :
    List (TestVector TerminatingStackInput TerminatingVisibleResult) :=
  [terminatingReturnVector, terminatingRevertStackConformanceVector]


-- @@ L80-81 verbatim
def terminatingStackConformanceVectorIds : List String :=
  terminatingStackConformanceTestVectors.map TestVector.id


-- @@ L83-84 verbatim
theorem terminatingStackConformanceTestVectors_length :
    terminatingStackConformanceTestVectors.length = 2 := rfl


-- @@ L86-88 verbatim
theorem terminatingStackConformanceVectorIds_eq :
    terminatingStackConformanceVectorIds =
      ["terminating-stack-return", "terminating-stack-revert"] := rfl


-- @@ L90-91 verbatim
theorem terminatingStackConformanceVectorIds_length :
    terminatingStackConformanceVectorIds.length = 2 := rfl


-- @@ L93-95 verbatim
theorem terminatingStackConformanceVectorIds_nodup :
    terminatingStackConformanceVectorIds.Nodup := by
  decide


-- @@ L97-97 verbatim
end TerminatingStackExecution

-- @@ L98-98 verbatim
end Conformance

-- @@ L99-99 verbatim
end EvmAsm.EL
