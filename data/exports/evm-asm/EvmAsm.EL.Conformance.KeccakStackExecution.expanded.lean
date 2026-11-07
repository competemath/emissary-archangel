/-
  EvmAsm.EL.Conformance.KeccakStackExecution

  Lean-side conformance vector for the KECCAK256 stack execution bridge
  (GH #111 / GH #125).
-/

module

public import EvmAsm.EL.Conformance
public import EvmAsm.EL.KeccakStackExecutionBridge


-- @@ L13-13 verbatim
@[expose] public section


-- @@ L15-15 verbatim
namespace EvmAsm.EL

-- @@ L16-16 verbatim
namespace Conformance

-- @@ L17-17 verbatim
namespace KeccakStackExecution


-- @@ L19-19 verbatim
abbrev Byte := EvmAsm.EL.Byte

-- @@ L20-20 verbatim
abbrev EvmWord := EvmAsm.Evm64.EvmWord

-- @@ L21-21 verbatim
abbrev AcceleratorInput := EvmAsm.EL.KeccakInputBridge.AcceleratorInput

-- @@ L22-22 verbatim
abbrev AcceleratorOutput := EvmAsm.EL.KeccakResultBridge.AcceleratorOutput


-- @@ L24-27 verbatim
structure KeccakStackInput where
  memory : List Byte
  stack : List EvmWord
  deriving Repr


-- @@ L29-30 verbatim
def readByteAt (memory : List Byte) (addr : Nat) : Byte :=
  memory.getD addr 0


-- @@ L32-33 verbatim
def zeroHash : EvmAsm.EL.KeccakResultBridge.HashBytes :=
  fun _ => 0


-- @@ L35-39 verbatim
def vectorAccelerator (input : AcceleratorInput) : AcceleratorOutput :=
  if input.bytes = [(0xbb : Byte), 0xcc] then
    { hash := zeroHash }
  else
    { hash := fun _ => 0xff }


-- @@ L41-43 verbatim
def runKeccakStack? (input : KeccakStackInput) : Option (List EvmWord) :=
  EvmAsm.EL.KeccakStackExecutionBridge.runKeccakStack?
    vectorAccelerator (readByteAt input.memory) input.stack


-- @@ L45-50 verbatim
def keccakStackVector : TestVector KeccakStackInput (List EvmWord) :=
  { id := "keccak-stack-vector"
    input :=
      { memory := [(0xaa : Byte), 0xbb, 0xcc]
        stack := [(1 : EvmWord), 2, 99] }
    expected := .value [(0 : EvmWord), 99] }


-- @@ L52-60 verbatim
/-- KECCAK256 stack execution requires both offset and size operands.
    Distinctive token: keccakStackUnderflowConformanceVector #111 #125. -/
def keccakStackUnderflowConformanceVector :
    TestVector KeccakStackInput (List EvmWord) :=
  { id := "keccak-stack-underflow"
    input :=
      { memory := [(0xaa : Byte), 0xbb, 0xcc]
        stack := [(1 : EvmWord)] }
    expected := .error "stack-underflow" }


-- @@ L62-67 verbatim
/-- KECCAK stack conformance inputs as reusable test vectors.
    Distinctive token:
    KeccakStackExecutionConformance.keccakStackConformanceTestVectors #111 #125. -/
def keccakStackConformanceTestVectors :
    List (TestVector KeccakStackInput (List EvmWord)) :=
  [keccakStackVector, keccakStackUnderflowConformanceVector]


-- @@ L69-70 verbatim
def keccakStackConformanceVectorIds : List String :=
  keccakStackConformanceTestVectors.map TestVector.id


-- @@ L72-73 verbatim
theorem keccakStackConformanceTestVectors_length :
    keccakStackConformanceTestVectors.length = 2 := rfl


-- @@ L75-77 verbatim
theorem keccakStackConformanceVectorIds_eq :
    keccakStackConformanceVectorIds =
      ["keccak-stack-vector", "keccak-stack-underflow"] := rfl


-- @@ L79-80 verbatim
theorem keccakStackConformanceVectorIds_length :
    keccakStackConformanceVectorIds.length = 2 := rfl


-- @@ L82-84 verbatim
theorem keccakStackConformanceVectorIds_nodup :
    keccakStackConformanceVectorIds.Nodup := by
  decide


-- @@ L86-91 verbatim
theorem runKeccakStack?_vector :
    runKeccakStack?
      { memory := [(0xaa : Byte), 0xbb, 0xcc]
        stack := [(1 : EvmWord), 2, 99] } =
      some [(0 : EvmWord), 99] := by
  rfl


-- @@ L93-97 verbatim
theorem runKeccakStack?_underflow :
    runKeccakStack?
      { memory := [(0xaa : Byte), 0xbb, 0xcc]
        stack := [(1 : EvmWord)] } =
      none := rfl


-- @@ L99-106 verbatim
theorem keccakStackVector_passed :
    checkVector? runKeccakStack? keccakStackVector = .passed :=
  checkVector?_some_passed runKeccakStack?
    "keccak-stack-vector"
    { memory := [(0xaa : Byte), 0xbb, 0xcc]
      stack := [(1 : EvmWord), 2, 99] }
    [(0 : EvmWord), 99]
    runKeccakStack?_vector


-- @@ L108-116 verbatim
theorem keccakStackUnderflowConformanceVector_errored :
    checkVector? runKeccakStack? keccakStackUnderflowConformanceVector =
      .errored "keccak-stack-underflow" "stack-underflow" :=
  checkVector?_none_error runKeccakStack?
    "keccak-stack-underflow"
    "stack-underflow"
    { memory := [(0xaa : Byte), 0xbb, 0xcc]
      stack := [(1 : EvmWord)] }
    runKeccakStack?_underflow


-- @@ L118-122 verbatim
/-- Compact checked-vector batch for KECCAK stack execution.
    Distinctive token:
    KeccakStackExecutionConformance.keccakStackConformanceVectors #111 #125. -/
def keccakStackConformanceVectors : List CheckResult :=
  checkBatch? runKeccakStack? keccakStackConformanceTestVectors


-- @@ L124-128 verbatim
theorem keccakStackConformanceVectors_passed :
    keccakStackConformanceVectors =
      [.passed, .errored "keccak-stack-underflow" "stack-underflow"] := by
  simp [keccakStackConformanceVectors, keccakStackConformanceTestVectors,
    keccakStackVector_passed, keccakStackUnderflowConformanceVector_errored]


-- @@ L130-130 verbatim
end KeccakStackExecution

-- @@ L131-131 verbatim
end Conformance

-- @@ L132-132 verbatim
end EvmAsm.EL
