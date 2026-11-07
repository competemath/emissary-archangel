/-
  EvmAsm.EL.Conformance.Code

  Initial Lean-side conformance vector for executable code helpers
  (GH #125 / GH #107 / GH #118).
-/

module

public import EvmAsm.EL.Conformance
public import EvmAsm.Evm64.Code.CopyExec
public import EvmAsm.Evm64.Code.CopyArgsStackDecode


-- @@ L14-14 verbatim
@[expose] public section


-- @@ L16-16 verbatim
namespace EvmAsm.EL

-- @@ L17-17 verbatim
namespace Conformance

-- @@ L18-18 verbatim
namespace Code


-- @@ L20-20 verbatim
abbrev EvmWord := EvmAsm.Evm64.EvmWord


-- @@ L22-28 verbatim
/-- Input shape for a CODECOPY executable-helper conformance vector. -/
structure CodeCopyInput where
  code : List (BitVec 8)
  destOffset : EvmWord
  codeOffset : EvmWord
  size : EvmWord
  deriving Repr


-- @@ L30-34 verbatim
/-- Input shape for a CODECOPY stack-decoder conformance vector. -/
structure CodeCopyStackInput where
  code : List (BitVec 8)
  stack : List EvmWord
  deriving Repr


-- @@ L36-40 verbatim
def runCodeCopy (input : CodeCopyInput) : List (BitVec 8) :=
  EvmAsm.Evm64.CodeCopyExec.copiedBytesFromArgs
    input.code
    (EvmAsm.Evm64.CodeCopyArgs.copyArgs
      input.destOffset input.codeOffset input.size)


-- @@ L42-45 verbatim
def runCodeCopyStack? (input : CodeCopyStackInput) :
    Option (List (BitVec 8)) :=
  EvmAsm.Evm64.CodeCopyArgsStackDecode.decodeCodeCopyStack? input.stack
    |>.map (EvmAsm.Evm64.CodeCopyExec.copiedBytesFromArgs input.code)


-- @@ L47-57 verbatim
/-- CODECOPY zero-pads bytes copied past the end of code.
    Distinctive token: codeCopyZeroPadVector #125 #107 #118. -/
def codeCopyZeroPadVector :
    TestVector CodeCopyInput (List (BitVec 8)) :=
  { id := "codecopy-zero-pad"
    input :=
      { code := [(0x60 : BitVec 8), (0xaa : BitVec 8)]
        destOffset := 64
        codeOffset := 1
        size := 4 }
    expected := .value [(0xaa : BitVec 8), 0, 0, 0] }


-- @@ L59-69 verbatim
/-- Stack-decoded CODECOPY uses stack words as
    `destOffset, codeOffset, size`; the executable helper here returns only
    the copied byte sequence. Distinctive token: runCodeCopyStack?
    #107 #118 #125. -/
def codeCopyStackVector :
    TestVector CodeCopyStackInput (List (BitVec 8)) :=
  { id := "codecopy-stack-decode"
    input :=
      { code := [(0x60 : BitVec 8), (0xaa : BitVec 8)]
        stack := [(64 : EvmWord), (1 : EvmWord), (4 : EvmWord)] }
    expected := .value [(0xaa : BitVec 8), 0, 0, 0] }


-- @@ L71-78 verbatim
/-- CODECOPY stack decoding fails unless all three stack operands exist. -/
def codeCopyStackUnderflowVector :
    TestVector CodeCopyStackInput (List (BitVec 8)) :=
  { id := "codecopy-stack-underflow"
    input :=
      { code := [(0x60 : BitVec 8), (0xaa : BitVec 8)]
        stack := [(64 : EvmWord), (1 : EvmWord)] }
    expected := .error "stack-underflow" }


-- @@ L80-86 verbatim
theorem runCodeCopy_zeroPad :
    runCodeCopy
      { code := [(0x60 : BitVec 8), (0xaa : BitVec 8)]
        destOffset := 64
        codeOffset := 1
        size := 4 } =
      [(0xaa : BitVec 8), 0, 0, 0] := rfl


-- @@ L88-92 verbatim
theorem runCodeCopyStack_decoded :
    runCodeCopyStack?
      { code := [(0x60 : BitVec 8), (0xaa : BitVec 8)]
        stack := [(64 : EvmWord), (1 : EvmWord), (4 : EvmWord)] } =
      some [(0xaa : BitVec 8), 0, 0, 0] := rfl


-- @@ L94-97 verbatim
theorem runCodeCopyStack_underflow :
    runCodeCopyStack?
      { code := [(0x60 : BitVec 8), (0xaa : BitVec 8)]
        stack := [(64 : EvmWord), (1 : EvmWord)] } = none := rfl


-- @@ L99-108 verbatim
theorem codeCopyZeroPadVector_passed :
    checkVector runCodeCopy codeCopyZeroPadVector = .passed :=
  checkVector_value_passed runCodeCopy
    "codecopy-zero-pad"
    { code := [(0x60 : BitVec 8), (0xaa : BitVec 8)]
      destOffset := (64 : EvmWord)
      codeOffset := (1 : EvmWord)
      size := (4 : EvmWord) }
    [(0xaa : BitVec 8), 0, 0, 0]
    runCodeCopy_zeroPad


-- @@ L110-117 verbatim
theorem codeCopyStackVector_passed :
    checkVector? runCodeCopyStack? codeCopyStackVector = .passed :=
  checkVector?_some_passed runCodeCopyStack?
    "codecopy-stack-decode"
    { code := [(0x60 : BitVec 8), (0xaa : BitVec 8)]
      stack := [(64 : EvmWord), (1 : EvmWord), (4 : EvmWord)] }
    [(0xaa : BitVec 8), 0, 0, 0]
    runCodeCopyStack_decoded


-- @@ L119-127 verbatim
theorem codeCopyStackUnderflowVector_errored :
    checkVector? runCodeCopyStack? codeCopyStackUnderflowVector =
      .errored "codecopy-stack-underflow" "stack-underflow" :=
  checkVector?_none_error runCodeCopyStack?
    "codecopy-stack-underflow"
    "stack-underflow"
    { code := [(0x60 : BitVec 8), (0xaa : BitVec 8)]
      stack := [(64 : EvmWord), (1 : EvmWord)] }
    runCodeCopyStack_underflow


-- @@ L129-135 verbatim
/-- Vector IDs for code executable-helper conformance coverage.
    Distinctive token: codeConformanceVectorIds #125 #107 #118. -/
def codeConformanceVectorIds : List String :=
  [ codeCopyZeroPadVector.id
  , codeCopyStackVector.id
  , codeCopyStackUnderflowVector.id
  ]


-- @@ L137-142 verbatim
theorem codeConformanceVectorIds_eq :
    codeConformanceVectorIds =
      [ "codecopy-zero-pad"
      , "codecopy-stack-decode"
      , "codecopy-stack-underflow"
      ] := rfl


-- @@ L144-145 verbatim
theorem codeConformanceVectorIds_length :
    codeConformanceVectorIds.length = 3 := rfl


-- @@ L147-149 verbatim
theorem codeConformanceVectorIds_nodup :
    codeConformanceVectorIds.Nodup := by
  decide


-- @@ L151-157 verbatim
/-- Compact checked-vector batch for code executable helpers.
    Distinctive token: codeConformanceVectors #125 #107 #118. -/
def codeConformanceVectors : List CheckResult :=
  [ checkVector runCodeCopy codeCopyZeroPadVector
  , checkVector? runCodeCopyStack? codeCopyStackVector
  , checkVector? runCodeCopyStack? codeCopyStackUnderflowVector
  ]


-- @@ L159-163 verbatim
theorem codeConformanceVectors_passed :
    codeConformanceVectors =
      [.passed, .passed, .errored "codecopy-stack-underflow" "stack-underflow"] := by
  simp [codeConformanceVectors, codeCopyZeroPadVector_passed]
  exact ⟨codeCopyStackVector_passed, codeCopyStackUnderflowVector_errored⟩


-- @@ L165-165 verbatim
end Code

-- @@ L166-166 verbatim
end Conformance

-- @@ L167-167 verbatim
end EvmAsm.EL
