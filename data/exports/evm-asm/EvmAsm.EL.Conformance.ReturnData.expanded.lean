/-
  EvmAsm.EL.Conformance.ReturnData

  Initial Lean-side conformance vector for executable returndata helpers
  (GH #125 / GH #114).
-/

module

public import EvmAsm.EL.Conformance
public import EvmAsm.Evm64.ReturnData.CopyExec
public import EvmAsm.Evm64.ReturnData.CopyArgsStackDecode


-- @@ L14-14 verbatim
@[expose] public section


-- @@ L16-16 verbatim
namespace EvmAsm.EL

-- @@ L17-17 verbatim
namespace Conformance

-- @@ L18-18 verbatim
namespace ReturnData


-- @@ L20-20 verbatim
abbrev EvmWord := EvmAsm.Evm64.EvmWord


-- @@ L22-28 verbatim
/-- Input shape for a RETURNDATACOPY executable-helper conformance vector. -/
structure ReturnDataCopyInput where
  data : List (BitVec 8)
  destOffset : EvmWord
  dataOffset : EvmWord
  size : EvmWord
  deriving Repr


-- @@ L30-34 verbatim
/-- Input shape for a RETURNDATACOPY stack-decoder conformance vector. -/
structure ReturnDataCopyStackInput where
  data : List (BitVec 8)
  stack : List EvmWord
  deriving Repr


-- @@ L36-40 verbatim
def runReturnDataCopy (input : ReturnDataCopyInput) : List (BitVec 8) :=
  EvmAsm.Evm64.ReturnDataCopyExec.copiedBytesFromArgs
    input.data
    (EvmAsm.Evm64.ReturnDataCopyArgs.copyArgs
      input.destOffset input.dataOffset input.size)


-- @@ L42-45 verbatim
def runReturnDataCopyStack? (input : ReturnDataCopyStackInput) :
    Option (List (BitVec 8)) :=
  EvmAsm.Evm64.ReturnDataCopyArgsStackDecode.decodeReturnDataCopyStack? input.stack
    |>.map (EvmAsm.Evm64.ReturnDataCopyExec.copiedBytesFromArgs input.data)


-- @@ L47-57 verbatim
/-- RETURNDATACOPY zero-pads bytes copied past the end of returndata.
    Distinctive token: returnDataCopyZeroPadVector #125 #114. -/
def returnDataCopyZeroPadVector :
    TestVector ReturnDataCopyInput (List (BitVec 8)) :=
  { id := "returndatacopy-zero-pad"
    input :=
      { data := [(0xaa : BitVec 8), (0xbb : BitVec 8)]
        destOffset := 32
        dataOffset := 1
        size := 4 }
    expected := .value [(0xbb : BitVec 8), 0, 0, 0] }


-- @@ L59-69 verbatim
/-- Stack-decoded RETURNDATACOPY uses stack words as
    `destOffset, dataOffset, size`; the executable helper here returns only
    the copied byte sequence. Distinctive token: runReturnDataCopyStack?
    #107 #114 #125. -/
def returnDataCopyStackVector :
    TestVector ReturnDataCopyStackInput (List (BitVec 8)) :=
  { id := "returndatacopy-stack-decode"
    input :=
      { data := [(0xaa : BitVec 8), (0xbb : BitVec 8)]
        stack := [(32 : EvmWord), (1 : EvmWord), (4 : EvmWord)] }
    expected := .value [(0xbb : BitVec 8), 0, 0, 0] }


-- @@ L71-78 verbatim
/-- RETURNDATACOPY stack decoding fails unless all three stack operands exist. -/
def returnDataCopyStackUnderflowVector :
    TestVector ReturnDataCopyStackInput (List (BitVec 8)) :=
  { id := "returndatacopy-stack-underflow"
    input :=
      { data := [(0xaa : BitVec 8), (0xbb : BitVec 8)]
        stack := [(32 : EvmWord), (1 : EvmWord)] }
    expected := .error "stack-underflow" }


-- @@ L80-86 verbatim
theorem runReturnDataCopy_zeroPad :
    runReturnDataCopy
      { data := [(0xaa : BitVec 8), (0xbb : BitVec 8)]
        destOffset := 32
        dataOffset := 1
        size := 4 } =
      [(0xbb : BitVec 8), 0, 0, 0] := rfl


-- @@ L88-92 verbatim
theorem runReturnDataCopyStack_decoded :
    runReturnDataCopyStack?
      { data := [(0xaa : BitVec 8), (0xbb : BitVec 8)]
        stack := [(32 : EvmWord), (1 : EvmWord), (4 : EvmWord)] } =
      some [(0xbb : BitVec 8), 0, 0, 0] := rfl


-- @@ L94-97 verbatim
theorem runReturnDataCopyStack_underflow :
    runReturnDataCopyStack?
      { data := [(0xaa : BitVec 8), (0xbb : BitVec 8)]
        stack := [(32 : EvmWord), (1 : EvmWord)] } = none := rfl


-- @@ L99-108 verbatim
theorem returnDataCopyZeroPadVector_passed :
    checkVector runReturnDataCopy returnDataCopyZeroPadVector = .passed :=
  checkVector_value_passed runReturnDataCopy
    "returndatacopy-zero-pad"
    { data := [(0xaa : BitVec 8), (0xbb : BitVec 8)]
      destOffset := (32 : EvmWord)
      dataOffset := (1 : EvmWord)
      size := (4 : EvmWord) }
    [(0xbb : BitVec 8), 0, 0, 0]
    runReturnDataCopy_zeroPad


-- @@ L110-117 verbatim
theorem returnDataCopyStackVector_passed :
    checkVector? runReturnDataCopyStack? returnDataCopyStackVector = .passed :=
  checkVector?_some_passed runReturnDataCopyStack?
    "returndatacopy-stack-decode"
    { data := [(0xaa : BitVec 8), (0xbb : BitVec 8)]
      stack := [(32 : EvmWord), (1 : EvmWord), (4 : EvmWord)] }
    [(0xbb : BitVec 8), 0, 0, 0]
    runReturnDataCopyStack_decoded


-- @@ L119-127 verbatim
theorem returnDataCopyStackUnderflowVector_errored :
    checkVector? runReturnDataCopyStack? returnDataCopyStackUnderflowVector =
      .errored "returndatacopy-stack-underflow" "stack-underflow" :=
  checkVector?_none_error runReturnDataCopyStack?
    "returndatacopy-stack-underflow"
    "stack-underflow"
    { data := [(0xaa : BitVec 8), (0xbb : BitVec 8)]
      stack := [(32 : EvmWord), (1 : EvmWord)] }
    runReturnDataCopyStack_underflow


-- @@ L129-135 verbatim
/-- Vector IDs for returndata executable-helper conformance coverage.
    Distinctive token: returnDataConformanceVectorIds #125 #114. -/
def returnDataConformanceVectorIds : List String :=
  [ returnDataCopyZeroPadVector.id
  , returnDataCopyStackVector.id
  , returnDataCopyStackUnderflowVector.id
  ]


-- @@ L137-142 verbatim
theorem returnDataConformanceVectorIds_eq :
    returnDataConformanceVectorIds =
      [ "returndatacopy-zero-pad"
      , "returndatacopy-stack-decode"
      , "returndatacopy-stack-underflow"
      ] := rfl


-- @@ L144-145 verbatim
theorem returnDataConformanceVectorIds_length :
    returnDataConformanceVectorIds.length = 3 := rfl


-- @@ L147-149 verbatim
theorem returnDataConformanceVectorIds_nodup :
    returnDataConformanceVectorIds.Nodup := by
  decide


-- @@ L151-157 verbatim
/-- Compact checked-vector batch for returndata executable helpers.
    Distinctive token: returnDataConformanceVectors #125 #114. -/
def returnDataConformanceVectors : List CheckResult :=
  [ checkVector runReturnDataCopy returnDataCopyZeroPadVector
  , checkVector? runReturnDataCopyStack? returnDataCopyStackVector
  , checkVector? runReturnDataCopyStack? returnDataCopyStackUnderflowVector
  ]


-- @@ L159-165 verbatim
theorem returnDataConformanceVectors_passed :
    returnDataConformanceVectors =
      [.passed, .passed,
        .errored "returndatacopy-stack-underflow" "stack-underflow"] := by
  simp [returnDataConformanceVectors, returnDataCopyZeroPadVector_passed]
  exact ⟨returnDataCopyStackVector_passed,
    returnDataCopyStackUnderflowVector_errored⟩


-- @@ L167-167 verbatim
end ReturnData

-- @@ L168-168 verbatim
end Conformance

-- @@ L169-169 verbatim
end EvmAsm.EL
