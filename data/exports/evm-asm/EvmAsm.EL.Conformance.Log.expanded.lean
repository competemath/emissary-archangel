/-
  EvmAsm.EL.Conformance.Log

  Compact Lean-side conformance vectors for LOG data memory helpers
  (GH #125 / GH #112).
-/

module

public import EvmAsm.EL.Conformance
public import EvmAsm.EL.LogDataBridge


-- @@ L13-13 verbatim
@[expose] public section


-- @@ L15-15 verbatim
namespace EvmAsm.EL

-- @@ L16-16 verbatim
namespace Conformance

-- @@ L17-17 verbatim
namespace Log


-- @@ L19-19 verbatim
abbrev Byte := EvmAsm.EL.Byte

-- @@ L20-20 verbatim
abbrev EvmWord := EvmAsm.Evm64.EvmWord

-- @@ L21-21 verbatim
abbrev LogArgs := EvmAsm.Evm64.LogArgs.Args


-- @@ L23-27 verbatim
/-- Input shape for LOG data-memory executable-helper conformance vectors. -/
structure LogDataInput where
  memory : List Byte
  args : LogArgs
  deriving Repr


-- @@ L29-30 verbatim
def readByteAt (memory : List Byte) (addr : Nat) : Byte :=
  memory.getD addr 0


-- @@ L32-34 verbatim
def runLogData (input : LogDataInput) : List Byte :=
  EvmAsm.EL.LogDataBridge.logDataFromMemory
    (readByteAt input.memory) input.args


-- @@ L36-37 verbatim
def mkLogArgs (offset size : EvmWord) (topics : List EvmWord) : LogArgs :=
  { data := { offset := offset, size := size }, topics := topics }


-- @@ L39-46 verbatim
/-- LOG data reads exactly the requested offset/size byte slice.
    Distinctive token: Log.logDataSliceVector #125 #112. -/
def logDataSliceVector : TestVector LogDataInput (List Byte) :=
  { id := "log-data-slice"
    input :=
      { memory := [(0xaa : Byte), 0xbb, 0xcc, 0xdd]
        args := mkLogArgs 1 2 [(0x01 : EvmWord)] }
    expected := .value [(0xbb : Byte), 0xcc] }


-- @@ L48-54 verbatim
/-- LOG with zero data size reads no memory bytes. -/
def logDataZeroSizeVector : TestVector LogDataInput (List Byte) :=
  { id := "log-data-zero-size"
    input :=
      { memory := [(0xaa : Byte), 0xbb]
        args := mkLogArgs 1 0 [] }
    expected := .value [] }


-- @@ L56-60 verbatim
theorem runLogData_slice :
    runLogData
      { memory := [(0xaa : Byte), 0xbb, 0xcc, 0xdd]
        args := mkLogArgs 1 2 [(0x01 : EvmWord)] } =
      [(0xbb : Byte), 0xcc] := rfl


-- @@ L62-65 verbatim
theorem runLogData_zeroSize :
    runLogData
      { memory := [(0xaa : Byte), 0xbb]
        args := mkLogArgs 1 0 [] } = [] := rfl


-- @@ L67-74 verbatim
theorem logDataSliceVector_passed :
    checkVector runLogData logDataSliceVector = .passed :=
  checkVector_value_passed runLogData
    "log-data-slice"
    { memory := [(0xaa : Byte), 0xbb, 0xcc, 0xdd]
      args := mkLogArgs 1 2 [(0x01 : EvmWord)] }
    [(0xbb : Byte), 0xcc]
    runLogData_slice


-- @@ L76-83 verbatim
theorem logDataZeroSizeVector_passed :
    checkVector runLogData logDataZeroSizeVector = .passed :=
  checkVector_value_passed runLogData
    "log-data-zero-size"
    { memory := [(0xaa : Byte), 0xbb]
      args := mkLogArgs 1 0 [] }
    []
    runLogData_zeroSize


-- @@ L85-90 verbatim
/-- Vector IDs for LOG data-memory conformance coverage.
    Distinctive token: logDataConformanceVectorIds #125 #112. -/
def logDataConformanceVectorIds : List String :=
  [ logDataSliceVector.id
  , logDataZeroSizeVector.id
  ]


-- @@ L92-96 verbatim
theorem logDataConformanceVectorIds_eq :
    logDataConformanceVectorIds =
      [ "log-data-slice"
      , "log-data-zero-size"
      ] := rfl


-- @@ L98-99 verbatim
theorem logDataConformanceVectorIds_length :
    logDataConformanceVectorIds.length = 2 := rfl


-- @@ L101-103 verbatim
theorem logDataConformanceVectorIds_nodup :
    logDataConformanceVectorIds.Nodup := by
  decide


-- @@ L105-110 verbatim
/-- Compact checked-vector batch for LOG data memory helpers.
    Distinctive token: Log.logDataConformanceVectors #125 #112. -/
def logDataConformanceVectors : List CheckResult :=
  [ checkVector runLogData logDataSliceVector
  , checkVector runLogData logDataZeroSizeVector
  ]


-- @@ L112-115 verbatim
theorem logDataConformanceVectors_passed :
    logDataConformanceVectors = [.passed, .passed] := by
  simp [logDataConformanceVectors, logDataSliceVector_passed,
    logDataZeroSizeVector_passed]


-- @@ L117-117 verbatim
end Log

-- @@ L118-118 verbatim
end Conformance

-- @@ L119-119 verbatim
end EvmAsm.EL
