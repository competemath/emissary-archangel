/-
  EvmAsm.EL.Conformance.SignedArithmeticStackExecution

  Lean-side conformance vectors for the SDIV/SMOD stack execution bridges
  (GH #90 / GH #125).
-/

module

public import EvmAsm.EL.Conformance
public import EvmAsm.Evm64.SDiv.StackExecutionBridge
public import EvmAsm.Evm64.SMod.StackExecutionBridge


-- @@ L14-14 verbatim
@[expose] public section


-- @@ L16-16 verbatim
namespace EvmAsm.EL

-- @@ L17-17 verbatim
namespace Conformance

-- @@ L18-18 verbatim
namespace SignedArithmeticStackExecution


-- @@ L20-20 verbatim
abbrev EvmWord := EvmAsm.Evm64.EvmWord


-- @@ L22-22 verbatim
abbrev SDivStackState := EvmAsm.Evm64.SDivStackExecutionBridge.SDivStackState


-- @@ L24-24 verbatim
abbrev SDivStackResult := EvmAsm.Evm64.SDivStackExecutionBridge.SDivStackResult


-- @@ L26-26 verbatim
abbrev SModStackState := EvmAsm.Evm64.SModStackExecutionBridge.SModStackState


-- @@ L28-28 verbatim
abbrev SModStackResult := EvmAsm.Evm64.SModStackExecutionBridge.SModStackResult


-- @@ L30-31 verbatim
deriving instance DecidableEq for
  EvmAsm.Evm64.SDivStackExecutionBridge.SDivVisibleEffects


-- @@ L33-34 verbatim
deriving instance DecidableEq for
  EvmAsm.Evm64.SDivStackExecutionBridge.SDivStackResult


-- @@ L36-37 verbatim
deriving instance DecidableEq for
  EvmAsm.Evm64.SModStackExecutionBridge.SModVisibleEffects


-- @@ L39-40 verbatim
deriving instance DecidableEq for
  EvmAsm.Evm64.SModStackExecutionBridge.SModStackResult


-- @@ L42-43 verbatim
abbrev runSDivStack? (input : SDivStackState) : Option SDivStackResult :=
  EvmAsm.Evm64.SDivStackExecutionBridge.runSDivStack? input


-- @@ L45-46 verbatim
abbrev runSModStack? (input : SModStackState) : Option SModStackResult :=
  EvmAsm.Evm64.SModStackExecutionBridge.runSModStack? input


-- @@ L48-54 verbatim
def sdivZeroDivisorVector : TestVector SDivStackState SDivStackResult :=
  { id := "sdiv-stack-zero-divisor"
    input := { stack := [9, 0, 42] }
    expected :=
      .value
        { effects := { stackWords := [0] }
          stack := [42] } }


-- @@ L56-62 verbatim
def sdivIntMinNegOneVector : TestVector SDivStackState SDivStackResult :=
  { id := "sdiv-stack-int-min-neg-one"
    input := { stack := [BitVec.intMin 256, (-1 : EvmWord), 42] }
    expected :=
      .value
        { effects := { stackWords := [BitVec.intMin 256] }
          stack := [42] } }


-- @@ L64-70 verbatim
def sdivPosPosVector : TestVector SDivStackState SDivStackResult :=
  { id := "sdiv-stack-pos-pos"
    input := { stack := [9, 2, 42] }
    expected :=
      .value
        { effects := { stackWords := [4] }
          stack := [42] } }


-- @@ L72-78 verbatim
def sdivNegNegVector : TestVector SDivStackState SDivStackResult :=
  { id := "sdiv-stack-neg-neg"
    input := { stack := [(-9 : EvmWord), (-2 : EvmWord), 42] }
    expected :=
      .value
        { effects := { stackWords := [4] }
          stack := [42] } }


-- @@ L80-86 verbatim
def sdivPosNegTruncVector : TestVector SDivStackState SDivStackResult :=
  { id := "sdiv-stack-pos-neg-trunc"
    input := { stack := [7, (-2 : EvmWord), 42] }
    expected :=
      .value
        { effects := { stackWords := [(-3 : EvmWord)] }
          stack := [42] } }


-- @@ L88-91 verbatim
def sdivUnderflowVector : TestVector SDivStackState SDivStackResult :=
  { id := "sdiv-stack-underflow"
    input := { stack := [7] }
    expected := .error "stack-underflow" }


-- @@ L93-99 verbatim
def smodZeroDivisorVector : TestVector SModStackState SModStackResult :=
  { id := "smod-stack-zero-divisor"
    input := { stack := [9, 0, 42] }
    expected :=
      .value
        { effects := { stackWords := [0] }
          stack := [42] } }


-- @@ L101-107 verbatim
def smodNegPosSignVector : TestVector SModStackState SModStackResult :=
  { id := "smod-stack-neg-pos-sign"
    input := { stack := [(-3 : EvmWord), 2, 42] }
    expected :=
      .value
        { effects := { stackWords := [(-1 : EvmWord)] }
          stack := [42] } }


-- @@ L109-115 verbatim
def smodPosNegSignVector : TestVector SModStackState SModStackResult :=
  { id := "smod-stack-pos-neg-sign"
    input := { stack := [3, (-2 : EvmWord), 42] }
    expected :=
      .value
        { effects := { stackWords := [1] }
          stack := [42] } }


-- @@ L117-120 verbatim
def smodUnderflowVector : TestVector SModStackState SModStackResult :=
  { id := "smod-stack-underflow"
    input := { stack := [] }
    expected := .error "stack-underflow" }


-- @@ L122-132 verbatim
/-- SDIV stack conformance inputs as reusable test vectors.
    Distinctive token:
    SignedArithmeticStackExecutionConformance.sdivStackConformanceTestVectors #90 #125. -/
def sdivStackConformanceTestVectors : List (TestVector SDivStackState SDivStackResult) :=
  [ sdivZeroDivisorVector
  , sdivIntMinNegOneVector
  , sdivPosPosVector
  , sdivNegNegVector
  , sdivPosNegTruncVector
  , sdivUnderflowVector
  ]


-- @@ L134-142 verbatim
/-- SMOD stack conformance inputs as reusable test vectors.
    Distinctive token:
    SignedArithmeticStackExecutionConformance.smodStackConformanceTestVectors #90 #125. -/
def smodStackConformanceTestVectors : List (TestVector SModStackState SModStackResult) :=
  [ smodZeroDivisorVector
  , smodNegPosSignVector
  , smodPosNegSignVector
  , smodUnderflowVector
  ]


-- @@ L144-145 verbatim
theorem sdivStackConformanceTestVectors_length :
    sdivStackConformanceTestVectors.length = 6 := rfl


-- @@ L147-148 verbatim
theorem smodStackConformanceTestVectors_length :
    smodStackConformanceTestVectors.length = 4 := rfl


-- @@ L150-151 verbatim
def signedArithmeticConformanceTestVectorCount : Nat :=
  sdivStackConformanceTestVectors.length + smodStackConformanceTestVectors.length


-- @@ L153-154 verbatim
theorem signedArithmeticConformanceTestVectorCount_eq :
    signedArithmeticConformanceTestVectorCount = 10 := rfl


-- @@ L156-157 verbatim
def sdivStackConformanceVectorIds : List String :=
  sdivStackConformanceTestVectors.map TestVector.id


-- @@ L159-160 verbatim
def smodStackConformanceVectorIds : List String :=
  smodStackConformanceTestVectors.map TestVector.id


-- @@ L162-163 verbatim
def signedArithmeticConformanceVectorIds : List String :=
  sdivStackConformanceVectorIds ++ smodStackConformanceVectorIds


-- @@ L165-173 verbatim
theorem sdivStackConformanceVectorIds_eq :
    sdivStackConformanceVectorIds =
      [ "sdiv-stack-zero-divisor"
      , "sdiv-stack-int-min-neg-one"
      , "sdiv-stack-pos-pos"
      , "sdiv-stack-neg-neg"
      , "sdiv-stack-pos-neg-trunc"
      , "sdiv-stack-underflow"
      ] := rfl


-- @@ L175-181 verbatim
theorem smodStackConformanceVectorIds_eq :
    smodStackConformanceVectorIds =
      [ "smod-stack-zero-divisor"
      , "smod-stack-neg-pos-sign"
      , "smod-stack-pos-neg-sign"
      , "smod-stack-underflow"
      ] := rfl


-- @@ L183-195 verbatim
theorem signedArithmeticConformanceVectorIds_eq :
    signedArithmeticConformanceVectorIds =
      [ "sdiv-stack-zero-divisor"
      , "sdiv-stack-int-min-neg-one"
      , "sdiv-stack-pos-pos"
      , "sdiv-stack-neg-neg"
      , "sdiv-stack-pos-neg-trunc"
      , "sdiv-stack-underflow"
      , "smod-stack-zero-divisor"
      , "smod-stack-neg-pos-sign"
      , "smod-stack-pos-neg-sign"
      , "smod-stack-underflow"
      ] := rfl


-- @@ L197-198 verbatim
theorem sdivStackConformanceVectorIds_length :
    sdivStackConformanceVectorIds.length = 6 := rfl


-- @@ L200-201 verbatim
theorem smodStackConformanceVectorIds_length :
    smodStackConformanceVectorIds.length = 4 := rfl


-- @@ L203-204 verbatim
theorem signedArithmeticConformanceVectorIds_length :
    signedArithmeticConformanceVectorIds.length = 10 := rfl


-- @@ L206-208 verbatim
theorem sdivStackConformanceVectorIds_nodup :
    sdivStackConformanceVectorIds.Nodup := by
  decide


-- @@ L210-212 verbatim
theorem smodStackConformanceVectorIds_nodup :
    smodStackConformanceVectorIds.Nodup := by
  decide


-- @@ L214-216 verbatim
theorem signedArithmeticConformanceVectorIds_nodup :
    signedArithmeticConformanceVectorIds.Nodup := by
  decide


-- @@ L218-227 verbatim
def signedArithmeticValueVectorIds : List String :=
  [ "sdiv-stack-zero-divisor"
  , "sdiv-stack-int-min-neg-one"
  , "sdiv-stack-pos-pos"
  , "sdiv-stack-neg-neg"
  , "sdiv-stack-pos-neg-trunc"
  , "smod-stack-zero-divisor"
  , "smod-stack-neg-pos-sign"
  , "smod-stack-pos-neg-sign"
  ]


-- @@ L229-232 verbatim
def signedArithmeticErrorVectorIds : List String :=
  [ "sdiv-stack-underflow"
  , "smod-stack-underflow"
  ]


-- @@ L234-235 verbatim
theorem signedArithmeticValueVectorIds_length :
    signedArithmeticValueVectorIds.length = 8 := rfl


-- @@ L237-238 verbatim
theorem signedArithmeticErrorVectorIds_length :
    signedArithmeticErrorVectorIds.length = 2 := rfl


-- @@ L240-242 verbatim
theorem signedArithmeticValueVectorIds_nodup :
    signedArithmeticValueVectorIds.Nodup := by
  decide


-- @@ L244-246 verbatim
theorem signedArithmeticErrorVectorIds_nodup :
    signedArithmeticErrorVectorIds.Nodup := by
  decide


-- @@ L248-251 verbatim
theorem signedArithmeticValueVectorIds_subset_all :
    ∀ id ∈ signedArithmeticValueVectorIds,
      id ∈ signedArithmeticConformanceVectorIds := by
  decide


-- @@ L253-256 verbatim
theorem signedArithmeticErrorVectorIds_subset_all :
    ∀ id ∈ signedArithmeticErrorVectorIds,
      id ∈ signedArithmeticConformanceVectorIds := by
  decide


-- @@ L258-261 verbatim
theorem signedArithmeticValueVectorIds_no_error :
    ∀ id ∈ signedArithmeticValueVectorIds,
      id ∉ signedArithmeticErrorVectorIds := by
  decide


-- @@ L263-268 verbatim
theorem runSDivStack?_zero_divisor_vector :
    runSDivStack? { stack := [(9 : EvmWord), 0, 42] } =
      some { effects := { stackWords := [0] }, stack := [42] } := by
  simpa using
    EvmAsm.Evm64.SDivStackExecutionBridge.runSDivStack?_zero_divisor
      (9 : EvmWord) [(42 : EvmWord)]


-- @@ L270-275 verbatim
theorem runSDivStack?_intMin_neg_one_vector :
    runSDivStack? { stack := [BitVec.intMin 256, (-1 : EvmWord), 42] } =
      some { effects := { stackWords := [BitVec.intMin 256] }, stack := [42] } := by
  simpa using
    EvmAsm.Evm64.SDivStackExecutionBridge.runSDivStack?_intMin_neg_one
      [(42 : EvmWord)]


-- @@ L277-286 verbatim
theorem runSDivStack?_pos_pos_vector :
    runSDivStack? { stack := [(9 : EvmWord), (2 : EvmWord), 42] } =
      some { effects := { stackWords := [4] }, stack := [42] } := by
  have h : EvmAsm.Evm64.SDivArgs.sdivResultFromArgs
      (EvmAsm.Evm64.SDivArgs.sdivArgs (9 : EvmWord) (2 : EvmWord)) = (4 : EvmWord) := by
    unfold EvmAsm.Evm64.SDivArgs.sdivResultFromArgs EvmAsm.Evm64.SDivArgs.sdivArgs
      EvmAsm.Evm64.EvmWord.sdiv
    decide
  unfold runSDivStack?
  rw [EvmAsm.Evm64.SDivStackExecutionBridge.runSDivStack?_cons, h]


-- @@ L288-297 verbatim
theorem runSDivStack?_neg_neg_vector :
    runSDivStack? { stack := [(-9 : EvmWord), (-2 : EvmWord), 42] } =
      some { effects := { stackWords := [4] }, stack := [42] } := by
  have h : EvmAsm.Evm64.SDivArgs.sdivResultFromArgs
      (EvmAsm.Evm64.SDivArgs.sdivArgs (-9 : EvmWord) (-2 : EvmWord)) = (4 : EvmWord) := by
    unfold EvmAsm.Evm64.SDivArgs.sdivResultFromArgs EvmAsm.Evm64.SDivArgs.sdivArgs
      EvmAsm.Evm64.EvmWord.sdiv
    decide
  unfold runSDivStack?
  rw [EvmAsm.Evm64.SDivStackExecutionBridge.runSDivStack?_cons, h]


-- @@ L299-304 verbatim
theorem runSDivStack?_pos_neg_trunc_vector :
    runSDivStack? { stack := [(7 : EvmWord), (-2 : EvmWord), 42] } =
      some { effects := { stackWords := [(-3 : EvmWord)] }, stack := [42] } := by
  simpa using
    EvmAsm.Evm64.SDivStackExecutionBridge.runSDivStack?_pos_neg_trunc
      [(42 : EvmWord)]


-- @@ L306-307 verbatim
theorem runSDivStack?_underflow_vector :
    runSDivStack? { stack := [(7 : EvmWord)] } = none := rfl


-- @@ L309-314 verbatim
theorem runSModStack?_zero_divisor_vector :
    runSModStack? { stack := [(9 : EvmWord), 0, 42] } =
      some { effects := { stackWords := [0] }, stack := [42] } := by
  simpa using
    EvmAsm.Evm64.SModStackExecutionBridge.runSModStack?_zero_divisor
      (9 : EvmWord) [(42 : EvmWord)]


-- @@ L316-321 verbatim
theorem runSModStack?_neg_pos_sign_vector :
    runSModStack? { stack := [(-3 : EvmWord), 2, 42] } =
      some { effects := { stackWords := [(-1 : EvmWord)] }, stack := [42] } := by
  simpa using
    EvmAsm.Evm64.SModStackExecutionBridge.runSModStack?_neg_pos_sign
      [(42 : EvmWord)]


-- @@ L323-328 verbatim
theorem runSModStack?_pos_neg_sign_vector :
    runSModStack? { stack := [(3 : EvmWord), (-2 : EvmWord), 42] } =
      some { effects := { stackWords := [1] }, stack := [42] } := by
  simpa using
    EvmAsm.Evm64.SModStackExecutionBridge.runSModStack?_pos_neg_sign
      [(42 : EvmWord)]


-- @@ L330-331 verbatim
theorem runSModStack?_underflow_vector :
    runSModStack? { stack := [] } = none := rfl


-- @@ L333-339 verbatim
theorem sdivZeroDivisorVector_passed :
    checkVector? runSDivStack? sdivZeroDivisorVector = .passed :=
  checkVector?_some_passed runSDivStack?
    "sdiv-stack-zero-divisor"
    { stack := [(9 : EvmWord), 0, 42] }
    { effects := { stackWords := [0] }, stack := [(42 : EvmWord)] }
    runSDivStack?_zero_divisor_vector


-- @@ L341-347 verbatim
theorem sdivIntMinNegOneVector_passed :
    checkVector? runSDivStack? sdivIntMinNegOneVector = .passed :=
  checkVector?_some_passed runSDivStack?
    "sdiv-stack-int-min-neg-one"
    { stack := [BitVec.intMin 256, (-1 : EvmWord), 42] }
    { effects := { stackWords := [BitVec.intMin 256] }, stack := [(42 : EvmWord)] }
    runSDivStack?_intMin_neg_one_vector


-- @@ L349-355 verbatim
theorem sdivPosPosVector_passed :
    checkVector? runSDivStack? sdivPosPosVector = .passed :=
  checkVector?_some_passed runSDivStack?
    "sdiv-stack-pos-pos"
    { stack := [(9 : EvmWord), (2 : EvmWord), 42] }
    { effects := { stackWords := [4] }, stack := [(42 : EvmWord)] }
    runSDivStack?_pos_pos_vector


-- @@ L357-363 verbatim
theorem sdivNegNegVector_passed :
    checkVector? runSDivStack? sdivNegNegVector = .passed :=
  checkVector?_some_passed runSDivStack?
    "sdiv-stack-neg-neg"
    { stack := [(-9 : EvmWord), (-2 : EvmWord), 42] }
    { effects := { stackWords := [4] }, stack := [(42 : EvmWord)] }
    runSDivStack?_neg_neg_vector


-- @@ L365-371 verbatim
theorem sdivPosNegTruncVector_passed :
    checkVector? runSDivStack? sdivPosNegTruncVector = .passed :=
  checkVector?_some_passed runSDivStack?
    "sdiv-stack-pos-neg-trunc"
    { stack := [(7 : EvmWord), (-2 : EvmWord), 42] }
    { effects := { stackWords := [(-3 : EvmWord)] }, stack := [(42 : EvmWord)] }
    runSDivStack?_pos_neg_trunc_vector


-- @@ L373-380 verbatim
theorem sdivUnderflowVector_passed :
    checkVector? runSDivStack? sdivUnderflowVector =
      .errored "sdiv-stack-underflow" "stack-underflow" :=
  checkVector?_none_error runSDivStack?
    "sdiv-stack-underflow"
    "stack-underflow"
    { stack := [(7 : EvmWord)] }
    runSDivStack?_underflow_vector


-- @@ L382-388 verbatim
theorem smodZeroDivisorVector_passed :
    checkVector? runSModStack? smodZeroDivisorVector = .passed :=
  checkVector?_some_passed runSModStack?
    "smod-stack-zero-divisor"
    { stack := [(9 : EvmWord), 0, 42] }
    { effects := { stackWords := [0] }, stack := [(42 : EvmWord)] }
    runSModStack?_zero_divisor_vector


-- @@ L390-396 verbatim
theorem smodNegPosSignVector_passed :
    checkVector? runSModStack? smodNegPosSignVector = .passed :=
  checkVector?_some_passed runSModStack?
    "smod-stack-neg-pos-sign"
    { stack := [(-3 : EvmWord), 2, 42] }
    { effects := { stackWords := [(-1 : EvmWord)] }, stack := [(42 : EvmWord)] }
    runSModStack?_neg_pos_sign_vector


-- @@ L398-404 verbatim
theorem smodPosNegSignVector_passed :
    checkVector? runSModStack? smodPosNegSignVector = .passed :=
  checkVector?_some_passed runSModStack?
    "smod-stack-pos-neg-sign"
    { stack := [(3 : EvmWord), (-2 : EvmWord), 42] }
    { effects := { stackWords := [1] }, stack := [(42 : EvmWord)] }
    runSModStack?_pos_neg_sign_vector


-- @@ L406-413 verbatim
theorem smodUnderflowVector_passed :
    checkVector? runSModStack? smodUnderflowVector =
      .errored "smod-stack-underflow" "stack-underflow" :=
  checkVector?_none_error runSModStack?
    "smod-stack-underflow"
    "stack-underflow"
    { stack := [] }
    runSModStack?_underflow_vector


-- @@ L415-420 verbatim
/-- Compact checked-vector batch for signed arithmetic stack execution.
    Distinctive token:
    SignedArithmeticStackExecutionConformance.signedArithmeticConformanceVectors #90 #125. -/
def signedArithmeticConformanceVectors : List CheckResult :=
  checkBatch? runSDivStack? sdivStackConformanceTestVectors ++
    checkBatch? runSModStack? smodStackConformanceTestVectors


-- @@ L422-441 verbatim
theorem signedArithmeticConformanceVectors_passed :
    signedArithmeticConformanceVectors =
      [ .passed
      , .passed
      , .passed
      , .passed
      , .passed
      , .errored "sdiv-stack-underflow" "stack-underflow"
      , .passed
      , .passed
      , .passed
      , .errored "smod-stack-underflow" "stack-underflow"
      ] := by
  simp [signedArithmeticConformanceVectors, sdivZeroDivisorVector_passed,
    sdivStackConformanceTestVectors, smodStackConformanceTestVectors,
    sdivIntMinNegOneVector_passed, sdivPosPosVector_passed,
    sdivNegNegVector_passed, sdivPosNegTruncVector_passed,
    sdivUnderflowVector_passed, smodZeroDivisorVector_passed,
    smodNegPosSignVector_passed, smodPosNegSignVector_passed,
    smodUnderflowVector_passed]


-- @@ L443-443 verbatim
end SignedArithmeticStackExecution

-- @@ L444-444 verbatim
end Conformance

-- @@ L445-445 verbatim
end EvmAsm.EL
