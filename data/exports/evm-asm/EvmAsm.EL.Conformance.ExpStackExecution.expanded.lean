/-
  EvmAsm.EL.Conformance.ExpStackExecution

  Lean-side conformance vectors for the EXP stack execution bridge
  (GH #92 / GH #125).
-/

module

public import EvmAsm.EL.Conformance
public import EvmAsm.Evm64.Exp.StackExecutionBridge


-- @@ L13-13 verbatim
@[expose] public section


-- @@ L15-15 verbatim
namespace EvmAsm.EL

-- @@ L16-16 verbatim
namespace Conformance

-- @@ L17-17 verbatim
namespace ExpStackExecution


-- @@ L19-19 verbatim
abbrev EvmWord := EvmAsm.Evm64.EvmWord


-- @@ L21-21 verbatim
abbrev ExpStackState := EvmAsm.Evm64.ExpStackExecutionBridge.ExpStackState


-- @@ L23-23 verbatim
abbrev ExpStackResult := EvmAsm.Evm64.ExpStackExecutionBridge.ExpStackResult


-- @@ L25-26 verbatim
abbrev ExpVisibleEffects :=
  EvmAsm.Evm64.ExpStackExecutionBridge.ExpVisibleEffects


-- @@ L28-29 verbatim
deriving instance DecidableEq for
  EvmAsm.Evm64.ExpStackExecutionBridge.ExpVisibleEffects


-- @@ L31-32 verbatim
deriving instance DecidableEq for
  EvmAsm.Evm64.ExpStackExecutionBridge.ExpStackResult


-- @@ L34-35 verbatim
def runExpStack? (input : ExpStackState) : Option ExpStackResult :=
  EvmAsm.Evm64.ExpStackExecutionBridge.runExpStack? input


-- @@ L37-47 verbatim
/-- EXP with stack [2, 8, 99] returns 256 on top of [99]. -/
def expStackValueVector : TestVector ExpStackState ExpStackResult :=
  { id := "exp-stack-value"
    input := { stack := [2, 8, 99] }
    expected :=
      .value
        { effects :=
            { stackWords := [256]
              dynamicGas := 50
              totalGas := 60 }
          stack := [99] } }


-- @@ L49-59 verbatim
/-- EXP with zero base and zero exponent returns 1. -/
def expStackZeroZeroVector : TestVector ExpStackState ExpStackResult :=
  { id := "exp-stack-zero-zero"
    input := { stack := [0, 0, 99] }
    expected :=
      .value
        { effects :=
            { stackWords := [1]
              dynamicGas := 0
              totalGas := 10 }
          stack := [99] } }


-- @@ L61-72 verbatim
/-- EXP with max base and zero exponent returns one with no dynamic gas.
    Distinctive token: exp-stack-max-zero-exponent #92 #125. -/
def expStackMaxZeroExponentVector : TestVector ExpStackState ExpStackResult :=
  { id := "exp-stack-max-zero-exponent"
    input := { stack := [(-1 : EvmWord), 0, 99] }
    expected :=
      .value
        { effects :=
            { stackWords := [1]
              dynamicGas := 0
              totalGas := 10 }
          stack := [99] } }


-- @@ L74-85 verbatim
/-- EXP with exponent one returns the base word.
    Distinctive token: expStackOneExponentVector #92 #125. -/
def expStackOneExponentVector : TestVector ExpStackState ExpStackResult :=
  { id := "exp-stack-one-exponent"
    input := { stack := [7, 1, 99] }
    expected :=
      .value
        { effects :=
            { stackWords := [7]
              dynamicGas := 50
              totalGas := 60 }
          stack := [99] } }


-- @@ L87-98 verbatim
/-- EXP edge vector required by GH #92: `2^256 = 0 mod 2^256`.
    Distinctive token: expStackTwo256Vector #92 #125. -/
def expStackTwo256Vector : TestVector ExpStackState ExpStackResult :=
  { id := "exp-stack-two-256"
    input := { stack := [2, 256, 99] }
    expected :=
      .value
        { effects :=
            { stackWords := [0]
              dynamicGas := 100
              totalGas := 110 }
          stack := [99] } }


-- @@ L100-112 verbatim
/-- EXP with base one and max exponent returns one while charging max
    exponent-byte gas.
    Distinctive token: exp-stack-one-max-exponent #92 #125. -/
def expStackOneMaxExponentVector : TestVector ExpStackState ExpStackResult :=
  { id := "exp-stack-one-max-exponent"
    input := { stack := [1, (-1 : EvmWord), 99] }
    expected :=
      .value
        { effects :=
            { stackWords := [1]
              dynamicGas := 1600
              totalGas := 1610 }
          stack := [99] } }


-- @@ L114-123 verbatim
def expStackZeroOneVector : TestVector ExpStackState ExpStackResult :=
  { id := "exp-stack-zero-one"
    input := { stack := [0, 1, 99] }
    expected :=
      .value
        { effects :=
            { stackWords := [0]
              dynamicGas := 50
              totalGas := 60 }
          stack := [99] } }


-- @@ L125-134 verbatim
def expStackZeroMaxExponentVector : TestVector ExpStackState ExpStackResult :=
  { id := "exp-stack-zero-max-exponent"
    input := { stack := [0, (-1 : EvmWord), 99] }
    expected :=
      .value
        { effects :=
            { stackWords := [0]
              dynamicGas := 1600
              totalGas := 1610 }
          stack := [99] } }


-- @@ L136-145 verbatim
def expStackTwo128Vector : TestVector ExpStackState ExpStackResult :=
  { id := "exp-stack-two-128"
    input := { stack := [2, 128, 99] }
    expected :=
      .value
        { effects :=
            { stackWords := [BitVec.ofNat 256 (2^128)]
              dynamicGas := 50
              totalGas := 60 }
          stack := [99] } }


-- @@ L147-158 verbatim
/-- EXP with max base and exponent one returns the max word.
    Distinctive token: exp-stack-max-one-exponent #92 #125. -/
def expStackMaxOneExponentVector : TestVector ExpStackState ExpStackResult :=
  { id := "exp-stack-max-one-exponent"
    input := { stack := [(-1 : EvmWord), 1, 99] }
    expected :=
      .value
        { effects :=
            { stackWords := [(-1 : EvmWord)]
              dynamicGas := 50
              totalGas := 60 }
          stack := [99] } }


-- @@ L160-169 verbatim
def expStackTwo64Vector : TestVector ExpStackState ExpStackResult :=
  { id := "exp-stack-two-64"
    input := { stack := [2, 64, 99] }
    expected :=
      .value
        { effects :=
            { stackWords := [BitVec.ofNat 256 (2^64)]
              dynamicGas := 50
              totalGas := 60 }
          stack := [99] } }


-- @@ L171-180 verbatim
def expStackTwo255Vector : TestVector ExpStackState ExpStackResult :=
  { id := "exp-stack-two-255"
    input := { stack := [2, 255, 99] }
    expected :=
      .value
        { effects :=
            { stackWords := [BitVec.ofNat 256 (2^255)]
              dynamicGas := 50
              totalGas := 60 }
          stack := [99] } }


-- @@ L182-185 verbatim
def expStackUnderflowVector : TestVector ExpStackState ExpStackResult :=
  { id := "exp-stack-underflow"
    input := { stack := [2] }
    expected := .error "stack-underflow" }


-- @@ L187-204 verbatim
/-- EXP stack conformance inputs as reusable test vectors.
    Distinctive token:
    ExpStackExecutionConformance.expStackConformanceTestVectors #92 #125. -/
def expStackConformanceTestVectors : List (TestVector ExpStackState ExpStackResult) :=
  [ expStackValueVector
  , expStackZeroZeroVector
  , expStackMaxZeroExponentVector
  , expStackOneExponentVector
  , expStackTwo256Vector
  , expStackOneMaxExponentVector
  , expStackZeroOneVector
  , expStackZeroMaxExponentVector
  , expStackTwo128Vector
  , expStackMaxOneExponentVector
  , expStackTwo64Vector
  , expStackTwo255Vector
  , expStackUnderflowVector
  ]


-- @@ L206-207 verbatim
def expStackConformanceVectorIds : List String :=
  expStackConformanceTestVectors.map TestVector.id


-- @@ L209-210 verbatim
theorem expStackConformanceTestVectors_length :
    expStackConformanceTestVectors.length = 13 := rfl


-- @@ L212-227 verbatim
theorem expStackConformanceVectorIds_eq :
    expStackConformanceVectorIds =
      [ "exp-stack-value"
      , "exp-stack-zero-zero"
      , "exp-stack-max-zero-exponent"
      , "exp-stack-one-exponent"
      , "exp-stack-two-256"
      , "exp-stack-one-max-exponent"
      , "exp-stack-zero-one"
      , "exp-stack-zero-max-exponent"
      , "exp-stack-two-128"
      , "exp-stack-max-one-exponent"
      , "exp-stack-two-64"
      , "exp-stack-two-255"
      , "exp-stack-underflow"
      ] := rfl


-- @@ L229-230 verbatim
theorem expStackConformanceVectorIds_length :
    expStackConformanceVectorIds.length = 13 := rfl


-- @@ L232-234 verbatim
theorem expStackConformanceVectorIds_nodup :
    expStackConformanceVectorIds.Nodup := by
  decide


-- @@ L236-249 verbatim
def expStackValueVectorIds : List String :=
  [ "exp-stack-value"
  , "exp-stack-zero-zero"
  , "exp-stack-max-zero-exponent"
  , "exp-stack-one-exponent"
  , "exp-stack-two-256"
  , "exp-stack-one-max-exponent"
  , "exp-stack-zero-one"
  , "exp-stack-zero-max-exponent"
  , "exp-stack-two-128"
  , "exp-stack-max-one-exponent"
  , "exp-stack-two-64"
  , "exp-stack-two-255"
  ]


-- @@ L251-252 verbatim
def expStackErrorVectorIds : List String :=
  ["exp-stack-underflow"]


-- @@ L254-256 verbatim
theorem expStackValueVectorIds_subset_all :
    ∀ id ∈ expStackValueVectorIds, id ∈ expStackConformanceVectorIds := by
  decide


-- @@ L258-260 verbatim
theorem expStackErrorVectorIds_subset_all :
    ∀ id ∈ expStackErrorVectorIds, id ∈ expStackConformanceVectorIds := by
  decide


-- @@ L262-264 verbatim
theorem expStackValueVectorIds_no_error :
    ∀ id ∈ expStackValueVectorIds, id ∉ expStackErrorVectorIds := by
  decide


-- @@ L266-288 verbatim
theorem runExpStack?_value :
    runExpStack? { stack := [(2 : EvmWord), (8 : EvmWord), (99 : EvmWord)] } =
      some
        { effects :=
            { stackWords := [(256 : EvmWord)]
              dynamicGas := 50
              totalGas := 60 }
          stack := [(99 : EvmWord)] } := by
  change EvmAsm.Evm64.ExpStackExecutionBridge.runExpStack?
      { stack := [(2 : EvmWord), (8 : EvmWord), (99 : EvmWord)] } =
    some
      { effects :=
          { stackWords := [(256 : EvmWord)]
            dynamicGas := 50
            totalGas := 60 }
        stack := [(99 : EvmWord)] }
  rw [EvmAsm.Evm64.ExpStackExecutionBridge.runExpStack?_cons]
  simp only [EvmAsm.Evm64.ExpArgs.expResultFromArgs, EvmAsm.Evm64.ExpArgs.expArgs,
    EvmAsm.Evm64.ExpArgs.expDynamicCostFromArgs, EvmAsm.Evm64.ExpArgs.expTotalGasFromArgs]
  rw [show EvmAsm.Evm64.EvmWord.exp (2 : EvmWord) (8 : EvmWord) = (256 : EvmWord) from by
    apply BitVec.eq_of_toNat_eq; rw [EvmAsm.Evm64.EvmWord.exp_correct]; decide]
  rw [EvmAsm.Evm64.ExpGas.expDynamicCostFromExponent_of_pos_lt_256 (by decide) (by decide)]
  rw [EvmAsm.Evm64.ExpGas.expTotalGasFromExponent_of_pos_lt_256 (by decide) (by decide)]


-- @@ L290-299 verbatim
theorem runExpStack?_zero_zero :
    runExpStack? { stack := [(0 : EvmWord), (0 : EvmWord), (99 : EvmWord)] } =
      some
        { effects :=
            { stackWords := [(1 : EvmWord)]
              dynamicGas := 0
              totalGas := 10 }
          stack := [(99 : EvmWord)] } := by
  exact EvmAsm.Evm64.ExpStackExecutionBridge.runExpStack?_zero_zero
    [(99 : EvmWord)]


-- @@ L301-319 verbatim
theorem runExpStack?_max_zero_exponent :
    runExpStack?
        { stack := [(-1 : EvmWord), (0 : EvmWord), (99 : EvmWord)] } =
      some
        { effects :=
            { stackWords := [(1 : EvmWord)]
              dynamicGas := 0
              totalGas := 10 }
          stack := [(99 : EvmWord)] } := by
  change EvmAsm.Evm64.ExpStackExecutionBridge.runExpStack?
      { stack := [(-1 : EvmWord), (0 : EvmWord), (99 : EvmWord)] } =
    some
      { effects :=
          { stackWords := [(1 : EvmWord)]
            dynamicGas := 0
            totalGas := 10 }
        stack := [(99 : EvmWord)] }
  exact EvmAsm.Evm64.ExpStackExecutionBridge.runExpStack?_max_zero_exponent
    [(99 : EvmWord)]


-- @@ L321-330 verbatim
theorem runExpStack?_one_exponent :
    runExpStack? { stack := [(7 : EvmWord), (1 : EvmWord), (99 : EvmWord)] } =
      some
        { effects :=
            { stackWords := [(7 : EvmWord)]
              dynamicGas := 50
              totalGas := 60 }
          stack := [(99 : EvmWord)] } := by
  exact EvmAsm.Evm64.ExpStackExecutionBridge.runExpStack?_one_exponent 7
    [(99 : EvmWord)]


-- @@ L332-340 verbatim
theorem runExpStack?_two_256 :
    runExpStack? { stack := [(2 : EvmWord), (256 : EvmWord), (99 : EvmWord)] } =
      some
        { effects :=
            { stackWords := [(0 : EvmWord)]
              dynamicGas := 100
              totalGas := 110 }
          stack := [(99 : EvmWord)] } := by
  exact EvmAsm.Evm64.ExpStackExecutionBridge.runExpStack?_two_256 [(99 : EvmWord)]


-- @@ L342-361 verbatim
theorem runExpStack?_one_max_exponent :
    runExpStack?
        { stack := [(1 : EvmWord), (-1 : EvmWord), (99 : EvmWord)] } =
      some
        { effects :=
            { stackWords := [(1 : EvmWord)]
              dynamicGas := 1600
              totalGas := 1610 }
          stack := [(99 : EvmWord)] } := by
  change EvmAsm.Evm64.ExpStackExecutionBridge.runExpStack?
      { stack := [(1 : EvmWord), (-1 : EvmWord), (99 : EvmWord)] } =
    some
      { effects :=
          { stackWords := [(1 : EvmWord)]
            dynamicGas := 1600
            totalGas := 1610 }
        stack := [(99 : EvmWord)] }
  rw [EvmAsm.Evm64.ExpStackExecutionBridge.runExpStack?_one_left]
  rw [EvmAsm.Evm64.ExpArgs.expDynamicCostFromArgs_max_exponent]
  rw [EvmAsm.Evm64.ExpArgs.expTotalGasFromArgs_max_exponent]


-- @@ L363-372 verbatim
theorem runExpStack?_zero_one :
    runExpStack? { stack := [(0 : EvmWord), (1 : EvmWord), (99 : EvmWord)] } =
      some
        { effects :=
            { stackWords := [(0 : EvmWord)]
              dynamicGas := 50
              totalGas := 60 }
          stack := [(99 : EvmWord)] } := by
  exact EvmAsm.Evm64.ExpStackExecutionBridge.runExpStack?_zero_one
    [(99 : EvmWord)]


-- @@ L374-384 verbatim
theorem runExpStack?_zero_max_exponent :
    runExpStack?
        { stack := [(0 : EvmWord), (-1 : EvmWord), (99 : EvmWord)] } =
      some
        { effects :=
            { stackWords := [(0 : EvmWord)]
              dynamicGas := 1600
              totalGas := 1610 }
          stack := [(99 : EvmWord)] } := by
  exact EvmAsm.Evm64.ExpStackExecutionBridge.runExpStack?_zero_max_exponent
    [(99 : EvmWord)]


-- @@ L386-394 verbatim
theorem runExpStack?_two_128 :
    runExpStack? { stack := [(2 : EvmWord), (128 : EvmWord), (99 : EvmWord)] } =
      some
        { effects :=
            { stackWords := [BitVec.ofNat 256 (2^128)]
              dynamicGas := 50
              totalGas := 60 }
          stack := [(99 : EvmWord)] } := by
  exact EvmAsm.Evm64.ExpStackExecutionBridge.runExpStack?_two_128 [(99 : EvmWord)]


-- @@ L396-414 verbatim
theorem runExpStack?_max_one_exponent :
    runExpStack?
        { stack := [(-1 : EvmWord), (1 : EvmWord), (99 : EvmWord)] } =
      some
        { effects :=
            { stackWords := [(-1 : EvmWord)]
              dynamicGas := 50
              totalGas := 60 }
          stack := [(99 : EvmWord)] } := by
  change EvmAsm.Evm64.ExpStackExecutionBridge.runExpStack?
      { stack := [(-1 : EvmWord), (1 : EvmWord), (99 : EvmWord)] } =
    some
      { effects :=
          { stackWords := [(-1 : EvmWord)]
            dynamicGas := 50
            totalGas := 60 }
        stack := [(99 : EvmWord)] }
  exact EvmAsm.Evm64.ExpStackExecutionBridge.runExpStack?_max_one_exponent
    [(99 : EvmWord)]


-- @@ L416-424 verbatim
theorem runExpStack?_two_64 :
    runExpStack? { stack := [(2 : EvmWord), (64 : EvmWord), (99 : EvmWord)] } =
      some
        { effects :=
            { stackWords := [BitVec.ofNat 256 (2^64)]
              dynamicGas := 50
              totalGas := 60 }
          stack := [(99 : EvmWord)] } := by
  exact EvmAsm.Evm64.ExpStackExecutionBridge.runExpStack?_two_64 [(99 : EvmWord)]


-- @@ L426-434 verbatim
theorem runExpStack?_two_255 :
    runExpStack? { stack := [(2 : EvmWord), (255 : EvmWord), (99 : EvmWord)] } =
      some
        { effects :=
            { stackWords := [BitVec.ofNat 256 (2^255)]
              dynamicGas := 50
              totalGas := 60 }
          stack := [(99 : EvmWord)] } := by
  exact EvmAsm.Evm64.ExpStackExecutionBridge.runExpStack?_two_255 [(99 : EvmWord)]


-- @@ L436-437 verbatim
theorem runExpStack?_underflow :
    runExpStack? { stack := [(2 : EvmWord)] } = none := rfl


-- @@ L439-449 verbatim
theorem expStackValueVector_passed :
    checkVector? runExpStack? expStackValueVector = .passed :=
  checkVector?_some_passed runExpStack?
    "exp-stack-value"
    { stack := [(2 : EvmWord), (8 : EvmWord), (99 : EvmWord)] }
    { effects :=
        { stackWords := [(256 : EvmWord)]
          dynamicGas := 50
          totalGas := 60 }
      stack := [(99 : EvmWord)] }
    runExpStack?_value


-- @@ L451-461 verbatim
theorem expStackZeroZeroVector_passed :
    checkVector? runExpStack? expStackZeroZeroVector = .passed :=
  checkVector?_some_passed runExpStack?
    "exp-stack-zero-zero"
    { stack := [(0 : EvmWord), (0 : EvmWord), (99 : EvmWord)] }
    { effects :=
        { stackWords := [(1 : EvmWord)]
          dynamicGas := 0
          totalGas := 10 }
      stack := [(99 : EvmWord)] }
    runExpStack?_zero_zero


-- @@ L463-473 verbatim
theorem expStackMaxZeroExponentVector_passed :
    checkVector? runExpStack? expStackMaxZeroExponentVector = .passed :=
  checkVector?_some_passed runExpStack?
    "exp-stack-max-zero-exponent"
    { stack := [(-1 : EvmWord), (0 : EvmWord), (99 : EvmWord)] }
    { effects :=
        { stackWords := [(1 : EvmWord)]
          dynamicGas := 0
          totalGas := 10 }
      stack := [(99 : EvmWord)] }
    runExpStack?_max_zero_exponent


-- @@ L475-485 verbatim
theorem expStackOneExponentVector_passed :
    checkVector? runExpStack? expStackOneExponentVector = .passed :=
  checkVector?_some_passed runExpStack?
    "exp-stack-one-exponent"
    { stack := [(7 : EvmWord), (1 : EvmWord), (99 : EvmWord)] }
    { effects :=
        { stackWords := [(7 : EvmWord)]
          dynamicGas := 50
          totalGas := 60 }
      stack := [(99 : EvmWord)] }
    runExpStack?_one_exponent


-- @@ L487-497 verbatim
theorem expStackTwo256Vector_passed :
    checkVector? runExpStack? expStackTwo256Vector = .passed :=
  checkVector?_some_passed runExpStack?
    "exp-stack-two-256"
    { stack := [(2 : EvmWord), (256 : EvmWord), (99 : EvmWord)] }
    { effects :=
        { stackWords := [(0 : EvmWord)]
          dynamicGas := 100
          totalGas := 110 }
      stack := [(99 : EvmWord)] }
    runExpStack?_two_256


-- @@ L499-509 verbatim
theorem expStackOneMaxExponentVector_passed :
    checkVector? runExpStack? expStackOneMaxExponentVector = .passed :=
  checkVector?_some_passed runExpStack?
    "exp-stack-one-max-exponent"
    { stack := [(1 : EvmWord), (-1 : EvmWord), (99 : EvmWord)] }
    { effects :=
        { stackWords := [(1 : EvmWord)]
          dynamicGas := 1600
          totalGas := 1610 }
      stack := [(99 : EvmWord)] }
    runExpStack?_one_max_exponent


-- @@ L511-521 verbatim
theorem expStackZeroOneVector_passed :
    checkVector? runExpStack? expStackZeroOneVector = .passed :=
  checkVector?_some_passed runExpStack?
    "exp-stack-zero-one"
    { stack := [(0 : EvmWord), (1 : EvmWord), (99 : EvmWord)] }
    { effects :=
        { stackWords := [(0 : EvmWord)]
          dynamicGas := 50
          totalGas := 60 }
      stack := [(99 : EvmWord)] }
    runExpStack?_zero_one


-- @@ L523-533 verbatim
theorem expStackZeroMaxExponentVector_passed :
    checkVector? runExpStack? expStackZeroMaxExponentVector = .passed :=
  checkVector?_some_passed runExpStack?
    "exp-stack-zero-max-exponent"
    { stack := [(0 : EvmWord), (-1 : EvmWord), (99 : EvmWord)] }
    { effects :=
        { stackWords := [(0 : EvmWord)]
          dynamicGas := 1600
          totalGas := 1610 }
      stack := [(99 : EvmWord)] }
    runExpStack?_zero_max_exponent


-- @@ L535-545 verbatim
theorem expStackTwo128Vector_passed :
    checkVector? runExpStack? expStackTwo128Vector = .passed :=
  checkVector?_some_passed runExpStack?
    "exp-stack-two-128"
    { stack := [(2 : EvmWord), (128 : EvmWord), (99 : EvmWord)] }
    { effects :=
        { stackWords := [BitVec.ofNat 256 (2^128)]
          dynamicGas := 50
          totalGas := 60 }
      stack := [(99 : EvmWord)] }
    runExpStack?_two_128


-- @@ L547-557 verbatim
theorem expStackMaxOneExponentVector_passed :
    checkVector? runExpStack? expStackMaxOneExponentVector = .passed :=
  checkVector?_some_passed runExpStack?
    "exp-stack-max-one-exponent"
    { stack := [(-1 : EvmWord), (1 : EvmWord), (99 : EvmWord)] }
    { effects :=
        { stackWords := [(-1 : EvmWord)]
          dynamicGas := 50
          totalGas := 60 }
      stack := [(99 : EvmWord)] }
    runExpStack?_max_one_exponent


-- @@ L559-569 verbatim
theorem expStackTwo64Vector_passed :
    checkVector? runExpStack? expStackTwo64Vector = .passed :=
  checkVector?_some_passed runExpStack?
    "exp-stack-two-64"
    { stack := [(2 : EvmWord), (64 : EvmWord), (99 : EvmWord)] }
    { effects :=
        { stackWords := [BitVec.ofNat 256 (2^64)]
          dynamicGas := 50
          totalGas := 60 }
      stack := [(99 : EvmWord)] }
    runExpStack?_two_64


-- @@ L571-581 verbatim
theorem expStackTwo255Vector_passed :
    checkVector? runExpStack? expStackTwo255Vector = .passed :=
  checkVector?_some_passed runExpStack?
    "exp-stack-two-255"
    { stack := [(2 : EvmWord), (255 : EvmWord), (99 : EvmWord)] }
    { effects :=
        { stackWords := [BitVec.ofNat 256 (2^255)]
          dynamicGas := 50
          totalGas := 60 }
      stack := [(99 : EvmWord)] }
    runExpStack?_two_255


-- @@ L583-590 verbatim
theorem expStackUnderflowVector_passed :
    checkVector? runExpStack? expStackUnderflowVector =
      .errored "exp-stack-underflow" "stack-underflow" :=
  checkVector?_none_error runExpStack?
    "exp-stack-underflow"
    "stack-underflow"
    { stack := [(2 : EvmWord)] }
    runExpStack?_underflow


-- @@ L592-595 verbatim
/-- Compact checked-vector batch for EXP stack execution.
    Distinctive token: ExpStackExecutionConformance.expStackConformanceVectors #92 #125. -/
def expStackConformanceVectors : List CheckResult :=
  checkBatch? runExpStack? expStackConformanceTestVectors


-- @@ L597-624 verbatim
theorem expStackConformanceVectors_passed :
    expStackConformanceVectors =
      [ .passed
      , .passed
      , .passed
      , .passed
      , .passed
      , .passed
      , .passed
      , .passed
      , .passed
      , .passed
      , .passed
      , .passed
      , .errored "exp-stack-underflow" "stack-underflow"
      ] := by
  simp [expStackConformanceVectors, expStackConformanceTestVectors,
    expStackValueVector_passed, expStackZeroZeroVector_passed,
    expStackMaxZeroExponentVector_passed,
    expStackOneExponentVector_passed,
    expStackTwo256Vector_passed,
    expStackOneMaxExponentVector_passed,
    expStackZeroOneVector_passed,
    expStackZeroMaxExponentVector_passed,
    expStackMaxOneExponentVector_passed,
    expStackTwo128Vector_passed, expStackTwo64Vector_passed,
    expStackTwo255Vector_passed,
    expStackUnderflowVector_passed]


-- @@ L626-626 verbatim
end ExpStackExecution

-- @@ L627-627 verbatim
end Conformance

-- @@ L628-628 verbatim
end EvmAsm.EL
