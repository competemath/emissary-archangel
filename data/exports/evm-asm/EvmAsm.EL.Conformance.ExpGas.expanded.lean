/-
  EvmAsm.EL.Conformance.ExpGas

  Lean-side conformance vectors for EXP exponent-byte gas accounting
  (GH #125, exercising the GH #92 executable helper).
-/

module

public import EvmAsm.EL.Conformance
public import EvmAsm.Evm64.Exp.Gas


-- @@ L13-13 verbatim
@[expose] public section


-- @@ L15-15 verbatim
namespace EvmAsm.EL

-- @@ L16-16 verbatim
namespace Conformance

-- @@ L17-17 verbatim
namespace ExpGas


-- @@ L19-19 verbatim
abbrev EvmWord := EvmAsm.Evm64.EvmWord


-- @@ L21-24 verbatim
/-- Input shape for an EXP gas executable-helper conformance vector. -/
structure ExpGasInput where
  exponent : EvmWord
  deriving Repr


-- @@ L26-27 verbatim
def runExpGas (input : ExpGasInput) : Nat :=
  EvmAsm.Evm64.ExpGas.expTotalGasFromExponent input.exponent


-- @@ L29-34 verbatim
/-- EXP with zero exponent charges only the static/base EXP gas.
    Distinctive token: expGasZeroExponentVector. -/
def expGasZeroExponentVector : TestVector ExpGasInput Nat :=
  { id := "exp-gas-zero-exponent"
    input := { exponent := 0 }
    expected := .value 10 }


-- @@ L36-40 verbatim
/-- A one-byte nonzero exponent adds one 50-gas exponent-byte charge. -/
def expGasOneByteExponentVector : TestVector ExpGasInput Nat :=
  { id := "exp-gas-one-byte-exponent"
    input := { exponent := 1 }
    expected := .value 60 }


-- @@ L42-47 verbatim
/-- Exponent 255 is the upper end of the one-byte exponent gas range.
    Distinctive token: exp-gas-one-byte-upper. -/
def expGasOneByteUpperVector : TestVector ExpGasInput Nat :=
  { id := "exp-gas-one-byte-upper"
    input := { exponent := 255 }
    expected := .value 60 }


-- @@ L49-53 verbatim
/-- Exponent 256 is the first two-byte threshold and charges 10 + 2 * 50. -/
def expGasTwoByteThresholdVector : TestVector ExpGasInput Nat :=
  { id := "exp-gas-two-byte-threshold"
    input := { exponent := 256 }
    expected := .value 110 }


-- @@ L55-59 verbatim
/-- The maximum 256-bit exponent occupies all 32 bytes. -/
def expGasMaxExponentVector : TestVector ExpGasInput Nat :=
  { id := "exp-gas-max-exponent"
    input := { exponent := -1 }
    expected := .value 1610 }


-- @@ L61-63 verbatim
theorem runExpGas_zero :
    runExpGas { exponent := (0 : EvmWord) } = 10 :=
  EvmAsm.Evm64.ExpGas.expTotalGasFromExponent_zero


-- @@ L65-68 verbatim
theorem runExpGas_one :
    runExpGas { exponent := (1 : EvmWord) } = 60 :=
  EvmAsm.Evm64.ExpGas.expTotalGasFromExponent_of_pos_lt_256
    (by decide) (by decide)


-- @@ L70-73 verbatim
theorem runExpGas_255 :
    runExpGas { exponent := (255 : EvmWord) } = 60 :=
  EvmAsm.Evm64.ExpGas.expTotalGasFromExponent_of_pos_lt_256
    (by decide) (by decide)


-- @@ L75-77 verbatim
theorem runExpGas_256 :
    runExpGas { exponent := (256 : EvmWord) } = 110 :=
  EvmAsm.Evm64.ExpGas.expTotalGasFromExponent_256


-- @@ L79-81 verbatim
theorem runExpGas_max :
    runExpGas { exponent := (-1 : EvmWord) } = 1610 :=
  EvmAsm.Evm64.ExpGas.expTotalGasFromExponent_max


-- @@ L83-89 verbatim
theorem expGasZeroExponentVector_passed :
    checkVector runExpGas expGasZeroExponentVector = .passed :=
  checkVector_value_passed runExpGas
    "exp-gas-zero-exponent"
    { exponent := (0 : EvmWord) }
    10
    runExpGas_zero


-- @@ L91-97 verbatim
theorem expGasOneByteExponentVector_passed :
    checkVector runExpGas expGasOneByteExponentVector = .passed :=
  checkVector_value_passed runExpGas
    "exp-gas-one-byte-exponent"
    { exponent := (1 : EvmWord) }
    60
    runExpGas_one


-- @@ L99-105 verbatim
theorem expGasOneByteUpperVector_passed :
    checkVector runExpGas expGasOneByteUpperVector = .passed :=
  checkVector_value_passed runExpGas
    "exp-gas-one-byte-upper"
    { exponent := (255 : EvmWord) }
    60
    runExpGas_255


-- @@ L107-113 verbatim
theorem expGasTwoByteThresholdVector_passed :
    checkVector runExpGas expGasTwoByteThresholdVector = .passed :=
  checkVector_value_passed runExpGas
    "exp-gas-two-byte-threshold"
    { exponent := (256 : EvmWord) }
    110
    runExpGas_256


-- @@ L115-121 verbatim
theorem expGasMaxExponentVector_passed :
    checkVector runExpGas expGasMaxExponentVector = .passed :=
  checkVector_value_passed runExpGas
    "exp-gas-max-exponent"
    { exponent := (-1 : EvmWord) }
    1610
    runExpGas_max


-- @@ L123-131 verbatim
/-- Vector IDs for EXP gas executable-helper conformance coverage.
    Distinctive token: expGasConformanceVectorIds #125 #92. -/
def expGasConformanceVectorIds : List String :=
  [ expGasZeroExponentVector.id
  , expGasOneByteExponentVector.id
  , expGasOneByteUpperVector.id
  , expGasTwoByteThresholdVector.id
  , expGasMaxExponentVector.id
  ]


-- @@ L133-140 verbatim
theorem expGasConformanceVectorIds_eq :
    expGasConformanceVectorIds =
      [ "exp-gas-zero-exponent"
      , "exp-gas-one-byte-exponent"
      , "exp-gas-one-byte-upper"
      , "exp-gas-two-byte-threshold"
      , "exp-gas-max-exponent"
      ] := rfl


-- @@ L142-143 verbatim
theorem expGasConformanceVectorIds_length :
    expGasConformanceVectorIds.length = 5 := rfl


-- @@ L145-147 verbatim
theorem expGasConformanceVectorIds_nodup :
    expGasConformanceVectorIds.Nodup := by
  decide


-- @@ L149-157 verbatim
/-- Compact checked-vector batch for EXP gas executable helpers.
    Distinctive token: expGasConformanceVectors. -/
def expGasConformanceVectors : List CheckResult :=
  [ checkVector runExpGas expGasZeroExponentVector
  , checkVector runExpGas expGasOneByteExponentVector
  , checkVector runExpGas expGasOneByteUpperVector
  , checkVector runExpGas expGasTwoByteThresholdVector
  , checkVector runExpGas expGasMaxExponentVector
  ]


-- @@ L159-163 verbatim
theorem expGasConformanceVectors_passed :
    expGasConformanceVectors = [.passed, .passed, .passed, .passed, .passed] := by
  simp [expGasConformanceVectors, expGasZeroExponentVector_passed,
    expGasOneByteExponentVector_passed, expGasOneByteUpperVector_passed,
    expGasTwoByteThresholdVector_passed, expGasMaxExponentVector_passed]


-- @@ L165-165 verbatim
end ExpGas

-- @@ L166-166 verbatim
end Conformance

-- @@ L167-167 verbatim
end EvmAsm.EL
