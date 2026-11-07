/-
  EvmAsm.Stateless.SpecRef.WideFeeArithmetic

  The unbounded fee arithmetic used by the Amsterdam reference.  The guest
  still has a fixed-width implementation until the atomic Stage 3 change,
  so this file deliberately does not change routing or acceptance.  It gives
  that change one semantic vocabulary: canonical variable-width values for
  base-fee recurrence, EIP-1559 pricing, gas debits, fee credits, and
  GASPRICE.
-/

module

public import EvmAsm.EL.RLP.VariableUint
public import EvmAsm.Stateless.SpecRef.Gas
public import EvmAsm.Stateless.SpecRef.SeamShell
public import Mathlib.Tactic.NormNum
meta import EvmAsm.EL.RLP.VariableUint
meta import EvmAsm.Stateless.SpecRef.Gas
meta import EvmAsm.Stateless.SpecRef.SeamShell
meta import Mathlib.Tactic.NormNum


-- @@ L23-23 verbatim
@[expose] public section


-- @@ L25-25 verbatim
namespace EvmAsm.Stateless.SpecRef


-- @@ L27-27 verbatim
open EvmAsm.EL.RLP


-- @@ L29-29 verbatim
/-! ## Base-fee recurrence -/


-- @@ L31-32 verbatim
def baseFeeIncreaseDelta (parentFee gasUsedDelta target : Uint) : Uint :=
  max ((parentFee * gasUsedDelta / target) / 8) 1


-- @@ L34-35 verbatim
def baseFeeDecreaseDelta (parentFee gasUsedDelta target : Uint) : Uint :=
  (parentFee * gasUsedDelta / target) / 8


-- @@ L37-45 verbatim
def baseFeeRecurrenceWide (parentGasUsed parentGasTarget parentFee : Uint) : Uint :=
  if parentGasUsed == parentGasTarget then
    parentFee
  else if parentGasUsed > parentGasTarget then
    parentFee + baseFeeIncreaseDelta parentFee
      (parentGasUsed - parentGasTarget) parentGasTarget
  else
    parentFee - baseFeeDecreaseDelta parentFee
      (parentGasTarget - parentGasUsed) parentGasTarget


-- @@ L47-49 verbatim
def calculateBaseFeeWide (blockGasLimit parentGasLimit parentGasUsed parentFee : Uint) :
    Except SpecError Uint :=
  calculate_base_fee_per_gas blockGasLimit parentGasLimit parentGasUsed parentFee


-- @@ L51-54 verbatim
theorem baseFeeIncreaseDelta_eq_reference (parentFee gasUsedDelta target : Uint) :
    baseFeeIncreaseDelta parentFee gasUsedDelta target =
      max ((parentFee * gasUsedDelta / target) / 8) 1 := by
  rfl


-- @@ L56-59 verbatim
theorem baseFeeDecreaseDelta_eq_reference (parentFee gasUsedDelta target : Uint) :
    baseFeeDecreaseDelta parentFee gasUsedDelta target =
      (parentFee * gasUsedDelta / target) / 8 := by
  rfl


-- @@ L61-65 verbatim
theorem calculateBaseFeeWide_eq_reference
    (blockGasLimit parentGasLimit parentGasUsed parentFee : Uint) :
    calculateBaseFeeWide blockGasLimit parentGasLimit parentGasUsed parentFee =
    calculate_base_fee_per_gas blockGasLimit parentGasLimit parentGasUsed parentFee := by
  rfl


-- @@ L67-67 verbatim
/-! ## EIP-1559 pricing -/


-- @@ L69-73 verbatim
def priorityFeeWide (maxPriority maxFee baseFee : RlpUint) : Option RlpUint :=
  if maxFee.value < baseFee.value then
    none
  else
    some (RlpUint.ofNat (min maxPriority.value (maxFee.value - baseFee.value)))


-- @@ L75-77 verbatim
def effectiveGasPriceWide (maxPriority maxFee baseFee : RlpUint) : Option RlpUint := do
  let priority ← priorityFeeWide maxPriority maxFee baseFee
  pure (RlpUint.ofNat (baseFee.value + priority.value))


-- @@ L79-80 verbatim
def legacyGasPriceWide (gasPrice baseFee : RlpUint) : Option RlpUint :=
  if gasPrice.value < baseFee.value then none else some gasPrice


-- @@ L82-83 verbatim
def maxGasFeeWide (gas : Uint) (maxFee : RlpUint) : Uint :=
  gas * maxFee.value


-- @@ L85-86 verbatim
def gasDebitWide (gasUsed : Uint) (effectivePrice : RlpUint) : Uint :=
  gasUsed * effectivePrice.value


-- @@ L88-89 verbatim
def feeCreditWide (gasUsed : Uint) (priority : RlpUint) : Uint :=
  gasUsed * priority.value


-- @@ L91-92 verbatim
def gasPriceWide (maxPriority maxFee baseFee : RlpUint) : Option RlpUint :=
  effectiveGasPriceWide maxPriority maxFee baseFee


-- @@ L94-100 verbatim
theorem priorityFeeWide_value
    (maxPriority maxFee baseFee : RlpUint) :
    (priorityFeeWide maxPriority maxFee baseFee).map RlpUint.value =
      if maxFee.value < baseFee.value then none
      else some (min maxPriority.value (maxFee.value - baseFee.value)) := by
  unfold priorityFeeWide
  split <;> simp


-- @@ L102-109 verbatim
theorem effectiveGasPriceWide_value
    (maxPriority maxFee baseFee : RlpUint) :
    (effectiveGasPriceWide maxPriority maxFee baseFee).map RlpUint.value =
      if maxFee.value < baseFee.value then none
      else some (baseFee.value +
        min maxPriority.value (maxFee.value - baseFee.value)) := by
  unfold effectiveGasPriceWide priorityFeeWide
  split <;> simp [RlpUint.ofNat_value]


-- @@ L111-115 verbatim
theorem legacyGasPriceWide_value (gasPrice baseFee : RlpUint) :
    (legacyGasPriceWide gasPrice baseFee).map RlpUint.value =
      if gasPrice.value < baseFee.value then none else some gasPrice.value := by
  unfold legacyGasPriceWide
  split <;> simp


-- @@ L117-119 verbatim
theorem gasPriceWide_eq_effective :
    gasPriceWide = effectiveGasPriceWide := by
  rfl


-- @@ L121-125 verbatim
/-! ## Constructive boundary examples

The 33-byte value is accepted by the wide surface and is deliberately not
projected through `RlpUint.toU256?`.  The other vectors cover the priority,
effective-price, debit, and fee-credit branches used by the machine seam. -/


-- @@ L127-129 verbatim
def wideFee256 : RlpUint :=
  ⟨(1 : Byte) :: List.replicate 32 0, by
    simp [isCanonicalUintContent]⟩


-- @@ L131-132 verbatim
theorem wideFee256_width : wideFee256.width = 33 := by
  simp [wideFee256, RlpUint.width]


-- @@ L134-135 verbatim
theorem wideFee256_value : wideFee256.value = 2 ^ 256 := by
  simp [wideFee256, RlpUint.value, Nat.fromBytesBE]


-- @@ L137-157 verbatim
theorem wideFee256_not_u256 : ¬ wideFee256.fitsU256 := by
  unfold RlpUint.fitsU256 RlpUint.width
  simp [wideFee256]

#guard wideFee256.width == 33
#guard wideFee256.value == 2 ^ 256
#guard (priorityFeeWide (RlpUint.ofNat 2) (RlpUint.ofNat 100)
    (RlpUint.ofNat 10)).map RlpUint.value == some 2
#guard (priorityFeeWide (RlpUint.ofNat 200) (RlpUint.ofNat 100)
    (RlpUint.ofNat 10)).map RlpUint.value == some 90
#guard (priorityFeeWide (RlpUint.ofNat 2) (RlpUint.ofNat 9)
    (RlpUint.ofNat 10)).isNone
#guard (effectiveGasPriceWide (RlpUint.ofNat 2) (RlpUint.ofNat 100)
    (RlpUint.ofNat 10)).map RlpUint.value == some 12
#guard (legacyGasPriceWide (RlpUint.ofNat 100) (RlpUint.ofNat 10)).map
    RlpUint.value == some 100
#guard gasDebitWide 21000 (RlpUint.ofNat 12) == 252000
#guard feeCreditWide 21000 (RlpUint.ofNat 2) == 42000
#guard baseFeeRecurrenceWide 15000000 15000000 1000000000 == 1000000000
#guard baseFeeRecurrenceWide 30000000 15000000 1000000000 == 1125000000
#guard baseFeeRecurrenceWide 0 15000000 1000000000 == 875000000


-- @@ L159-159 verbatim
end EvmAsm.Stateless.SpecRef
