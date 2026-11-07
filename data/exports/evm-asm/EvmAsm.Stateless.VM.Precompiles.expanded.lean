/-
  EvmAsm.Stateless.VM.Precompiles

  Dispatch and pure framing helpers for precompile addresses
  (0x01..0x14 + 0x100 for P256VERIFY).

  ## Implementation status

  Per the project plan (see `~/.claude/plans/please-cut-a-branch-warm-wand.md`
  and `PLAN.md` "Stateless Guest"), precompile dispatch started as
  an unimplemented frontier:

  - ECRECOVER, SHA-256, RIPEMD-160, IDENTITY, MODEXP
  - ALT_BN128 ADD / MUL / PAIRING (BN254)
  - BLAKE2F
  - POINT_EVALUATION (EIP-4844 KZG)
  - BLS12-381 G1/G2 ADD/MSM, PAIRING, MAP
  - SECP256R1_VERIFY (P256)

  Unsupported concrete call sites still trigger `REASON_PRECOMPILE + addr`
  per the reason-code table in `Stateless/Unimplemented.lean`. Implemented
  slices in this file expose pure EVM return-data/gas framing first, then
  later CALL/STATICCALL wiring can call those helpers.

  ## What's NOT in this file

  Hashes needed for **block processing** (KECCAK256 for header
  hashing, MPT, code hashing, tx hashing, address derivation;
  SHA-256 for SSZ Merkleization of the output) are bridged
  separately and do NOT route through this file. They live in
  `EvmAsm/EL/Keccak*EcallBridge.lean` (existing) and
  `EvmAsm/Stateless/Bridges/Sha256EcallBridge.lean` (scaffolded
  in PR-K12). See `docs/execution-specs-feedback.md` #1 for the
  cost-picture discussion.

-/

module

public import EvmAsm.EL.Bn254G1AddEcallBridge
public import EvmAsm.EL.Bn254G1MulEcallBridge
public import EvmAsm.EL.Bn254PairingEcallBridge
public import EvmAsm.EL.Bls12G1MsmEcallBridge
public import EvmAsm.EL.Bls12G2MsmEcallBridge
public import EvmAsm.EL.Bls12PairingEcallBridge
public import EvmAsm.EL.Bls12MapFpToG1EcallBridge
public import EvmAsm.EL.Bls12MapFp2ToG2EcallBridge
public import EvmAsm.EL.Bls12G1AddEcallBridge
public import EvmAsm.EL.Bls12G2AddEcallBridge
public import EvmAsm.EL.KzgPointEvalEcallBridge
public import EvmAsm.EL.ModexpEcallBridge
public import EvmAsm.EL.Secp256r1VerifyEcallBridge


-- @@ L54-54 verbatim
public section


-- @@ L56-56 verbatim
namespace EvmAsm.Stateless.VM.Precompiles


-- @@ L58-58 verbatim
abbrev Byte := EvmAsm.EL.Byte

-- @@ L59-59 verbatim
abbrev ByteList := List Byte

-- @@ L60-60 verbatim
abbrev ZkvmStatus := EvmAsm.Accelerators.ZkvmStatus


-- @@ L62-62 verbatim
namespace BN254


-- @@ L64-70 verbatim
/-- Gas constants for the BN254 precompiles at a fork. -/
structure GasSchedule where
  ecadd : Nat
  ecmul : Nat
  pairingBase : Nat
  pairingPerPoint : Nat
  deriving Repr


-- @@ L72-77 verbatim
/-- Byzantium gas schedule from execution-specs. -/
def byzantiumGasSchedule : GasSchedule :=
  { ecadd := 500
    ecmul := 40000
    pairingBase := 100000
    pairingPerPoint := 80000 }


-- @@ L79-84 verbatim
/-- Istanbul-and-later gas schedule, still current in Osaka/BPO forks. -/
def currentGasSchedule : GasSchedule :=
  { ecadd := 150
    ecmul := 6000
    pairingBase := 45000
    pairingPerPoint := 34000 }


-- @@ L86-87 verbatim
/-- BN254 G1 addition precompile address. -/
def addAddress : Nat := 0x06


-- @@ L89-90 verbatim
/-- BN254 G1 scalar multiplication precompile address. -/
def mulAddress : Nat := 0x07


-- @@ L92-93 verbatim
/-- BN254 pairing precompile address. -/
def pairingAddress : Nat := 0x08


-- @@ L95-96 verbatim
/-- BN254 add reads two 64-byte G1 points, with EVM `buffer_read` zero padding. -/
def addInputLength : Nat := 128


-- @@ L98-99 verbatim
/-- BN254 mul reads one 64-byte G1 point and one 32-byte scalar. -/
def mulInputLength : Nat := 96


-- @@ L101-102 verbatim
/-- BN254 pairing consumes 192-byte G1/G2 pairs. -/
def pairingPairLength : Nat := 192


-- @@ L104-108 verbatim
/-- `U256(1).to_be_bytes32()`. -/
-- `@[expose]`: an exported in-file lemma proves a value fact about this body by rfl.
@[expose]
def successWordOutput : ByteList :=
  List.replicate 31 (0 : Byte) ++ [1]


-- @@ L110-114 verbatim
/-- `U256(0).to_be_bytes32()`. -/
-- `@[expose]`: an exported in-file lemma proves a value fact about this body by rfl.
@[expose]
def zeroWordOutput : ByteList :=
  List.replicate 32 (0 : Byte)


-- @@ L116-119 verbatim
/-- Invalid point, malformed pairing length, or accelerator failure returns no bytes. -/
-- `@[expose]`: an exported in-file lemma proves a value fact about this body by rfl.
@[expose]
def emptyOutput : ByteList := []


-- @@ L121-125 verbatim
structure Result where
  status : ZkvmStatus
  output : ByteList
  gasCharged : Nat
  deriving Repr


-- @@ L127-127 verbatim
namespace Add


-- @@ L129-129 verbatim
abbrev MemoryReader := EvmAsm.EL.Bn254G1AddInputBridge.MemoryReader

-- @@ L130-130 verbatim
abbrev AcceleratorInput := EvmAsm.EL.Bn254G1AddInputBridge.AcceleratorInput

-- @@ L131-131 verbatim
abbrev AcceleratorOutput := EvmAsm.EL.Bn254G1AddResultBridge.AcceleratorOutput


-- @@ L133-136 verbatim
def acceleratorInputFromCallData (memory : MemoryReader) (dataStart : Nat) :
    AcceleratorInput :=
  EvmAsm.EL.Bn254G1AddInputBridge.bn254G1AddInputFromMemory
    memory dataStart (dataStart + 64)


-- @@ L138-149 verbatim
def execute
    (schedule : GasSchedule)
    (accelerator : AcceleratorInput → ZkvmStatus × AcceleratorOutput)
    (memory : MemoryReader) (dataStart : Nat) : Result :=
  let result := accelerator (acceleratorInputFromCallData memory dataStart)
  match result.1 with
  | .eok =>
      { status := result.1
        output := EvmAsm.EL.Bn254G1AddResultBridge.outputBytesList result.2
        gasCharged := schedule.ecadd }
  | .efail =>
      { status := result.1, output := emptyOutput, gasCharged := schedule.ecadd }


-- @@ L151-158 verbatim
@[simp] theorem execute_status
    (schedule : GasSchedule)
    (accelerator : AcceleratorInput → ZkvmStatus × AcceleratorOutput)
    (memory : MemoryReader) (dataStart : Nat) :
    (execute schedule accelerator memory dataStart).status =
      (accelerator (acceleratorInputFromCallData memory dataStart)).1 := by
  cases h_status : (accelerator (acceleratorInputFromCallData memory dataStart)).1 <;>
    simp [execute, h_status]


-- @@ L160-168 verbatim
@[simp] theorem execute_output_eok
    (schedule : GasSchedule)
    (accelerator : AcceleratorInput → ZkvmStatus × AcceleratorOutput)
    (memory : MemoryReader) (dataStart : Nat)
    (h_status : (accelerator (acceleratorInputFromCallData memory dataStart)).1 = .eok) :
    (execute schedule accelerator memory dataStart).output =
      EvmAsm.EL.Bn254G1AddResultBridge.outputBytesList
        (accelerator (acceleratorInputFromCallData memory dataStart)).2 := by
  simp [execute, h_status]


-- @@ L170-176 verbatim
@[simp] theorem execute_output_efail
    (schedule : GasSchedule)
    (accelerator : AcceleratorInput → ZkvmStatus × AcceleratorOutput)
    (memory : MemoryReader) (dataStart : Nat)
    (h_status : (accelerator (acceleratorInputFromCallData memory dataStart)).1 = .efail) :
    (execute schedule accelerator memory dataStart).output = emptyOutput := by
  simp [execute, h_status]


-- @@ L178-184 verbatim
@[simp] theorem execute_gasCharged
    (schedule : GasSchedule)
    (accelerator : AcceleratorInput → ZkvmStatus × AcceleratorOutput)
    (memory : MemoryReader) (dataStart : Nat) :
    (execute schedule accelerator memory dataStart).gasCharged = schedule.ecadd := by
  cases h_status : (accelerator (acceleratorInputFromCallData memory dataStart)).1 <;>
    simp [execute, h_status]


-- @@ L186-186 verbatim
end Add


-- @@ L188-188 verbatim
namespace Mul


-- @@ L190-190 verbatim
abbrev MemoryReader := EvmAsm.EL.Bn254G1MulInputBridge.MemoryReader

-- @@ L191-191 verbatim
abbrev AcceleratorInput := EvmAsm.EL.Bn254G1MulInputBridge.AcceleratorInput

-- @@ L192-192 verbatim
abbrev AcceleratorResult := EvmAsm.EL.Bn254G1MulResultBridge.AcceleratorResult


-- @@ L194-197 verbatim
def acceleratorInputFromCallData (memory : MemoryReader) (dataStart : Nat) :
    AcceleratorInput :=
  EvmAsm.EL.Bn254G1MulInputBridge.bn254G1MulInputFromMemory
    memory dataStart (dataStart + 64)


-- @@ L199-210 verbatim
def execute
    (schedule : GasSchedule)
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart : Nat) : Result :=
  let result := accelerator (acceleratorInputFromCallData memory dataStart)
  match result.status with
  | .eok =>
      { status := result.status
        output := EvmAsm.EL.Bn254G1MulResultBridge.g1PointBytesList result.output.point
        gasCharged := schedule.ecmul }
  | .efail =>
      { status := result.status, output := emptyOutput, gasCharged := schedule.ecmul }


-- @@ L212-219 verbatim
@[simp] theorem execute_status
    (schedule : GasSchedule)
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart : Nat) :
    (execute schedule accelerator memory dataStart).status =
      (accelerator (acceleratorInputFromCallData memory dataStart)).status := by
  cases h_status : (accelerator (acceleratorInputFromCallData memory dataStart)).status <;>
    simp [execute, h_status]


-- @@ L221-229 verbatim
@[simp] theorem execute_output_eok
    (schedule : GasSchedule)
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart : Nat)
    (h_status : (accelerator (acceleratorInputFromCallData memory dataStart)).status = .eok) :
    (execute schedule accelerator memory dataStart).output =
      EvmAsm.EL.Bn254G1MulResultBridge.g1PointBytesList
        (accelerator (acceleratorInputFromCallData memory dataStart)).output.point := by
  simp [execute, h_status]


-- @@ L231-237 verbatim
@[simp] theorem execute_output_efail
    (schedule : GasSchedule)
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart : Nat)
    (h_status : (accelerator (acceleratorInputFromCallData memory dataStart)).status = .efail) :
    (execute schedule accelerator memory dataStart).output = emptyOutput := by
  simp [execute, h_status]


-- @@ L239-245 verbatim
@[simp] theorem execute_gasCharged
    (schedule : GasSchedule)
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart : Nat) :
    (execute schedule accelerator memory dataStart).gasCharged = schedule.ecmul := by
  cases h_status : (accelerator (acceleratorInputFromCallData memory dataStart)).status <;>
    simp [execute, h_status]


-- @@ L247-247 verbatim
end Mul


-- @@ L249-249 verbatim
namespace Pairing


-- @@ L251-251 verbatim
abbrev MemoryReader := EvmAsm.EL.Bn254PairingInputBridge.MemoryReader

-- @@ L252-252 verbatim
abbrev AcceleratorInput := EvmAsm.EL.Bn254PairingInputBridge.AcceleratorInput

-- @@ L253-253 verbatim
abbrev AcceleratorResult := EvmAsm.EL.Bn254PairingResultBridge.AcceleratorResult


-- @@ L255-256 verbatim
def numPairs (dataLength : Nat) : Nat :=
  dataLength / pairingPairLength


-- @@ L258-259 verbatim
def gasCharged (schedule : GasSchedule) (dataLength : Nat) : Nat :=
  schedule.pairingBase + schedule.pairingPerPoint * numPairs dataLength


-- @@ L261-266 verbatim
def acceleratorInputFromCallData
    (memory : MemoryReader) (dataStart dataLength : Nat) : AcceleratorInput :=
  EvmAsm.EL.Bn254PairingInputBridge.bn254PairingInputFromMemory
    memory dataStart (numPairs dataLength)

-- `@[expose]`: an exported in-file lemma proves a value fact about this body by rfl.

-- @@ L267-269 verbatim
@[expose]
def outputFromVerified (verified : Bool) : ByteList :=
  if verified then successWordOutput else zeroWordOutput


-- @@ L271-290 verbatim
def execute
    (schedule : GasSchedule)
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart dataLength : Nat) : Result :=
  if dataLength % pairingPairLength = 0 then
    let input := acceleratorInputFromCallData memory dataStart dataLength
    let result := accelerator input
    match result.status with
    | .eok =>
        { status := result.status
          output := outputFromVerified result.output.verified
          gasCharged := gasCharged schedule dataLength }
    | .efail =>
        { status := result.status
          output := emptyOutput
          gasCharged := gasCharged schedule dataLength }
  else
    { status := .efail
      output := emptyOutput
      gasCharged := gasCharged schedule dataLength }


-- @@ L292-293 verbatim
@[simp] theorem outputFromVerified_true :
    outputFromVerified true = successWordOutput := rfl


-- @@ L295-296 verbatim
@[simp] theorem outputFromVerified_false :
    outputFromVerified false = zeroWordOutput := rfl


-- @@ L298-307 verbatim
@[simp] theorem execute_badLength
    (schedule : GasSchedule)
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart dataLength : Nat)
    (h_length : dataLength % pairingPairLength ≠ 0) :
    execute schedule accelerator memory dataStart dataLength =
      { status := .efail
        output := emptyOutput
        gasCharged := gasCharged schedule dataLength } := by
  simp [execute, h_length]


-- @@ L309-318 verbatim
@[simp] theorem execute_status_validLength
    (schedule : GasSchedule)
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart dataLength : Nat)
    (h_length : dataLength % pairingPairLength = 0) :
    (execute schedule accelerator memory dataStart dataLength).status =
      (accelerator (acceleratorInputFromCallData memory dataStart dataLength)).status := by
  cases h_status :
      (accelerator (acceleratorInputFromCallData memory dataStart dataLength)).status <;>
    simp [execute, h_length, h_status]


-- @@ L320-330 verbatim
@[simp] theorem execute_gasCharged
    (schedule : GasSchedule)
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart dataLength : Nat) :
    (execute schedule accelerator memory dataStart dataLength).gasCharged =
      gasCharged schedule dataLength := by
  by_cases h_length : dataLength % pairingPairLength = 0
  · cases h_status :
        (accelerator (acceleratorInputFromCallData memory dataStart dataLength)).status <;>
      simp [execute, h_length, h_status]
  · simp [execute, h_length]


-- @@ L332-332 verbatim
end Pairing


-- @@ L334-336 verbatim
theorem successWordOutput_length :
    successWordOutput.length = 32 := by
  simp [successWordOutput]


-- @@ L338-340 verbatim
theorem zeroWordOutput_length :
    zeroWordOutput.length = 32 := by
  simp [zeroWordOutput]


-- @@ L342-343 verbatim
theorem emptyOutput_length :
    emptyOutput.length = 0 := rfl


-- @@ L345-345 verbatim
end BN254


-- @@ L347-347 verbatim
namespace Modexp


-- @@ L349-349 verbatim
abbrev AcceleratorInput := EvmAsm.EL.ModexpInputBridge.AcceleratorInput

-- @@ L350-350 verbatim
abbrev AcceleratorResult := EvmAsm.EL.ModexpResultBridge.AcceleratorResult


-- @@ L352-353 verbatim
/-- MODEXP precompile address. -/
def address : Nat := 0x05


-- @@ L355-356 verbatim
/-- Osaka/EIP-7823 maximum byte length for base, exponent, and modulus. -/
def maxComponentLength : Nat := 1024


-- @@ L358-359 verbatim
/-- MODEXP call-data header size: base length, exponent length, modulus length. -/
def headerLength : Nat := 96


-- @@ L361-368 verbatim
/-- Executable-spec `buffer_read(data, start, size)` with zero padding. -/
-- `@[expose]`: an exported in-file lemma proves a value fact about this body by rfl.
@[expose]
def bufferRead (data : ByteList) (start size : Nat) : ByteList :=
  (List.range size).map fun i =>
    match data[start + i]? with
    | some b => b
    | none => 0


-- @@ L370-372 verbatim
/-- Decode a big-endian unsigned integer from a byte list. -/
def natFromBytesBE (bytes : ByteList) : Nat :=
  EvmAsm.EL.RLP.Nat.fromBytesBE bytes


-- @@ L374-376 verbatim
/-- Read a 32-byte big-endian length field from MODEXP call data. -/
def readLength (data : ByteList) (offset : Nat) : Nat :=
  natFromBytesBE (bufferRead data offset 32)


-- @@ L378-379 verbatim
def baseLength (data : ByteList) : Nat :=
  readLength data 0


-- @@ L381-382 verbatim
def exponentLength (data : ByteList) : Nat :=
  readLength data 32


-- @@ L384-385 verbatim
def modulusLength (data : ByteList) : Nat :=
  readLength data 64


-- @@ L387-388 verbatim
def exponentStart (data : ByteList) : Nat :=
  headerLength + baseLength data


-- @@ L390-391 verbatim
def modulusStart (data : ByteList) : Nat :=
  exponentStart data + exponentLength data


-- @@ L393-394 verbatim
def exponentHead (data : ByteList) : Nat :=
  natFromBytesBE (bufferRead data (exponentStart data) (min 32 (exponentLength data)))


-- @@ L396-402 verbatim
/-- EIP-2565/Osaka multiplication complexity. -/
-- `@[expose]`: reached transitively by an exported in-file rfl lemma about `gasCost`.
@[expose]
def complexity (baseLen modulusLen : Nat) : Nat :=
  let maxLen := max baseLen modulusLen
  let words := (maxLen + 7) / 8
  if maxLen > 32 then 2 * words * words else 16


-- @@ L404-415 verbatim
/-- EIP-2565/Osaka adjusted exponent iteration count. -/
-- `@[expose]`: reached transitively by an exported in-file rfl lemma about `gasCost`.
@[expose]
def iterations (exponentLen exponentHead : Nat) : Nat :=
  let count :=
    if exponentLen ≤ 32 ∧ exponentHead = 0 then
      0
    else if exponentLen ≤ 32 then
      exponentHead.log2
    else
      16 * (exponentLen - 32) + exponentHead.log2
  max count 1


-- @@ L417-421 verbatim
/-- Osaka MODEXP gas cost from execution-specs `modexp.gas_cost`. -/
-- `@[expose]`: an exported in-file lemma proves a value fact about this body by rfl.
@[expose]
def gasCost (baseLen modulusLen exponentLen exponentHead : Nat) : Nat :=
  max 500 (complexity baseLen modulusLen * iterations exponentLen exponentHead)


-- @@ L423-424 verbatim
def gasCostFromCallData (data : ByteList) : Nat :=
  gasCost (baseLength data) (modulusLength data) (exponentLength data) (exponentHead data)


-- @@ L426-429 verbatim
def componentLengthsValid (data : ByteList) : Prop :=
  baseLength data ≤ maxComponentLength ∧
  exponentLength data ≤ maxComponentLength ∧
  modulusLength data ≤ maxComponentLength


-- @@ L431-434 verbatim
def componentLengthsValidBool (data : ByteList) : Bool :=
  baseLength data ≤ maxComponentLength &&
  exponentLength data ≤ maxComponentLength &&
  modulusLength data ≤ maxComponentLength


-- @@ L436-439 verbatim
def acceleratorInputFromCallData (data : ByteList) : AcceleratorInput :=
  { base := bufferRead data headerLength (baseLength data)
    exp := bufferRead data (exponentStart data) (exponentLength data)
    modulus := bufferRead data (modulusStart data) (modulusLength data) }


-- @@ L441-451 verbatim
/-- Result surface exposed to the caller by the pure MODEXP framing layer.

`exceptional = true` represents Osaka's pre-gas length-cap halt. Otherwise
`gasCharged` is the decoded MODEXP gas cost and `output` is the precompile
return data. -/
structure Result where
  exceptional : Bool
  status : ZkvmStatus
  output : ByteList
  gasCharged : Nat
  deriving Repr


-- @@ L453-457 verbatim
def exceptionalResult : Result :=
  { exceptional := true
    status := .efail
    output := []
    gasCharged := 0 }


-- @@ L459-485 verbatim
def execute
    (accelerator : AcceleratorInput → AcceleratorResult)
    (data : ByteList) : Result :=
  if componentLengthsValidBool data then
    let gas := gasCostFromCallData data
    if baseLength data = 0 ∧ modulusLength data = 0 then
      { exceptional := false
        status := .eok
        output := []
        gasCharged := gas }
    else
      let result := EvmAsm.EL.ModexpEcallBridge.executeModexpEcall accelerator
        (EvmAsm.EL.ModexpEcallBridge.requestFromInput
          (acceleratorInputFromCallData data))
      match result.status with
      | .eok =>
          { exceptional := false
            status := result.status
            output := result.output.bytes
            gasCharged := gas }
      | .efail =>
          { exceptional := false
            status := result.status
            output := []
            gasCharged := gas }
  else
    exceptionalResult


-- @@ L487-489 verbatim
@[simp] theorem bufferRead_length (data : ByteList) (start size : Nat) :
    (bufferRead data start size).length = size := by
  simp [bufferRead]


-- @@ L491-492 verbatim
@[simp] theorem bufferRead_zero (data : ByteList) (start : Nat) :
    bufferRead data start 0 = [] := rfl


-- @@ L494-496 verbatim
theorem acceleratorInputFromCallData_base_length (data : ByteList) :
    (acceleratorInputFromCallData data).base.length = baseLength data := by
  simp [acceleratorInputFromCallData]


-- @@ L498-500 verbatim
theorem acceleratorInputFromCallData_exp_length (data : ByteList) :
    (acceleratorInputFromCallData data).exp.length = exponentLength data := by
  simp [acceleratorInputFromCallData]


-- @@ L502-504 verbatim
theorem acceleratorInputFromCallData_modulus_length (data : ByteList) :
    (acceleratorInputFromCallData data).modulus.length = modulusLength data := by
  simp [acceleratorInputFromCallData]


-- @@ L506-509 verbatim
@[simp] theorem complexity_small (baseLen modulusLen : Nat)
    (h_max : max baseLen modulusLen ≤ 32) :
    complexity baseLen modulusLen = 16 := by
  simp [complexity, Nat.not_lt.mpr h_max]


-- @@ L511-514 verbatim
@[simp] theorem iterations_zero_head (exponentLen : Nat)
    (h_len : exponentLen ≤ 32) :
    iterations exponentLen 0 = 1 := by
  simp [iterations, h_len]


-- @@ L516-518 verbatim
theorem gasCost_minimum (baseLen modulusLen exponentLen exponentHead : Nat) :
    500 ≤ gasCost baseLen modulusLen exponentLen exponentHead := by
  simp [gasCost]


-- @@ L520-521 verbatim
theorem gasCost_zero_lengths :
    gasCost 0 0 0 0 = 500 := rfl


-- @@ L523-524 verbatim
theorem gasCost_one_byte_small_exp :
    gasCost 1 1 1 1 = 500 := rfl


-- @@ L526-531 verbatim
@[simp] theorem execute_badLengths
    (accelerator : AcceleratorInput → AcceleratorResult)
    (data : ByteList)
    (h_valid : componentLengthsValidBool data = false) :
    execute accelerator data = exceptionalResult := by
  simp [execute, h_valid]


-- @@ L533-544 verbatim
@[simp] theorem execute_zero_base_zero_modulus
    (accelerator : AcceleratorInput → AcceleratorResult)
    (data : ByteList)
    (h_valid : componentLengthsValidBool data = true)
    (h_base : baseLength data = 0)
    (h_modulus : modulusLength data = 0) :
    execute accelerator data =
      { exceptional := false
        status := .eok
        output := []
        gasCharged := gasCostFromCallData data } := by
  simp [execute, h_valid, h_base, h_modulus]


-- @@ L546-558 verbatim
@[simp] theorem execute_gasCharged_valid
    (accelerator : AcceleratorInput → AcceleratorResult)
    (data : ByteList)
    (h_valid : componentLengthsValidBool data = true) :
    (execute accelerator data).gasCharged = gasCostFromCallData data := by
  by_cases h_zero : baseLength data = 0 ∧ modulusLength data = 0
  · simp [execute, h_valid, h_zero.1, h_zero.2]
  · have h_not : ¬ (baseLength data = 0 ∧ modulusLength data = 0) := h_zero
    cases h_status :
        (EvmAsm.EL.ModexpEcallBridge.executeModexpEcall accelerator
          (EvmAsm.EL.ModexpEcallBridge.requestFromInput
            (acceleratorInputFromCallData data))).status <;>
      simp [execute, h_valid, h_not, h_status]


-- @@ L560-560 verbatim
end Modexp


-- @@ L562-562 verbatim
namespace BLS12


-- @@ L564-564 verbatim
namespace G1Msm


-- @@ L566-566 verbatim
abbrev MemoryReader := EvmAsm.EL.Bls12G1MsmInputBridge.MemoryReader

-- @@ L567-567 verbatim
abbrev AcceleratorInput := EvmAsm.EL.Bls12G1MsmInputBridge.AcceleratorInput

-- @@ L568-568 verbatim
abbrev AcceleratorResult := EvmAsm.EL.Bls12G1MsmResultBridge.AcceleratorResult


-- @@ L570-571 verbatim
/-- EVM precompile address for BLS12-381 G1 MSM. -/
def address : Nat := 0x0c


-- @@ L573-574 verbatim
/-- Osaka executable-spec G1 MSM call-data item width: 128-byte G1 plus 32-byte scalar. -/
def lengthPerPair : Nat := 160


-- @@ L576-577 verbatim
/-- Osaka executable-spec `GasCosts.PRECOMPILE_BLS_G1MUL`. -/
def g1MulGas : Nat := 12000


-- @@ L579-580 verbatim
/-- Osaka executable-spec BLS discount multiplier. -/
def multiplier : Nat := 1000


-- @@ L582-583 verbatim
/-- Osaka executable-spec max discount for G1 MSM with more than 128 pairs. -/
def g1MaxDiscount : Nat := 519


-- @@ L585-602 verbatim
/-- Osaka executable-spec `G1_K_DISCOUNT`, indexed by `k - 1` for `1 <= k <= 128`. -/
def g1KDiscount : List Nat :=
  [ 1000, 949, 848, 797, 764, 750, 738, 728
  , 719, 712, 705, 698, 692, 687, 682, 677
  , 673, 669, 665, 661, 658, 654, 651, 648
  , 645, 642, 640, 637, 635, 632, 630, 627
  , 625, 623, 621, 619, 617, 615, 613, 611
  , 609, 608, 606, 604, 603, 601, 599, 598
  , 596, 595, 593, 592, 591, 589, 588, 586
  , 585, 584, 582, 581, 580, 579, 577, 576
  , 575, 574, 573, 572, 570, 569, 568, 567
  , 566, 565, 564, 563, 562, 561, 560, 559
  , 558, 557, 556, 555, 554, 553, 552, 551
  , 550, 549, 548, 547, 547, 546, 545, 544
  , 543, 542, 541, 540, 540, 539, 538, 537
  , 536, 536, 535, 534, 533, 532, 532, 531
  , 530, 529, 528, 528, 527, 526, 525, 525
  , 524, 523, 522, 522, 521, 520, 520, 519 ]


-- @@ L604-607 verbatim
/-- Invalid length or accelerator failure returns no bytes. -/
-- `@[expose]`: an exported in-file lemma proves a value fact about this body by rfl.
@[expose]
def emptyOutput : ByteList := []


-- @@ L609-618 verbatim
/--
Result surface exposed by the pure BLS12-381 G1 MSM framing layer.
`exceptional = true` records executable-spec `InvalidParameter` cases.
-/
structure Result where
  exceptional : Bool
  status : ZkvmStatus
  output : ByteList
  gasCharged : Nat
  deriving Repr


-- @@ L620-621 verbatim
def numPairs (dataLength : Nat) : Nat :=
  dataLength / lengthPerPair


-- @@ L623-624 verbatim
def validInputLength (dataLength : Nat) : Bool :=
  dataLength != 0 && dataLength % lengthPerPair == 0


-- @@ L626-627 verbatim
def validInputLengthBool (dataLength : Nat) : Bool :=
  validInputLength dataLength


-- @@ L629-635 verbatim
def discount (k : Nat) : Nat :=
  if k = 0 then
    0
  else if k <= 128 then
    g1KDiscount.getD (k - 1) g1MaxDiscount
  else
    g1MaxDiscount


-- @@ L637-639 verbatim
def gasCharged (dataLength : Nat) : Nat :=
  let k := numPairs dataLength
  k * g1MulGas * discount k / multiplier


-- @@ L641-644 verbatim
def acceleratorInputFromCallData
    (memory : MemoryReader) (dataStart dataLength : Nat) : AcceleratorInput :=
  EvmAsm.EL.Bls12G1MsmInputBridge.bls12G1MsmInputFromMemory
    memory dataStart (numPairs dataLength)


-- @@ L646-650 verbatim
def exceptionalResult : Result :=
  { exceptional := true
    status := .efail
    output := emptyOutput
    gasCharged := 0 }


-- @@ L652-676 verbatim
/--
Pure BLS12-381 G1 MSM precompile framing. This owns the EVM-side Osaka length
and gas rules, then delegates curve arithmetic to the supplied accelerator.
-/
def execute
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart dataLength : Nat) : Result :=
  if validInputLengthBool dataLength then
    let gas := gasCharged dataLength
    let input := acceleratorInputFromCallData memory dataStart dataLength
    let result := EvmAsm.EL.Bls12G1MsmEcallBridge.executeBls12G1MsmEcall accelerator
      (EvmAsm.EL.Bls12G1MsmEcallBridge.requestFromInput input)
    match result.status with
    | .eok =>
        { exceptional := false
          status := result.status
          output := EvmAsm.EL.Bls12G1MsmResultBridge.g1PointBytesList result.output.point
          gasCharged := gas }
    | .efail =>
        { exceptional := false
          status := result.status
          output := emptyOutput
          gasCharged := gas }
  else
    exceptionalResult


-- @@ L678-680 verbatim
theorem g1KDiscount_length :
    g1KDiscount.length = 128 := by
  set_option maxRecDepth 1000 in decide


-- @@ L682-683 verbatim
theorem emptyOutput_length :
    emptyOutput.length = 0 := rfl


-- @@ L685-687 verbatim
@[simp] theorem validInputLengthBool_zero :
    validInputLengthBool 0 = false := by
  simp [validInputLengthBool, validInputLength]


-- @@ L689-692 verbatim
@[simp] theorem validInputLengthBool_bad_mod
    (dataLength : Nat) (h_mod : dataLength % lengthPerPair ≠ 0) :
    validInputLengthBool dataLength = false := by
  simp [validInputLengthBool, validInputLength, h_mod]


-- @@ L694-696 verbatim
@[simp] theorem numPairs_lengthPerPair_mul (k : Nat) :
    numPairs (lengthPerPair * k) = k := by
  simp [numPairs, lengthPerPair]


-- @@ L698-700 verbatim
@[simp] theorem discount_zero :
    discount 0 = 0 := by
  simp [discount]


-- @@ L702-705 verbatim
@[simp] theorem discount_le_128
    (k : Nat) (h_pos : k ≠ 0) (h_le : k <= 128) :
    discount k = g1KDiscount.getD (k - 1) g1MaxDiscount := by
  simp [discount, h_pos, h_le]


-- @@ L707-713 verbatim
@[simp] theorem discount_gt_128
    (k : Nat) (h_gt : Not (k <= 128)) :
    discount k = g1MaxDiscount := by
  have h_pos : k ≠ 0 := by
    intro h_zero
    exact h_gt (by simp [h_zero])
  simp [discount, h_pos, h_gt]


-- @@ L715-717 verbatim
@[simp] theorem gasCharged_valid_pairs (k : Nat) :
    gasCharged (lengthPerPair * k) = k * g1MulGas * discount k / multiplier := by
  simp [gasCharged]


-- @@ L719-724 verbatim
@[simp] theorem acceleratorInputFromCallData_numPairs
    (memory : MemoryReader) (dataStart dataLength : Nat) :
    (acceleratorInputFromCallData memory dataStart dataLength).numPairs =
      numPairs dataLength := by
  simp [acceleratorInputFromCallData,
    EvmAsm.EL.Bls12G1MsmInputBridge.bls12G1MsmInputFromMemory_numPairs]


-- @@ L726-731 verbatim
@[simp] theorem execute_badLength
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart dataLength : Nat)
    (h_valid : validInputLengthBool dataLength = false) :
    execute accelerator memory dataStart dataLength = exceptionalResult := by
  simp [execute, h_valid]


-- @@ L733-743 verbatim
@[simp] theorem execute_status_validLength
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart dataLength : Nat)
    (h_valid : validInputLengthBool dataLength = true) :
    (execute accelerator memory dataStart dataLength).status =
      (accelerator (acceleratorInputFromCallData memory dataStart dataLength)).status := by
  cases h_status :
      (accelerator (acceleratorInputFromCallData memory dataStart dataLength)).status <;>
    simp [execute, h_valid, h_status,
      EvmAsm.EL.Bls12G1MsmEcallBridge.executeBls12G1MsmEcall,
      EvmAsm.EL.Bls12G1MsmEcallBridge.requestFromInput]


-- @@ L745-756 verbatim
@[simp] theorem execute_output_eok
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart dataLength : Nat)
    (h_valid : validInputLengthBool dataLength = true)
    (h_status :
      (accelerator (acceleratorInputFromCallData memory dataStart dataLength)).status = .eok) :
    (execute accelerator memory dataStart dataLength).output =
      EvmAsm.EL.Bls12G1MsmResultBridge.g1PointBytesList
        (accelerator (acceleratorInputFromCallData memory dataStart dataLength)).output.point := by
  simp [execute, h_valid, h_status,
    EvmAsm.EL.Bls12G1MsmEcallBridge.executeBls12G1MsmEcall,
    EvmAsm.EL.Bls12G1MsmEcallBridge.requestFromInput]


-- @@ L758-767 verbatim
@[simp] theorem execute_output_efail
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart dataLength : Nat)
    (h_valid : validInputLengthBool dataLength = true)
    (h_status :
      (accelerator (acceleratorInputFromCallData memory dataStart dataLength)).status = .efail) :
    (execute accelerator memory dataStart dataLength).output = emptyOutput := by
  simp [execute, h_valid, h_status,
    EvmAsm.EL.Bls12G1MsmEcallBridge.executeBls12G1MsmEcall,
    EvmAsm.EL.Bls12G1MsmEcallBridge.requestFromInput]


-- @@ L769-780 verbatim
@[simp] theorem execute_gasCharged
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart dataLength : Nat) :
    (execute accelerator memory dataStart dataLength).gasCharged =
      if validInputLengthBool dataLength then gasCharged dataLength else 0 := by
  by_cases h_valid : validInputLengthBool dataLength
  . cases h_status :
        (accelerator (acceleratorInputFromCallData memory dataStart dataLength)).status <;>
      simp [execute, h_valid, h_status,
        EvmAsm.EL.Bls12G1MsmEcallBridge.executeBls12G1MsmEcall,
        EvmAsm.EL.Bls12G1MsmEcallBridge.requestFromInput]
  . simp [execute, exceptionalResult, h_valid]


-- @@ L782-782 verbatim
end G1Msm


-- @@ L784-784 verbatim
namespace G2Msm


-- @@ L786-786 verbatim
abbrev MemoryReader := EvmAsm.EL.Bls12G2MsmInputBridge.MemoryReader

-- @@ L787-787 verbatim
abbrev AcceleratorInput := EvmAsm.EL.Bls12G2MsmInputBridge.AcceleratorInput

-- @@ L788-788 verbatim
abbrev AcceleratorResult := EvmAsm.EL.Bls12G2MsmResultBridge.AcceleratorResult


-- @@ L790-791 verbatim
/-- EVM precompile address for BLS12-381 G2 MSM. -/
def address : Nat := 0x0e


-- @@ L793-794 verbatim
/-- Osaka executable-spec G2 MSM call-data item width: 256-byte G2 plus 32-byte scalar. -/
def lengthPerPair : Nat := 288


-- @@ L796-797 verbatim
/-- Osaka executable-spec `GasCosts.PRECOMPILE_BLS_G2MUL`. -/
def g2MulGas : Nat := 22500


-- @@ L799-800 verbatim
/-- Osaka executable-spec BLS discount multiplier. -/
def multiplier : Nat := 1000


-- @@ L802-803 verbatim
/-- Osaka executable-spec max discount for G2 MSM with more than 128 pairs. -/
def g2MaxDiscount : Nat := 524


-- @@ L805-822 verbatim
/-- Osaka executable-spec `G2_K_DISCOUNT`, indexed by `k - 1` for `1 <= k <= 128`. -/
def g2KDiscount : List Nat :=
  [ 1000, 1000, 923, 884, 855, 832, 812, 796
  , 782, 770, 759, 749, 740, 732, 724, 717
  , 711, 704, 699, 693, 688, 683, 679, 674
  , 670, 666, 663, 659, 655, 652, 649, 646
  , 643, 640, 637, 634, 632, 629, 627, 624
  , 622, 620, 618, 615, 613, 611, 609, 607
  , 606, 604, 602, 600, 598, 597, 595, 593
  , 592, 590, 589, 587, 586, 584, 583, 582
  , 580, 579, 578, 576, 575, 574, 573, 571
  , 570, 569, 568, 567, 566, 565, 563, 562
  , 561, 560, 559, 558, 557, 556, 555, 554
  , 553, 552, 552, 551, 550, 549, 548, 547
  , 546, 545, 545, 544, 543, 542, 541, 541
  , 540, 539, 538, 537, 537, 536, 535, 535
  , 534, 533, 532, 532, 531, 530, 530, 529
  , 528, 528, 527, 526, 526, 525, 524, 524 ]


-- @@ L824-827 verbatim
/-- Invalid length or accelerator failure returns no bytes. -/
-- `@[expose]`: an exported in-file lemma proves a value fact about this body by rfl.
@[expose]
def emptyOutput : ByteList := []


-- @@ L829-838 verbatim
/--
Result surface exposed by the pure BLS12-381 G2 MSM framing layer.
`exceptional = true` records executable-spec `InvalidParameter` cases.
-/
structure Result where
  exceptional : Bool
  status : ZkvmStatus
  output : ByteList
  gasCharged : Nat
  deriving Repr


-- @@ L840-841 verbatim
def numPairs (dataLength : Nat) : Nat :=
  dataLength / lengthPerPair


-- @@ L843-844 verbatim
def validInputLength (dataLength : Nat) : Bool :=
  dataLength != 0 && dataLength % lengthPerPair == 0


-- @@ L846-847 verbatim
def validInputLengthBool (dataLength : Nat) : Bool :=
  validInputLength dataLength


-- @@ L849-855 verbatim
def discount (k : Nat) : Nat :=
  if k = 0 then
    0
  else if k <= 128 then
    g2KDiscount.getD (k - 1) g2MaxDiscount
  else
    g2MaxDiscount


-- @@ L857-859 verbatim
def gasCharged (dataLength : Nat) : Nat :=
  let k := numPairs dataLength
  k * g2MulGas * discount k / multiplier


-- @@ L861-864 verbatim
def acceleratorInputFromCallData
    (memory : MemoryReader) (dataStart dataLength : Nat) : AcceleratorInput :=
  EvmAsm.EL.Bls12G2MsmInputBridge.bls12G2MsmInputFromMemory
    memory dataStart (numPairs dataLength)


-- @@ L866-870 verbatim
def exceptionalResult : Result :=
  { exceptional := true
    status := .efail
    output := emptyOutput
    gasCharged := 0 }


-- @@ L872-896 verbatim
/--
Pure BLS12-381 G2 MSM precompile framing. This owns the EVM-side Osaka length
and gas rules, then delegates curve arithmetic to the supplied accelerator.
-/
def execute
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart dataLength : Nat) : Result :=
  if validInputLengthBool dataLength then
    let gas := gasCharged dataLength
    let input := acceleratorInputFromCallData memory dataStart dataLength
    let result := EvmAsm.EL.Bls12G2MsmEcallBridge.executeBls12G2MsmEcall accelerator
      (EvmAsm.EL.Bls12G2MsmEcallBridge.requestFromInput input)
    match result.status with
    | .eok =>
        { exceptional := false
          status := result.status
          output := EvmAsm.EL.Bls12G2MsmResultBridge.g2PointBytesList result.output.point
          gasCharged := gas }
    | .efail =>
        { exceptional := false
          status := result.status
          output := emptyOutput
          gasCharged := gas }
  else
    exceptionalResult


-- @@ L898-900 verbatim
theorem g2KDiscount_length :
    g2KDiscount.length = 128 := by
  set_option maxRecDepth 1000 in decide


-- @@ L902-903 verbatim
theorem emptyOutput_length :
    emptyOutput.length = 0 := rfl


-- @@ L905-907 verbatim
@[simp] theorem validInputLengthBool_zero :
    validInputLengthBool 0 = false := by
  simp [validInputLengthBool, validInputLength]


-- @@ L909-912 verbatim
@[simp] theorem validInputLengthBool_bad_mod
    (dataLength : Nat) (h_mod : dataLength % lengthPerPair ≠ 0) :
    validInputLengthBool dataLength = false := by
  simp [validInputLengthBool, validInputLength, h_mod]


-- @@ L914-916 verbatim
@[simp] theorem numPairs_lengthPerPair_mul (k : Nat) :
    numPairs (lengthPerPair * k) = k := by
  simp [numPairs, lengthPerPair]


-- @@ L918-920 verbatim
@[simp] theorem discount_zero :
    discount 0 = 0 := by
  simp [discount]


-- @@ L922-925 verbatim
@[simp] theorem discount_le_128
    (k : Nat) (h_pos : k ≠ 0) (h_le : k <= 128) :
    discount k = g2KDiscount.getD (k - 1) g2MaxDiscount := by
  simp [discount, h_pos, h_le]


-- @@ L927-933 verbatim
@[simp] theorem discount_gt_128
    (k : Nat) (h_gt : Not (k <= 128)) :
    discount k = g2MaxDiscount := by
  have h_pos : k ≠ 0 := by
    intro h_zero
    exact h_gt (by simp [h_zero])
  simp [discount, h_pos, h_gt]


-- @@ L935-937 verbatim
@[simp] theorem gasCharged_valid_pairs (k : Nat) :
    gasCharged (lengthPerPair * k) = k * g2MulGas * discount k / multiplier := by
  simp [gasCharged]


-- @@ L939-944 verbatim
@[simp] theorem acceleratorInputFromCallData_numPairs
    (memory : MemoryReader) (dataStart dataLength : Nat) :
    (acceleratorInputFromCallData memory dataStart dataLength).numPairs =
      numPairs dataLength := by
  simp [acceleratorInputFromCallData,
    EvmAsm.EL.Bls12G2MsmInputBridge.bls12G2MsmInputFromMemory_numPairs]


-- @@ L946-951 verbatim
@[simp] theorem execute_badLength
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart dataLength : Nat)
    (h_valid : validInputLengthBool dataLength = false) :
    execute accelerator memory dataStart dataLength = exceptionalResult := by
  simp [execute, h_valid]


-- @@ L953-963 verbatim
@[simp] theorem execute_status_validLength
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart dataLength : Nat)
    (h_valid : validInputLengthBool dataLength = true) :
    (execute accelerator memory dataStart dataLength).status =
      (accelerator (acceleratorInputFromCallData memory dataStart dataLength)).status := by
  cases h_status :
      (accelerator (acceleratorInputFromCallData memory dataStart dataLength)).status <;>
    simp [execute, h_valid, h_status,
      EvmAsm.EL.Bls12G2MsmEcallBridge.executeBls12G2MsmEcall,
      EvmAsm.EL.Bls12G2MsmEcallBridge.requestFromInput]


-- @@ L965-976 verbatim
@[simp] theorem execute_output_eok
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart dataLength : Nat)
    (h_valid : validInputLengthBool dataLength = true)
    (h_status :
      (accelerator (acceleratorInputFromCallData memory dataStart dataLength)).status = .eok) :
    (execute accelerator memory dataStart dataLength).output =
      EvmAsm.EL.Bls12G2MsmResultBridge.g2PointBytesList
        (accelerator (acceleratorInputFromCallData memory dataStart dataLength)).output.point := by
  simp [execute, h_valid, h_status,
    EvmAsm.EL.Bls12G2MsmEcallBridge.executeBls12G2MsmEcall,
    EvmAsm.EL.Bls12G2MsmEcallBridge.requestFromInput]


-- @@ L978-987 verbatim
@[simp] theorem execute_output_efail
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart dataLength : Nat)
    (h_valid : validInputLengthBool dataLength = true)
    (h_status :
      (accelerator (acceleratorInputFromCallData memory dataStart dataLength)).status = .efail) :
    (execute accelerator memory dataStart dataLength).output = emptyOutput := by
  simp [execute, h_valid, h_status,
    EvmAsm.EL.Bls12G2MsmEcallBridge.executeBls12G2MsmEcall,
    EvmAsm.EL.Bls12G2MsmEcallBridge.requestFromInput]


-- @@ L989-1000 verbatim
@[simp] theorem execute_gasCharged
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart dataLength : Nat) :
    (execute accelerator memory dataStart dataLength).gasCharged =
      if validInputLengthBool dataLength then gasCharged dataLength else 0 := by
  by_cases h_valid : validInputLengthBool dataLength
  · cases h_status :
        (accelerator (acceleratorInputFromCallData memory dataStart dataLength)).status <;>
      simp [execute, h_valid, h_status,
        EvmAsm.EL.Bls12G2MsmEcallBridge.executeBls12G2MsmEcall,
        EvmAsm.EL.Bls12G2MsmEcallBridge.requestFromInput]
  · simp [execute, exceptionalResult, h_valid]


-- @@ L1002-1002 verbatim
end G2Msm


-- @@ L1004-1004 verbatim
namespace Pairing


-- @@ L1006-1006 verbatim
abbrev MemoryReader := EvmAsm.EL.Bls12PairingInputBridge.MemoryReader

-- @@ L1007-1007 verbatim
abbrev PairingPair := EvmAsm.EL.Bls12PairingInputBridge.PairingPair

-- @@ L1008-1008 verbatim
abbrev AcceleratorInput := EvmAsm.EL.Bls12PairingInputBridge.AcceleratorInput

-- @@ L1009-1009 verbatim
abbrev AcceleratorResult := EvmAsm.EL.Bls12PairingResultBridge.AcceleratorResult

-- @@ L1010-1010 verbatim
abbrev G1PointBytes := EvmAsm.EL.Bls12PairingInputBridge.G1PointBytes

-- @@ L1011-1011 verbatim
abbrev G2PointBytes := EvmAsm.EL.Bls12PairingInputBridge.G2PointBytes


-- @@ L1013-1014 verbatim
/-- EVM precompile address for BLS12-381 pairing. -/
def address : Nat := 0x0f


-- @@ L1016-1017 verbatim
/-- BLS12 pairing consumes one 128-byte G1 point and one 256-byte G2 point per pair. -/
def pairLength : Nat := 384


-- @@ L1019-1020 verbatim
/-- Osaka executable-spec BLS12 pairing base gas. -/
def baseGas : Nat := 37700


-- @@ L1022-1023 verbatim
/-- Osaka executable-spec BLS12 pairing per-pair gas. -/
def perPairGas : Nat := 32600


-- @@ L1025-1029 verbatim
/-- BLS12 pairing returns a 32-byte boolean word on successful accelerator execution. -/
-- `@[expose]`: an exported in-file lemma proves a value fact about this body by rfl.
@[expose]
def successWordOutput : ByteList :=
  List.replicate 31 (0 : Byte) ++ [1]


-- @@ L1031-1035 verbatim
/-- BLS12 pairing false result word. -/
-- `@[expose]`: an exported in-file lemma proves a value fact about this body by rfl.
@[expose]
def zeroWordOutput : ByteList :=
  List.replicate 32 (0 : Byte)


-- @@ L1037-1040 verbatim
/-- Invalid length, invalid points, or accelerator failure returns no bytes. -/
-- `@[expose]`: an exported in-file lemma proves a value fact about this body by rfl.
@[expose]
def emptyOutput : ByteList := []


-- @@ L1042-1044 verbatim
/-- Number of pairing pairs in a valid EVM BLS12 pairing call payload. -/
def numPairs (dataLength : Nat) : Nat :=
  dataLength / pairLength


-- @@ L1046-1048 verbatim
/-- Osaka executable-spec gas formula: `32600 * k + 37700`. -/
def gasCostFromLength (dataLength : Nat) : Nat :=
  perPairGas * numPairs dataLength + baseGas


-- @@ L1050-1052 verbatim
/-- EVM-side validity guard: pairing input must be nonempty and divisible by 384. -/
def inputLengthValid (dataLength : Nat) : Bool :=
  dataLength != 0 && dataLength % pairLength == 0


-- @@ L1054-1063 verbatim
/--
Result surface exposed by the pure BLS12-381 pairing framing layer.
`exceptional = true` records executable-spec `InvalidParameter` cases.
-/
structure Result where
  exceptional : Bool
  status : ZkvmStatus
  output : ByteList
  gasCharged : Nat
  deriving Repr


-- @@ L1065-1067 verbatim
/-- Drop the 16-byte EIP-2537 field-element padding and keep the 48-byte Fp payload. -/
def fpPayloadFromEvmField (memory : MemoryReader) (fieldStart : Nat) : Fin 48 → Byte :=
  fun i => memory (fieldStart + 16 + i.toNat)


-- @@ L1069-1076 verbatim
/-- Convert a 128-byte EIP-2537 G1 point into the accelerator's 96-byte G1 payload. -/
def g1PointFromEvmBytes (memory : MemoryReader) (pointStart : Nat) : G1PointBytes :=
  fun i =>
    let n := i.toNat
    if n < 48 then
      memory (pointStart + 16 + n)
    else
      memory (pointStart + 64 + 16 + (n - 48))


-- @@ L1078-1089 verbatim
/-- Convert a 256-byte EIP-2537 G2 point into the accelerator's 192-byte G2 payload. -/
def g2PointFromEvmBytes (memory : MemoryReader) (pointStart : Nat) : G2PointBytes :=
  fun i =>
    let n := i.toNat
    if n < 48 then
      memory (pointStart + 16 + n)
    else if n < 96 then
      memory (pointStart + 64 + 16 + (n - 48))
    else if n < 144 then
      memory (pointStart + 128 + 16 + (n - 96))
    else
      memory (pointStart + 192 + 16 + (n - 144))


-- @@ L1091-1094 verbatim
/-- Read one EIP-2537 BLS12 pairing pair: 128-byte G1 followed by 256-byte G2. -/
def pairingPairFromEvmBytes (memory : MemoryReader) (pairStart : Nat) : PairingPair :=
  { g1 := g1PointFromEvmBytes memory pairStart
    g2 := g2PointFromEvmBytes memory (pairStart + 128) }


-- @@ L1096-1100 verbatim
/-- Read `numPairs` consecutive 384-byte EIP-2537 BLS12 pairing pairs. -/
def pairingPairsFromEvmBytes
    (memory : MemoryReader) (pairsStart numPairs : Nat) : List PairingPair :=
  (List.range numPairs).map
    (fun i => pairingPairFromEvmBytes memory (pairsStart + pairLength * i))


-- @@ L1102-1110 verbatim
/--
Build the accelerator input from EVM call data after the executable-spec length
check. Point/subgroup validation and pairing arithmetic are supplied by the
accelerator model.
-/
def acceleratorInputFromCallData
    (memory : MemoryReader) (dataStart dataLength : Nat) : AcceleratorInput :=
  { pairs := pairingPairsFromEvmBytes memory dataStart (numPairs dataLength)
    numPairs := numPairs dataLength }


-- @@ L1112-1116 verbatim
/-- Convert the accelerator boolean into the EVM 32-byte return word. -/
-- `@[expose]`: an exported in-file lemma proves a value fact about this body by rfl.
@[expose]
def outputFromVerified (verified : Bool) : ByteList :=
  if verified then successWordOutput else zeroWordOutput


-- @@ L1118-1149 verbatim
/--
Pure BLS12-381 pairing precompile framing. This models the executable-spec
length guard, gas formula, accelerator call, and 32-byte boolean output.
-/
def execute
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart dataLength : Nat) : Result :=
  if dataLength = 0 then
    { exceptional := true
      status := .efail
      output := emptyOutput
      gasCharged := 0 }
  else if dataLength % pairLength = 0 then
    let input := acceleratorInputFromCallData memory dataStart dataLength
    let result := EvmAsm.EL.Bls12PairingEcallBridge.executeBls12PairingEcall accelerator
      (EvmAsm.EL.Bls12PairingEcallBridge.requestFromInput input)
    match result.status with
    | .eok =>
        { exceptional := false
          status := result.status
          output := outputFromVerified result.output.verified
          gasCharged := gasCostFromLength dataLength }
    | .efail =>
        { exceptional := true
          status := result.status
          output := emptyOutput
          gasCharged := gasCostFromLength dataLength }
  else
    { exceptional := true
      status := .efail
      output := emptyOutput
      gasCharged := 0 }


-- @@ L1151-1153 verbatim
theorem successWordOutput_length :
    successWordOutput.length = 32 := by
  simp [successWordOutput]


-- @@ L1155-1157 verbatim
theorem zeroWordOutput_length :
    zeroWordOutput.length = 32 := by
  simp [zeroWordOutput]


-- @@ L1159-1160 verbatim
theorem emptyOutput_length :
    emptyOutput.length = 0 := rfl


-- @@ L1162-1165 verbatim
theorem pairingPairsFromEvmBytes_length
    (memory : MemoryReader) (pairsStart numPairs : Nat) :
    (pairingPairsFromEvmBytes memory pairsStart numPairs).length = numPairs := by
  simp [pairingPairsFromEvmBytes]


-- @@ L1167-1171 verbatim
theorem acceleratorInputFromCallData_pairs_length
    (memory : MemoryReader) (dataStart dataLength : Nat) :
    (acceleratorInputFromCallData memory dataStart dataLength).pairs.length =
      numPairs dataLength := by
  simp [acceleratorInputFromCallData, pairingPairsFromEvmBytes_length]


-- @@ L1173-1174 verbatim
@[simp] theorem outputFromVerified_true :
    outputFromVerified true = successWordOutput := rfl


-- @@ L1176-1177 verbatim
@[simp] theorem outputFromVerified_false :
    outputFromVerified false = zeroWordOutput := rfl


-- @@ L1179-1187 verbatim
@[simp] theorem execute_zeroLength
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart : Nat) :
    execute accelerator memory dataStart 0 =
      { exceptional := true
        status := .efail
        output := emptyOutput
        gasCharged := 0 } := by
  simp [execute]


-- @@ L1189-1199 verbatim
@[simp] theorem execute_badLength_mod
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart dataLength : Nat)
    (h_nonzero : dataLength ≠ 0)
    (h_mod : dataLength % pairLength ≠ 0) :
    execute accelerator memory dataStart dataLength =
      { exceptional := true
        status := .efail
        output := emptyOutput
        gasCharged := 0 } := by
  simp [execute, h_nonzero, h_mod]


-- @@ L1201-1216 verbatim
@[simp] theorem execute_status
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart dataLength : Nat)
    (h_valid : inputLengthValid dataLength = true) :
    (execute accelerator memory dataStart dataLength).status =
      (accelerator (acceleratorInputFromCallData memory dataStart dataLength)).status := by
  have h_nonzero : dataLength ≠ 0 := by
    intro h_zero
    simp [inputLengthValid, h_zero] at h_valid
  have h_mod : dataLength % pairLength = 0 := by
    simpa [inputLengthValid, h_nonzero] using h_valid
  cases h_status :
      (accelerator (acceleratorInputFromCallData memory dataStart dataLength)).status <;>
    simp [execute, h_nonzero, h_mod, h_status,
      EvmAsm.EL.Bls12PairingEcallBridge.executeBls12PairingEcall,
      EvmAsm.EL.Bls12PairingEcallBridge.requestFromInput]


-- @@ L1218-1234 verbatim
@[simp] theorem execute_output_eok
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart dataLength : Nat)
    (h_valid : inputLengthValid dataLength = true)
    (h_status :
      (accelerator (acceleratorInputFromCallData memory dataStart dataLength)).status = .eok) :
    (execute accelerator memory dataStart dataLength).output =
      outputFromVerified
        (accelerator (acceleratorInputFromCallData memory dataStart dataLength)).output.verified := by
  have h_nonzero : dataLength ≠ 0 := by
    intro h_zero
    simp [inputLengthValid, h_zero] at h_valid
  have h_mod : dataLength % pairLength = 0 := by
    simpa [inputLengthValid, h_nonzero] using h_valid
  simp [execute, h_nonzero, h_mod, h_status,
    EvmAsm.EL.Bls12PairingEcallBridge.executeBls12PairingEcall,
    EvmAsm.EL.Bls12PairingEcallBridge.requestFromInput]


-- @@ L1236-1250 verbatim
@[simp] theorem execute_output_efail
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart dataLength : Nat)
    (h_valid : inputLengthValid dataLength = true)
    (h_status :
      (accelerator (acceleratorInputFromCallData memory dataStart dataLength)).status = .efail) :
    (execute accelerator memory dataStart dataLength).output = emptyOutput := by
  have h_nonzero : dataLength ≠ 0 := by
    intro h_zero
    simp [inputLengthValid, h_zero] at h_valid
  have h_mod : dataLength % pairLength = 0 := by
    simpa [inputLengthValid, h_nonzero] using h_valid
  simp [execute, h_nonzero, h_mod, h_status,
    EvmAsm.EL.Bls12PairingEcallBridge.executeBls12PairingEcall,
    EvmAsm.EL.Bls12PairingEcallBridge.requestFromInput]


-- @@ L1252-1254 verbatim
theorem outputFromVerified_length (verified : Bool) :
    (outputFromVerified verified).length = 32 := by
  cases verified <;> simp [outputFromVerified, successWordOutput_length, zeroWordOutput_length]


-- @@ L1256-1264 verbatim
theorem execute_output_eok_length
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart dataLength : Nat)
    (h_valid : inputLengthValid dataLength = true)
    (h_status :
      (accelerator (acceleratorInputFromCallData memory dataStart dataLength)).status = .eok) :
    (execute accelerator memory dataStart dataLength).output.length = 32 := by
  simp [execute_output_eok accelerator memory dataStart dataLength h_valid h_status,
    outputFromVerified_length]


-- @@ L1266-1280 verbatim
@[simp] theorem execute_gasCharged
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart dataLength : Nat) :
    (execute accelerator memory dataStart dataLength).gasCharged =
      if inputLengthValid dataLength then gasCostFromLength dataLength else 0 := by
  by_cases h_zero : dataLength = 0
  · subst dataLength
    simp [execute, inputLengthValid]
  · by_cases h_mod : dataLength % pairLength = 0
    · cases h_status :
          (accelerator (acceleratorInputFromCallData memory dataStart dataLength)).status <;>
        simp [execute, inputLengthValid, h_zero, h_mod, h_status,
          EvmAsm.EL.Bls12PairingEcallBridge.executeBls12PairingEcall,
          EvmAsm.EL.Bls12PairingEcallBridge.requestFromInput]
    · simp [execute, inputLengthValid, h_zero, h_mod]


-- @@ L1282-1282 verbatim
end Pairing


-- @@ L1284-1284 verbatim
namespace MapFpToG1


-- @@ L1286-1286 verbatim
abbrev MemoryReader := EvmAsm.EL.Bls12MapFpToG1InputBridge.MemoryReader

-- @@ L1287-1287 verbatim
abbrev AcceleratorInput := EvmAsm.EL.Bls12MapFpToG1InputBridge.AcceleratorInput

-- @@ L1288-1288 verbatim
abbrev AcceleratorResult := EvmAsm.EL.Bls12MapFpToG1ResultBridge.AcceleratorResult


-- @@ L1290-1291 verbatim
/-- EVM precompile address for BLS12-381 map-Fp-to-G1. -/
def address : Nat := 0x10


-- @@ L1293-1296 verbatim
/-- Osaka executable-spec fixed gas cost for BLS12-381 map-Fp-to-G1. -/
-- `@[expose]`: an exported in-file lemma proves a value fact about this body by rfl.
@[expose]
def gasCost : Nat := 5500


-- @@ L1298-1299 verbatim
/-- BLS12 map-Fp-to-G1 consumes exactly one 64-byte Fp element. -/
def inputLength : Nat := 64


-- @@ L1301-1304 verbatim
/-- Invalid length, invalid field element, or accelerator failure returns no bytes. -/
-- `@[expose]`: an exported in-file lemma proves a value fact about this body by rfl.
@[expose]
def emptyOutput : ByteList := []


-- @@ L1306-1315 verbatim
/--
Result surface exposed by the pure BLS12-381 map-Fp-to-G1 framing layer.
`exceptional = true` records executable-spec `InvalidParameter` cases.
-/
structure Result where
  exceptional : Bool
  status : ZkvmStatus
  output : ByteList
  gasCharged : Nat
  deriving Repr


-- @@ L1317-1324 verbatim
/--
Build the accelerator input from EVM call data. The executable spec first checks
`len(data) == 64`; callers must guard this helper with that exact length check.
-/
def acceleratorInputFromCallData (memory : MemoryReader) (dataStart : Nat) :
    AcceleratorInput :=
  EvmAsm.EL.Bls12MapFpToG1InputBridge.bls12MapFpToG1InputFromMemory
    memory dataStart


-- @@ L1326-1352 verbatim
/--
Pure BLS12-381 map-Fp-to-G1 precompile framing. Field-element validation and
map-to-curve arithmetic are supplied by the accelerator model.
-/
def execute
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart dataLength : Nat) : Result :=
  if dataLength = inputLength then
    let input := acceleratorInputFromCallData memory dataStart
    let result := EvmAsm.EL.Bls12MapFpToG1EcallBridge.executeBls12MapFpToG1Ecall accelerator
      (EvmAsm.EL.Bls12MapFpToG1EcallBridge.requestFromInput input)
    match result.status with
    | .eok =>
        { exceptional := false
          status := result.status
          output := EvmAsm.EL.Bls12MapFpToG1ResultBridge.g1PointBytesList result.output.point
          gasCharged := gasCost }
    | .efail =>
        { exceptional := true
          status := result.status
          output := emptyOutput
          gasCharged := gasCost }
  else
    { exceptional := true
      status := .efail
      output := emptyOutput
      gasCharged := 0 }


-- @@ L1354-1355 verbatim
theorem emptyOutput_length :
    emptyOutput.length = 0 := rfl


-- @@ L1357-1366 verbatim
@[simp] theorem execute_badLength
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart dataLength : Nat)
    (h_length : dataLength ≠ inputLength) :
    execute accelerator memory dataStart dataLength =
      { exceptional := true
        status := .efail
        output := emptyOutput
        gasCharged := 0 } := by
  simp [execute, h_length]


-- @@ L1368-1376 verbatim
@[simp] theorem execute_status
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart : Nat) :
    (execute accelerator memory dataStart inputLength).status =
      (accelerator (acceleratorInputFromCallData memory dataStart)).status := by
  cases h_status : (accelerator (acceleratorInputFromCallData memory dataStart)).status <;>
    simp [execute, inputLength, h_status,
      EvmAsm.EL.Bls12MapFpToG1EcallBridge.executeBls12MapFpToG1Ecall,
      EvmAsm.EL.Bls12MapFpToG1EcallBridge.requestFromInput]


-- @@ L1378-1387 verbatim
@[simp] theorem execute_output_eok
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart : Nat)
    (h_status : (accelerator (acceleratorInputFromCallData memory dataStart)).status = .eok) :
    (execute accelerator memory dataStart inputLength).output =
      EvmAsm.EL.Bls12MapFpToG1ResultBridge.g1PointBytesList
        (accelerator (acceleratorInputFromCallData memory dataStart)).output.point := by
  simp [execute, inputLength, h_status,
    EvmAsm.EL.Bls12MapFpToG1EcallBridge.executeBls12MapFpToG1Ecall,
    EvmAsm.EL.Bls12MapFpToG1EcallBridge.requestFromInput]


-- @@ L1389-1396 verbatim
@[simp] theorem execute_output_efail
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart : Nat)
    (h_status : (accelerator (acceleratorInputFromCallData memory dataStart)).status = .efail) :
    (execute accelerator memory dataStart inputLength).output = emptyOutput := by
  simp [execute, inputLength, h_status,
    EvmAsm.EL.Bls12MapFpToG1EcallBridge.executeBls12MapFpToG1Ecall,
    EvmAsm.EL.Bls12MapFpToG1EcallBridge.requestFromInput]


-- @@ L1398-1404 verbatim
theorem execute_output_eok_length
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart : Nat)
    (h_status : (accelerator (acceleratorInputFromCallData memory dataStart)).status = .eok) :
    (execute accelerator memory dataStart inputLength).output.length = 96 := by
  simp [execute_output_eok accelerator memory dataStart h_status,
    EvmAsm.EL.Bls12MapFpToG1ResultBridge.g1PointBytesList_length]


-- @@ L1406-1417 verbatim
@[simp] theorem execute_gasCharged
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart dataLength : Nat) :
    (execute accelerator memory dataStart dataLength).gasCharged =
      if dataLength = inputLength then gasCost else 0 := by
  by_cases h_length : dataLength = inputLength
  · subst dataLength
    cases h_status : (accelerator (acceleratorInputFromCallData memory dataStart)).status <;>
      simp [execute, inputLength, h_status,
        EvmAsm.EL.Bls12MapFpToG1EcallBridge.executeBls12MapFpToG1Ecall,
        EvmAsm.EL.Bls12MapFpToG1EcallBridge.requestFromInput]
  · simp [execute, h_length]


-- @@ L1419-1419 verbatim
end MapFpToG1


-- @@ L1421-1421 verbatim
namespace MapFp2ToG2


-- @@ L1423-1423 verbatim
abbrev MemoryReader := EvmAsm.EL.Bls12MapFp2ToG2InputBridge.MemoryReader

-- @@ L1424-1424 verbatim
abbrev AcceleratorInput := EvmAsm.EL.Bls12MapFp2ToG2InputBridge.AcceleratorInput

-- @@ L1425-1425 verbatim
abbrev AcceleratorResult := EvmAsm.EL.Bls12MapFp2ToG2ResultBridge.AcceleratorResult


-- @@ L1427-1428 verbatim
/-- EVM precompile address for BLS12-381 map-Fp2-to-G2. -/
def address : Nat := 0x11


-- @@ L1430-1433 verbatim
/-- Osaka executable-spec fixed gas cost for BLS12-381 map-Fp2-to-G2. -/
-- `@[expose]`: an exported in-file lemma proves a value fact about this body by rfl.
@[expose]
def gasCost : Nat := 23800


-- @@ L1435-1436 verbatim
/-- BLS12 map-Fp2-to-G2 consumes exactly one 128-byte Fp2 element. -/
def inputLength : Nat := 128


-- @@ L1438-1441 verbatim
/-- Invalid length, invalid field element, or accelerator failure returns no bytes. -/
-- `@[expose]`: an exported in-file lemma proves a value fact about this body by rfl.
@[expose]
def emptyOutput : ByteList := []


-- @@ L1443-1452 verbatim
/--
Result surface exposed by the pure BLS12-381 map-Fp2-to-G2 framing layer.
`exceptional = true` records executable-spec `InvalidParameter` cases.
-/
structure Result where
  exceptional : Bool
  status : ZkvmStatus
  output : ByteList
  gasCharged : Nat
  deriving Repr


-- @@ L1454-1461 verbatim
/--
Build the accelerator input from EVM call data. The executable spec first checks
`len(data) == 128`; callers must guard this helper with that exact length check.
-/
def acceleratorInputFromCallData (memory : MemoryReader) (dataStart : Nat) :
    AcceleratorInput :=
  EvmAsm.EL.Bls12MapFp2ToG2InputBridge.bls12MapFp2ToG2InputFromMemory
    memory dataStart


-- @@ L1463-1489 verbatim
/--
Pure BLS12-381 map-Fp2-to-G2 precompile framing. Field-element validation and
map-to-curve arithmetic are supplied by the accelerator model.
-/
def execute
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart dataLength : Nat) : Result :=
  if dataLength = inputLength then
    let input := acceleratorInputFromCallData memory dataStart
    let result := EvmAsm.EL.Bls12MapFp2ToG2EcallBridge.executeBls12MapFp2ToG2Ecall accelerator
      (EvmAsm.EL.Bls12MapFp2ToG2EcallBridge.requestFromInput input)
    match result.status with
    | .eok =>
        { exceptional := false
          status := result.status
          output := EvmAsm.EL.Bls12MapFp2ToG2ResultBridge.g2PointBytesList result.output.point
          gasCharged := gasCost }
    | .efail =>
        { exceptional := true
          status := result.status
          output := emptyOutput
          gasCharged := gasCost }
  else
    { exceptional := true
      status := .efail
      output := emptyOutput
      gasCharged := 0 }


-- @@ L1491-1492 verbatim
theorem emptyOutput_length :
    emptyOutput.length = 0 := rfl


-- @@ L1494-1503 verbatim
@[simp] theorem execute_badLength
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart dataLength : Nat)
    (h_length : dataLength ≠ inputLength) :
    execute accelerator memory dataStart dataLength =
      { exceptional := true
        status := .efail
        output := emptyOutput
        gasCharged := 0 } := by
  simp [execute, h_length]


-- @@ L1505-1513 verbatim
@[simp] theorem execute_status
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart : Nat) :
    (execute accelerator memory dataStart inputLength).status =
      (accelerator (acceleratorInputFromCallData memory dataStart)).status := by
  cases h_status : (accelerator (acceleratorInputFromCallData memory dataStart)).status <;>
    simp [execute, inputLength, h_status,
      EvmAsm.EL.Bls12MapFp2ToG2EcallBridge.executeBls12MapFp2ToG2Ecall,
      EvmAsm.EL.Bls12MapFp2ToG2EcallBridge.requestFromInput]


-- @@ L1515-1524 verbatim
@[simp] theorem execute_output_eok
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart : Nat)
    (h_status : (accelerator (acceleratorInputFromCallData memory dataStart)).status = .eok) :
    (execute accelerator memory dataStart inputLength).output =
      EvmAsm.EL.Bls12MapFp2ToG2ResultBridge.g2PointBytesList
        (accelerator (acceleratorInputFromCallData memory dataStart)).output.point := by
  simp [execute, inputLength, h_status,
    EvmAsm.EL.Bls12MapFp2ToG2EcallBridge.executeBls12MapFp2ToG2Ecall,
    EvmAsm.EL.Bls12MapFp2ToG2EcallBridge.requestFromInput]


-- @@ L1526-1533 verbatim
@[simp] theorem execute_output_efail
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart : Nat)
    (h_status : (accelerator (acceleratorInputFromCallData memory dataStart)).status = .efail) :
    (execute accelerator memory dataStart inputLength).output = emptyOutput := by
  simp [execute, inputLength, h_status,
    EvmAsm.EL.Bls12MapFp2ToG2EcallBridge.executeBls12MapFp2ToG2Ecall,
    EvmAsm.EL.Bls12MapFp2ToG2EcallBridge.requestFromInput]


-- @@ L1535-1541 verbatim
theorem execute_output_eok_length
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart : Nat)
    (h_status : (accelerator (acceleratorInputFromCallData memory dataStart)).status = .eok) :
    (execute accelerator memory dataStart inputLength).output.length = 192 := by
  simp [execute_output_eok accelerator memory dataStart h_status,
    EvmAsm.EL.Bls12MapFp2ToG2ResultBridge.g2PointBytesList_length]


-- @@ L1543-1554 verbatim
@[simp] theorem execute_gasCharged
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart dataLength : Nat) :
    (execute accelerator memory dataStart dataLength).gasCharged =
      if dataLength = inputLength then gasCost else 0 := by
  by_cases h_length : dataLength = inputLength
  · subst dataLength
    cases h_status : (accelerator (acceleratorInputFromCallData memory dataStart)).status <;>
      simp [execute, inputLength, h_status,
        EvmAsm.EL.Bls12MapFp2ToG2EcallBridge.executeBls12MapFp2ToG2Ecall,
        EvmAsm.EL.Bls12MapFp2ToG2EcallBridge.requestFromInput]
  · simp [execute, h_length]


-- @@ L1556-1556 verbatim
end MapFp2ToG2



-- @@ L1559-1559 verbatim
namespace G1Add


-- @@ L1561-1561 verbatim
abbrev MemoryReader := EvmAsm.EL.Bls12G1AddInputBridge.MemoryReader

-- @@ L1562-1562 verbatim
abbrev AcceleratorInput := EvmAsm.EL.Bls12G1AddInputBridge.AcceleratorInput

-- @@ L1563-1563 verbatim
abbrev AcceleratorResult := EvmAsm.EL.Bls12G1AddResultBridge.AcceleratorResult

-- @@ L1564-1564 verbatim
abbrev G1PointBytes := EvmAsm.EL.Bls12G1AddInputBridge.G1PointBytes


-- @@ L1566-1567 verbatim
/-- EVM precompile address for BLS12-381 G1 addition. -/
def address : Nat := 0x0b


-- @@ L1569-1572 verbatim
/-- Osaka executable-spec fixed gas cost for BLS12-381 G1 addition. -/
-- `@[expose]`: an exported in-file lemma proves a value fact about this body by rfl.
@[expose]
def gasCost : Nat := 375


-- @@ L1574-1575 verbatim
/-- BLS12 G1 ADD consumes exactly two 128-byte EIP-2537 G1 points. -/
def inputLength : Nat := 256


-- @@ L1577-1578 verbatim
/-- Offset of the second input point in the EVM call payload. -/
def p2Offset : Nat := 128


-- @@ L1580-1583 verbatim
/-- Invalid length, invalid point encoding, or accelerator failure returns no bytes. -/
-- `@[expose]`: an exported in-file lemma proves a value fact about this body by rfl.
@[expose]
def emptyOutput : ByteList := []


-- @@ L1585-1594 verbatim
/--
Result surface exposed by the pure BLS12-381 G1 ADD framing layer.
`exceptional = true` records executable-spec `InvalidParameter` cases.
-/
structure Result where
  exceptional : Bool
  status : ZkvmStatus
  output : ByteList
  gasCharged : Nat
  deriving Repr


-- @@ L1596-1603 verbatim
/-- Convert a 128-byte EIP-2537 G1 point into the accelerator's 96-byte G1 payload. -/
def g1PointFromEvmBytes (memory : MemoryReader) (pointStart : Nat) : G1PointBytes :=
  fun i =>
    let n := i.toNat
    if n < 48 then
      memory (pointStart + 16 + n)
    else
      memory (pointStart + 64 + 16 + (n - 48))


-- @@ L1605-1612 verbatim
/--
Build the accelerator input from EVM call data. The executable spec first checks
`len(data) == 256`; callers must guard this helper with that exact length check.
-/
def acceleratorInputFromCallData (memory : MemoryReader) (dataStart : Nat) :
    AcceleratorInput :=
  { p1 := g1PointFromEvmBytes memory dataStart
    p2 := g1PointFromEvmBytes memory (dataStart + p2Offset) }


-- @@ L1614-1640 verbatim
/--
Pure BLS12-381 G1 ADD precompile framing. Point validation and curve arithmetic
are supplied by the accelerator model.
-/
def execute
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart dataLength : Nat) : Result :=
  if dataLength = inputLength then
    let input := acceleratorInputFromCallData memory dataStart
    let result := EvmAsm.EL.Bls12G1AddEcallBridge.executeBls12G1AddEcall accelerator
      (EvmAsm.EL.Bls12G1AddEcallBridge.requestFromInput input)
    match result.status with
    | .eok =>
        { exceptional := false
          status := result.status
          output := EvmAsm.EL.Bls12G1AddResultBridge.g1PointBytesList result.output.point
          gasCharged := gasCost }
    | .efail =>
        { exceptional := true
          status := result.status
          output := emptyOutput
          gasCharged := gasCost }
  else
    { exceptional := true
      status := .efail
      output := emptyOutput
      gasCharged := 0 }


-- @@ L1642-1643 verbatim
theorem emptyOutput_length :
    emptyOutput.length = 0 := rfl


-- @@ L1645-1654 verbatim
@[simp] theorem execute_badLength
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart dataLength : Nat)
    (h_length : dataLength ≠ inputLength) :
    execute accelerator memory dataStart dataLength =
      { exceptional := true
        status := .efail
        output := emptyOutput
        gasCharged := 0 } := by
  simp [execute, h_length]


-- @@ L1656-1664 verbatim
@[simp] theorem execute_status
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart : Nat) :
    (execute accelerator memory dataStart inputLength).status =
      (accelerator (acceleratorInputFromCallData memory dataStart)).status := by
  cases h_status : (accelerator (acceleratorInputFromCallData memory dataStart)).status <;>
    simp [execute, inputLength, h_status,
      EvmAsm.EL.Bls12G1AddEcallBridge.executeBls12G1AddEcall,
      EvmAsm.EL.Bls12G1AddEcallBridge.requestFromInput]


-- @@ L1666-1675 verbatim
@[simp] theorem execute_output_eok
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart : Nat)
    (h_status : (accelerator (acceleratorInputFromCallData memory dataStart)).status = .eok) :
    (execute accelerator memory dataStart inputLength).output =
      EvmAsm.EL.Bls12G1AddResultBridge.g1PointBytesList
        (accelerator (acceleratorInputFromCallData memory dataStart)).output.point := by
  simp [execute, inputLength, h_status,
    EvmAsm.EL.Bls12G1AddEcallBridge.executeBls12G1AddEcall,
    EvmAsm.EL.Bls12G1AddEcallBridge.requestFromInput]


-- @@ L1677-1684 verbatim
@[simp] theorem execute_output_efail
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart : Nat)
    (h_status : (accelerator (acceleratorInputFromCallData memory dataStart)).status = .efail) :
    (execute accelerator memory dataStart inputLength).output = emptyOutput := by
  simp [execute, inputLength, h_status,
    EvmAsm.EL.Bls12G1AddEcallBridge.executeBls12G1AddEcall,
    EvmAsm.EL.Bls12G1AddEcallBridge.requestFromInput]


-- @@ L1686-1692 verbatim
theorem execute_output_eok_length
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart : Nat)
    (h_status : (accelerator (acceleratorInputFromCallData memory dataStart)).status = .eok) :
    (execute accelerator memory dataStart inputLength).output.length = 96 := by
  simp [execute_output_eok accelerator memory dataStart h_status,
    EvmAsm.EL.Bls12G1AddResultBridge.g1PointBytesList_length]


-- @@ L1694-1705 verbatim
@[simp] theorem execute_gasCharged
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart dataLength : Nat) :
    (execute accelerator memory dataStart dataLength).gasCharged =
      if dataLength = inputLength then gasCost else 0 := by
  by_cases h_length : dataLength = inputLength
  · subst dataLength
    cases h_status : (accelerator (acceleratorInputFromCallData memory dataStart)).status <;>
      simp [execute, inputLength, h_status,
        EvmAsm.EL.Bls12G1AddEcallBridge.executeBls12G1AddEcall,
        EvmAsm.EL.Bls12G1AddEcallBridge.requestFromInput]
  · simp [execute, h_length]


-- @@ L1707-1707 verbatim
end G1Add


-- @@ L1709-1709 verbatim
namespace G2Add


-- @@ L1711-1711 verbatim
abbrev MemoryReader := EvmAsm.EL.Bls12G2AddInputBridge.MemoryReader

-- @@ L1712-1712 verbatim
abbrev AcceleratorInput := EvmAsm.EL.Bls12G2AddInputBridge.AcceleratorInput

-- @@ L1713-1713 verbatim
abbrev AcceleratorResult := EvmAsm.EL.Bls12G2AddResultBridge.AcceleratorResult

-- @@ L1714-1714 verbatim
abbrev G2PointBytes := EvmAsm.EL.Bls12G2AddInputBridge.G2PointBytes


-- @@ L1716-1717 verbatim
/-- EVM precompile address for BLS12-381 G2 addition. -/
def address : Nat := 0x0d


-- @@ L1719-1722 verbatim
/-- Osaka executable-spec fixed gas cost for BLS12-381 G2 addition. -/
-- `@[expose]`: an exported in-file lemma proves a value fact about this body by rfl.
@[expose]
def gasCost : Nat := 600


-- @@ L1724-1725 verbatim
/-- BLS12 G2 ADD consumes exactly two 256-byte EIP-2537 G2 points. -/
def inputLength : Nat := 512


-- @@ L1727-1728 verbatim
/-- Offset of the second input point in the EVM call payload. -/
def p2Offset : Nat := 256


-- @@ L1730-1733 verbatim
/-- Invalid length, invalid point encoding, or accelerator failure returns no bytes. -/
-- `@[expose]`: an exported in-file lemma proves a value fact about this body by rfl.
@[expose]
def emptyOutput : ByteList := []


-- @@ L1735-1744 verbatim
/--
Result surface exposed by the pure BLS12-381 G2 ADD framing layer.
`exceptional = true` records executable-spec `InvalidParameter` cases.
-/
structure Result where
  exceptional : Bool
  status : ZkvmStatus
  output : ByteList
  gasCharged : Nat
  deriving Repr


-- @@ L1746-1757 verbatim
/-- Convert a 256-byte EIP-2537 G2 point into the accelerator's 192-byte G2 payload. -/
def g2PointFromEvmBytes (memory : MemoryReader) (pointStart : Nat) : G2PointBytes :=
  fun i =>
    let n := i.toNat
    if n < 48 then
      memory (pointStart + 16 + n)
    else if n < 96 then
      memory (pointStart + 64 + 16 + (n - 48))
    else if n < 144 then
      memory (pointStart + 128 + 16 + (n - 96))
    else
      memory (pointStart + 192 + 16 + (n - 144))


-- @@ L1759-1766 verbatim
/--
Build the accelerator input from EVM call data. The executable spec first checks
`len(data) == 512`; callers must guard this helper with that exact length check.
-/
def acceleratorInputFromCallData (memory : MemoryReader) (dataStart : Nat) :
    AcceleratorInput :=
  { p1 := g2PointFromEvmBytes memory dataStart
    p2 := g2PointFromEvmBytes memory (dataStart + p2Offset) }


-- @@ L1768-1794 verbatim
/--
Pure BLS12-381 G2 ADD precompile framing. Point validation and curve arithmetic
are supplied by the accelerator model.
-/
def execute
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart dataLength : Nat) : Result :=
  if dataLength = inputLength then
    let input := acceleratorInputFromCallData memory dataStart
    let result := EvmAsm.EL.Bls12G2AddEcallBridge.executeBls12G2AddEcall accelerator
      (EvmAsm.EL.Bls12G2AddEcallBridge.requestFromInput input)
    match result.status with
    | .eok =>
        { exceptional := false
          status := result.status
          output := EvmAsm.EL.Bls12G2AddResultBridge.g2PointBytesList result.output.point
          gasCharged := gasCost }
    | .efail =>
        { exceptional := true
          status := result.status
          output := emptyOutput
          gasCharged := gasCost }
  else
    { exceptional := true
      status := .efail
      output := emptyOutput
      gasCharged := 0 }


-- @@ L1796-1797 verbatim
theorem emptyOutput_length :
    emptyOutput.length = 0 := rfl


-- @@ L1799-1808 verbatim
@[simp] theorem execute_badLength
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart dataLength : Nat)
    (h_length : dataLength ≠ inputLength) :
    execute accelerator memory dataStart dataLength =
      { exceptional := true
        status := .efail
        output := emptyOutput
        gasCharged := 0 } := by
  simp [execute, h_length]


-- @@ L1810-1818 verbatim
@[simp] theorem execute_status
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart : Nat) :
    (execute accelerator memory dataStart inputLength).status =
      (accelerator (acceleratorInputFromCallData memory dataStart)).status := by
  cases h_status : (accelerator (acceleratorInputFromCallData memory dataStart)).status <;>
    simp [execute, inputLength, h_status,
      EvmAsm.EL.Bls12G2AddEcallBridge.executeBls12G2AddEcall,
      EvmAsm.EL.Bls12G2AddEcallBridge.requestFromInput]


-- @@ L1820-1829 verbatim
@[simp] theorem execute_output_eok
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart : Nat)
    (h_status : (accelerator (acceleratorInputFromCallData memory dataStart)).status = .eok) :
    (execute accelerator memory dataStart inputLength).output =
      EvmAsm.EL.Bls12G2AddResultBridge.g2PointBytesList
        (accelerator (acceleratorInputFromCallData memory dataStart)).output.point := by
  simp [execute, inputLength, h_status,
    EvmAsm.EL.Bls12G2AddEcallBridge.executeBls12G2AddEcall,
    EvmAsm.EL.Bls12G2AddEcallBridge.requestFromInput]


-- @@ L1831-1838 verbatim
@[simp] theorem execute_output_efail
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart : Nat)
    (h_status : (accelerator (acceleratorInputFromCallData memory dataStart)).status = .efail) :
    (execute accelerator memory dataStart inputLength).output = emptyOutput := by
  simp [execute, inputLength, h_status,
    EvmAsm.EL.Bls12G2AddEcallBridge.executeBls12G2AddEcall,
    EvmAsm.EL.Bls12G2AddEcallBridge.requestFromInput]


-- @@ L1840-1846 verbatim
theorem execute_output_eok_length
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart : Nat)
    (h_status : (accelerator (acceleratorInputFromCallData memory dataStart)).status = .eok) :
    (execute accelerator memory dataStart inputLength).output.length = 192 := by
  simp [execute_output_eok accelerator memory dataStart h_status,
    EvmAsm.EL.Bls12G2AddResultBridge.g2PointBytesList_length]


-- @@ L1848-1859 verbatim
@[simp] theorem execute_gasCharged
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart dataLength : Nat) :
    (execute accelerator memory dataStart dataLength).gasCharged =
      if dataLength = inputLength then gasCost else 0 := by
  by_cases h_length : dataLength = inputLength
  · subst dataLength
    cases h_status : (accelerator (acceleratorInputFromCallData memory dataStart)).status <;>
      simp [execute, inputLength, h_status,
        EvmAsm.EL.Bls12G2AddEcallBridge.executeBls12G2AddEcall,
        EvmAsm.EL.Bls12G2AddEcallBridge.requestFromInput]
  · simp [execute, h_length]


-- @@ L1861-1861 verbatim
end G2Add



-- @@ L1864-1864 verbatim
end BLS12


-- @@ L1866-1866 verbatim
namespace KzgPointEvaluation


-- @@ L1868-1868 verbatim
abbrev MemoryReader := EvmAsm.EL.KzgPointEvalInputBridge.MemoryReader

-- @@ L1869-1869 verbatim
abbrev Bytes32 := EvmAsm.EL.KzgPointEvalInputBridge.Bytes32

-- @@ L1870-1870 verbatim
abbrev AcceleratorInput := EvmAsm.EL.KzgPointEvalInputBridge.AcceleratorInput

-- @@ L1871-1871 verbatim
abbrev AcceleratorResult := EvmAsm.EL.KzgPointEvalResultBridge.AcceleratorResult


-- @@ L1873-1874 verbatim
/-- EVM precompile address for EIP-4844 KZG point evaluation. -/
def address : Nat := 0x0a


-- @@ L1876-1879 verbatim
/-- Osaka/BPO executable-spec fixed gas cost for KZG point evaluation. -/
-- `@[expose]`: an exported in-file lemma proves a value fact about this body by rfl.
@[expose]
def gasCost : Nat := 50000


-- @@ L1881-1882 verbatim
/-- KZG point evaluation consumes exactly 192 bytes. -/
def inputLength : Nat := 192


-- @@ L1884-1884 verbatim
def versionedHashOffset : Nat := 0

-- @@ L1885-1885 verbatim
def zOffset : Nat := 32

-- @@ L1886-1886 verbatim
def yOffset : Nat := 64

-- @@ L1887-1887 verbatim
def commitmentOffset : Nat := 96

-- @@ L1888-1888 verbatim
def proofOffset : Nat := 144


-- @@ L1890-1892 verbatim
/-- `U256(4096).to_be_bytes32()`, i.e. `FIELD_ELEMENTS_PER_BLOB`. -/
def fieldElementsPerBlobOutput : ByteList :=
  List.replicate 30 (0 : Byte) ++ [0x10, 0x00]


-- @@ L1894-1899 verbatim
/-- `U256(BLS_MODULUS).to_be_bytes32()` from execution-specs. -/
def blsModulusOutput : ByteList :=
  [ 0x73, 0xed, 0xa7, 0x53, 0x29, 0x9d, 0x7d, 0x48
  , 0x33, 0x39, 0xd8, 0x08, 0x09, 0xa1, 0xd8, 0x05
  , 0x53, 0xbd, 0xa4, 0x02, 0xff, 0xfe, 0x5b, 0xfe
  , 0xff, 0xff, 0xff, 0xff, 0x00, 0x00, 0x00, 0x01 ]


-- @@ L1901-1905 verbatim
/-- Successful KZG point evaluation returns `FIELD_ELEMENTS_PER_BLOB || BLS_MODULUS`. -/
-- `@[expose]`: an exported in-file lemma proves a value fact about this body by rfl.
@[expose]
def successOutput : ByteList :=
  fieldElementsPerBlobOutput ++ blsModulusOutput


-- @@ L1907-1910 verbatim
/-- Invalid length, invalid hash/proof, or accelerator failure returns no bytes. -/
-- `@[expose]`: an exported in-file lemma proves a value fact about this body by rfl.
@[expose]
def emptyOutput : ByteList := []


-- @@ L1912-1922 verbatim
/--
Result surface exposed by the pure precompile framing layer. `exceptional`
records execution-spec `KZGProofError` cases; later CALL/STATICCALL wiring can
translate that into the enclosing EVM failure semantics.
-/
structure Result where
  exceptional : Bool
  status : ZkvmStatus
  output : ByteList
  gasCharged : Nat
  deriving Repr


-- @@ L1924-1927 verbatim
/-- The versioned hash is the first 32 bytes of the precompile payload. -/
def versionedHashFromCallData (memory : MemoryReader) (dataStart : Nat) : Bytes32 :=
  EvmAsm.EL.KzgPointEvalInputBridge.bytes32FromMemory
    memory (dataStart + versionedHashOffset)


-- @@ L1929-1941 verbatim
/--
Build the accelerator input from the EVM call data. The executable spec first
checks `len(data) == 192`; callers must guard this helper with that exact
length check. Field starts mirror `point_evaluation.py`.
-/
def acceleratorInputFromCallData (memory : MemoryReader) (dataStart : Nat) :
    AcceleratorInput :=
  EvmAsm.EL.KzgPointEvalInputBridge.kzgPointEvalInputFromMemory
    memory
    (dataStart + commitmentOffset)
    (dataStart + zOffset)
    (dataStart + yOffset)
    (dataStart + proofOffset)


-- @@ L1943-1947 verbatim
/-- Convert the accelerator proof-verification result to EVM return data. -/
-- `@[expose]`: an exported in-file lemma proves a value fact about this body by rfl.
@[expose]
def outputFromVerified (verified : Bool) : ByteList :=
  if verified then successOutput else emptyOutput


-- @@ L1949-1990 verbatim
/--
Pure KZG point-evaluation precompile framing. This models the executable-spec
guards and return-data shape:

* input length must be exactly 192 bytes;
* the supplied `versionedHashIsValid` hook checks
  `kzg_commitment_to_versioned_hash(commitment) == versioned_hash`;
* the supplied accelerator verifies `(commitment, z, y, proof)`;
* success returns `FIELD_ELEMENTS_PER_BLOB || BLS_MODULUS`.
-/
def execute
    (versionedHashIsValid : Bytes32 → AcceleratorInput → Bool)
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart dataLength : Nat) : Result :=
  if dataLength = inputLength then
    let input := acceleratorInputFromCallData memory dataStart
    let versionedHash := versionedHashFromCallData memory dataStart
    if versionedHashIsValid versionedHash input then
      let request := EvmAsm.EL.KzgPointEvalEcallBridge.requestFromInput input
      let result := EvmAsm.EL.KzgPointEvalEcallBridge.executeKzgPointEvalEcall
        accelerator request
      match result.status with
      | .eok =>
          { exceptional := !result.output.verified
            status := if result.output.verified then .eok else .efail
            output := outputFromVerified result.output.verified
            gasCharged := gasCost }
      | .efail =>
          { exceptional := true
            status := result.status
            output := emptyOutput
            gasCharged := gasCost }
    else
      { exceptional := true
        status := .efail
        output := emptyOutput
        gasCharged := gasCost }
  else
    { exceptional := true
      status := .efail
      output := emptyOutput
      gasCharged := 0 }


-- @@ L1992-1994 verbatim
theorem fieldElementsPerBlobOutput_length :
    fieldElementsPerBlobOutput.length = 32 := by
  decide


-- @@ L1996-1998 verbatim
theorem blsModulusOutput_length :
    blsModulusOutput.length = 32 := by
  decide


-- @@ L2000-2002 verbatim
theorem successOutput_length :
    successOutput.length = 64 := by
  decide


-- @@ L2004-2005 verbatim
theorem emptyOutput_length :
    emptyOutput.length = 0 := rfl


-- @@ L2007-2008 verbatim
@[simp] theorem outputFromVerified_true :
    outputFromVerified true = successOutput := rfl


-- @@ L2010-2011 verbatim
@[simp] theorem outputFromVerified_false :
    outputFromVerified false = emptyOutput := rfl


-- @@ L2013-2023 verbatim
@[simp] theorem execute_badLength
    (versionedHashIsValid : Bytes32 → AcceleratorInput → Bool)
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart dataLength : Nat)
    (h_length : dataLength ≠ inputLength) :
    execute versionedHashIsValid accelerator memory dataStart dataLength =
      { exceptional := true
        status := .efail
        output := emptyOutput
        gasCharged := 0 } := by
  simp [execute, h_length]


-- @@ L2025-2038 verbatim
@[simp] theorem execute_invalidVersionedHash
    (versionedHashIsValid : Bytes32 → AcceleratorInput → Bool)
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart : Nat)
    (h_hash :
      versionedHashIsValid
        (versionedHashFromCallData memory dataStart)
        (acceleratorInputFromCallData memory dataStart) = false) :
    execute versionedHashIsValid accelerator memory dataStart inputLength =
      { exceptional := true
        status := .efail
        output := emptyOutput
        gasCharged := gasCost } := by
  simp [execute, inputLength, h_hash]


-- @@ L2040-2056 verbatim
@[simp] theorem execute_output_verified
    (versionedHashIsValid : Bytes32 → AcceleratorInput → Bool)
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart : Nat)
    (h_hash :
      versionedHashIsValid
        (versionedHashFromCallData memory dataStart)
        (acceleratorInputFromCallData memory dataStart) = true)
    (h_status :
      (accelerator (acceleratorInputFromCallData memory dataStart)).status = .eok)
    (h_verified :
      (accelerator (acceleratorInputFromCallData memory dataStart)).output.verified = true) :
    (execute versionedHashIsValid accelerator memory dataStart inputLength).output =
      successOutput := by
  simp [execute, inputLength, h_hash, h_status, h_verified,
    EvmAsm.EL.KzgPointEvalEcallBridge.executeKzgPointEvalEcall,
    EvmAsm.EL.KzgPointEvalEcallBridge.requestFromInput]


-- @@ L2058-2074 verbatim
@[simp] theorem execute_output_unverified
    (versionedHashIsValid : Bytes32 → AcceleratorInput → Bool)
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart : Nat)
    (h_hash :
      versionedHashIsValid
        (versionedHashFromCallData memory dataStart)
        (acceleratorInputFromCallData memory dataStart) = true)
    (h_status :
      (accelerator (acceleratorInputFromCallData memory dataStart)).status = .eok)
    (h_verified :
      (accelerator (acceleratorInputFromCallData memory dataStart)).output.verified = false) :
    (execute versionedHashIsValid accelerator memory dataStart inputLength).output =
      emptyOutput := by
  simp [execute, inputLength, h_hash, h_status, h_verified,
    EvmAsm.EL.KzgPointEvalEcallBridge.executeKzgPointEvalEcall,
    EvmAsm.EL.KzgPointEvalEcallBridge.requestFromInput]


-- @@ L2076-2096 verbatim
@[simp] theorem execute_gasCharged
    (versionedHashIsValid : Bytes32 → AcceleratorInput → Bool)
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart dataLength : Nat) :
    (execute versionedHashIsValid accelerator memory dataStart dataLength).gasCharged =
      if dataLength = inputLength then gasCost else 0 := by
  by_cases h_length : dataLength = inputLength
  · subst dataLength
    cases h_hash :
        versionedHashIsValid
          (versionedHashFromCallData memory dataStart)
          (acceleratorInputFromCallData memory dataStart)
    · simp [execute, inputLength, h_hash]
    · cases h_status :
          (accelerator (acceleratorInputFromCallData memory dataStart)).status <;>
        cases h_verified :
          (accelerator (acceleratorInputFromCallData memory dataStart)).output.verified <;>
        simp [execute, inputLength, h_hash, h_status, h_verified,
          EvmAsm.EL.KzgPointEvalEcallBridge.executeKzgPointEvalEcall,
          EvmAsm.EL.KzgPointEvalEcallBridge.requestFromInput]
  · simp [execute, h_length]


-- @@ L2098-2098 verbatim
end KzgPointEvaluation


-- @@ L2100-2100 verbatim
namespace P256Verify


-- @@ L2102-2102 verbatim
abbrev MemoryReader := EvmAsm.EL.Secp256r1VerifyInputBridge.MemoryReader

-- @@ L2103-2103 verbatim
abbrev AcceleratorInput := EvmAsm.EL.Secp256r1VerifyInputBridge.AcceleratorInput

-- @@ L2104-2104 verbatim
abbrev AcceleratorResult := EvmAsm.EL.Secp256r1VerifyResultBridge.AcceleratorResult


-- @@ L2106-2107 verbatim
/-- EVM precompile address for P256VERIFY / secp256r1 verification. -/
def address : Nat := 0x100


-- @@ L2109-2112 verbatim
/-- Osaka/BPO executable-spec gas cost for P256VERIFY. -/
-- `@[expose]`: an exported in-file lemma proves a value fact about this body by rfl.
@[expose]
def gasCost : Nat := 6900


-- @@ L2114-2115 verbatim
/-- P256VERIFY consumes exactly five 32-byte fields. -/
def inputLength : Nat := 160


-- @@ L2117-2121 verbatim
/-- Successful P256VERIFY returns `left_pad_zero_bytes(b"\x01", 32)`. -/
-- `@[expose]`: an exported in-file lemma proves a value fact about this body by rfl.
@[expose]
def successOutput : ByteList :=
  List.replicate 31 (0 : Byte) ++ [1]


-- @@ L2123-2126 verbatim
/-- Invalid input, invalid signature, or accelerator failure returns no bytes. -/
-- `@[expose]`: an exported in-file lemma proves a value fact about this body by rfl.
@[expose]
def emptyOutput : ByteList := []


-- @@ L2128-2133 verbatim
/-- Result surface exposed to the caller by the pure precompile framing layer. -/
structure Result where
  status : ZkvmStatus
  output : ByteList
  gasCharged : Nat
  deriving Repr


-- @@ L2135-2143 verbatim
/--
Build the fixed accelerator input fields from the EVM call data. The executable
spec first checks `len(data) == 160`; callers must guard this helper with that
length check. Field starts mirror `p256verify.py`: msg, r, s, qx, qy.
-/
def acceleratorInputFromCallData (memory : MemoryReader) (dataStart : Nat) :
    AcceleratorInput :=
  EvmAsm.EL.Secp256r1VerifyInputBridge.secp256r1VerifyInputFromMemory
    memory dataStart (dataStart + 32) (dataStart + 96)


-- @@ L2145-2149 verbatim
/-- Convert a successful accelerator boolean to the EVM return-data bytes. -/
-- `@[expose]`: an exported in-file lemma proves a value fact about this body by rfl.
@[expose]
def outputFromVerified (verified : Bool) : ByteList :=
  if verified then successOutput else emptyOutput


-- @@ L2151-2170 verbatim
/--
Pure P256VERIFY precompile framing. This models the EVM-side guards and
return-data shape; scalar bounds, curve membership, and signature validation are
part of the supplied accelerator model, matching the existing secp256r1 bridge.
-/
def execute
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart dataLength : Nat) : Result :=
  if dataLength = inputLength then
    let input := acceleratorInputFromCallData memory dataStart
    let result := accelerator input
    match result.status with
    | .eok =>
        { status := result.status
          output := outputFromVerified result.output.verified
          gasCharged := gasCost }
    | .efail =>
        { status := result.status, output := emptyOutput, gasCharged := gasCost }
  else
    { status := .eok, output := emptyOutput, gasCharged := gasCost }


-- @@ L2172-2174 verbatim
theorem successOutput_length :
    successOutput.length = 32 := by
  simp [successOutput]


-- @@ L2176-2177 verbatim
theorem emptyOutput_length :
    emptyOutput.length = 0 := rfl


-- @@ L2179-2180 verbatim
@[simp] theorem outputFromVerified_true :
    outputFromVerified true = successOutput := rfl


-- @@ L2182-2183 verbatim
@[simp] theorem outputFromVerified_false :
    outputFromVerified false = emptyOutput := rfl


-- @@ L2185-2191 verbatim
@[simp] theorem execute_badLength
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart dataLength : Nat)
    (h_length : dataLength ≠ inputLength) :
    execute accelerator memory dataStart dataLength =
      { status := .eok, output := emptyOutput, gasCharged := gasCost } := by
  simp [execute, h_length]


-- @@ L2193-2199 verbatim
@[simp] theorem execute_status
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart : Nat) :
    (execute accelerator memory dataStart inputLength).status =
      (accelerator (acceleratorInputFromCallData memory dataStart)).status := by
  cases h_status : (accelerator (acceleratorInputFromCallData memory dataStart)).status <;>
    simp [execute, inputLength, h_status]


-- @@ L2201-2208 verbatim
@[simp] theorem execute_output_eok
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart : Nat)
    (h_status : (accelerator (acceleratorInputFromCallData memory dataStart)).status = .eok) :
    (execute accelerator memory dataStart inputLength).output =
      outputFromVerified
        (accelerator (acceleratorInputFromCallData memory dataStart)).output.verified := by
  simp [execute, inputLength, h_status]


-- @@ L2210-2215 verbatim
@[simp] theorem execute_output_efail
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart : Nat)
    (h_status : (accelerator (acceleratorInputFromCallData memory dataStart)).status = .efail) :
    (execute accelerator memory dataStart inputLength).output = emptyOutput := by
  simp [execute, inputLength, h_status]


-- @@ L2217-2225 verbatim
@[simp] theorem execute_gasCharged
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart dataLength : Nat) :
    (execute accelerator memory dataStart dataLength).gasCharged = gasCost := by
  by_cases h_length : dataLength = inputLength
  · subst dataLength
    cases h_status : (accelerator (acceleratorInputFromCallData memory dataStart)).status <;>
      simp [execute, inputLength, h_status]
  · simp [execute, h_length]


-- @@ L2227-2227 verbatim
end P256Verify


-- @@ L2229-2229 verbatim
end EvmAsm.Stateless.VM.Precompiles
