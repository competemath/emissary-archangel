/-
  EvmAsm.Stateless.SpecRef.Ssz

  Port of `execution-specs/src/ethereum/forks/amsterdam/stateless_ssz.py`
  (`@tests-zkevm@v0.6.0`, `40f956fab`): the SSZ container schemas mirroring
  the domain dataclasses, plus the to/from-SSZ conversion functions.

  Each Python `class SszX(Container)` becomes an `SszType` descriptor
  (`sszXType`); each `_x_to_ssz` becomes `xToSsz : … → SszValue`; each
  `_ssz_to_x` becomes `sszToX : SszValue → Except SpecError …`. The generic
  `encode_bytes` / `decode_bytes` / `hash_tree_root` live in `SszCodec.lean`.

  Field ORDER in every `SszType.container`/`SszValue.container` matches the
  Python class field order exactly (SSZ is order-sensitive), so the
  positional `getField` accessors in the `sszToX` direction line up with
  the class attributes.
-/

module

public import EvmAsm.Stateless.SpecRef.SszCodec
meta import EvmAsm.Stateless.SpecRef.SszCodec


-- @@ L24-24 verbatim
@[expose] public section


-- @@ L26-26 verbatim
namespace EvmAsm.Stateless.SpecRef


-- @@ L28-28 verbatim
/-! ## SSZ max-length constants (`stateless_ssz.py:54`–`89`) -/


-- @@ L30-30 verbatim
def MAX_EXTRA_DATA_BYTES : Nat := 32

-- @@ L31-31 verbatim
def MAX_BYTES_PER_TRANSACTION : Nat := 2 ^ 30

-- @@ L32-32 verbatim
def MAX_TRANSACTIONS_PER_PAYLOAD : Nat := 2 ^ 20

-- @@ L33-33 verbatim
def MAX_WITHDRAWALS_PER_PAYLOAD : Nat := 2 ^ 4

-- @@ L34-34 verbatim
def MAX_BLOB_COMMITMENTS_PER_BLOCK : Nat := 4096

-- @@ L35-35 verbatim
def MAX_DEPOSIT_REQUESTS_PER_PAYLOAD : Nat := 2 ^ 13

-- @@ L36-36 verbatim
def MAX_WITHDRAWAL_REQUESTS_PER_PAYLOAD : Nat := 2 ^ 4

-- @@ L37-37 verbatim
def MAX_CONSOLIDATION_REQUESTS_PER_PAYLOAD : Nat := 2 ^ 1

-- @@ L38-38 verbatim
def MAX_BUILDER_DEPOSIT_REQUESTS_PER_PAYLOAD : Nat := 2 ^ 6

-- @@ L39-39 verbatim
def MAX_BUILDER_EXIT_REQUESTS_PER_PAYLOAD : Nat := 2 ^ 4

-- @@ L40-40 verbatim
def MAX_BLOCK_ACCESS_LIST_BYTES : Nat := MAX_BYTES_PER_TRANSACTION

-- @@ L41-41 verbatim
def MAX_WITNESS_NODES : Nat := 2 ^ 22

-- @@ L42-42 verbatim
def MAX_WITNESS_CODES : Nat := 2 ^ 18

-- @@ L43-43 verbatim
def MAX_WITNESS_HEADERS : Nat := 256

-- @@ L44-44 verbatim
def MAX_BYTES_PER_WITNESS_NODE : Nat := 2 ^ 10

-- @@ L45-45 verbatim
def MAX_BYTES_PER_CODE : Nat := 2 ^ 16

-- @@ L46-46 verbatim
def MAX_BYTES_PER_HEADER : Nat := 2 ^ 10

-- @@ L47-47 verbatim
def MAX_OPTIONAL_FORK_ACTIVATION_VALUES : Nat := 1

-- @@ L48-48 verbatim
def MAX_PUBLIC_KEYS : Nat := 2 ^ 15

-- @@ L49-49 verbatim
def PUBLIC_KEY_BYTES : Nat := 65


-- @@ L51-54 verbatim
/-! Stateless guest input bytes are schema-prefixed: `schema_id ||
    encoded_payload`, where `schema_id = fork_index || schema_revision`
    (`stateless_ssz.py:83`–`98`). Amsterdam is fork `0x15`, and revision
    `0x01` uses SSZ `encode(SszStatelessInput)` for the payload. -/


-- @@ L56-57 verbatim
/-- `STATELESS_INPUT_SCHEMA_FORK_INDEX` (`stateless_ssz.py:89`). -/
def STATELESS_INPUT_SCHEMA_FORK_INDEX : Nat := ProtocolFork.Amsterdam.value

-- @@ L58-59 verbatim
/-- `STATELESS_INPUT_SCHEMA_REVISION` (`stateless_ssz.py:90`). -/
def STATELESS_INPUT_SCHEMA_REVISION : Nat := 0x01

-- @@ L60-62 verbatim
/-- `STATELESS_INPUT_SCHEMA_ID` (`stateless_ssz.py:91`). -/
def STATELESS_INPUT_SCHEMA_ID : Nat :=
  (STATELESS_INPUT_SCHEMA_FORK_INDEX <<< 8) ||| STATELESS_INPUT_SCHEMA_REVISION

-- @@ L63-67 verbatim
/-- `STATELESS_INPUT_SCHEMA_ID_SIZE` (`stateless_ssz.py:94`). -/
def STATELESS_INPUT_SCHEMA_ID_SIZE : Nat := 2

-- The two-byte big-endian prefix is `15 01`.
#guard STATELESS_INPUT_SCHEMA_ID == 0x1501


-- @@ L69-69 verbatim
/-! ## SSZ type descriptors (mirror the `Container` classes) -/


-- @@ L71-72 verbatim
/-- `Bytes32` / `ByteVector[32]`. -/
def bytes32Type : SszType := .byteVector 32

-- @@ L73-74 verbatim
/-- `uint64`. -/
def u64Type : SszType := .uint 8

-- @@ L75-76 verbatim
/-- `uint256`. -/
def u256Type : SszType := .uint 32


-- @@ L78-80 verbatim
/-- `SszWithdrawal` (`stateless_ssz.py:80`). -/
def sszWithdrawalType : SszType :=
  .container [u64Type, u64Type, .byteVector 20, u64Type]


-- @@ L82-89 verbatim
/-- `SszExecutionPayload` (`stateless_ssz.py:89`). -/
def sszExecutionPayloadType : SszType :=
  .container [bytes32Type, .byteVector 20, bytes32Type, bytes32Type,
    .byteVector 256, bytes32Type, u64Type, u64Type, u64Type, u64Type,
    .byteList MAX_EXTRA_DATA_BYTES, u256Type, bytes32Type,
    .list (.byteList MAX_BYTES_PER_TRANSACTION) MAX_TRANSACTIONS_PER_PAYLOAD,
    .list sszWithdrawalType MAX_WITHDRAWALS_PER_PAYLOAD,
    u64Type, u64Type, .byteList MAX_BLOCK_ACCESS_LIST_BYTES, u64Type]


-- @@ L91-93 verbatim
/-- `SszDepositRequest` (`stateless_ssz.py:115`). -/
def sszDepositRequestType : SszType :=
  .container [.byteVector 48, bytes32Type, u64Type, .byteVector 96, u64Type]


-- @@ L95-97 verbatim
/-- `SszWithdrawalRequest` (`stateless_ssz.py:125`). -/
def sszWithdrawalRequestType : SszType :=
  .container [.byteVector 20, .byteVector 48, u64Type]


-- @@ L99-101 verbatim
/-- `SszConsolidationRequest` (`stateless_ssz.py:133`). -/
def sszConsolidationRequestType : SszType :=
  .container [.byteVector 20, .byteVector 48, .byteVector 48]


-- @@ L103-105 verbatim
/-- `SszBuilderDepositRequest` (`stateless_ssz.py:141`). -/
def sszBuilderDepositRequestType : SszType :=
  .container [.byteVector 48, bytes32Type, u64Type, .byteVector 96]


-- @@ L107-109 verbatim
/-- `SszBuilderExitRequest` (`stateless_ssz.py:150`). -/
def sszBuilderExitRequestType : SszType :=
  .container [.byteVector 20, .byteVector 48]


-- @@ L111-117 verbatim
/-- `SszExecutionRequests` (`stateless_ssz.py:141`). -/
def sszExecutionRequestsType : SszType :=
  .container [.list sszDepositRequestType MAX_DEPOSIT_REQUESTS_PER_PAYLOAD,
    .list sszWithdrawalRequestType MAX_WITHDRAWAL_REQUESTS_PER_PAYLOAD,
    .list sszConsolidationRequestType MAX_CONSOLIDATION_REQUESTS_PER_PAYLOAD,
    .list sszBuilderDepositRequestType MAX_BUILDER_DEPOSIT_REQUESTS_PER_PAYLOAD,
    .list sszBuilderExitRequestType MAX_BUILDER_EXIT_REQUESTS_PER_PAYLOAD]


-- @@ L119-123 verbatim
/-- `SszNewPayloadRequest` (`stateless_ssz.py:153`). -/
def sszNewPayloadRequestType : SszType :=
  .container [sszExecutionPayloadType,
    .list bytes32Type MAX_BLOB_COMMITMENTS_PER_BLOCK,
    bytes32Type, sszExecutionRequestsType]


-- @@ L125-129 verbatim
/-- `SszExecutionWitness` (`stateless_ssz.py:162`). -/
def sszExecutionWitnessType : SszType :=
  .container [.list (.byteList MAX_BYTES_PER_WITNESS_NODE) MAX_WITNESS_NODES,
    .list (.byteList MAX_BYTES_PER_CODE) MAX_WITNESS_CODES,
    .list (.byteList MAX_BYTES_PER_HEADER) MAX_WITNESS_HEADERS]


-- @@ L131-133 verbatim
/-- `SszOptionalForkActivationValue = List[uint64, 1]` (`stateless_ssz.py:75`). -/
def sszOptionalForkActivationValueType : SszType :=
  .list u64Type MAX_OPTIONAL_FORK_ACTIVATION_VALUES


-- @@ L135-137 verbatim
/-- `SszForkActivation` (`stateless_ssz.py:199`). -/
def sszForkActivationType : SszType :=
  .container [sszOptionalForkActivationValueType, sszOptionalForkActivationValueType]


-- @@ L139-142 verbatim
/-- `SszForkConfig` (`stateless_ssz.py:206`). v0.6.0 drops the `fork`
    (uint64) and `blob_schedule` (zero-or-one list) fields. -/
def sszForkConfigType : SszType :=
  .container [sszForkActivationType]


-- @@ L144-146 verbatim
/-- `SszChainConfig` (`stateless_ssz.py:212`). -/
def sszChainConfigType : SszType :=
  .container [u64Type, sszForkConfigType]


-- @@ L148-151 verbatim
/-- `SszStatelessInput` (`stateless_ssz.py:219`). -/
def sszStatelessInputType : SszType :=
  .container [sszNewPayloadRequestType, sszExecutionWitnessType, sszChainConfigType,
    .list (.byteVector PUBLIC_KEY_BYTES) MAX_PUBLIC_KEYS]


-- @@ L153-155 verbatim
/-- `SszStatelessValidationResult` (`stateless_ssz.py:214`). -/
def sszStatelessValidationResultType : SszType :=
  .container [bytes32Type, .bool, sszChainConfigType]


-- @@ L157-157 verbatim
/-! ## Accessors for the `ssz_to_*` direction -/


-- @@ L159-161 verbatim
def asContainerV : SszValue → Except SpecError (List SszValue)
  | .container fs => .ok fs
  | _ => .error (.sszError "expected container")


-- @@ L163-165 verbatim
def asUintV : SszValue → Except SpecError Nat
  | .uint _ v => .ok v
  | _ => .error (.sszError "expected uint")


-- @@ L167-169 verbatim
def asBoolV : SszValue → Except SpecError Bool
  | .bool b => .ok b
  | _ => .error (.sszError "expected bool")


-- @@ L171-174 verbatim
def asBytesV : SszValue → Except SpecError Bytes
  | .byteVector d => .ok d
  | .byteList _ d => .ok d
  | _ => .error (.sszError "expected bytes")


-- @@ L176-178 verbatim
def asListV : SszValue → Except SpecError (List SszValue)
  | .list _ _ es => .ok es
  | _ => .error (.sszError "expected list")


-- @@ L180-183 verbatim
def getField (fs : List SszValue) (i : Nat) : Except SpecError SszValue :=
  match fs[i]? with
  | some v => .ok v
  | none => .error (.sszError s!"missing field {i}")


-- @@ L185-185 verbatim
/-! ## `_withdrawal_to_ssz` / `_ssz_to_withdrawal` (`:239`, `:249`) -/


-- @@ L187-189 verbatim
def withdrawalToSsz (w : Withdrawal) : SszValue :=
  .container [.uint 8 w.index, .uint 8 w.validatorIndex,
    .byteVector w.address, .uint 8 w.amount]


-- @@ L191-197 verbatim
def sszToWithdrawal (sv : SszValue) : Except SpecError Withdrawal := do
  let fs ← asContainerV sv
  let index ← asUintV (← getField fs 0)
  let validatorIndex ← asUintV (← getField fs 1)
  let address ← asBytesV (← getField fs 2)
  let amount ← asUintV (← getField fs 3)
  pure { index, validatorIndex, address, amount }


-- @@ L199-199 verbatim
/-! ## `_payload_to_ssz` / `_ssz_to_payload` (`:262`, `:299`) -/


-- @@ L201-212 verbatim
def payloadToSsz (p : ExecutionPayload) : SszValue :=
  .container [.byteVector p.parentHash, .byteVector p.feeRecipient,
    .byteVector p.stateRoot, .byteVector p.receiptsRoot, .byteVector p.logsBloom,
    .byteVector p.prevRandao, .uint 8 p.blockNumber, .uint 8 p.gasLimit,
    .uint 8 p.gasUsed, .uint 8 p.timestamp,
    .byteList MAX_EXTRA_DATA_BYTES p.extraData, .uint 32 p.baseFeePerGas,
    .byteVector p.blockHash,
    .list MAX_TRANSACTIONS_PER_PAYLOAD none
      (p.transactions.map (fun t => .byteList MAX_BYTES_PER_TRANSACTION t)),
    .list MAX_WITHDRAWALS_PER_PAYLOAD none (p.withdrawals.map withdrawalToSsz),
    .uint 8 p.blobGasUsed, .uint 8 p.excessBlobGas,
    .byteList MAX_BLOCK_ACCESS_LIST_BYTES p.blockAccessList, .uint 8 p.slotNumber]


-- @@ L214-239 verbatim
def sszToPayload (sv : SszValue) : Except SpecError ExecutionPayload := do
  let fs ← asContainerV sv
  let parentHash ← asBytesV (← getField fs 0)
  let feeRecipient ← asBytesV (← getField fs 1)
  let stateRoot ← asBytesV (← getField fs 2)
  let receiptsRoot ← asBytesV (← getField fs 3)
  let logsBloom ← asBytesV (← getField fs 4)
  let prevRandao ← asBytesV (← getField fs 5)
  let blockNumber ← asUintV (← getField fs 6)
  let gasLimit ← asUintV (← getField fs 7)
  let gasUsed ← asUintV (← getField fs 8)
  let timestamp ← asUintV (← getField fs 9)
  let extraData ← asBytesV (← getField fs 10)
  let baseFeePerGas ← asUintV (← getField fs 11)
  let blockHash ← asBytesV (← getField fs 12)
  let transactions ← (← asListV (← getField fs 13)).mapM asBytesV
  let withdrawals ← (← asListV (← getField fs 14)).mapM sszToWithdrawal
  let blobGasUsed ← asUintV (← getField fs 15)
  let excessBlobGas ← asUintV (← getField fs 16)
  let blockAccessList ← asBytesV (← getField fs 17)
  let slotNumber ← asUintV (← getField fs 18)
  let payload : ExecutionPayload :=
    { parentHash, feeRecipient, stateRoot, receiptsRoot, logsBloom, prevRandao,
      blockNumber, gasLimit, gasUsed, timestamp, extraData, baseFeePerGas, blockHash,
      transactions, withdrawals, blobGasUsed, excessBlobGas, blockAccessList, slotNumber }
  pure payload


-- @@ L241-241 verbatim
/-! ## Request conversions (`:326`, `:337`, `:348`, `:359`, `:370`, `:381`) -/


-- @@ L243-245 verbatim
def depositRequestToSsz (d : DepositRequest) : SszValue :=
  .container [.byteVector d.pubkey, .byteVector d.withdrawalCredentials,
    .uint 8 d.amount, .byteVector d.signature, .uint 8 d.index]


-- @@ L247-254 verbatim
def sszToDepositRequest (sv : SszValue) : Except SpecError DepositRequest := do
  let fs ← asContainerV sv
  let pubkey ← asBytesV (← getField fs 0)
  let withdrawalCredentials ← asBytesV (← getField fs 1)
  let amount ← asUintV (← getField fs 2)
  let signature ← asBytesV (← getField fs 3)
  let index ← asUintV (← getField fs 4)
  pure { pubkey, withdrawalCredentials, amount, signature, index }


-- @@ L256-257 verbatim
def withdrawalRequestToSsz (w : WithdrawalRequest) : SszValue :=
  .container [.byteVector w.sourceAddress, .byteVector w.validatorPubkey, .uint 8 w.amount]


-- @@ L259-264 verbatim
def sszToWithdrawalRequest (sv : SszValue) : Except SpecError WithdrawalRequest := do
  let fs ← asContainerV sv
  let sourceAddress ← asBytesV (← getField fs 0)
  let validatorPubkey ← asBytesV (← getField fs 1)
  let amount ← asUintV (← getField fs 2)
  pure { sourceAddress, validatorPubkey, amount }


-- @@ L266-267 verbatim
def consolidationRequestToSsz (c : ConsolidationRequest) : SszValue :=
  .container [.byteVector c.sourceAddress, .byteVector c.sourcePubkey, .byteVector c.targetPubkey]


-- @@ L269-274 verbatim
def sszToConsolidationRequest (sv : SszValue) : Except SpecError ConsolidationRequest := do
  let fs ← asContainerV sv
  let sourceAddress ← asBytesV (← getField fs 0)
  let sourcePubkey ← asBytesV (← getField fs 1)
  let targetPubkey ← asBytesV (← getField fs 2)
  pure { sourceAddress, sourcePubkey, targetPubkey }


-- @@ L276-278 verbatim
def builderDepositRequestToSsz (b : BuilderDepositRequest) : SszValue :=
  .container [.byteVector b.pubkey, .byteVector b.withdrawalCredentials,
    .uint 8 b.amount, .byteVector b.signature]


-- @@ L280-286 verbatim
def sszToBuilderDepositRequest (sv : SszValue) : Except SpecError BuilderDepositRequest := do
  let fs ← asContainerV sv
  let pubkey ← asBytesV (← getField fs 0)
  let withdrawalCredentials ← asBytesV (← getField fs 1)
  let amount ← asUintV (← getField fs 2)
  let signature ← asBytesV (← getField fs 3)
  pure { pubkey, withdrawalCredentials, amount, signature }


-- @@ L288-289 verbatim
def builderExitRequestToSsz (b : BuilderExitRequest) : SszValue :=
  .container [.byteVector b.sourceAddress, .byteVector b.pubkey]


-- @@ L291-295 verbatim
def sszToBuilderExitRequest (sv : SszValue) : Except SpecError BuilderExitRequest := do
  let fs ← asContainerV sv
  let sourceAddress ← asBytesV (← getField fs 0)
  let pubkey ← asBytesV (← getField fs 1)
  pure { sourceAddress, pubkey }


-- @@ L297-297 verbatim
/-! ## `_execution_requests_to_ssz` / `_ssz_to_execution_requests` (`:392`, `:409`) -/


-- @@ L299-308 verbatim
def executionRequestsToSsz (er : ExecutionRequests) : SszValue :=
  .container [
    .list MAX_DEPOSIT_REQUESTS_PER_PAYLOAD none (er.deposits.map depositRequestToSsz),
    .list MAX_WITHDRAWAL_REQUESTS_PER_PAYLOAD none (er.withdrawals.map withdrawalRequestToSsz),
    .list MAX_CONSOLIDATION_REQUESTS_PER_PAYLOAD none
      (er.consolidations.map consolidationRequestToSsz),
    .list MAX_BUILDER_DEPOSIT_REQUESTS_PER_PAYLOAD none
      (er.builderDeposits.map builderDepositRequestToSsz),
    .list MAX_BUILDER_EXIT_REQUESTS_PER_PAYLOAD none
      (er.builderExits.map builderExitRequestToSsz)]


-- @@ L310-317 verbatim
def sszToExecutionRequests (sv : SszValue) : Except SpecError ExecutionRequests := do
  let fs ← asContainerV sv
  let deposits ← (← asListV (← getField fs 0)).mapM sszToDepositRequest
  let withdrawals ← (← asListV (← getField fs 1)).mapM sszToWithdrawalRequest
  let consolidations ← (← asListV (← getField fs 2)).mapM sszToConsolidationRequest
  let builderDeposits ← (← asListV (← getField fs 3)).mapM sszToBuilderDepositRequest
  let builderExits ← (← asListV (← getField fs 4)).mapM sszToBuilderExitRequest
  pure { deposits, withdrawals, consolidations, builderDeposits, builderExits }


-- @@ L319-319 verbatim
/-! ## `_new_payload_request_to_ssz` / `_ssz_to_new_payload_request` (`:424`, `:438`) -/


-- @@ L321-326 verbatim
def newPayloadRequestToSsz (npr : NewPayloadRequest) : SszValue :=
  .container [payloadToSsz npr.executionPayload,
    .list MAX_BLOB_COMMITMENTS_PER_BLOCK none
      (npr.versionedHashes.map (fun vh => .byteVector vh)),
    .byteVector npr.parentBeaconBlockRoot,
    executionRequestsToSsz npr.executionRequests]


-- @@ L328-334 verbatim
def sszToNewPayloadRequest (sv : SszValue) : Except SpecError NewPayloadRequest := do
  let fs ← asContainerV sv
  let executionPayload ← sszToPayload (← getField fs 0)
  let versionedHashes ← (← asListV (← getField fs 1)).mapM asBytesV
  let parentBeaconBlockRoot ← asBytesV (← getField fs 2)
  let executionRequests ← sszToExecutionRequests (← getField fs 3)
  pure { executionPayload, versionedHashes, parentBeaconBlockRoot, executionRequests }


-- @@ L336-336 verbatim
/-! ## `_witness_to_ssz` / `_ssz_to_witness` (`:452`, `:469`) -/


-- @@ L338-342 verbatim
def witnessToSsz (w : ExecutionWitness) : SszValue :=
  .container [
    .list MAX_WITNESS_NODES none (w.state.map (fun s => .byteList MAX_BYTES_PER_WITNESS_NODE s)),
    .list MAX_WITNESS_CODES none (w.codes.map (fun c => .byteList MAX_BYTES_PER_CODE c)),
    .list MAX_WITNESS_HEADERS none (w.headers.map (fun h => .byteList MAX_BYTES_PER_HEADER h))]


-- @@ L344-349 verbatim
def sszToWitness (sv : SszValue) : Except SpecError ExecutionWitness := do
  let fs ← asContainerV sv
  let state ← (← asListV (← getField fs 0)).mapM asBytesV
  let codes ← (← asListV (← getField fs 1)).mapM asBytesV
  let headers ← (← asListV (← getField fs 2)).mapM asBytesV
  pure { state, codes, headers }


-- @@ L351-351 verbatim
/-! ## `_optional_u64_to_ssz` / `_ssz_to_optional_u64` (`:480`, `:489`) -/


-- @@ L353-356 verbatim
def optionalU64ToSsz (value : Option U64) : SszValue :=
  match value with
  | none => .list MAX_OPTIONAL_FORK_ACTIVATION_VALUES (some 8) []
  | some v => .list MAX_OPTIONAL_FORK_ACTIVATION_VALUES (some 8) [.uint 8 v]


-- @@ L358-362 verbatim
def sszToOptionalU64 (sv : SszValue) : Except SpecError (Option U64) := do
  let es ← asListV sv
  match es with
  | [] => pure none
  | v :: _ => pure (some (← asUintV v))


-- @@ L364-364 verbatim
/-! ## `_fork_activation_to_ssz` / `_ssz_to_fork_activation` (`:498`, `:508`) -/


-- @@ L366-367 verbatim
def forkActivationToSsz (a : ForkActivation) : SszValue :=
  .container [optionalU64ToSsz a.blockNumber, optionalU64ToSsz a.timestamp]


-- @@ L369-373 verbatim
def sszToForkActivation (sv : SszValue) : Except SpecError ForkActivation := do
  let fs ← asContainerV sv
  let blockNumber ← sszToOptionalU64 (← getField fs 0)
  let timestamp ← sszToOptionalU64 (← getField fs 1)
  pure { blockNumber, timestamp }


-- @@ L375-375 verbatim
/-! ## `_fork_config_to_ssz` / `_ssz_to_fork_config` (`:515`, `:524`) -/


-- @@ L377-378 verbatim
def forkConfigToSsz (fc : ForkConfig) : SszValue :=
  .container [forkActivationToSsz fc.activation]


-- @@ L380-383 verbatim
def sszToForkConfig (sv : SszValue) : Except SpecError ForkConfig := do
  let fs ← asContainerV sv
  let activation ← sszToForkActivation (← getField fs 0)
  pure { activation }


-- @@ L385-385 verbatim
/-! ## `_chain_config_to_ssz` / `_ssz_to_chain_config` (`:533`, `:543`) -/


-- @@ L387-388 verbatim
def chainConfigToSsz (cc : ChainConfig) : SszValue :=
  .container [.uint 8 cc.chainId, forkConfigToSsz cc.activeFork]


-- @@ L390-394 verbatim
def sszToChainConfig (sv : SszValue) : Except SpecError ChainConfig := do
  let fs ← asContainerV sv
  let chainId ← asUintV (← getField fs 0)
  let activeFork ← sszToForkConfig (← getField fs 1)
  pure { chainId, activeFork }


-- @@ L396-396 verbatim
/-! ## `stateless_input_to_ssz` / `ssz_to_stateless_input` (`:608`, `:630`) -/


-- @@ L398-404 verbatim
def statelessInputToSsz (si : StatelessInput) : Except SpecError SszValue := do
  for pk in si.publicKeys do
    if pk.length ≠ PUBLIC_KEY_BYTES then
      throw (.publicKeyWrongLength pk.length)
  pure (.container [newPayloadRequestToSsz si.newPayloadRequest,
    witnessToSsz si.witness, chainConfigToSsz si.chainConfig,
    .list MAX_PUBLIC_KEYS none (si.publicKeys.map (fun pk => .byteVector pk))])


-- @@ L406-412 verbatim
def sszToStatelessInput (sv : SszValue) : Except SpecError StatelessInput := do
  let fs ← asContainerV sv
  let newPayloadRequest ← sszToNewPayloadRequest (← getField fs 0)
  let witness ← sszToWitness (← getField fs 1)
  let chainConfig ← sszToChainConfig (← getField fs 2)
  let publicKeys ← (← asListV (← getField fs 3)).mapM asBytesV
  pure { newPayloadRequest, witness, chainConfig, publicKeys }


-- @@ L414-414 verbatim
/-! ## `validation_result_to_ssz` / `ssz_to_validation_result` (`:644`, `:655`) -/


-- @@ L416-418 verbatim
def validationResultToSsz (vr : StatelessValidationResult) : SszValue :=
  .container [.byteVector vr.newPayloadRequestRoot, .bool vr.successfulValidation,
    chainConfigToSsz vr.chainConfig]


-- @@ L420-425 verbatim
def sszToValidationResult (sv : SszValue) : Except SpecError StatelessValidationResult := do
  let fs ← asContainerV sv
  let newPayloadRequestRoot ← asBytesV (← getField fs 0)
  let successfulValidation ← asBoolV (← getField fs 1)
  let chainConfig ← sszToChainConfig (← getField fs 2)
  pure { newPayloadRequestRoot, successfulValidation, chainConfig }


-- @@ L427-427 verbatim
/-! ## Sanity: SSZ container round-trips (serialize → deserialize → domain) -/


-- @@ L429-441 verbatim
/-- A `ChainConfig` exercising an empty and a present optional (`none`
    block_number, `some` timestamp). -/
def sanityChainConfig : ChainConfig :=
  { chainId := 1
    activeFork :=
      { activation := { blockNumber := none, timestamp := some 100 } } }

-- Round-trip a `ChainConfig` through SSZ bytes and back.
#guard
  (do
    let bytes := (chainConfigToSsz sanityChainConfig).serialize
    let sv ← deserialize sszChainConfigType bytes
    sszToChainConfig sv).toOption == some sanityChainConfig


-- @@ L443-461 verbatim
/-- A `StatelessValidationResult` (fixed + bool + nested container). -/
def sanityResult : StatelessValidationResult :=
  { newPayloadRequestRoot := List.replicate 32 (0x11 : Byte)
    successfulValidation := true
    chainConfig := sanityChainConfig }

-- Round-trip a `StatelessValidationResult`.
#guard
  (do
    let bytes := (validationResultToSsz sanityResult).serialize
    let sv ← deserialize sszStatelessValidationResultType bytes
    sszToValidationResult sv).toOption == some sanityResult

-- v0.6.0 witness resource bounds from `stateless_ssz.py`.
#guard MAX_WITNESS_NODES == 2 ^ 22
#guard MAX_WITNESS_CODES == 2 ^ 18
#guard MAX_BYTES_PER_WITNESS_NODE == 2 ^ 10
#guard MAX_BYTES_PER_CODE == 2 ^ 16
#guard MAX_PUBLIC_KEYS == 2 ^ 15


-- @@ L463-472 verbatim
/-! ## Serialize→deserialize round-trip for the validation-result schema

    Layered bottom-up (activation → forkConfig → chainConfig → result), each
    at explicit fuel `f + k`: serialization and deserialization descend the
    schema in lockstep, so each layer needs one fuel unit more than the one
    below, and the top level instantiates `f` to land on `sszFuel`. Values
    come back *as decoded* (`uint` fields mod `2^64`), so no well-formedness
    hypotheses are needed anywhere except the 32-byte root — exactly the
    shape the guest robustness theorem (`run_stateless_guest_total`,
    `Guest.lean`) wants. -/


-- @@ L474-478 verbatim
/-- As-decoded truncation of a `ForkActivation`: `uint64` fields survive an
    SSZ round-trip mod `2^64`. -/
def truncActivation (a : ForkActivation) : ForkActivation :=
  { blockNumber := a.blockNumber.map (· % 2 ^ 64)
    timestamp := a.timestamp.map (· % 2 ^ 64) }


-- @@ L480-486 verbatim
/-- As-decoded truncation of a `ChainConfig`. -/
def truncConfig (cc : ChainConfig) : ChainConfig :=
  { chainId := cc.chainId % 2 ^ 64
    activeFork := { activation := truncActivation cc.activeFork.activation } }

-- Constructor/value-level ground facts (payload-independent), plus
-- `decide`-checked fixed sizes of the concrete schemas involved.

-- @@ L487-488 verbatim
private theorem listType_isVariable (e : SszType) (l : Nat) :
    (SszType.list e l).isVariable = true := rfl

-- @@ L489-489 verbatim
private theorem u64Type_basicSize : u64Type.basicSize? = some 8 := rfl

-- @@ L490-491 verbatim
private theorem listVal_isVariable (l : Nat) (ebs : Option Nat) (es : List SszValue) :
    (SszValue.list l ebs es).isVariable = true := rfl

-- @@ L492-493 verbatim
private theorem uintVal_isVariable (w v : Nat) :
    (SszValue.uint w v).isVariable = false := rfl

-- @@ L494-494 verbatim
private theorem u64Type_isVariable : u64Type.isVariable = false := by decide

-- @@ L495-495 verbatim
private theorem u64Type_fixedSize : u64Type.fixedSize = 8 := by decide

-- @@ L496-498 verbatim
private theorem activationCtor_fixedSize :
    (SszType.container [SszType.list u64Type 1, SszType.list u64Type 1]).fixedSize = 8 := by
  decide


-- @@ L500-520 verbatim
private theorem forkActivation_roundtrip (f : Nat) (a : ForkActivation) :
    deserializeAux (f + 3) sszForkActivationType
        (SszValue.serializeAux (f + 3) (forkActivationToSsz a))
      = .ok (forkActivationToSsz (truncActivation a)) := by
  obtain ⟨bn, ts⟩ := a
  cases bn <;> cases ts <;>
    · simp [forkActivationToSsz, truncActivation, optionalU64ToSsz,
        SszValue.serializeAux, sszAssembleSeq, deserializeAux,
        sszForkActivationType, sszOptionalForkActivationValueType,
        collectHeads, readOffset, headsToSegments, offsetsNondecreasing,
        sliceBytes, natToBytesLE_length, bytesLEtoNat_natToBytesLE,
        List.drop_append,
        List.take_of_length_le, List.drop_of_length_le,
        listType_isVariable,
        u64Type_basicSize, listVal_isVariable, uintVal_isVariable,
        u64Type_isVariable, u64Type_fixedSize, activationCtor_fixedSize,
        sszOffsetSize, MAX_OPTIONAL_FORK_ACTIVATION_VALUES]
      rfl

-- Gate lemmas: the container length/offset checks are always false on
-- round-trip inputs (the data is at least as long as the fixed section).

-- @@ L521-522 verbatim
private theorem add_lt_self_eq_false (a b : Nat) : (a + b < a) = False :=
  eq_false (by omega)

-- @@ L523-524 verbatim
private theorem gateD (L : Nat) : (8 + (4 + L) < 12) = False :=
  eq_false (by omega)

-- @@ L525-526 verbatim
private theorem gateE (L : Nat) : (32 + (4 + L + 1) < 37) = False :=
  eq_false (by omega)


-- @@ L528-530 verbatim
private theorem forkActivationVal_isVariable (a : ForkActivation) :
    (forkActivationToSsz a).isVariable = true := by
  obtain ⟨bn, ts⟩ := a; cases bn <;> rfl

-- @@ L531-532 verbatim
private theorem forkActivationType_isVariable :
    sszForkActivationType.isVariable = true := by decide

-- @@ L533-534 verbatim
private theorem forkConfigCtor_fixedSize :
    (SszType.container [sszForkActivationType]).fixedSize = 4 := by decide


-- @@ L536-548 verbatim
private theorem forkConfig_roundtrip (f : Nat) (fc : ForkConfig) :
    deserializeAux (f + 4) sszForkConfigType
        (SszValue.serializeAux (f + 4) (forkConfigToSsz fc))
      = .ok (forkConfigToSsz { activation := truncActivation fc.activation }) := by
  rw [deserializeAux.eq_def]
  simp [forkConfigToSsz, SszValue.serializeAux, sszAssembleSeq,
    sszForkConfigType, collectHeads, readOffset, headsToSegments,
    offsetsNondecreasing, sliceBytes, natToBytesLE_length,
    bytesLEtoNat_natToBytesLE, List.drop_append, List.take_of_length_le,
    List.drop_of_length_le, forkActivationVal_isVariable,
    forkActivationType_isVariable, forkConfigCtor_fixedSize, sszOffsetSize,
    add_lt_self_eq_false, forkActivation_roundtrip f fc.activation]
  rfl


-- @@ L550-552 verbatim
private theorem forkConfigVal_isVariable (fc : ForkConfig) :
    (forkConfigToSsz fc).isVariable = true := by
  obtain ⟨⟨bn, ts⟩⟩ := fc; cases bn <;> rfl

-- @@ L553-554 verbatim
private theorem forkConfigType_isVariable :
    sszForkConfigType.isVariable = true := by decide

-- @@ L555-556 verbatim
private theorem chainConfigCtor_fixedSize :
    (SszType.container [u64Type, sszForkConfigType]).fixedSize = 12 := by decide


-- @@ L558-561 verbatim
private theorem u64_roundtrip (f v : Nat) :
    deserializeAux (f + 1) u64Type (natToBytesLE 8 v)
      = .ok (.uint 8 (v % 2 ^ 64)) := by
  simp [deserializeAux, u64Type, natToBytesLE_length, bytesLEtoNat_natToBytesLE]


-- @@ L563-563 verbatim
private theorem arithD (L : Nat) : 8 + (4 + L) - 12 = L := by omega


-- @@ L565-579 verbatim
private theorem chainConfig_roundtrip (f : Nat) (cc : ChainConfig) :
    deserializeAux (f + 5) sszChainConfigType
        (SszValue.serializeAux (f + 5) (chainConfigToSsz cc))
      = .ok (chainConfigToSsz (truncConfig cc)) := by
  rw [deserializeAux.eq_def]
  simp [chainConfigToSsz, truncConfig, SszValue.serializeAux, sszAssembleSeq,
    sszChainConfigType, collectHeads, readOffset,
    headsToSegments, offsetsNondecreasing, sliceBytes, natToBytesLE_length,
    bytesLEtoNat_natToBytesLE, List.drop_append, List.take_of_length_le,
    List.drop_of_length_le,
    forkConfigVal_isVariable, forkConfigType_isVariable, uintVal_isVariable,
    u64Type_isVariable, u64Type_fixedSize, chainConfigCtor_fixedSize,
    sszOffsetSize, gateD, arithD,
    u64_roundtrip, forkConfig_roundtrip f cc.activeFork]
  rfl


-- @@ L581-583 verbatim
private theorem chainConfigVal_isVariable (cc : ChainConfig) :
    (chainConfigToSsz cc).isVariable = true := by
  obtain ⟨cid, ⟨⟨bn, ts⟩⟩⟩ := cc; cases bn <;> rfl

-- @@ L584-585 verbatim
private theorem chainConfigType_isVariable :
    sszChainConfigType.isVariable = true := by decide

-- @@ L586-587 verbatim
private theorem byteVectorVal_isVariable (d : Bytes) :
    (SszValue.byteVector d).isVariable = false := rfl

-- @@ L588-589 verbatim
private theorem boolVal_isVariable (b : Bool) :
    (SszValue.bool b).isVariable = false := rfl

-- @@ L590-590 verbatim
private theorem bytes32Type_isVariable : bytes32Type.isVariable = false := by decide

-- @@ L591-591 verbatim
private theorem bytes32Type_fixedSize : bytes32Type.fixedSize = 32 := by decide

-- @@ L592-592 verbatim
private theorem boolType_isVariable : SszType.bool.isVariable = false := by decide

-- @@ L593-593 verbatim
private theorem boolType_fixedSize : SszType.bool.fixedSize = 1 := by decide

-- @@ L594-596 verbatim
private theorem resultCtor_fixedSize :
    (SszType.container [bytes32Type, SszType.bool, sszChainConfigType]).fixedSize = 37 := by
  decide


-- @@ L598-600 verbatim
private theorem byteVector32_roundtrip (f : Nat) (d : Bytes) (h : d.length = 32) :
    deserializeAux (f + 1) bytes32Type d = .ok (.byteVector d) := by
  simp [deserializeAux, bytes32Type, h]


-- @@ L602-612 verbatim
private theorem arithE (L : Nat) : 32 + (4 + L + 1) - 37 = L := by omega

-- The validation-result schema is exactly 6 SSZ layers deep (result
-- container → chainConfig → forkConfig → activation → optional-value
-- list → uint64), so `validationResult_roundtrip` needs `f + 6` fuel and
-- its user (`run_stateless_guest_total`, `Guest.lean`) instantiates
-- `f := 58` to land on `sszFuel`. This pin makes `58` a derived quantity
-- rather than a tuned one: if `sszFuel` or the layer count moves, the
-- arithmetic breaks here, loudly, instead of surfacing as an opaque fuel
-- exhaustion inside a proof.
#guard 58 + 6 == sszFuel


-- @@ L614-640 verbatim
/-- Serialize→deserialize round-trip for `StatelessValidationResult`, at
    any sufficient fuel. The only hypothesis is the 32-byte root; `uint64`
    payloads come back mod `2^64` (`truncConfig`), so no other
    well-formedness is required. -/
theorem validationResult_roundtrip (f : Nat) (vr : StatelessValidationResult)
    (hroot : vr.newPayloadRequestRoot.length = 32) :
    deserializeAux (f + 6) sszStatelessValidationResultType
        (SszValue.serializeAux (f + 6) (validationResultToSsz vr))
      = .ok (validationResultToSsz
          { newPayloadRequestRoot := vr.newPayloadRequestRoot
            successfulValidation := vr.successfulValidation
            chainConfig := truncConfig vr.chainConfig }) := by
  obtain ⟨root, succ, cc⟩ := vr
  cases succ <;>
    · rw [deserializeAux.eq_def]
      simp [validationResultToSsz, SszValue.serializeAux, sszAssembleSeq,
        sszStatelessValidationResultType, collectHeads,
        readOffset, headsToSegments, offsetsNondecreasing, sliceBytes,
        natToBytesLE_length, bytesLEtoNat_natToBytesLE, List.drop_append,
        List.take_of_length_le, List.drop_of_length_le,
        List.take_append_of_le_length, chainConfigVal_isVariable,
        chainConfigType_isVariable, byteVectorVal_isVariable,
        boolVal_isVariable, bytes32Type_isVariable, bytes32Type_fixedSize,
        boolType_isVariable, boolType_fixedSize, resultCtor_fixedSize,
        sszOffsetSize, hroot, gateE, arithE,
        byteVector32_roundtrip, chainConfig_roundtrip f cc]
      rfl


-- @@ L642-642 verbatim
end EvmAsm.Stateless.SpecRef
