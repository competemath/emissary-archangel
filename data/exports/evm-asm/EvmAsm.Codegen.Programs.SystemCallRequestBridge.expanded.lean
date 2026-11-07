/-
  EvmAsm.Codegen.Programs.SystemCallRequestBridge

  GH #11578 — the request-derive half of the EIP-7002/EIP-7251 seam.

  `derive_withdrawal_requests` and `derive_consolidation_requests` are seven
  instruction ABI shims.  They tail-jump to `stage_system_call`; they do not
  parse, stride through, or copy the return-data buffer.  This module therefore
  proves the pure request framing that surrounds the shims, rather than
  pretending that a machine triple exists for the unproven dispatcher call.

  The reference operation is `process_general_purpose_requests`
  (`Stateless/SpecRef/Fork.lean:493-512`): a successful checked system call
  contributes `0x01 :: return_data` or `0x02 :: return_data` exactly when the
  returned byte list is non-empty.  `encode_execution_requests` in
  `SpecRef/SeamShell.lean` has the same per-kind prefix shape for its typed
  engine-API input, but it is the opposite side of the seam; this file keeps
  the raw execution-derived body opaque, as the reference does.

  The pure framing lemmas below intentionally carry no `stage_system_call`
  premise: the list identity is unconditional and does not establish any
  machine fact about the tail-called dispatcher.  The missing machine contract
  remains a separate registered obligation in `Progress.Obligations`.
-/

module

public import EvmAsm.Stateless.SpecRef.SeamShell
meta import EvmAsm.Stateless.SpecRef.SeamShell


-- @@ L31-31 verbatim
@[expose] public section


-- @@ L33-33 verbatim
namespace EvmAsm.Codegen.SystemCallRequestBridge


-- @@ L35-35 verbatim
open EvmAsm.Stateless.SpecRef


-- @@ L37-37 verbatim
/-! ## Pure request framing -/


-- @@ L39-40 verbatim
/-- The EIP-7002 request-list type byte. -/
def withdrawalRequestType : Byte := 0x01


-- @@ L42-43 verbatim
/-- The EIP-7251 request-list type byte. -/
def consolidationRequestType : Byte := 0x02


-- @@ L45-53 verbatim
/-- Append one execution-derived request blob iff its return data is non-empty.

    This is the common pure part of `process_general_purpose_requests` for the
    two checked predeploys.  The body is intentionally opaque: fixed widths
    such as 76 and 116 belong to the predeploy output format, not to this
    request-derive operation. -/
def appendDerivedRequest (requests : List Bytes) (requestType : Byte)
    (returnData : Bytes) : List Bytes :=
  requests ++ if returnData.length > 0 then [requestType :: returnData] else []


-- @@ L55-58 verbatim
/-- Withdrawal derivation's pure output projection. -/
def deriveWithdrawalRequestOutput (requests : List Bytes)
    (returnData : Bytes) : List Bytes :=
  appendDerivedRequest requests withdrawalRequestType returnData


-- @@ L60-63 verbatim
/-- Consolidation derivation's pure output projection. -/
def deriveConsolidationRequestOutput (requests : List Bytes)
    (returnData : Bytes) : List Bytes :=
  appendDerivedRequest requests consolidationRequestType returnData


-- @@ L65-69 verbatim
/-! ## The two framing triples

    These are deliberately parallel.  Their only difference is the request
    type byte; neither carries a staging premise or an input-domain
    restriction. -/


-- @@ L71-92 verbatim
/-- Pure request-derive triple for `derive_withdrawal_requests`.

    Given any future contract for the tail-called staging seam, the derive
    result contributes exactly the EIP-7002 type-prefixed body on the success
    path, and contributes no blob for an empty return-data list.  This proves
    framing only; it does not prove `stage_system_call` or the predeploy. -/
theorem deriveWithdrawalRequests_request_derive_triple
    :
    ∀ (status : Nat) (returnData : Bytes)
      (requests : List Bytes),
      (status = 0 ∧
        deriveWithdrawalRequestOutput requests returnData =
          requests ++
            (if returnData.length > 0 then
              [withdrawalRequestType :: returnData] else [])) ∨
        status ≠ 0 := by
  intro status returnData requests
  by_cases h_status : status = 0
  · left
    refine ⟨h_status, ?_⟩
    simp [deriveWithdrawalRequestOutput, appendDerivedRequest]
  · exact Or.inr h_status


-- @@ L94-113 verbatim
/-- Pure request-derive triple for `derive_consolidation_requests`.

    This has the same hypotheses and post shape as the withdrawal triple.  The
    equality of shapes is intentional: only the EIP-7251 type byte changes. -/
theorem deriveConsolidationRequests_request_derive_triple
    :
    ∀ (status : Nat) (returnData : Bytes)
      (requests : List Bytes),
      (status = 0 ∧
        deriveConsolidationRequestOutput requests returnData =
          requests ++
            (if returnData.length > 0 then
              [consolidationRequestType :: returnData] else [])) ∨
        status ≠ 0 := by
  intro status returnData requests
  by_cases h_status : status = 0
  · left
    refine ⟨h_status, ?_⟩
    simp [deriveConsolidationRequestOutput, appendDerivedRequest]
  · exact Or.inr h_status


-- @@ L115-122 verbatim
/-! ## The SeamShell encoder projections

    The projection and matching lemmas below tie the raw-body framing above to
    the corresponding halves of `encode_execution_requests`.  The matching
    lemmas intentionally take the body/list correspondence as a hypothesis:
    `SpecRef` keeps fixed-width request fields as untyped `Bytes`, so a 20/48/8
    or 20/48/48 width theorem would be a new input-domain claim rather than a
    fact about this derive seam. -/


-- @@ L124-127 verbatim
/-- The withdrawal arm of `encode_execution_requests`, exposed by projection. -/
def encodeWithdrawalRequestHalf (requests : ExecutionRequests) : List Bytes :=
  if requests.withdrawals.isEmpty then [] else
    [withdrawalRequestType :: requests.withdrawals.flatMap _encode_withdrawal]


-- @@ L129-132 verbatim
/-- The consolidation arm of `encode_execution_requests`, exposed by projection. -/
def encodeConsolidationRequestHalf (requests : ExecutionRequests) : List Bytes :=
  if requests.consolidations.isEmpty then [] else
    [consolidationRequestType :: requests.consolidations.flatMap _encode_consolidation]


-- @@ L134-145 verbatim
/-- `encode_execution_requests` written as its five request arms, with the two
    execution-derived arms named above.  This is only a projection of the
    SeamShell definition; it does not parse or validate a returned body. -/
def encodeExecutionRequestsRequestArms (requests : ExecutionRequests) : List Bytes :=
  (if requests.deposits.isEmpty then [] else
    [0x00 :: (requests.deposits.flatMap _encode_deposit)])
  ++ encodeWithdrawalRequestHalf requests
  ++ encodeConsolidationRequestHalf requests
  ++ (if requests.builderDeposits.isEmpty then [] else
    [0x03 :: (requests.builderDeposits.flatMap _encode_builder_deposit)])
  ++ (if requests.builderExits.isEmpty then [] else
    [0x04 :: (requests.builderExits.flatMap _encode_builder_exit)])


-- @@ L147-151 verbatim
theorem encodeExecutionRequests_eq_request_arms
    (requests : ExecutionRequests) :
    encodeExecutionRequestsRequestArms requests =
      encode_execution_requests requests := by
  rfl


-- @@ L153-158 verbatim
theorem encodeExecutionRequests_withdrawal_half_eq
    (requests : ExecutionRequests) :
    encodeWithdrawalRequestHalf requests =
      (if requests.withdrawals.isEmpty then [] else
        [0x01 :: requests.withdrawals.flatMap _encode_withdrawal]) := by
  rfl


-- @@ L160-165 verbatim
theorem encodeExecutionRequests_consolidation_half_eq
    (requests : ExecutionRequests) :
    encodeConsolidationRequestHalf requests =
      (if requests.consolidations.isEmpty then [] else
        [0x02 :: requests.consolidations.flatMap _encode_consolidation]) := by
  rfl


-- @@ L167-190 verbatim
/-- A withdrawal body that is known to be the encoded withdrawal list, together
    with the nonempty/empty correspondence, is exactly the encoder's
    withdrawal arm.  The two hypotheses are output-shape facts; they are not
    silently promoted to an input-domain restriction on the derive shim. -/
theorem deriveWithdrawalRequestOutput_matches_encode_half
    (requests : ExecutionRequests) (body : Bytes)
    (h_body : body = requests.withdrawals.flatMap _encode_withdrawal)
    (h_nonempty : body.length > 0 ↔ ¬ requests.withdrawals.isEmpty) :
    deriveWithdrawalRequestOutput [] body =
      encodeWithdrawalRequestHalf requests := by
  subst body
  cases h_withdrawals : requests.withdrawals with
  | nil =>
    simp [deriveWithdrawalRequestOutput, appendDerivedRequest,
      encodeWithdrawalRequestHalf, h_withdrawals]
  | cons withdrawal withdrawals =>
    have h_len :
        (requests.withdrawals.flatMap _encode_withdrawal).length > 0 :=
      h_nonempty.mpr (by simp [h_withdrawals])
    rw [h_withdrawals] at h_len
    simp only [deriveWithdrawalRequestOutput, appendDerivedRequest,
      List.nil_append]
    rw [if_pos h_len]
    simp [encodeWithdrawalRequestHalf, h_withdrawals]


-- @@ L192-214 verbatim
/-- Consolidation counterpart of
    `deriveWithdrawalRequestOutput_matches_encode_half`, with the identical
    hypothesis and postcondition shape and only the EIP-7251 arm changed. -/
theorem deriveConsolidationRequestOutput_matches_encode_half
    (requests : ExecutionRequests) (body : Bytes)
    (h_body : body = requests.consolidations.flatMap _encode_consolidation)
    (h_nonempty : body.length > 0 ↔ ¬ requests.consolidations.isEmpty) :
    deriveConsolidationRequestOutput [] body =
      encodeConsolidationRequestHalf requests := by
  subst body
  cases h_consolidations : requests.consolidations with
  | nil =>
    simp [deriveConsolidationRequestOutput, appendDerivedRequest,
      encodeConsolidationRequestHalf, h_consolidations]
  | cons consolidation consolidations =>
    have h_len :
        (requests.consolidations.flatMap _encode_consolidation).length > 0 :=
      h_nonempty.mpr (by simp [h_consolidations])
    rw [h_consolidations] at h_len
    simp only [deriveConsolidationRequestOutput, appendDerivedRequest,
      List.nil_append]
    rw [if_pos h_len]
    simp [encodeConsolidationRequestHalf, h_consolidations]


-- @@ L216-216 verbatim
/-! ## Small executable witnesses -/


-- @@ L218-218 verbatim
#guard withdrawalRequestType == (0x01 : Byte)

-- @@ L219-219 verbatim
#guard consolidationRequestType == (0x02 : Byte)

-- @@ L220-220 verbatim
#guard deriveWithdrawalRequestOutput [] [] == []

-- @@ L221-221 verbatim
#guard deriveWithdrawalRequestOutput [] [0xAA] == [[0x01, 0xAA]]

-- @@ L222-222 verbatim
#guard deriveConsolidationRequestOutput [] [] == []

-- @@ L223-223 verbatim
#guard deriveConsolidationRequestOutput [] [0xBB] == [[0x02, 0xBB]]


-- @@ L225-225 verbatim
end EvmAsm.Codegen.SystemCallRequestBridge
