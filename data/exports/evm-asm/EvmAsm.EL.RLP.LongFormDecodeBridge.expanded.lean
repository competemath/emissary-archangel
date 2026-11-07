/-
  EvmAsm.EL.RLP.LongFormDecodeBridge

  Long-form decode bridges using the packaged read-length result (GH #120).
-/

module

public import EvmAsm.EL.RLP.PrefixDecode
public import EvmAsm.EL.RLP.ListDecodeBridge
public import EvmAsm.EL.RLP.ReadLengthBridge


-- @@ L13-13 verbatim
public section


-- @@ L15-15 verbatim
namespace EvmAsm.EL.RLP


-- @@ L17-17 verbatim
namespace LongFormDecodeBridge


-- @@ L19-19 verbatim
abbrev LengthFieldResult := ReadLengthBridge.LengthFieldResult


-- @@ L21-45 verbatim
/--
Long byte-string branch expressed through the packaged length-field result.

Distinctive token: RLP.LongFormDecodeBridge.decodeAux_long_bytes_lengthField #120.
-/
theorem decodeAux_long_bytes_lengthField
    (fuel : Nat) (pfx : Byte) (rest : List Byte)
    (lengthField : LengthFieldResult)
    (h_class : classifyPrefix pfx = .longBytes)
    (h_len : ReadLengthBridge.decodeLengthField? rest
      (rlpPrefixLongBytesLenOfLen pfx) = some lengthField) :
    decodeAux (fuel + 1) (pfx :: rest) =
      if lengthField.length ≤ 55 then none
      else
        match takeBytes lengthField.rest lengthField.length with
        | none => none
        | some (data, rest'') => some (.bytes data, rest'') := by
  cases lengthField with
  | mk lenVal rest' =>
      have h_read := (ReadLengthBridge.decodeLengthField?_eq_some_iff).1 h_len
      rw [decodeAux_cons_longBytes_of_classifyPrefix fuel pfx rest h_class]
      by_cases h_short : lenVal ≤ 55
      · simp [h_read, h_short]
      · simp [h_read, h_short]
        cases takeBytes rest' lenVal <;> rfl


-- @@ L47-57 verbatim
theorem decodeAux_long_bytes_lengthField_none
    (fuel : Nat) (pfx : Byte) (rest : List Byte)
    (h_class : classifyPrefix pfx = .longBytes)
    (h_len : ReadLengthBridge.decodeLengthField? rest
      (rlpPrefixLongBytesLenOfLen pfx) = none) :
    decodeAux (fuel + 1) (pfx :: rest) = none := by
  rw [decodeAux_cons_longBytes_of_classifyPrefix fuel pfx rest h_class]
  unfold ReadLengthBridge.decodeLengthField? at h_len
  cases h_read : readLength rest (rlpPrefixLongBytesLenOfLen pfx) with
  | none => rfl
  | some decoded => simp [h_read] at h_len


-- @@ L59-68 verbatim
theorem decodeAux_long_bytes_lengthField_short_rejected
    (fuel : Nat) (pfx : Byte) (rest : List Byte)
    (lengthField : LengthFieldResult)
    (h_class : classifyPrefix pfx = .longBytes)
    (h_len : ReadLengthBridge.decodeLengthField? rest
      (rlpPrefixLongBytesLenOfLen pfx) = some lengthField)
    (h_short : lengthField.length ≤ 55) :
    decodeAux (fuel + 1) (pfx :: rest) = none := by
  rw [decodeAux_long_bytes_lengthField fuel pfx rest lengthField h_class h_len]
  simp [h_short]


-- @@ L70-81 verbatim
theorem decodeAux_long_bytes_lengthField_payload
    (fuel : Nat) (pfx : Byte) (rest data rest'' : List Byte)
    (lengthField : LengthFieldResult)
    (h_class : classifyPrefix pfx = .longBytes)
    (h_len : ReadLengthBridge.decodeLengthField? rest
      (rlpPrefixLongBytesLenOfLen pfx) = some lengthField)
    (h_long : ¬ lengthField.length ≤ 55)
    (h_take : takeBytes lengthField.rest lengthField.length =
      some (data, rest'')) :
    decodeAux (fuel + 1) (pfx :: rest) = some (.bytes data, rest'') := by
  rw [decodeAux_long_bytes_lengthField fuel pfx rest lengthField h_class h_len]
  simp [h_long, h_take]


-- @@ L83-117 verbatim
/-- Long list branch expressed through the packaged length-field result. -/
theorem decodeAux_long_list_lengthField
    (fuel : Nat) (pfx : Byte) (rest : List Byte)
    (lengthField : LengthFieldResult)
    (h_class : classifyPrefix pfx = .longList)
    (h_len : ReadLengthBridge.decodeLengthField? rest
      (rlpPrefixLongListLenOfLen pfx) = some lengthField) :
    decodeAux (fuel + 1) (pfx :: rest) =
      if lengthField.length ≤ 55 then none
      else
        match takeBytes lengthField.rest lengthField.length with
        | none => none
        | some (payload, rest'') =>
            match decodeItems fuel payload with
            | none => none
            | some (items, leftover) =>
                if List.isEmpty leftover then some (.list items, rest'') else none := by
  cases lengthField with
  | mk lenVal rest' =>
      have h_read := (ReadLengthBridge.decodeLengthField?_eq_some_iff).1 h_len
      rw [decodeAux_cons_longList_of_classifyPrefix fuel pfx rest h_class]
      by_cases h_short : lenVal ≤ 55
      · simp [h_read, h_short]
      · simp [h_read, h_short]
        cases h_take : takeBytes rest' lenVal with
        | none => rfl
        | some decoded =>
            cases decoded with
            | mk payload rest'' =>
                cases h_decode : decodeItems fuel payload with
                | none => simp [h_decode]
                | some decodedItems =>
                    cases decodedItems with
                    | mk items leftover =>
                        simp [h_decode]


-- @@ L119-154 verbatim
/--
Long list branch expressed through both the packaged length-field result and
the list-payload decoder bridge.

Distinctive token:
LongFormDecodeBridge.decodeAux_long_list_lengthField_decodeListPayload #120.
-/
theorem decodeAux_long_list_lengthField_decodeListPayload
    (fuel : Nat) (pfx : Byte) (rest : List Byte)
    (lengthField : LengthFieldResult)
    (h_class : classifyPrefix pfx = .longList)
    (h_len : ReadLengthBridge.decodeLengthField? rest
      (rlpPrefixLongListLenOfLen pfx) = some lengthField) :
    decodeAux (fuel + 1) (pfx :: rest) =
      if lengthField.length ≤ 55 then none
      else
        match takeBytes lengthField.rest lengthField.length with
        | none => none
        | some (payload, rest'') => (do
            let items ← ListDecodeBridge.decodeListPayload fuel payload
            some (.list items, rest'')) := by
  rw [decodeAux_long_list_lengthField fuel pfx rest lengthField h_class h_len]
  by_cases h_short : lengthField.length ≤ 55
  · simp [h_short]
  · simp [h_short]
    cases h_take : takeBytes lengthField.rest lengthField.length with
    | none => rfl
    | some decoded =>
        cases decoded with
        | mk payload rest'' =>
            cases h_decode : decodeItems fuel payload with
            | none => simp [ListDecodeBridge.decodeListPayload, h_decode]
            | some decodedItems =>
                cases decodedItems with
                | mk items leftover =>
                    cases leftover <;> simp [ListDecodeBridge.decodeListPayload, h_decode]


-- @@ L156-166 verbatim
theorem decodeAux_long_list_lengthField_none
    (fuel : Nat) (pfx : Byte) (rest : List Byte)
    (h_class : classifyPrefix pfx = .longList)
    (h_len : ReadLengthBridge.decodeLengthField? rest
      (rlpPrefixLongListLenOfLen pfx) = none) :
    decodeAux (fuel + 1) (pfx :: rest) = none := by
  rw [decodeAux_cons_longList_of_classifyPrefix fuel pfx rest h_class]
  unfold ReadLengthBridge.decodeLengthField? at h_len
  cases h_read : readLength rest (rlpPrefixLongListLenOfLen pfx) with
  | none => rfl
  | some decoded => simp [h_read] at h_len


-- @@ L168-177 verbatim
theorem decodeAux_long_list_lengthField_short_rejected
    (fuel : Nat) (pfx : Byte) (rest : List Byte)
    (lengthField : LengthFieldResult)
    (h_class : classifyPrefix pfx = .longList)
    (h_len : ReadLengthBridge.decodeLengthField? rest
      (rlpPrefixLongListLenOfLen pfx) = some lengthField)
    (h_short : lengthField.length ≤ 55) :
    decodeAux (fuel + 1) (pfx :: rest) = none := by
  rw [decodeAux_long_list_lengthField fuel pfx rest lengthField h_class h_len]
  simp [h_short]


-- @@ L179-191 verbatim
theorem decodeAux_long_list_lengthField_success
    (fuel : Nat) (pfx : Byte) (rest payload rest'' : List Byte)
    (items : List RLPItem) (lengthField : LengthFieldResult)
    (h_class : classifyPrefix pfx = .longList)
    (h_len : ReadLengthBridge.decodeLengthField? rest
      (rlpPrefixLongListLenOfLen pfx) = some lengthField)
    (h_long : ¬ lengthField.length ≤ 55)
    (h_take : takeBytes lengthField.rest lengthField.length =
      some (payload, rest''))
    (h_decode : decodeItems fuel payload = some (items, [])) :
    decodeAux (fuel + 1) (pfx :: rest) = some (.list items, rest'') := by
  rw [decodeAux_long_list_lengthField fuel pfx rest lengthField h_class h_len]
  simp [h_long, h_take, h_decode]


-- @@ L193-193 verbatim
end LongFormDecodeBridge


-- @@ L195-195 verbatim
end EvmAsm.EL.RLP
