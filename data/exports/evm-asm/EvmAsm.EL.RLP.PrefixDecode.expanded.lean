/-
  EvmAsm.EL.RLP.PrefixDecode

  Bridges from the pure RLP prefix classifier to the canonical decoder.
-/

module

public import EvmAsm.EL.RLP.Decode
public import EvmAsm.EL.RLP.Prefix


-- @@ L12-12 verbatim
@[expose] public section


-- @@ L14-14 verbatim
namespace EvmAsm.EL.RLP


-- @@ L16-23 verbatim
/-- Minimal semantic target for an executable prefix decoder.

It reports the RLP prefix class and the number of header bytes before the
payload. Empty input has no prefix to classify. -/
def decodePrefixInfo (input : List Byte) : Option (PrefixClass × Nat) :=
  match input with
  | [] => none
  | pfx :: _ => some (classifyPrefix pfx, rlpPrefixHeaderBytes pfx)


-- @@ L25-26 verbatim
theorem decodePrefixInfo_nil :
    decodePrefixInfo ([] : List Byte) = none := rfl


-- @@ L28-30 verbatim
theorem decodePrefixInfo_cons (pfx : Byte) (rest : List Byte) :
    decodePrefixInfo (pfx :: rest) =
      some (classifyPrefix pfx, rlpPrefixHeaderBytes pfx) := rfl


-- @@ L32-38 verbatim
/-- A classified single-byte prefix selects the single-byte `decodeAux` branch. -/
theorem decodeAux_cons_singleByte_of_classifyPrefix
    (nDepth : Nat) (pfx : Byte) (rest : List Byte)
    (h : classifyPrefix pfx = .singleByte) :
    decodeAux (nDepth + 1) (pfx :: rest) = some (.bytes [pfx], rest) := by
  have h_lt := (classifyPrefix_singleByte_iff pfx).mp h
  simp [decodeAux, h_lt]


-- @@ L40-54 verbatim
/-- A classified short-byte-string prefix selects the short-string branch. -/
theorem decodeAux_cons_shortBytes_of_classifyPrefix
    (nDepth : Nat) (pfx : Byte) (rest : List Byte)
    (h : classifyPrefix pfx = .shortBytes) :
    decodeAux (nDepth + 1) (pfx :: rest) =
      (do
        let (data, rest') ← takeBytes rest (rlpPrefixShortBytesPayloadLen pfx)
        match data with
        | [b] => if b.toNat < 0x80 then none else some (.bytes data, rest')
        | _ => some (.bytes data, rest')) := by
  have h_range := (classifyPrefix_shortBytes_iff pfx).mp h
  have h_not_lt : ¬ pfx.toNat < 0x80 := by omega
  unfold decodeAux rlpPrefixShortBytesPayloadLen
  simp [h_not_lt, h_range.2]
  rfl


-- @@ L56-71 verbatim
/-- A classified long-byte-string prefix selects the long-string branch. -/
theorem decodeAux_cons_longBytes_of_classifyPrefix
    (nDepth : Nat) (pfx : Byte) (rest : List Byte)
    (h : classifyPrefix pfx = .longBytes) :
    decodeAux (nDepth + 1) (pfx :: rest) =
      (do
        let (lenVal, rest') ← readLength rest (rlpPrefixLongBytesLenOfLen pfx)
        if lenVal ≤ 55 then none
        else do
          let (data, rest'') ← takeBytes rest' lenVal
          some (.bytes data, rest'')) := by
  have h_range := (classifyPrefix_longBytes_iff pfx).mp h
  have h_not_lt : ¬ pfx.toNat < 0x80 := by omega
  have h_not_short : ¬ pfx.toNat ≤ 0xB7 := by omega
  unfold decodeAux rlpPrefixLongBytesLenOfLen
  simp [h_not_lt, h_not_short, h_range.2]


-- @@ L73-87 verbatim
/-- A classified short-list prefix selects the short-list branch. -/
theorem decodeAux_cons_shortList_of_classifyPrefix
    (nDepth : Nat) (pfx : Byte) (rest : List Byte)
    (h : classifyPrefix pfx = .shortList) :
    decodeAux (nDepth + 1) (pfx :: rest) =
      (do
        let (payload, rest') ← takeBytes rest (rlpPrefixShortListPayloadLen pfx)
        let (items, leftover) ← decodeItems nDepth payload
        if List.isEmpty leftover then some (.list items, rest') else none) := by
  have h_range := (classifyPrefix_shortList_iff pfx).mp h
  have h_not_lt : ¬ pfx.toNat < 0x80 := by omega
  have h_not_shortBytes : ¬ pfx.toNat ≤ 0xB7 := by omega
  have h_not_longBytes : ¬ pfx.toNat ≤ 0xBF := by omega
  unfold decodeAux rlpPrefixShortListPayloadLen
  simp [h_not_lt, h_not_shortBytes, h_not_longBytes, h_range.2]


-- @@ L89-107 verbatim
/-- A classified long-list prefix selects the long-list branch. -/
theorem decodeAux_cons_longList_of_classifyPrefix
    (nDepth : Nat) (pfx : Byte) (rest : List Byte)
    (h : classifyPrefix pfx = .longList) :
    decodeAux (nDepth + 1) (pfx :: rest) =
      (do
        let (lenVal, rest') ← readLength rest (rlpPrefixLongListLenOfLen pfx)
        if lenVal ≤ 55 then none
        else do
          let (payload, rest'') ← takeBytes rest' lenVal
          let (items, leftover) ← decodeItems nDepth payload
          if List.isEmpty leftover then some (.list items, rest'') else none) := by
  have h_range := (classifyPrefix_longList_iff pfx).mp h
  have h_not_lt : ¬ pfx.toNat < 0x80 := by omega
  have h_not_shortBytes : ¬ pfx.toNat ≤ 0xB7 := by omega
  have h_not_longBytes : ¬ pfx.toNat ≤ 0xBF := by omega
  have h_not_shortList : ¬ pfx.toNat ≤ 0xF7 := by omega
  unfold decodeAux rlpPrefixLongListLenOfLen
  simp [h_not_lt, h_not_shortBytes, h_not_longBytes, h_not_shortList]


-- @@ L109-150 verbatim
/--
  Classifier-dispatch form of the `decodeAux` prefix branch equations. This
  packages the five class-specific bridge lemmas into one semantic target for
  executable prefix classifiers.
-/
theorem decodeAux_cons_eq_classifyPrefix_match
    (nDepth : Nat) (pfx : Byte) (rest : List Byte) :
    decodeAux (nDepth + 1) (pfx :: rest) =
      match classifyPrefix pfx with
      | .singleByte => some (.bytes [pfx], rest)
      | .shortBytes =>
          (do
            let (data, rest') ← takeBytes rest (rlpPrefixShortBytesPayloadLen pfx)
            match data with
            | [b] => if b.toNat < 0x80 then none else some (.bytes data, rest')
            | _ => some (.bytes data, rest'))
      | .longBytes =>
          (do
            let (lenVal, rest') ← readLength rest (rlpPrefixLongBytesLenOfLen pfx)
            if lenVal ≤ 55 then none
            else do
              let (data, rest'') ← takeBytes rest' lenVal
              some (.bytes data, rest''))
      | .shortList =>
          (do
            let (payload, rest') ← takeBytes rest (rlpPrefixShortListPayloadLen pfx)
            let (items, leftover) ← decodeItems nDepth payload
            if List.isEmpty leftover then some (.list items, rest') else none)
      | .longList =>
          (do
            let (lenVal, rest') ← readLength rest (rlpPrefixLongListLenOfLen pfx)
            if lenVal ≤ 55 then none
            else do
              let (payload, rest'') ← takeBytes rest' lenVal
              let (items, leftover) ← decodeItems nDepth payload
              if List.isEmpty leftover then some (.list items, rest'') else none) := by
  cases h : classifyPrefix pfx
  · rw [decodeAux_cons_singleByte_of_classifyPrefix nDepth pfx rest h]
  · rw [decodeAux_cons_shortBytes_of_classifyPrefix nDepth pfx rest h]
  · rw [decodeAux_cons_longBytes_of_classifyPrefix nDepth pfx rest h]
  · rw [decodeAux_cons_shortList_of_classifyPrefix nDepth pfx rest h]
  · rw [decodeAux_cons_longList_of_classifyPrefix nDepth pfx rest h]


-- @@ L152-189 verbatim
/--
  Top-level `decode` wrapper version of `decodeAux_cons_eq_classifyPrefix_match`.
  This exposes the pure prefix classifier as the first dispatch point for every
  nonempty RLP input stream.
-/
theorem decode_cons_eq_classifyPrefix_match (pfx : Byte) (rest : List Byte) :
    decode (pfx :: rest) =
      match classifyPrefix pfx with
      | .singleByte => some (.bytes [pfx], rest)
      | .shortBytes =>
          (do
            let (data, rest') ← takeBytes rest (rlpPrefixShortBytesPayloadLen pfx)
            match data with
            | [b] => if b.toNat < 0x80 then none else some (.bytes data, rest')
            | _ => some (.bytes data, rest'))
      | .longBytes =>
          (do
            let (lenVal, rest') ← readLength rest (rlpPrefixLongBytesLenOfLen pfx)
            if lenVal ≤ 55 then none
            else do
              let (data, rest'') ← takeBytes rest' lenVal
              some (.bytes data, rest''))
      | .shortList =>
          (do
            let (payload, rest') ← takeBytes rest (rlpPrefixShortListPayloadLen pfx)
            let (items, leftover) ← decodeItems (2 * rest.length + 1) payload
            if List.isEmpty leftover then some (.list items, rest') else none)
      | .longList =>
          (do
            let (lenVal, rest') ← readLength rest (rlpPrefixLongListLenOfLen pfx)
            if lenVal ≤ 55 then none
            else do
              let (payload, rest'') ← takeBytes rest' lenVal
              let (items, leftover) ← decodeItems (2 * rest.length + 1) payload
              if List.isEmpty leftover then some (.list items, rest'') else none) := by
  unfold decode
  rw [show 2 * (pfx :: rest).length = (2 * rest.length + 1) + 1 by simp; omega]
  exact decodeAux_cons_eq_classifyPrefix_match (2 * rest.length + 1) pfx rest


-- @@ L191-191 verbatim
end EvmAsm.EL.RLP
