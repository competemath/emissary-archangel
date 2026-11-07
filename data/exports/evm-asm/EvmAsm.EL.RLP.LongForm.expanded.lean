/-
  EvmAsm.EL.RLP.LongForm

  Branch lemmas for long-form byte-string and list decoding.
-/
module

public import EvmAsm.EL.RLP.Decode


-- @@ L10-10 verbatim
public section


-- @@ L12-12 verbatim
namespace EvmAsm.EL.RLP


-- @@ L14-14 verbatim
/-! ## Long-form byte strings -/


-- @@ L16-23 verbatim
theorem decodeAux_long_bytes_readLength_none (fuel : Nat) (pfx : Byte)
    (rest : List Byte)
    (hLong : 0xB7 < pfx.toNat) (hBytes : pfx.toNat ≤ 0xBF)
    (hRead : readLength rest (pfx.toNat - 0xB7) = none) :
    decodeAux (fuel + 1) (pfx :: rest) = none := by
  have hNotSingle : ¬ pfx.toNat < 0x80 := by omega
  have hNotShort : ¬ pfx.toNat ≤ 0xB7 := by omega
  simp [decodeAux, hNotSingle, hNotShort, hBytes, hRead]


-- @@ L25-33 verbatim
theorem decodeAux_long_bytes_short_length_rejected (fuel : Nat) (pfx : Byte)
    (rest rest' : List Byte) (lenVal : Nat)
    (hLong : 0xB7 < pfx.toNat) (hBytes : pfx.toNat ≤ 0xBF)
    (hRead : readLength rest (pfx.toNat - 0xB7) = some (lenVal, rest'))
    (hShort : lenVal ≤ 55) :
    decodeAux (fuel + 1) (pfx :: rest) = none := by
  have hNotSingle : ¬ pfx.toNat < 0x80 := by omega
  have hNotShort : ¬ pfx.toNat ≤ 0xB7 := by omega
  simp [decodeAux, hNotSingle, hNotShort, hBytes, hRead, hShort]


-- @@ L35-44 verbatim
theorem decodeAux_long_bytes_payload_none (fuel : Nat) (pfx : Byte)
    (rest rest' : List Byte) (lenVal : Nat)
    (hLong : 0xB7 < pfx.toNat) (hBytes : pfx.toNat ≤ 0xBF)
    (hRead : readLength rest (pfx.toNat - 0xB7) = some (lenVal, rest'))
    (hLen : ¬ lenVal ≤ 55)
    (hTake : takeBytes rest' lenVal = none) :
    decodeAux (fuel + 1) (pfx :: rest) = none := by
  have hNotSingle : ¬ pfx.toNat < 0x80 := by omega
  have hNotShort : ¬ pfx.toNat ≤ 0xB7 := by omega
  simp [decodeAux, hNotSingle, hNotShort, hBytes, hRead, hLen, hTake]


-- @@ L46-55 verbatim
theorem decodeAux_long_bytes_success (fuel : Nat) (pfx : Byte)
    (rest rest' rest'' data : List Byte) (lenVal : Nat)
    (hLong : 0xB7 < pfx.toNat) (hBytes : pfx.toNat ≤ 0xBF)
    (hRead : readLength rest (pfx.toNat - 0xB7) = some (lenVal, rest'))
    (hLen : ¬ lenVal ≤ 55)
    (hTake : takeBytes rest' lenVal = some (data, rest'')) :
    decodeAux (fuel + 1) (pfx :: rest) = some (.bytes data, rest'') := by
  have hNotSingle : ¬ pfx.toNat < 0x80 := by omega
  have hNotShort : ¬ pfx.toNat ≤ 0xB7 := by omega
  simp [decodeAux, hNotSingle, hNotShort, hBytes, hRead, hLen, hTake]


-- @@ L57-57 verbatim
/-! ## Long-form lists -/


-- @@ L59-69 verbatim
theorem decodeAux_long_list_readLength_none (fuel : Nat) (pfx : Byte)
    (rest : List Byte)
    (hLong : 0xF7 < pfx.toNat)
    (hRead : readLength rest (pfx.toNat - 0xF7) = none) :
    decodeAux (fuel + 1) (pfx :: rest) = none := by
  have hNotSingle : ¬ pfx.toNat < 0x80 := by omega
  have hNotShortBytes : ¬ pfx.toNat ≤ 0xB7 := by omega
  have hNotLongBytes : ¬ pfx.toNat ≤ 0xBF := by omega
  have hNotShortList : ¬ pfx.toNat ≤ 0xF7 := by omega
  simp [decodeAux, hNotSingle, hNotShortBytes, hNotLongBytes, hNotShortList,
    hRead]


-- @@ L71-82 verbatim
theorem decodeAux_long_list_short_length_rejected (fuel : Nat) (pfx : Byte)
    (rest rest' : List Byte) (lenVal : Nat)
    (hLong : 0xF7 < pfx.toNat)
    (hRead : readLength rest (pfx.toNat - 0xF7) = some (lenVal, rest'))
    (hShort : lenVal ≤ 55) :
    decodeAux (fuel + 1) (pfx :: rest) = none := by
  have hNotSingle : ¬ pfx.toNat < 0x80 := by omega
  have hNotShortBytes : ¬ pfx.toNat ≤ 0xB7 := by omega
  have hNotLongBytes : ¬ pfx.toNat ≤ 0xBF := by omega
  have hNotShortList : ¬ pfx.toNat ≤ 0xF7 := by omega
  simp [decodeAux, hNotSingle, hNotShortBytes, hNotLongBytes, hNotShortList,
    hRead, hShort]


-- @@ L84-96 verbatim
theorem decodeAux_long_list_payload_none (fuel : Nat) (pfx : Byte)
    (rest rest' : List Byte) (lenVal : Nat)
    (hLong : 0xF7 < pfx.toNat)
    (hRead : readLength rest (pfx.toNat - 0xF7) = some (lenVal, rest'))
    (hLen : ¬ lenVal ≤ 55)
    (hTake : takeBytes rest' lenVal = none) :
    decodeAux (fuel + 1) (pfx :: rest) = none := by
  have hNotSingle : ¬ pfx.toNat < 0x80 := by omega
  have hNotShortBytes : ¬ pfx.toNat ≤ 0xB7 := by omega
  have hNotLongBytes : ¬ pfx.toNat ≤ 0xBF := by omega
  have hNotShortList : ¬ pfx.toNat ≤ 0xF7 := by omega
  simp [decodeAux, hNotSingle, hNotShortBytes, hNotLongBytes, hNotShortList,
    hRead, hLen, hTake]


-- @@ L98-111 verbatim
theorem decodeAux_long_list_decode_none (fuel : Nat) (pfx : Byte)
    (rest rest' rest'' payload : List Byte) (lenVal : Nat)
    (hLong : 0xF7 < pfx.toNat)
    (hRead : readLength rest (pfx.toNat - 0xF7) = some (lenVal, rest'))
    (hLen : ¬ lenVal ≤ 55)
    (hTake : takeBytes rest' lenVal = some (payload, rest''))
    (hDecode : decodeItems fuel payload = none) :
    decodeAux (fuel + 1) (pfx :: rest) = none := by
  have hNotSingle : ¬ pfx.toNat < 0x80 := by omega
  have hNotShortBytes : ¬ pfx.toNat ≤ 0xB7 := by omega
  have hNotLongBytes : ¬ pfx.toNat ≤ 0xBF := by omega
  have hNotShortList : ¬ pfx.toNat ≤ 0xF7 := by omega
  simp [decodeAux, hNotSingle, hNotShortBytes, hNotLongBytes, hNotShortList,
    hRead, hLen, hTake, hDecode]


-- @@ L113-131 verbatim
theorem decodeAux_long_list_leftover_rejected (fuel : Nat) (pfx : Byte)
    (rest rest' rest'' payload leftover : List Byte) (items : List RLPItem)
    (lenVal : Nat)
    (hLong : 0xF7 < pfx.toNat)
    (hRead : readLength rest (pfx.toNat - 0xF7) = some (lenVal, rest'))
    (hLen : ¬ lenVal ≤ 55)
    (hTake : takeBytes rest' lenVal = some (payload, rest''))
    (hDecode : decodeItems fuel payload = some (items, leftover))
    (hLeftover : leftover ≠ []) :
    decodeAux (fuel + 1) (pfx :: rest) = none := by
  have hNotSingle : ¬ pfx.toNat < 0x80 := by omega
  have hNotShortBytes : ¬ pfx.toNat ≤ 0xB7 := by omega
  have hNotLongBytes : ¬ pfx.toNat ≤ 0xBF := by omega
  have hNotShortList : ¬ pfx.toNat ≤ 0xF7 := by omega
  cases leftover with
  | nil => exact False.elim (hLeftover rfl)
  | cons b bs =>
      simp [decodeAux, hNotSingle, hNotShortBytes, hNotLongBytes,
        hNotShortList, hRead, hLen, hTake, hDecode]


-- @@ L133-146 verbatim
theorem decodeAux_long_list_success (fuel : Nat) (pfx : Byte)
    (rest rest' rest'' payload : List Byte) (items : List RLPItem) (lenVal : Nat)
    (hLong : 0xF7 < pfx.toNat)
    (hRead : readLength rest (pfx.toNat - 0xF7) = some (lenVal, rest'))
    (hLen : ¬ lenVal ≤ 55)
    (hTake : takeBytes rest' lenVal = some (payload, rest''))
    (hDecode : decodeItems fuel payload = some (items, [])) :
    decodeAux (fuel + 1) (pfx :: rest) = some (.list items, rest'') := by
  have hNotSingle : ¬ pfx.toNat < 0x80 := by omega
  have hNotShortBytes : ¬ pfx.toNat ≤ 0xB7 := by omega
  have hNotLongBytes : ¬ pfx.toNat ≤ 0xBF := by omega
  have hNotShortList : ¬ pfx.toNat ≤ 0xF7 := by omega
  simp [decodeAux, hNotSingle, hNotShortBytes, hNotLongBytes, hNotShortList,
    hRead, hLen, hTake, hDecode]


-- @@ L148-148 verbatim
end EvmAsm.EL.RLP
