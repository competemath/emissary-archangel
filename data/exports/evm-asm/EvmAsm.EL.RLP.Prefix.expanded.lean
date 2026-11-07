/-
  EvmAsm.EL.RLP.Prefix

  Pure RLP prefix-byte classifier. This is the semantic target for the
  RISC-V prefix-classifier phase of the executable decoder.
-/

module

public import EvmAsm.EL.RLP.Basic


-- @@ L12-12 verbatim
@[expose] public section


-- @@ L14-14 verbatim
namespace EvmAsm.EL.RLP


-- @@ L16-23 verbatim
/-- The five Yellow Paper RLP prefix classes. -/
inductive PrefixClass where
  | singleByte
  | shortBytes
  | longBytes
  | shortList
  | longList
  deriving Repr, BEq, DecidableEq


-- @@ L25-32 verbatim
/-- Classify an RLP prefix byte by its numeric range. -/
def classifyPrefix (pfx : Byte) : PrefixClass :=
  let p := pfx.toNat
  if p < 0x80 then .singleByte
  else if p ≤ 0xB7 then .shortBytes
  else if p ≤ 0xBF then .longBytes
  else if p ≤ 0xF7 then .shortList
  else .longList


-- @@ L34-36 verbatim
/-- Payload length encoded directly in a short string prefix (`0x80..0xB7`). -/
def rlpPrefixShortBytesPayloadLen (pfx : Byte) : Nat :=
  pfx.toNat - 0x80


-- @@ L38-40 verbatim
/-- Number of length bytes following a long string prefix (`0xB8..0xBF`). -/
def rlpPrefixLongBytesLenOfLen (pfx : Byte) : Nat :=
  pfx.toNat - 0xB7


-- @@ L42-44 verbatim
/-- Payload length encoded directly in a short list prefix (`0xC0..0xF7`). -/
def rlpPrefixShortListPayloadLen (pfx : Byte) : Nat :=
  pfx.toNat - 0xC0


-- @@ L46-48 verbatim
/-- Number of length bytes following a long list prefix (`0xF8..0xFF`). -/
def rlpPrefixLongListLenOfLen (pfx : Byte) : Nat :=
  pfx.toNat - 0xF7


-- @@ L50-59 verbatim
/-!
Stated unfolding equations for the four payload-length defs. Use THESE in
`simp`/`rw`, not the def names: since v4.31, on-demand realization of a def's
unfolding lemma recurses ~4 stack frames per unit of a literal right subtrahend
(`- 0xF7` ≈ 1000 frames vs the hard 512 default), realizations are not exported
across modules, and no call-site `set_option maxRecDepth` reaches the
realization context — so `simp [rlpPrefixLongListLenOfLen]` in a downstream
module dies with `maximum recursion depth`. An ordinary `rfl` theorem sidesteps
realization entirely.
-/


-- @@ L61-62 verbatim
theorem rlpPrefixShortBytesPayloadLen_def (pfx : Byte) :
    rlpPrefixShortBytesPayloadLen pfx = pfx.toNat - 0x80 := rfl


-- @@ L64-65 verbatim
theorem rlpPrefixLongBytesLenOfLen_def (pfx : Byte) :
    rlpPrefixLongBytesLenOfLen pfx = pfx.toNat - 0xB7 := rfl


-- @@ L67-68 verbatim
theorem rlpPrefixShortListPayloadLen_def (pfx : Byte) :
    rlpPrefixShortListPayloadLen pfx = pfx.toNat - 0xC0 := rfl


-- @@ L70-71 verbatim
theorem rlpPrefixLongListLenOfLen_def (pfx : Byte) :
    rlpPrefixLongListLenOfLen pfx = pfx.toNat - 0xF7 := rfl


-- @@ L73-80 verbatim
/-- Total length-of-length byte count for an RLP prefix. Only long-form
    byte strings and lists carry an encoded payload length; all other
    prefixes have zero length bytes. -/
def rlpPrefixLenOfLen (pfx : Byte) : Nat :=
  match classifyPrefix pfx with
  | .longBytes => rlpPrefixLongBytesLenOfLen pfx
  | .longList => rlpPrefixLongListLenOfLen pfx
  | _ => 0


-- @@ L82-85 verbatim
/-- Total header bytes before payload for a long string prefix. This includes
    the prefix byte plus the encoded length bytes. -/
def rlpPrefixLongBytesHeaderBytes (pfx : Byte) : Nat :=
  1 + rlpPrefixLongBytesLenOfLen pfx


-- @@ L87-90 verbatim
/-- Total header bytes before payload for a long list prefix. This includes
    the prefix byte plus the encoded length bytes. -/
def rlpPrefixLongListHeaderBytes (pfx : Byte) : Nat :=
  1 + rlpPrefixLongListLenOfLen pfx


-- @@ L92-100 verbatim
/-- Total header bytes before payload for any RLP prefix class. Single-byte
    payloads have no header byte before the payload. -/
def rlpPrefixHeaderBytes (pfx : Byte) : Nat :=
  match classifyPrefix pfx with
  | .singleByte => 0
  | .shortBytes => 1
  | .longBytes => rlpPrefixLongBytesHeaderBytes pfx
  | .shortList => 1
  | .longList => rlpPrefixLongListHeaderBytes pfx


-- @@ L102-114 verbatim
theorem classifyPrefix_singleByte_iff (pfx : Byte) :
    classifyPrefix pfx = .singleByte ↔ pfx.toNat < 0x80 := by
  unfold classifyPrefix
  have h_bound : pfx.toNat < 256 := pfx.isLt
  by_cases h0 : pfx.toNat < 0x80
  · simp [h0]
  · by_cases h1 : pfx.toNat ≤ 0xB7
    · simp [h0, h1] <;> omega
    · by_cases h2 : pfx.toNat ≤ 0xBF
      · simp [h0, h1, h2] <;> omega
      · by_cases h3 : pfx.toNat ≤ 0xF7
        · simp [h0, h1, h2, h3] <;> omega
        · simp [h0, h1, h2, h3] <;> omega


-- @@ L116-128 verbatim
theorem classifyPrefix_shortBytes_iff (pfx : Byte) :
    classifyPrefix pfx = .shortBytes ↔ 0x80 ≤ pfx.toNat ∧ pfx.toNat ≤ 0xB7 := by
  unfold classifyPrefix
  have h_bound : pfx.toNat < 256 := pfx.isLt
  by_cases h0 : pfx.toNat < 0x80
  · simp [h0] <;> omega
  · by_cases h1 : pfx.toNat ≤ 0xB7
    · simp [h0, h1] <;> omega
    · by_cases h2 : pfx.toNat ≤ 0xBF
      · simp [h0, h1, h2] <;> omega
      · by_cases h3 : pfx.toNat ≤ 0xF7
        · simp [h0, h1, h2, h3] <;> omega
        · simp [h0, h1, h2, h3] <;> omega


-- @@ L130-142 verbatim
theorem classifyPrefix_longBytes_iff (pfx : Byte) :
    classifyPrefix pfx = .longBytes ↔ 0xB8 ≤ pfx.toNat ∧ pfx.toNat ≤ 0xBF := by
  unfold classifyPrefix
  have h_bound : pfx.toNat < 256 := pfx.isLt
  by_cases h0 : pfx.toNat < 0x80
  · simp [h0] <;> omega
  · by_cases h1 : pfx.toNat ≤ 0xB7
    · simp [h0, h1] <;> omega
    · by_cases h2 : pfx.toNat ≤ 0xBF
      · simp [h0, h1, h2] <;> omega
      · by_cases h3 : pfx.toNat ≤ 0xF7
        · simp [h0, h1, h2, h3] <;> omega
        · simp [h0, h1, h2, h3] <;> omega


-- @@ L144-156 verbatim
theorem classifyPrefix_shortList_iff (pfx : Byte) :
    classifyPrefix pfx = .shortList ↔ 0xC0 ≤ pfx.toNat ∧ pfx.toNat ≤ 0xF7 := by
  unfold classifyPrefix
  have h_bound : pfx.toNat < 256 := pfx.isLt
  by_cases h0 : pfx.toNat < 0x80
  · simp [h0] <;> omega
  · by_cases h1 : pfx.toNat ≤ 0xB7
    · simp [h0, h1] <;> omega
    · by_cases h2 : pfx.toNat ≤ 0xBF
      · simp [h0, h1, h2] <;> omega
      · by_cases h3 : pfx.toNat ≤ 0xF7
        · simp [h0, h1, h2, h3] <;> omega
        · simp [h0, h1, h2, h3] <;> omega


-- @@ L158-170 verbatim
theorem classifyPrefix_longList_iff (pfx : Byte) :
    classifyPrefix pfx = .longList ↔ 0xF8 ≤ pfx.toNat := by
  unfold classifyPrefix
  have h_bound : pfx.toNat < 256 := pfx.isLt
  by_cases h0 : pfx.toNat < 0x80
  · simp [h0] <;> omega
  · by_cases h1 : pfx.toNat ≤ 0xB7
    · simp [h0, h1] <;> omega
    · by_cases h2 : pfx.toNat ≤ 0xBF
      · simp [h0, h1, h2] <;> omega
      · by_cases h3 : pfx.toNat ≤ 0xF7
        · simp [h0, h1, h2, h3] <;> omega
        · simp [h0, h1, h2, h3] <;> omega


-- @@ L172-177 verbatim
theorem rlpPrefixShortBytesPayloadLen_le_55_of_class {pfx : Byte}
    (h : classifyPrefix pfx = .shortBytes) :
    rlpPrefixShortBytesPayloadLen pfx ≤ 55 := by
  rw [classifyPrefix_shortBytes_iff] at h
  unfold rlpPrefixShortBytesPayloadLen
  omega


-- @@ L179-184 verbatim
theorem rlpPrefixShortListPayloadLen_le_55_of_class {pfx : Byte}
    (h : classifyPrefix pfx = .shortList) :
    rlpPrefixShortListPayloadLen pfx ≤ 55 := by
  rw [classifyPrefix_shortList_iff] at h
  unfold rlpPrefixShortListPayloadLen
  omega


-- @@ L186-191 verbatim
theorem rlpPrefixLongBytesLenOfLen_pos_of_class {pfx : Byte}
    (h : classifyPrefix pfx = .longBytes) :
    0 < rlpPrefixLongBytesLenOfLen pfx := by
  rw [classifyPrefix_longBytes_iff] at h
  unfold rlpPrefixLongBytesLenOfLen
  omega


-- @@ L193-198 verbatim
theorem rlpPrefixLongBytesLenOfLen_le_8_of_class {pfx : Byte}
    (h : classifyPrefix pfx = .longBytes) :
    rlpPrefixLongBytesLenOfLen pfx ≤ 8 := by
  rw [classifyPrefix_longBytes_iff] at h
  unfold rlpPrefixLongBytesLenOfLen
  omega


-- @@ L200-205 verbatim
theorem rlpPrefixLongListLenOfLen_pos_of_class {pfx : Byte}
    (h : classifyPrefix pfx = .longList) :
    0 < rlpPrefixLongListLenOfLen pfx := by
  rw [classifyPrefix_longList_iff] at h
  unfold rlpPrefixLongListLenOfLen
  omega


-- @@ L207-213 verbatim
theorem rlpPrefixLongListLenOfLen_le_8_of_class {pfx : Byte}
    (h : classifyPrefix pfx = .longList) :
    rlpPrefixLongListLenOfLen pfx ≤ 8 := by
  rw [classifyPrefix_longList_iff] at h
  unfold rlpPrefixLongListLenOfLen
  have h_bound : pfx.toNat < 256 := pfx.isLt
  omega


-- @@ L215-219 verbatim
theorem rlpPrefixLenOfLen_eq_zero_of_singleByte {pfx : Byte}
    (h : classifyPrefix pfx = .singleByte) :
    rlpPrefixLenOfLen pfx = 0 := by
  unfold rlpPrefixLenOfLen
  rw [h]


-- @@ L221-225 verbatim
theorem rlpPrefixLenOfLen_eq_zero_of_shortBytes {pfx : Byte}
    (h : classifyPrefix pfx = .shortBytes) :
    rlpPrefixLenOfLen pfx = 0 := by
  unfold rlpPrefixLenOfLen
  rw [h]


-- @@ L227-231 verbatim
theorem rlpPrefixLenOfLen_eq_longBytesLenOfLen {pfx : Byte}
    (h : classifyPrefix pfx = .longBytes) :
    rlpPrefixLenOfLen pfx = rlpPrefixLongBytesLenOfLen pfx := by
  unfold rlpPrefixLenOfLen
  rw [h]


-- @@ L233-237 verbatim
theorem rlpPrefixLenOfLen_eq_zero_of_shortList {pfx : Byte}
    (h : classifyPrefix pfx = .shortList) :
    rlpPrefixLenOfLen pfx = 0 := by
  unfold rlpPrefixLenOfLen
  rw [h]


-- @@ L239-243 verbatim
theorem rlpPrefixLenOfLen_eq_longListLenOfLen {pfx : Byte}
    (h : classifyPrefix pfx = .longList) :
    rlpPrefixLenOfLen pfx = rlpPrefixLongListLenOfLen pfx := by
  unfold rlpPrefixLenOfLen
  rw [h]


-- @@ L245-250 verbatim
theorem rlpPrefixLenOfLen_le_8 (pfx : Byte) :
    rlpPrefixLenOfLen pfx ≤ 8 := by
  unfold rlpPrefixLenOfLen
  cases h : classifyPrefix pfx <;> simp
  · exact rlpPrefixLongBytesLenOfLen_le_8_of_class h
  · exact rlpPrefixLongListLenOfLen_le_8_of_class h


-- @@ L252-271 verbatim
theorem rlpPrefixLenOfLen_pos_iff_longClass (pfx : Byte) :
    0 < rlpPrefixLenOfLen pfx ↔
      classifyPrefix pfx = .longBytes ∨ classifyPrefix pfx = .longList := by
  constructor
  · intro h_pos
    cases h_class : classifyPrefix pfx
    · rw [rlpPrefixLenOfLen_eq_zero_of_singleByte h_class] at h_pos
      omega
    · rw [rlpPrefixLenOfLen_eq_zero_of_shortBytes h_class] at h_pos
      omega
    · exact Or.inl rfl
    · rw [rlpPrefixLenOfLen_eq_zero_of_shortList h_class] at h_pos
      omega
    · exact Or.inr rfl
  · intro h_long
    rcases h_long with h_longBytes | h_longList
    · rw [rlpPrefixLenOfLen_eq_longBytesLenOfLen h_longBytes]
      exact rlpPrefixLongBytesLenOfLen_pos_of_class h_longBytes
    · rw [rlpPrefixLenOfLen_eq_longListLenOfLen h_longList]
      exact rlpPrefixLongListLenOfLen_pos_of_class h_longList


-- @@ L273-277 verbatim
theorem rlpPrefixLenOfLen_pos_iff_long_ranges (pfx : Byte) :
    0 < rlpPrefixLenOfLen pfx ↔
      (0xB8 ≤ pfx.toNat ∧ pfx.toNat ≤ 0xBF) ∨ 0xF8 ≤ pfx.toNat := by
  rw [rlpPrefixLenOfLen_pos_iff_longClass,
    classifyPrefix_longBytes_iff, classifyPrefix_longList_iff]


-- @@ L279-282 verbatim
theorem rlpPrefixLongBytesHeaderBytes_pos (pfx : Byte) :
    0 < rlpPrefixLongBytesHeaderBytes pfx := by
  unfold rlpPrefixLongBytesHeaderBytes
  omega


-- @@ L284-289 verbatim
theorem rlpPrefixLongBytesHeaderBytes_le_9_of_class {pfx : Byte}
    (h : classifyPrefix pfx = .longBytes) :
    rlpPrefixLongBytesHeaderBytes pfx ≤ 9 := by
  unfold rlpPrefixLongBytesHeaderBytes
  have h_len := rlpPrefixLongBytesLenOfLen_le_8_of_class h
  omega


-- @@ L291-295 verbatim
theorem rlpPrefixLongBytesHeaderBytes_eq_lenOfLen_add_one (pfx : Byte) :
    rlpPrefixLongBytesHeaderBytes pfx =
      rlpPrefixLongBytesLenOfLen pfx + 1 := by
  unfold rlpPrefixLongBytesHeaderBytes
  omega


-- @@ L297-300 verbatim
theorem rlpPrefixLongListHeaderBytes_pos (pfx : Byte) :
    0 < rlpPrefixLongListHeaderBytes pfx := by
  unfold rlpPrefixLongListHeaderBytes
  omega


-- @@ L302-307 verbatim
theorem rlpPrefixLongListHeaderBytes_le_9_of_class {pfx : Byte}
    (h : classifyPrefix pfx = .longList) :
    rlpPrefixLongListHeaderBytes pfx ≤ 9 := by
  unfold rlpPrefixLongListHeaderBytes
  have h_len := rlpPrefixLongListLenOfLen_le_8_of_class h
  omega


-- @@ L309-313 verbatim
theorem rlpPrefixLongListHeaderBytes_eq_lenOfLen_add_one (pfx : Byte) :
    rlpPrefixLongListHeaderBytes pfx =
      rlpPrefixLongListLenOfLen pfx + 1 := by
  unfold rlpPrefixLongListHeaderBytes
  omega


-- @@ L315-319 verbatim
theorem rlpPrefixHeaderBytes_eq_zero_of_singleByte {pfx : Byte}
    (h : classifyPrefix pfx = .singleByte) :
    rlpPrefixHeaderBytes pfx = 0 := by
  unfold rlpPrefixHeaderBytes
  rw [h]


-- @@ L321-325 verbatim
theorem rlpPrefixHeaderBytes_eq_one_of_shortBytes {pfx : Byte}
    (h : classifyPrefix pfx = .shortBytes) :
    rlpPrefixHeaderBytes pfx = 1 := by
  unfold rlpPrefixHeaderBytes
  rw [h]


-- @@ L327-331 verbatim
theorem rlpPrefixHeaderBytes_eq_longBytesHeader_of_longBytes {pfx : Byte}
    (h : classifyPrefix pfx = .longBytes) :
    rlpPrefixHeaderBytes pfx = rlpPrefixLongBytesHeaderBytes pfx := by
  unfold rlpPrefixHeaderBytes
  rw [h]


-- @@ L333-337 verbatim
theorem rlpPrefixHeaderBytes_eq_one_of_shortList {pfx : Byte}
    (h : classifyPrefix pfx = .shortList) :
    rlpPrefixHeaderBytes pfx = 1 := by
  unfold rlpPrefixHeaderBytes
  rw [h]


-- @@ L339-343 verbatim
theorem rlpPrefixHeaderBytes_eq_longListHeader_of_longList {pfx : Byte}
    (h : classifyPrefix pfx = .longList) :
    rlpPrefixHeaderBytes pfx = rlpPrefixLongListHeaderBytes pfx := by
  unfold rlpPrefixHeaderBytes
  rw [h]


-- @@ L345-350 verbatim
theorem rlpPrefixHeaderBytes_le_9 (pfx : Byte) :
    rlpPrefixHeaderBytes pfx ≤ 9 := by
  unfold rlpPrefixHeaderBytes
  cases h : classifyPrefix pfx <;> simp
  · exact rlpPrefixLongBytesHeaderBytes_le_9_of_class h
  · exact rlpPrefixLongListHeaderBytes_le_9_of_class h


-- @@ L352-356 verbatim
theorem rlpPrefixHeaderBytes_pos_of_shortBytes {pfx : Byte}
    (h : classifyPrefix pfx = .shortBytes) :
    0 < rlpPrefixHeaderBytes pfx := by
  rw [rlpPrefixHeaderBytes_eq_one_of_shortBytes h]
  omega


-- @@ L358-362 verbatim
theorem rlpPrefixHeaderBytes_pos_of_longBytes {pfx : Byte}
    (h : classifyPrefix pfx = .longBytes) :
    0 < rlpPrefixHeaderBytes pfx := by
  rw [rlpPrefixHeaderBytes_eq_longBytesHeader_of_longBytes h]
  exact rlpPrefixLongBytesHeaderBytes_pos pfx


-- @@ L364-368 verbatim
theorem rlpPrefixHeaderBytes_pos_of_shortList {pfx : Byte}
    (h : classifyPrefix pfx = .shortList) :
    0 < rlpPrefixHeaderBytes pfx := by
  rw [rlpPrefixHeaderBytes_eq_one_of_shortList h]
  omega


-- @@ L370-374 verbatim
theorem rlpPrefixHeaderBytes_pos_of_longList {pfx : Byte}
    (h : classifyPrefix pfx = .longList) :
    0 < rlpPrefixHeaderBytes pfx := by
  rw [rlpPrefixHeaderBytes_eq_longListHeader_of_longList h]
  exact rlpPrefixLongListHeaderBytes_pos pfx


-- @@ L376-384 verbatim
theorem rlpPrefixHeaderBytes_pos_of_not_singleByte {pfx : Byte}
    (h : classifyPrefix pfx ≠ .singleByte) :
    0 < rlpPrefixHeaderBytes pfx := by
  cases h_class : classifyPrefix pfx
  · contradiction
  · exact rlpPrefixHeaderBytes_pos_of_shortBytes h_class
  · exact rlpPrefixHeaderBytes_pos_of_longBytes h_class
  · exact rlpPrefixHeaderBytes_pos_of_shortList h_class
  · exact rlpPrefixHeaderBytes_pos_of_longList h_class


-- @@ L386-401 verbatim
theorem rlpPrefixHeaderBytes_eq_zero_iff_singleByte (pfx : Byte) :
    rlpPrefixHeaderBytes pfx = 0 ↔ classifyPrefix pfx = .singleByte := by
  constructor
  · intro h_zero
    cases h_class : classifyPrefix pfx
    · rfl
    · have h_pos := rlpPrefixHeaderBytes_pos_of_shortBytes h_class
      omega
    · have h_pos := rlpPrefixHeaderBytes_pos_of_longBytes h_class
      omega
    · have h_pos := rlpPrefixHeaderBytes_pos_of_shortList h_class
      omega
    · have h_pos := rlpPrefixHeaderBytes_pos_of_longList h_class
      omega
  · intro h
    exact rlpPrefixHeaderBytes_eq_zero_of_singleByte h


-- @@ L403-406 verbatim
theorem rlpPrefixHeaderBytes_eq_zero_iff_lt_0x80 (pfx : Byte) :
    rlpPrefixHeaderBytes pfx = 0 ↔ pfx.toNat < 0x80 := by
  rw [rlpPrefixHeaderBytes_eq_zero_iff_singleByte,
    classifyPrefix_singleByte_iff]


-- @@ L408-415 verbatim
theorem rlpPrefixHeaderBytes_pos_iff_not_singleByte (pfx : Byte) :
    0 < rlpPrefixHeaderBytes pfx ↔ classifyPrefix pfx ≠ .singleByte := by
  constructor
  · intro h_pos h_single
    rw [rlpPrefixHeaderBytes_eq_zero_of_singleByte h_single] at h_pos
    omega
  · intro h
    exact rlpPrefixHeaderBytes_pos_of_not_singleByte h


-- @@ L417-428 verbatim
theorem rlpPrefixHeaderBytes_pos_iff_ge_0x80 (pfx : Byte) :
    0 < rlpPrefixHeaderBytes pfx ↔ 0x80 ≤ pfx.toNat := by
  rw [rlpPrefixHeaderBytes_pos_iff_not_singleByte]
  constructor
  · intro h_not_single
    have h_not_lt : ¬ pfx.toNat < 0x80 := by
      intro h_lt
      exact h_not_single ((classifyPrefix_singleByte_iff pfx).mpr h_lt)
    omega
  · intro h_ge h_single
    have h_lt := (classifyPrefix_singleByte_iff pfx).mp h_single
    omega


-- @@ L430-451 verbatim
theorem rlpPrefixHeaderBytes_eq_one_iff_shortClass (pfx : Byte) :
    rlpPrefixHeaderBytes pfx = 1 ↔
      classifyPrefix pfx = .shortBytes ∨ classifyPrefix pfx = .shortList := by
  constructor
  · intro h_one
    cases h_class : classifyPrefix pfx
    · rw [rlpPrefixHeaderBytes_eq_zero_of_singleByte h_class] at h_one
      omega
    · exact Or.inl rfl
    · rw [rlpPrefixHeaderBytes_eq_longBytesHeader_of_longBytes h_class] at h_one
      have h_len := rlpPrefixLongBytesLenOfLen_pos_of_class h_class
      unfold rlpPrefixLongBytesHeaderBytes at h_one
      omega
    · exact Or.inr rfl
    · rw [rlpPrefixHeaderBytes_eq_longListHeader_of_longList h_class] at h_one
      have h_len := rlpPrefixLongListLenOfLen_pos_of_class h_class
      unfold rlpPrefixLongListHeaderBytes at h_one
      omega
  · intro h_short
    rcases h_short with h_shortBytes | h_shortList
    · exact rlpPrefixHeaderBytes_eq_one_of_shortBytes h_shortBytes
    · exact rlpPrefixHeaderBytes_eq_one_of_shortList h_shortList


-- @@ L453-458 verbatim
theorem rlpPrefixHeaderBytes_eq_one_iff_short_ranges (pfx : Byte) :
    rlpPrefixHeaderBytes pfx = 1 ↔
      (0x80 ≤ pfx.toNat ∧ pfx.toNat ≤ 0xB7) ∨
      (0xC0 ≤ pfx.toNat ∧ pfx.toNat ≤ 0xF7) := by
  rw [rlpPrefixHeaderBytes_eq_one_iff_shortClass,
    classifyPrefix_shortBytes_iff, classifyPrefix_shortList_iff]


-- @@ L460-469 verbatim
theorem rlpPrefixHeaderBytes_pos_and_le_one_iff_short_ranges (pfx : Byte) :
    0 < rlpPrefixHeaderBytes pfx ∧ rlpPrefixHeaderBytes pfx ≤ 1 ↔
      (0x80 ≤ pfx.toNat ∧ pfx.toNat ≤ 0xB7) ∨
      (0xC0 ≤ pfx.toNat ∧ pfx.toNat ≤ 0xF7) := by
  constructor
  · intro h
    exact (rlpPrefixHeaderBytes_eq_one_iff_short_ranges pfx).mp (by omega)
  · intro h_short
    have h_one := (rlpPrefixHeaderBytes_eq_one_iff_short_ranges pfx).mpr h_short
    omega


-- @@ L471-494 verbatim
theorem rlpPrefixHeaderBytes_ge_two_iff_longClass (pfx : Byte) :
    2 ≤ rlpPrefixHeaderBytes pfx ↔
      classifyPrefix pfx = .longBytes ∨ classifyPrefix pfx = .longList := by
  constructor
  · intro h_two
    cases h_class : classifyPrefix pfx
    · rw [rlpPrefixHeaderBytes_eq_zero_of_singleByte h_class] at h_two
      omega
    · rw [rlpPrefixHeaderBytes_eq_one_of_shortBytes h_class] at h_two
      omega
    · exact Or.inl rfl
    · rw [rlpPrefixHeaderBytes_eq_one_of_shortList h_class] at h_two
      omega
    · exact Or.inr rfl
  · intro h_long
    rcases h_long with h_longBytes | h_longList
    · rw [rlpPrefixHeaderBytes_eq_longBytesHeader_of_longBytes h_longBytes]
      have h_len := rlpPrefixLongBytesLenOfLen_pos_of_class h_longBytes
      unfold rlpPrefixLongBytesHeaderBytes
      omega
    · rw [rlpPrefixHeaderBytes_eq_longListHeader_of_longList h_longList]
      have h_len := rlpPrefixLongListLenOfLen_pos_of_class h_longList
      unfold rlpPrefixLongListHeaderBytes
      omega


-- @@ L496-501 verbatim
theorem rlpPrefixHeaderBytes_ge_two_iff_long_ranges (pfx : Byte) :
    2 ≤ rlpPrefixHeaderBytes pfx ↔
      (0xB8 ≤ pfx.toNat ∧ pfx.toNat ≤ 0xBF) ∨
        0xF8 ≤ pfx.toNat := by
  rw [rlpPrefixHeaderBytes_ge_two_iff_longClass,
    classifyPrefix_longBytes_iff, classifyPrefix_longList_iff]


-- @@ L503-535 verbatim
theorem rlpPrefixHeaderBytes_lt_two_iff_non_long_ranges (pfx : Byte) :
    rlpPrefixHeaderBytes pfx < 2 ↔
      pfx.toNat < 0xB8 ∨
        (0xC0 ≤ pfx.toNat ∧ pfx.toNat ≤ 0xF7) := by
  have h_bound : pfx.toNat < 256 := pfx.isLt
  constructor
  · intro h_lt
    have h_not_long_ranges :
        ¬ ((0xB8 ≤ pfx.toNat ∧ pfx.toNat ≤ 0xBF) ∨
          0xF8 ≤ pfx.toNat) := by
      intro h_long_ranges
      have h_two :=
        (rlpPrefixHeaderBytes_ge_two_iff_long_ranges pfx).mpr h_long_ranges
      omega
    by_cases h_low : pfx.toNat < 0xB8
    · exact Or.inl h_low
    · right
      have h_not_long_bytes : ¬ (0xB8 ≤ pfx.toNat ∧ pfx.toNat ≤ 0xBF) := by
        intro h_long_bytes
        exact h_not_long_ranges (Or.inl h_long_bytes)
      have h_not_long_list : ¬ 0xF8 ≤ pfx.toNat := by
        intro h_long_list
        exact h_not_long_ranges (Or.inr h_long_list)
      omega
  · intro h_non_long
    by_cases h_lt : rlpPrefixHeaderBytes pfx < 2
    · exact h_lt
    have h_two : 2 ≤ rlpPrefixHeaderBytes pfx := by omega
    have h_long_ranges :=
      (rlpPrefixHeaderBytes_ge_two_iff_long_ranges pfx).mp h_two
    rcases h_non_long with h_low | h_short_list
    · rcases h_long_ranges with h_long_bytes | h_long_list <;> omega
    · rcases h_long_ranges with h_long_bytes | h_long_list <;> omega


-- @@ L537-547 verbatim
theorem rlpPrefixHeaderBytes_le_one_iff_non_long_ranges (pfx : Byte) :
    rlpPrefixHeaderBytes pfx ≤ 1 ↔
      pfx.toNat < 0xB8 ∨
        (0xC0 ≤ pfx.toNat ∧ pfx.toNat ≤ 0xF7) := by
  constructor
  · intro h_le
    exact (rlpPrefixHeaderBytes_lt_two_iff_non_long_ranges pfx).mp (by omega)
  · intro h_non_long
    have h_lt :=
      (rlpPrefixHeaderBytes_lt_two_iff_non_long_ranges pfx).mpr h_non_long
    omega


-- @@ L549-558 verbatim
theorem rlpPrefixHeaderBytes_eq_zero_or_one_iff_non_long_ranges (pfx : Byte) :
    rlpPrefixHeaderBytes pfx = 0 ∨ rlpPrefixHeaderBytes pfx = 1 ↔
      pfx.toNat < 0xB8 ∨
        (0xC0 ≤ pfx.toNat ∧ pfx.toNat ≤ 0xF7) := by
  rw [← rlpPrefixHeaderBytes_le_one_iff_non_long_ranges]
  constructor
  · intro h_zero_or_one
    rcases h_zero_or_one with h_zero | h_one <;> omega
  · intro h_le
    omega


-- @@ L560-571 verbatim
theorem rlpPrefixHeaderBytes_eq_zero_or_one_or_ge_two (pfx : Byte) :
    rlpPrefixHeaderBytes pfx = 0 ∨
      rlpPrefixHeaderBytes pfx = 1 ∨
      2 ≤ rlpPrefixHeaderBytes pfx := by
  cases h_class : classifyPrefix pfx
  · exact Or.inl (rlpPrefixHeaderBytes_eq_zero_of_singleByte h_class)
  · exact Or.inr (Or.inl (rlpPrefixHeaderBytes_eq_one_of_shortBytes h_class))
  · exact Or.inr (Or.inr
      ((rlpPrefixHeaderBytes_ge_two_iff_longClass pfx).mpr (Or.inl h_class)))
  · exact Or.inr (Or.inl (rlpPrefixHeaderBytes_eq_one_of_shortList h_class))
  · exact Or.inr (Or.inr
      ((rlpPrefixHeaderBytes_ge_two_iff_longClass pfx).mpr (Or.inr h_class)))


-- @@ L573-573 verbatim
end EvmAsm.EL.RLP
