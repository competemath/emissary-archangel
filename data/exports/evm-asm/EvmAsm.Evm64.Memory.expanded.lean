/-
  EvmAsm.Evm64.Memory

  Separation logic model for EVM memory (byte-addressable, zero-initialized,
  dynamically expandable) stored in RV64IM doubleword-aligned memory cells.

  Slice 1 (issue #99): defines the core `evmMemIs` assertion at dword-cell
  granularity plus the zero-initialized form `evmMemZero`.

  Slice 2 (issue #99): tracks the EVM memory high-water mark in a single
  scratch dword cell via `evmMemSizeIs`, and provides the pure expansion
  helper `evmMemExpand` that computes the new byte-size after an access of
  `(offset, length)`, rounded up to a 32-byte-word boundary as the EVM-spec
  requires. Subsequent slices wire this into MLOAD/MSTORE/MSTORE8 (slices
  3-5) and MSIZE (slice 6).

  Design choices (kept minimal for this slice):

  * EVM memory is modelled as a sequence of 64-bit cells, each owning eight
    consecutive bytes. Byte-level access (MSTORE8 / MLOAD at unaligned
    offsets) will be lifted on top of `evmMemIs` in later slices via the
    `ByteOps.lean` LBU/SB byte-level specs, which already operate on the
    underlying `↦ₘ` dword cells.
  * `numCells` is the dword (8-byte) count. The corresponding EVM byte size
    is `8 * numCells`. EVM memory expansion in the spec is in 32-byte words,
    which is a constraint enforced by the consumers (MSTORE/MLOAD specs),
    not by `evmMemIs` itself.
  * `contents : Nat → Word` is a pure function rather than a `ByteArray`
    so the assertion is total in `Nat` index — out-of-range indices simply
    have no cell asserted (they sit outside the sepConj chain). This
    matches how `evmStackIs` uses a `List EvmWord`.
-/

module

public import EvmAsm.Rv64.ByteOps
public import EvmAsm.Rv64.SepLogic


-- @@ L39-39 verbatim
@[expose] public section


-- @@ L41-41 verbatim
namespace EvmAsm.Evm64


-- @@ L43-43 verbatim
open EvmAsm.Rv64


-- @@ L45-56 verbatim
/-- `evmMemIs base numCells contents` asserts that `numCells` consecutive
    8-byte memory cells starting at `base` hold the values `contents 0 ..
    contents (numCells-1)`. The cells are stored at byte offsets
    `base + 0, base + 8, ..., base + 8*(numCells-1)`.

    This is the dword-cell view of EVM memory. Byte-level reads/writes are
    lifted on top via the `ByteOps.lean` LBU/SB specs in later slices. -/
def evmMemIs (base : Word) (numCells : Nat) (contents : Nat → Word) : Assertion :=
  match numCells with
  | 0     => empAssertion
  | n + 1 =>
      evmMemIs base n contents ** ((base + (BitVec.ofNat 64 (8 * n))) ↦ₘ contents n)


-- @@ L58-61 verbatim
/-- The zero-initialized EVM memory region: `numCells` dword cells, all 0.
    Models the EVM-spec invariant that unwritten memory reads as zero. -/
def evmMemZero (base : Word) (numCells : Nat) : Assertion :=
  evmMemIs base numCells (fun _ => 0)


-- @@ L63-64 verbatim
@[simp] theorem evmMemIs_zero {base : Word} {contents : Nat → Word} :
    evmMemIs base 0 contents = empAssertion := rfl


-- @@ L66-68 verbatim
theorem evmMemIs_succ {base : Word} {n : Nat} {contents : Nat → Word} :
    evmMemIs base (n + 1) contents =
      (evmMemIs base n contents ** ((base + (BitVec.ofNat 64 (8 * n))) ↦ₘ contents n)) := rfl


-- @@ L70-71 verbatim
@[simp] theorem evmMemZero_zero {base : Word} :
    evmMemZero base 0 = empAssertion := rfl


-- @@ L73-75 verbatim
theorem evmMemZero_succ {base : Word} {n : Nat} :
    evmMemZero base (n + 1) =
      (evmMemZero base n ** ((base + (BitVec.ofNat 64 (8 * n))) ↦ₘ 0)) := rfl


-- @@ L77-77 verbatim
/-! ## pcFree -/


-- @@ L79-85 verbatim
theorem pcFree_evmMemIs {base : Word} {n : Nat} {contents : Nat → Word} :
    (evmMemIs base n contents).pcFree := by
  induction n with
  | zero => exact pcFree_emp
  | succ k ih =>
      rw [evmMemIs_succ]
      exact pcFree_sepConj ih pcFree_memIs


-- @@ L87-89 verbatim
theorem pcFree_evmMemZero {base : Word} {n : Nat} :
    (evmMemZero base n).pcFree := by
  unfold evmMemZero; exact pcFree_evmMemIs


-- @@ L91-92 verbatim
instance (base : Word) (n : Nat) (contents : Nat → Word) :
    Assertion.PCFree (evmMemIs base n contents) := ⟨pcFree_evmMemIs⟩


-- @@ L94-95 verbatim
instance (base : Word) (n : Nat) : Assertion.PCFree (evmMemZero base n) :=
  ⟨pcFree_evmMemZero⟩


-- @@ L97-97 verbatim
/-! ## Byte-addressing adapters -/


-- @@ L99-102 verbatim
/-- The RV64 dword cell address that owns the EVM memory byte
    `memBase + byteAddr`. -/
def evmMemDwordAddr (memBase byteAddr : Word) : Word :=
  alignToDword (memBase + byteAddr)


-- @@ L104-107 verbatim
/-- The byte position, inside its owning RV64 dword, of EVM memory byte
    `memBase + byteAddr`. -/
def evmMemByteOffset (memBase byteAddr : Word) : Nat :=
  byteOffset (memBase + byteAddr)


-- @@ L109-111 verbatim
/-- Read the EVM memory byte at `byteAddr` from its owning RV64 dword value. -/
def evmMemByteRead (memBase byteAddr dwordVal : Word) : BitVec 8 :=
  extractByte dwordVal (evmMemByteOffset memBase byteAddr)


-- @@ L113-115 verbatim
/-- Own the RV64 dword cell that contains EVM memory byte `byteAddr`. -/
def evmMemDwordIs (memBase byteAddr dwordVal : Word) : Assertion :=
  evmMemDwordAddr memBase byteAddr ↦ₘ dwordVal


-- @@ L117-122 verbatim
/-- Own the post-state dword after writing byte `b` to EVM memory byte
    `byteAddr`, starting from old owning dword `oldDword`. -/
def evmMemByteWriteIs
    (memBase byteAddr oldDword : Word) (b : BitVec 8) : Assertion :=
  evmMemDwordIs memBase byteAddr
    (replaceByte oldDword (evmMemByteOffset memBase byteAddr) b)


-- @@ L124-125 verbatim
theorem evmMemDwordAddr_unfold {memBase byteAddr : Word} :
    evmMemDwordAddr memBase byteAddr = alignToDword (memBase + byteAddr) := rfl


-- @@ L127-128 verbatim
theorem evmMemByteOffset_unfold {memBase byteAddr : Word} :
    evmMemByteOffset memBase byteAddr = byteOffset (memBase + byteAddr) := rfl


-- @@ L130-133 verbatim
theorem evmMemByteOffset_lt_8 (memBase byteAddr : Word) :
    evmMemByteOffset memBase byteAddr < 8 := by
  unfold evmMemByteOffset
  exact byteOffset_lt_8


-- @@ L135-138 verbatim
theorem evmMemByteAccess_valid_iff_memAddr_valid (memBase byteAddr : Word) :
    isValidByteAccess (memBase + byteAddr) = true ↔
      isValidMemAddr (memBase + byteAddr) = true := by
  rfl


-- @@ L140-143 verbatim
theorem evmMemByteAccess_valid_of_memAddr_valid {memBase byteAddr : Word}
    (h_valid : isValidMemAddr (memBase + byteAddr) = true) :
    isValidByteAccess (memBase + byteAddr) = true := by
  exact (evmMemByteAccess_valid_iff_memAddr_valid memBase byteAddr).mpr h_valid


-- @@ L145-148 verbatim
/-- The byte position inside the owning RV64 dword, packaged as a `Fin 8`
    for direct use with byte-algebra lemmas. -/
def evmMemByteOffsetFin (memBase byteAddr : Word) : Fin 8 :=
  ⟨evmMemByteOffset memBase byteAddr, evmMemByteOffset_lt_8 memBase byteAddr⟩


-- @@ L150-152 verbatim
@[simp] theorem evmMemByteOffsetFin_val (memBase byteAddr : Word) :
    (evmMemByteOffsetFin memBase byteAddr).val =
      evmMemByteOffset memBase byteAddr := rfl


-- @@ L154-156 verbatim
theorem evmMemByteRead_unfold {memBase byteAddr dwordVal : Word} :
    evmMemByteRead memBase byteAddr dwordVal =
      extractByte dwordVal (evmMemByteOffset memBase byteAddr) := rfl


-- @@ L158-164 verbatim
theorem evmMemByteRead_replace_same
    (memBase byteAddr oldDword : Word) (b : BitVec 8) :
    evmMemByteRead memBase byteAddr
      (replaceByte oldDword (evmMemByteOffset memBase byteAddr) b) = b := by
  unfold evmMemByteRead evmMemByteOffset
  exact extractByte_replaceByte_same oldDword
    (evmMemByteOffsetFin memBase byteAddr) b


-- @@ L166-173 verbatim
/-- LBU-shaped bridge: zero-extending the byte read immediately after an EVM
    memory byte write yields the written byte, zero-extended to a word. -/
theorem evmMemByteRead_replace_same_zeroExtend
    (memBase byteAddr oldDword : Word) (b : BitVec 8) :
    (evmMemByteRead memBase byteAddr
      (replaceByte oldDword (evmMemByteOffset memBase byteAddr) b)).zeroExtend 64 =
      b.zeroExtend 64 := by
  rw [evmMemByteRead_replace_same]


-- @@ L175-182 verbatim
/-- LB-shaped bridge: sign-extending the byte read immediately after an EVM
    memory byte write yields the written byte, sign-extended to a word. -/
theorem evmMemByteRead_replace_same_signExtend
    (memBase byteAddr oldDword : Word) (b : BitVec 8) :
    (evmMemByteRead memBase byteAddr
      (replaceByte oldDword (evmMemByteOffset memBase byteAddr) b)).signExtend 64 =
      b.signExtend 64 := by
  rw [evmMemByteRead_replace_same]


-- @@ L184-186 verbatim
theorem evmMemDwordIs_unfold {memBase byteAddr dwordVal : Word} :
    evmMemDwordIs memBase byteAddr dwordVal =
      (evmMemDwordAddr memBase byteAddr ↦ₘ dwordVal) := rfl


-- @@ L188-192 verbatim
theorem evmMemByteWriteIs_unfold
    {memBase byteAddr oldDword : Word} {b : BitVec 8} :
    evmMemByteWriteIs memBase byteAddr oldDword b =
      evmMemDwordIs memBase byteAddr
        (replaceByte oldDword (evmMemByteOffset memBase byteAddr) b) := rfl


-- @@ L194-196 verbatim
theorem pcFree_evmMemDwordIs {memBase byteAddr dwordVal : Word} :
    (evmMemDwordIs memBase byteAddr dwordVal).pcFree := by
  unfold evmMemDwordIs; exact pcFree_memIs


-- @@ L198-201 verbatim
theorem pcFree_evmMemByteWriteIs
    {memBase byteAddr oldDword : Word} {b : BitVec 8} :
    (evmMemByteWriteIs memBase byteAddr oldDword b).pcFree := by
  unfold evmMemByteWriteIs; exact pcFree_evmMemDwordIs


-- @@ L203-205 verbatim
instance (memBase byteAddr dwordVal : Word) :
    Assertion.PCFree (evmMemDwordIs memBase byteAddr dwordVal) :=
  ⟨pcFree_evmMemDwordIs⟩


-- @@ L207-209 verbatim
instance (memBase byteAddr oldDword : Word) (b : BitVec 8) :
    Assertion.PCFree (evmMemByteWriteIs memBase byteAddr oldDword b) :=
  ⟨pcFree_evmMemByteWriteIs⟩


-- @@ L211-223 verbatim
/-! ## High-water mark / EVM memory expansion (slice 2)

  The EVM tracks a single dynamic byte-size for memory (MSIZE), which only
  grows: any access to byte range `[offset, offset + length)` expands the
  active memory to the smallest multiple of 32 that covers the access, and
  the new size is the max of the old size and that bound.

  We model the size as a single 64-bit cell held at a caller-chosen scratch
  location `sizeLoc`, owning the assertion that the cell holds the current
  byte-size. The pure helper `evmMemExpand` computes the new byte-size; the
  separation-logic specs in later slices (MLOAD/MSTORE/MSTORE8/MSIZE) will
  read this cell, replace it, and reason about the contents update via
  `evmMemSizeIs`. -/


-- @@ L225-230 verbatim
/-- The EVM memory size cell: an 8-byte cell at `sizeLoc` holding the current
    byte-size of EVM memory. The size is the high-water mark — bytes
    `[0, sizeBytes)` may be accessed; reads of unwritten bytes within that
    range still return zero (modelled by `evmMemZero`). -/
def evmMemSizeIs (sizeLoc : Word) (sizeBytes : Nat) : Assertion :=
  sizeLoc ↦ₘ BitVec.ofNat 64 sizeBytes


-- @@ L232-233 verbatim
theorem evmMemSizeIs_unfold {sizeLoc : Word} {sizeBytes : Nat} :
    evmMemSizeIs sizeLoc sizeBytes = (sizeLoc ↦ₘ BitVec.ofNat 64 sizeBytes) := rfl


-- @@ L235-237 verbatim
theorem pcFree_evmMemSizeIs {sizeLoc : Word} {sizeBytes : Nat} :
    (evmMemSizeIs sizeLoc sizeBytes).pcFree := by
  unfold evmMemSizeIs; exact pcFree_memIs


-- @@ L239-240 verbatim
instance (sizeLoc : Word) (sizeBytes : Nat) :
    Assertion.PCFree (evmMemSizeIs sizeLoc sizeBytes) := ⟨pcFree_evmMemSizeIs⟩


-- @@ L242-244 verbatim
/-- Round a byte count up to the next multiple of 32 (the EVM word size).
    `roundUpTo32 n = ((n + 31) / 32) * 32`. -/
def roundUpTo32 (n : Nat) : Nat := ((n + 31) / 32) * 32


-- @@ L246-246 verbatim
theorem roundUpTo32_zero : roundUpTo32 0 = 0 := by decide


-- @@ L248-253 verbatim
theorem roundUpTo32_le (n : Nat) : n ≤ roundUpTo32 n := by
  unfold roundUpTo32
  have h : n ≤ (n + 31) / 32 * 32 := by
    have := Nat.div_mul_le_self (n + 31) 32
    omega
  exact h


-- @@ L255-258 verbatim
theorem roundUpTo32_le_add_31 (n : Nat) :
    roundUpTo32 n ≤ n + 31 := by
  unfold roundUpTo32
  exact Nat.div_mul_le_self (n + 31) 32


-- @@ L260-261 verbatim
theorem roundUpTo32_dvd (n : Nat) : 32 ∣ roundUpTo32 n := by
  unfold roundUpTo32; exact ⟨(n + 31) / 32, (Nat.mul_comm _ _)⟩


-- @@ L263-267 verbatim
theorem roundUpTo32_eq_self_of_dvd (n : Nat) (h : 32 ∣ n) :
    roundUpTo32 n = n := by
  rcases h with ⟨k, rfl⟩
  unfold roundUpTo32
  omega


-- @@ L269-273 verbatim
theorem roundUpTo32_le_of_le_dvd {n m : Nat} (h_le : n ≤ m) (h_dvd : 32 ∣ m) :
    roundUpTo32 n ≤ m := by
  rcases h_dvd with ⟨k, rfl⟩
  unfold roundUpTo32
  omega


-- @@ L275-279 verbatim
theorem roundUpTo32_idempotent (n : Nat) : roundUpTo32 (roundUpTo32 n) = roundUpTo32 n := by
  unfold roundUpTo32
  -- (n+31)/32 * 32 is already a multiple of 32, so adding 31 and dividing
  -- by 32 yields the same quotient. omega handles Nat div/mod.
  omega


-- @@ L281-290 verbatim
/-- The pure EVM memory-expansion update: given the current high-water
    `sizeBytes` and an access `(offset, length)`, compute the new
    high-water mark.

    Per the EVM yellow paper, an access of zero length never expands memory.
    Otherwise the active memory grows to cover `[offset, offset + length)`,
    rounded up to a 32-byte boundary, and the new size is the max of the old
    size and that bound. -/
def evmMemExpand (sizeBytes offset length : Nat) : Nat :=
  if length = 0 then sizeBytes else max sizeBytes (roundUpTo32 (offset + length))


-- @@ L292-295 verbatim
/-- Zero-length accesses do not expand EVM memory. -/
@[simp] theorem evmMemExpand_zero_length (sizeBytes offset : Nat) :
    evmMemExpand sizeBytes offset 0 = sizeBytes := by
  unfold evmMemExpand; simp


-- @@ L297-302 verbatim
theorem evmMemExpand_ge_old (sizeBytes offset length : Nat) :
    sizeBytes ≤ evmMemExpand sizeBytes offset length := by
  unfold evmMemExpand
  by_cases h : length = 0
  · simp [h]
  · rw [if_neg h]; exact Nat.le_max_left _ _


-- @@ L304-308 verbatim
theorem evmMemExpand_ge_access (sizeBytes offset length : Nat) (hlen : length ≠ 0) :
    offset + length ≤ evmMemExpand sizeBytes offset length := by
  unfold evmMemExpand
  rw [if_neg hlen]
  exact Nat.le_trans (roundUpTo32_le _) (Nat.le_max_right _ _)


-- @@ L310-315 verbatim
theorem evmMemExpand_access_byte_lt
    (sizeBytes offset length byteIndex : Nat)
    (hlen : length ≠ 0) (h_byte : byteIndex < length) :
    offset + byteIndex < evmMemExpand sizeBytes offset length := by
  have h_end := evmMemExpand_ge_access sizeBytes offset length hlen
  omega


-- @@ L317-328 verbatim
theorem evmMemExpand_access_byte_dword_end_le
    (sizeBytes offset length byteIndex : Nat)
    (hlen : length ≠ 0) (h_byte : byteIndex < length) :
    ((offset + byteIndex) / 8 + 1) * 8 ≤
      evmMemExpand sizeBytes offset length := by
  unfold evmMemExpand
  rw [if_neg hlen]
  have h_round : ((offset + byteIndex) / 8 + 1) * 8 ≤
      roundUpTo32 (offset + length) := by
    unfold roundUpTo32
    omega
  exact Nat.le_trans h_round (Nat.le_max_right _ _)


-- @@ L330-339 verbatim
theorem evmMemExpand_access_byte_dword_start_lt
    (sizeBytes offset length byteIndex : Nat)
    (hlen : length ≠ 0) (h_byte : byteIndex < length) :
    ((offset + byteIndex) / 8) * 8 <
      evmMemExpand sizeBytes offset length := by
  have h_byte_lt :=
    evmMemExpand_access_byte_lt sizeBytes offset length byteIndex hlen h_byte
  have h_start_le : ((offset + byteIndex) / 8) * 8 ≤ offset + byteIndex := by
    exact Nat.div_mul_le_self (offset + byteIndex) 8
  exact Nat.lt_of_le_of_lt h_start_le h_byte_lt


-- @@ L341-352 verbatim
theorem evmMemExpand_access_byte_dword_interval
    (sizeBytes offset length byteIndex : Nat)
    (hlen : length ≠ 0) (h_byte : byteIndex < length) :
    ((offset + byteIndex) / 8) * 8 <
        evmMemExpand sizeBytes offset length ∧
      ((offset + byteIndex) / 8 + 1) * 8 ≤
        evmMemExpand sizeBytes offset length := by
  exact ⟨
    evmMemExpand_access_byte_dword_start_lt
      sizeBytes offset length byteIndex hlen h_byte,
    evmMemExpand_access_byte_dword_end_le
      sizeBytes offset length byteIndex hlen h_byte⟩


-- @@ L354-367 verbatim
theorem evmMemExpand_access_byte_dword_byte_lt
    (sizeBytes offset length byteIndex dwordByte : Nat)
    (hlen : length ≠ 0) (h_byte : byteIndex < length)
    (h_dwordByte : dwordByte < 8) :
    ((offset + byteIndex) / 8) * 8 + dwordByte <
      evmMemExpand sizeBytes offset length := by
  have h_interval :=
    evmMemExpand_access_byte_dword_interval
      sizeBytes offset length byteIndex hlen h_byte
  have h_lt_end :
      ((offset + byteIndex) / 8) * 8 + dwordByte <
        ((offset + byteIndex) / 8 + 1) * 8 := by
    omega
  exact Nat.lt_of_lt_of_le h_lt_end h_interval.2


-- @@ L369-374 verbatim
theorem evmMemExpand_access_dword_interval
    (sizeBytes offset length : Nat) (hlen : length ≠ 0) :
    (offset / 8) * 8 < evmMemExpand sizeBytes offset length ∧
      (offset / 8 + 1) * 8 ≤ evmMemExpand sizeBytes offset length := by
  exact evmMemExpand_access_byte_dword_interval
    sizeBytes offset length 0 hlen (Nat.pos_of_ne_zero hlen)


-- @@ L376-386 verbatim
theorem evmMemExpand_access_last_dword_interval
    (sizeBytes offset length : Nat) (hlen : length ≠ 0) :
    ((offset + (length - 1)) / 8) * 8 <
        evmMemExpand sizeBytes offset length ∧
      ((offset + (length - 1)) / 8 + 1) * 8 ≤
        evmMemExpand sizeBytes offset length := by
  have h_byte : length - 1 < length := by
    have h_pos : 0 < length := Nat.pos_of_ne_zero hlen
    omega
  exact evmMemExpand_access_byte_dword_interval
    sizeBytes offset length (length - 1) hlen h_byte


-- @@ L388-395 verbatim
theorem evmMemExpand_access_dword_span
    (sizeBytes offset length : Nat) (hlen : length ≠ 0) :
    (offset / 8) * 8 < evmMemExpand sizeBytes offset length ∧
      ((offset + (length - 1)) / 8 + 1) * 8 ≤
        evmMemExpand sizeBytes offset length := by
  exact ⟨
    (evmMemExpand_access_dword_interval sizeBytes offset length hlen).1,
    (evmMemExpand_access_last_dword_interval sizeBytes offset length hlen).2⟩


-- @@ L397-402 verbatim
/-- MLOAD and MSTORE access one full 32-byte EVM word. -/
theorem evmMemExpand_word_eq (sizeBytes offset : Nat) :
    evmMemExpand sizeBytes offset 32 =
      max sizeBytes (roundUpTo32 (offset + 32)) := by
  unfold evmMemExpand
  simp


-- @@ L404-409 verbatim
/-- Byte-granular memory writes such as MSTORE8 access one EVM memory byte. -/
theorem evmMemExpand_byte_eq (sizeBytes offset : Nat) :
    evmMemExpand sizeBytes offset 1 =
      max sizeBytes (roundUpTo32 (offset + 1)) := by
  unfold evmMemExpand
  simp


-- @@ L411-436 verbatim
theorem bitvec_select_word_eq_ofNat_max
    (sizeBytes rounded : Nat)
    (h_size : sizeBytes < 2^64)
    (h_round : rounded < 2^64) :
    (if BitVec.ult (BitVec.ofNat 64 sizeBytes) (BitVec.ofNat 64 rounded)
      then BitVec.ofNat 64 rounded else BitVec.ofNat 64 sizeBytes) =
      BitVec.ofNat 64 (max sizeBytes rounded) := by
  by_cases h_lt : sizeBytes < rounded
  · have h_ult :
        BitVec.ult (BitVec.ofNat 64 sizeBytes) (BitVec.ofNat 64 rounded) = true := by
      unfold BitVec.ult
      simp only [BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt h_size, Nat.mod_eq_of_lt h_round]
      simp [h_lt]
    have h_max : max sizeBytes rounded = rounded :=
      max_eq_right (Nat.le_of_lt h_lt)
    simp [h_ult, h_max]
  · have h_ult :
        BitVec.ult (BitVec.ofNat 64 sizeBytes) (BitVec.ofNat 64 rounded) = false := by
      unfold BitVec.ult
      simp only [BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt h_size, Nat.mod_eq_of_lt h_round]
      simp [h_lt]
    have h_max : max sizeBytes rounded = sizeBytes :=
      max_eq_left (by omega)
    simp [h_ult, h_max]


-- @@ L438-443 verbatim
theorem evmMemExpand_word_eq_old_of_end_le
    (sizeBytes offset : Nat) (h_end : offset + 32 ≤ sizeBytes)
    (h_size_dvd : 32 ∣ sizeBytes) :
    evmMemExpand sizeBytes offset 32 = sizeBytes := by
  rw [evmMemExpand_word_eq]
  exact max_eq_left (roundUpTo32_le_of_le_dvd h_end h_size_dvd)


-- @@ L445-450 verbatim
theorem evmMemExpand_word_eq_rounded_of_old_le
    (sizeBytes offset : Nat)
    (h_old : sizeBytes ≤ roundUpTo32 (offset + 32)) :
    evmMemExpand sizeBytes offset 32 = roundUpTo32 (offset + 32) := by
  rw [evmMemExpand_word_eq]
  exact max_eq_right h_old


-- @@ L452-456 verbatim
theorem evmMemExpand_word_eq_rounded_of_end_gt
    (sizeBytes offset : Nat) (h_end : sizeBytes < offset + 32) :
    evmMemExpand sizeBytes offset 32 = roundUpTo32 (offset + 32) := by
  exact evmMemExpand_word_eq_rounded_of_old_le sizeBytes offset
    (Nat.le_trans (Nat.le_of_lt h_end) (roundUpTo32_le (offset + 32)))


-- @@ L458-463 verbatim
theorem evmMemExpand_byte_eq_old_of_end_le
    (sizeBytes offset : Nat) (h_end : offset + 1 ≤ sizeBytes)
    (h_size_dvd : 32 ∣ sizeBytes) :
    evmMemExpand sizeBytes offset 1 = sizeBytes := by
  rw [evmMemExpand_byte_eq]
  exact max_eq_left (roundUpTo32_le_of_le_dvd h_end h_size_dvd)


-- @@ L465-470 verbatim
theorem evmMemExpand_byte_eq_rounded_of_old_le
    (sizeBytes offset : Nat)
    (h_old : sizeBytes ≤ roundUpTo32 (offset + 1)) :
    evmMemExpand sizeBytes offset 1 = roundUpTo32 (offset + 1) := by
  rw [evmMemExpand_byte_eq]
  exact max_eq_right h_old


-- @@ L472-479 verbatim
/--
  Named size-cell postcondition for a 32-byte MLOAD/MSTORE-style access.
  This keeps opcode specs from repeating the high-water expression in every
  postcondition while preserving the underlying `evmMemSizeIs` ownership.
-/
@[irreducible]
def evmMemSizeIsWordExpanded (sizeLoc : Word) (sizeBytes offset : Nat) : Assertion :=
  evmMemSizeIs sizeLoc (evmMemExpand sizeBytes offset 32)


-- @@ L481-486 verbatim
theorem evmMemSizeIsWordExpanded_unfold
    {sizeLoc : Word} {sizeBytes offset : Nat} :
    evmMemSizeIsWordExpanded sizeLoc sizeBytes offset =
      evmMemSizeIs sizeLoc (evmMemExpand sizeBytes offset 32) := by
  delta evmMemSizeIsWordExpanded
  rfl


-- @@ L488-492 verbatim
theorem evmMemSizeIsWordExpanded_unfold_max
    {sizeLoc : Word} {sizeBytes offset : Nat} :
    evmMemSizeIsWordExpanded sizeLoc sizeBytes offset =
      evmMemSizeIs sizeLoc (max sizeBytes (roundUpTo32 (offset + 32))) := by
  rw [evmMemSizeIsWordExpanded_unfold, evmMemExpand_word_eq]


-- @@ L494-500 verbatim
theorem evmMemSizeIsWordExpanded_eq_current_of_mload_within
    {sizeLoc : Word} {sizeBytes offset : Nat}
    (h_end : offset + 32 ≤ sizeBytes) (h_size_dvd : 32 ∣ sizeBytes) :
    evmMemSizeIsWordExpanded sizeLoc sizeBytes offset =
      evmMemSizeIs sizeLoc sizeBytes := by
  rw [evmMemSizeIsWordExpanded_unfold,
    evmMemExpand_word_eq_old_of_end_le sizeBytes offset h_end h_size_dvd]


-- @@ L502-508 verbatim
theorem evmMemSizeIsWordExpanded_eq_rounded_of_mload_within
    {sizeLoc : Word} {sizeBytes offset : Nat}
    (h_old : sizeBytes ≤ roundUpTo32 (offset + 32)) :
    evmMemSizeIsWordExpanded sizeLoc sizeBytes offset =
      evmMemSizeIs sizeLoc (roundUpTo32 (offset + 32)) := by
  rw [evmMemSizeIsWordExpanded_unfold,
    evmMemExpand_word_eq_rounded_of_old_le sizeBytes offset h_old]


-- @@ L510-516 verbatim
theorem evmMemSizeIsWordExpanded_eq_rounded_of_word_growth
    {sizeLoc : Word} {sizeBytes offset : Nat}
    (h_end : sizeBytes < offset + 32) :
    evmMemSizeIsWordExpanded sizeLoc sizeBytes offset =
      evmMemSizeIs sizeLoc (roundUpTo32 (offset + 32)) := by
  rw [evmMemSizeIsWordExpanded_unfold,
    evmMemExpand_word_eq_rounded_of_end_gt sizeBytes offset h_end]


-- @@ L518-522 verbatim
theorem pcFree_evmMemSizeIsWordExpanded
    {sizeLoc : Word} {sizeBytes offset : Nat} :
    (evmMemSizeIsWordExpanded sizeLoc sizeBytes offset).pcFree := by
  rw [evmMemSizeIsWordExpanded_unfold]
  exact pcFree_evmMemSizeIs


-- @@ L524-526 verbatim
instance (sizeLoc : Word) (sizeBytes offset : Nat) :
    Assertion.PCFree (evmMemSizeIsWordExpanded sizeLoc sizeBytes offset) :=
  ⟨pcFree_evmMemSizeIsWordExpanded⟩


-- @@ L528-534 verbatim
/--
  Named size-cell postcondition for a one-byte MSTORE8-style access.
  This mirrors `evmMemSizeIsWordExpanded` for byte-granular memory updates.
-/
@[irreducible]
def evmMemSizeIsByteExpanded (sizeLoc : Word) (sizeBytes offset : Nat) : Assertion :=
  evmMemSizeIs sizeLoc (evmMemExpand sizeBytes offset 1)


-- @@ L536-541 verbatim
theorem evmMemSizeIsByteExpanded_unfold
    {sizeLoc : Word} {sizeBytes offset : Nat} :
    evmMemSizeIsByteExpanded sizeLoc sizeBytes offset =
      evmMemSizeIs sizeLoc (evmMemExpand sizeBytes offset 1) := by
  delta evmMemSizeIsByteExpanded
  rfl


-- @@ L543-547 verbatim
theorem evmMemSizeIsByteExpanded_unfold_max
    {sizeLoc : Word} {sizeBytes offset : Nat} :
    evmMemSizeIsByteExpanded sizeLoc sizeBytes offset =
      evmMemSizeIs sizeLoc (max sizeBytes (roundUpTo32 (offset + 1))) := by
  rw [evmMemSizeIsByteExpanded_unfold, evmMemExpand_byte_eq]


-- @@ L549-555 verbatim
theorem evmMemSizeIsByteExpanded_eq_current_of_mstore8_within
    {sizeLoc : Word} {sizeBytes offset : Nat}
    (h_end : offset + 1 ≤ sizeBytes) (h_size_dvd : 32 ∣ sizeBytes) :
    evmMemSizeIsByteExpanded sizeLoc sizeBytes offset =
      evmMemSizeIs sizeLoc sizeBytes := by
  rw [evmMemSizeIsByteExpanded_unfold,
    evmMemExpand_byte_eq_old_of_end_le sizeBytes offset h_end h_size_dvd]


-- @@ L557-563 verbatim
theorem evmMemSizeIsByteExpanded_eq_rounded_of_mstore8_within
    {sizeLoc : Word} {sizeBytes offset : Nat}
    (h_old : sizeBytes ≤ roundUpTo32 (offset + 1)) :
    evmMemSizeIsByteExpanded sizeLoc sizeBytes offset =
      evmMemSizeIs sizeLoc (roundUpTo32 (offset + 1)) := by
  rw [evmMemSizeIsByteExpanded_unfold,
    evmMemExpand_byte_eq_rounded_of_old_le sizeBytes offset h_old]


-- @@ L565-569 verbatim
theorem pcFree_evmMemSizeIsByteExpanded
    {sizeLoc : Word} {sizeBytes offset : Nat} :
    (evmMemSizeIsByteExpanded sizeLoc sizeBytes offset).pcFree := by
  rw [evmMemSizeIsByteExpanded_unfold]
  exact pcFree_evmMemSizeIs


-- @@ L571-573 verbatim
instance (sizeLoc : Word) (sizeBytes offset : Nat) :
    Assertion.PCFree (evmMemSizeIsByteExpanded sizeLoc sizeBytes offset) :=
  ⟨pcFree_evmMemSizeIsByteExpanded⟩


-- @@ L575-579 verbatim
/-- MLOAD is a 32-byte byte-addressed access: expansion covers the byte just
    past the requested range for any starting byte offset. -/
theorem evmMemExpand_mload_ge_end (sizeBytes offset : Nat) :
    offset + 32 ≤ evmMemExpand sizeBytes offset 32 := by
  exact evmMemExpand_ge_access sizeBytes offset 32 (by decide)


-- @@ L581-586 verbatim
/-- MLOAD expansion covers the starting byte for any byte offset; no
    doubleword-alignment precondition is needed. -/
theorem evmMemExpand_mload_ge_start (sizeBytes offset : Nat) :
    offset ≤ evmMemExpand sizeBytes offset 32 := by
  have h_end := evmMemExpand_mload_ge_end sizeBytes offset
  omega


-- @@ L588-594 verbatim
/-- Every byte selected by MLOAD lies below the expanded high-water mark,
    independent of the offset's alignment. -/
theorem evmMemExpand_mload_byte_lt
    (sizeBytes offset byteIndex : Nat) (h_byte : byteIndex < 32) :
    offset + byteIndex < evmMemExpand sizeBytes offset 32 := by
  have h_end := evmMemExpand_mload_ge_end sizeBytes offset
  omega


-- @@ L596-600 verbatim
/-- MSTORE is also a 32-byte byte-addressed access: expansion covers the byte
    just past the requested range for any starting byte offset. -/
theorem evmMemExpand_mstore_ge_end (sizeBytes offset : Nat) :
    offset + 32 ≤ evmMemExpand sizeBytes offset 32 := by
  exact evmMemExpand_mload_ge_end sizeBytes offset


-- @@ L602-606 verbatim
/-- MSTORE expansion covers the starting byte for any byte offset; no
    doubleword-alignment precondition is needed. -/
theorem evmMemExpand_mstore_ge_start (sizeBytes offset : Nat) :
    offset ≤ evmMemExpand sizeBytes offset 32 := by
  exact evmMemExpand_mload_ge_start sizeBytes offset


-- @@ L608-613 verbatim
/-- Every byte selected by MSTORE lies below the expanded high-water mark,
    independent of the offset's alignment. -/
theorem evmMemExpand_mstore_byte_lt
    (sizeBytes offset byteIndex : Nat) (h_byte : byteIndex < 32) :
    offset + byteIndex < evmMemExpand sizeBytes offset 32 := by
  exact evmMemExpand_mload_byte_lt sizeBytes offset byteIndex h_byte


-- @@ L615-625 verbatim
theorem evmMemExpand_mload_byte_dword_end_le
    (sizeBytes offset byteIndex : Nat) (h_byte : byteIndex < 32) :
    ((offset + byteIndex) / 8 + 1) * 8 ≤
      evmMemExpand sizeBytes offset 32 := by
  unfold evmMemExpand
  rw [if_neg (by decide : (32 : Nat) ≠ 0)]
  have h_round : ((offset + byteIndex) / 8 + 1) * 8 ≤
      roundUpTo32 (offset + 32) := by
    unfold roundUpTo32
    omega
  exact Nat.le_trans h_round (Nat.le_max_right _ _)


-- @@ L627-631 verbatim
/-- MSTORE8 is a one-byte byte-addressed access: expansion covers the byte just
    past the requested range for any starting byte offset. -/
theorem evmMemExpand_mstore8_ge_end (sizeBytes offset : Nat) :
    offset + 1 ≤ evmMemExpand sizeBytes offset 1 := by
  exact evmMemExpand_ge_access sizeBytes offset 1 (by decide)


-- @@ L633-638 verbatim
/-- MSTORE8 expansion covers the starting byte for any byte offset; no
    doubleword-alignment precondition is needed. -/
theorem evmMemExpand_mstore8_ge_start (sizeBytes offset : Nat) :
    offset ≤ evmMemExpand sizeBytes offset 1 := by
  have h_end := evmMemExpand_mstore8_ge_end sizeBytes offset
  omega


-- @@ L640-646 verbatim
/-- Every byte selected by MSTORE8 lies below the expanded high-water mark,
    independent of the offset's alignment. -/
theorem evmMemExpand_mstore8_byte_lt
    (sizeBytes offset byteIndex : Nat) (h_byte : byteIndex < 1) :
    offset + byteIndex < evmMemExpand sizeBytes offset 1 := by
  have h_end := evmMemExpand_mstore8_ge_end sizeBytes offset
  omega


-- @@ L648-658 verbatim
theorem evmMemExpand_mstore8_byte_dword_end_le
    (sizeBytes offset byteIndex : Nat) (h_byte : byteIndex < 1) :
    ((offset + byteIndex) / 8 + 1) * 8 ≤
      evmMemExpand sizeBytes offset 1 := by
  unfold evmMemExpand
  rw [if_neg (by decide : (1 : Nat) ≠ 0)]
  have h_round : ((offset + byteIndex) / 8 + 1) * 8 ≤
      roundUpTo32 (offset + 1) := by
    unfold roundUpTo32
    omega
  exact Nat.le_trans h_round (Nat.le_max_right _ _)


-- @@ L660-667 verbatim
theorem evmMemExpand_mload_byte_dword_start_lt
    (sizeBytes offset byteIndex : Nat) (h_byte : byteIndex < 32) :
    ((offset + byteIndex) / 8) * 8 <
      evmMemExpand sizeBytes offset 32 := by
  have h_byte_lt := evmMemExpand_mload_byte_lt sizeBytes offset byteIndex h_byte
  have h_start_le : ((offset + byteIndex) / 8) * 8 ≤ offset + byteIndex := by
    exact Nat.div_mul_le_self (offset + byteIndex) 8
  exact Nat.lt_of_le_of_lt h_start_le h_byte_lt


-- @@ L669-676 verbatim
theorem evmMemExpand_mstore8_byte_dword_start_lt
    (sizeBytes offset byteIndex : Nat) (h_byte : byteIndex < 1) :
    ((offset + byteIndex) / 8) * 8 <
      evmMemExpand sizeBytes offset 1 := by
  have h_byte_lt := evmMemExpand_mstore8_byte_lt sizeBytes offset byteIndex h_byte
  have h_start_le : ((offset + byteIndex) / 8) * 8 ≤ offset + byteIndex := by
    exact Nat.div_mul_le_self (offset + byteIndex) 8
  exact Nat.lt_of_le_of_lt h_start_le h_byte_lt


-- @@ L678-686 verbatim
theorem evmMemExpand_mload_byte_dword_interval
    (sizeBytes offset byteIndex : Nat) (h_byte : byteIndex < 32) :
    ((offset + byteIndex) / 8) * 8 <
        evmMemExpand sizeBytes offset 32 ∧
      ((offset + byteIndex) / 8 + 1) * 8 ≤
        evmMemExpand sizeBytes offset 32 := by
  exact ⟨
    evmMemExpand_mload_byte_dword_start_lt sizeBytes offset byteIndex h_byte,
    evmMemExpand_mload_byte_dword_end_le sizeBytes offset byteIndex h_byte⟩


-- @@ L688-699 verbatim
theorem evmMemExpand_mload_byte_dword_byte_lt
    (sizeBytes offset byteIndex dwordByte : Nat)
    (h_byte : byteIndex < 32) (h_dword : dwordByte < 8) :
    ((offset + byteIndex) / 8) * 8 + dwordByte <
      evmMemExpand sizeBytes offset 32 := by
  have h_interval :=
    evmMemExpand_mload_byte_dword_interval sizeBytes offset byteIndex h_byte
  have h_lt_end :
      ((offset + byteIndex) / 8) * 8 + dwordByte <
        ((offset + byteIndex) / 8 + 1) * 8 := by
    omega
  exact Nat.lt_of_lt_of_le h_lt_end h_interval.2


-- @@ L701-705 verbatim
theorem evmMemExpand_mload_dword_interval
    (sizeBytes offset : Nat) :
    (offset / 8) * 8 < evmMemExpand sizeBytes offset 32 ∧
      (offset / 8 + 1) * 8 ≤ evmMemExpand sizeBytes offset 32 := by
  exact evmMemExpand_mload_byte_dword_interval sizeBytes offset 0 (by decide)


-- @@ L707-711 verbatim
theorem evmMemExpand_mload_last_dword_interval
    (sizeBytes offset : Nat) :
    ((offset + 31) / 8) * 8 < evmMemExpand sizeBytes offset 32 ∧
      ((offset + 31) / 8 + 1) * 8 ≤ evmMemExpand sizeBytes offset 32 := by
  exact evmMemExpand_mload_byte_dword_interval sizeBytes offset 31 (by decide)


-- @@ L713-719 verbatim
theorem evmMemExpand_mload_dword_span
    (sizeBytes offset : Nat) :
    (offset / 8) * 8 < evmMemExpand sizeBytes offset 32 ∧
      ((offset + 31) / 8 + 1) * 8 ≤ evmMemExpand sizeBytes offset 32 := by
  exact ⟨
    (evmMemExpand_mload_dword_interval sizeBytes offset).1,
    (evmMemExpand_mload_last_dword_interval sizeBytes offset).2⟩


-- @@ L721-725 verbatim
theorem evmMemExpand_mstore_byte_dword_end_le
    (sizeBytes offset byteIndex : Nat) (h_byte : byteIndex < 32) :
    ((offset + byteIndex) / 8 + 1) * 8 ≤
      evmMemExpand sizeBytes offset 32 := by
  exact evmMemExpand_mload_byte_dword_end_le sizeBytes offset byteIndex h_byte


-- @@ L727-731 verbatim
theorem evmMemExpand_mstore_byte_dword_start_lt
    (sizeBytes offset byteIndex : Nat) (h_byte : byteIndex < 32) :
    ((offset + byteIndex) / 8) * 8 <
      evmMemExpand sizeBytes offset 32 := by
  exact evmMemExpand_mload_byte_dword_start_lt sizeBytes offset byteIndex h_byte


-- @@ L733-739 verbatim
theorem evmMemExpand_mstore_byte_dword_interval
    (sizeBytes offset byteIndex : Nat) (h_byte : byteIndex < 32) :
    ((offset + byteIndex) / 8) * 8 <
        evmMemExpand sizeBytes offset 32 ∧
      ((offset + byteIndex) / 8 + 1) * 8 ≤
        evmMemExpand sizeBytes offset 32 := by
  exact evmMemExpand_mload_byte_dword_interval sizeBytes offset byteIndex h_byte


-- @@ L741-745 verbatim
theorem evmMemExpand_mstore_dword_interval
    (sizeBytes offset : Nat) :
    (offset / 8) * 8 < evmMemExpand sizeBytes offset 32 ∧
      (offset / 8 + 1) * 8 ≤ evmMemExpand sizeBytes offset 32 := by
  exact evmMemExpand_mload_dword_interval sizeBytes offset


-- @@ L747-751 verbatim
theorem evmMemExpand_mstore_last_dword_interval
    (sizeBytes offset : Nat) :
    ((offset + 31) / 8) * 8 < evmMemExpand sizeBytes offset 32 ∧
      ((offset + 31) / 8 + 1) * 8 ≤ evmMemExpand sizeBytes offset 32 := by
  exact evmMemExpand_mload_last_dword_interval sizeBytes offset


-- @@ L753-757 verbatim
theorem evmMemExpand_mstore_dword_span
    (sizeBytes offset : Nat) :
    (offset / 8) * 8 < evmMemExpand sizeBytes offset 32 ∧
      ((offset + 31) / 8 + 1) * 8 ≤ evmMemExpand sizeBytes offset 32 := by
  exact evmMemExpand_mload_dword_span sizeBytes offset


-- @@ L759-767 verbatim
theorem evmMemExpand_mstore8_byte_dword_interval
    (sizeBytes offset byteIndex : Nat) (h_byte : byteIndex < 1) :
    ((offset + byteIndex) / 8) * 8 <
        evmMemExpand sizeBytes offset 1 ∧
      ((offset + byteIndex) / 8 + 1) * 8 ≤
        evmMemExpand sizeBytes offset 1 := by
  exact ⟨
    evmMemExpand_mstore8_byte_dword_start_lt sizeBytes offset byteIndex h_byte,
    evmMemExpand_mstore8_byte_dword_end_le sizeBytes offset byteIndex h_byte⟩


-- @@ L769-780 verbatim
theorem evmMemExpand_mstore8_byte_dword_byte_lt
    (sizeBytes offset byteIndex dwordByte : Nat)
    (h_byte : byteIndex < 1) (h_dwordByte : dwordByte < 8) :
    ((offset + byteIndex) / 8) * 8 + dwordByte <
      evmMemExpand sizeBytes offset 1 := by
  have h_interval :=
    evmMemExpand_mstore8_byte_dword_interval sizeBytes offset byteIndex h_byte
  have h_lt_end :
      ((offset + byteIndex) / 8) * 8 + dwordByte <
        ((offset + byteIndex) / 8 + 1) * 8 := by
    omega
  exact Nat.lt_of_lt_of_le h_lt_end h_interval.2


-- @@ L782-787 verbatim
theorem evmMemExpand_mstore8_dword_byte_lt
    (sizeBytes offset dwordByte : Nat) (h_dwordByte : dwordByte < 8) :
    (offset / 8) * 8 + dwordByte <
      evmMemExpand sizeBytes offset 1 := by
  exact evmMemExpand_mstore8_byte_dword_byte_lt
    sizeBytes offset 0 dwordByte (by decide) h_dwordByte


-- @@ L789-793 verbatim
theorem evmMemExpand_mstore8_dword_interval
    (sizeBytes offset : Nat) :
    (offset / 8) * 8 < evmMemExpand sizeBytes offset 1 ∧
      (offset / 8 + 1) * 8 ≤ evmMemExpand sizeBytes offset 1 := by
  exact evmMemExpand_mstore8_byte_dword_interval sizeBytes offset 0 (by decide)


-- @@ L795-806 verbatim
theorem evmMemExpand_mstore_byte_dword_byte_lt
    (sizeBytes offset byteIndex dwordByte : Nat)
    (h_byte : byteIndex < 32) (h_dwordByte : dwordByte < 8) :
    ((offset + byteIndex) / 8) * 8 + dwordByte <
      evmMemExpand sizeBytes offset 32 := by
  have h_interval :=
    evmMemExpand_mstore_byte_dword_interval sizeBytes offset byteIndex h_byte
  have h_lt_end :
      ((offset + byteIndex) / 8) * 8 + dwordByte <
        ((offset + byteIndex) / 8 + 1) * 8 := by
    omega
  exact Nat.lt_of_lt_of_le h_lt_end h_interval.2


-- @@ L808-816 verbatim
theorem evmMemExpand_le_max_old_access_plus_31
    (sizeBytes offset length : Nat) :
    evmMemExpand sizeBytes offset length ≤ max sizeBytes (offset + length + 31) := by
  unfold evmMemExpand
  by_cases hlen : length = 0
  · simp [hlen]
  · rw [if_neg hlen]
    exact max_le (Nat.le_max_left _ _)
      (Nat.le_trans (roundUpTo32_le_add_31 (offset + length)) (Nat.le_max_right _ _))


-- @@ L818-827 verbatim
theorem evmMemExpand_le_of_old_le_and_access_le
    (sizeBytes offset length bound : Nat)
    (h_old : sizeBytes ≤ bound)
    (h_access : roundUpTo32 (offset + length) ≤ bound) :
    evmMemExpand sizeBytes offset length ≤ bound := by
  unfold evmMemExpand
  by_cases hlen : length = 0
  · simp [hlen, h_old]
  · rw [if_neg hlen]
    exact max_le h_old h_access


-- @@ L829-839 verbatim
/-- If the current high-water mark already covers the rounded access bound,
    the EVM memory size is unchanged. -/
theorem evmMemExpand_eq_old_of_access_le
    (sizeBytes offset length : Nat)
    (h : roundUpTo32 (offset + length) ≤ sizeBytes) :
    evmMemExpand sizeBytes offset length = sizeBytes := by
  unfold evmMemExpand
  by_cases hlen : length = 0
  · simp [hlen]
  · rw [if_neg hlen]
    exact max_eq_left h


-- @@ L841-849 verbatim
/-- If a nonzero access grows past the current high-water mark, the new EVM
    memory size is the rounded access bound. -/
theorem evmMemExpand_eq_access_of_old_le
    (sizeBytes offset length : Nat) (hlen : length ≠ 0)
    (h : sizeBytes ≤ roundUpTo32 (offset + length)) :
    evmMemExpand sizeBytes offset length = roundUpTo32 (offset + length) := by
  unfold evmMemExpand
  rw [if_neg hlen]
  exact max_eq_right h


-- @@ L851-863 verbatim
/-- The new high-water mark is always a multiple of 32 (when nonzero) — i.e.
    if the old size was 32-aligned, the new one is too. -/
theorem evmMemExpand_dvd_of_old_dvd (sizeBytes offset length : Nat)
    (h_old : 32 ∣ sizeBytes) :
    32 ∣ evmMemExpand sizeBytes offset length := by
  unfold evmMemExpand
  by_cases hlen : length = 0
  · simp [hlen]; exact h_old
  · simp [hlen]
    -- max of two multiples-of-32 is a multiple of 32
    rcases Nat.le_total sizeBytes (roundUpTo32 (offset + length)) with hle | hle
    · rw [Nat.max_eq_right hle]; exact roundUpTo32_dvd _
    · rw [Nat.max_eq_left hle]; exact h_old


-- @@ L865-872 verbatim
/-- Idempotence: re-expanding for the same access does not grow further. -/
theorem evmMemExpand_idempotent (sizeBytes offset length : Nat) :
    evmMemExpand (evmMemExpand sizeBytes offset length) offset length =
    evmMemExpand sizeBytes offset length := by
  unfold evmMemExpand
  by_cases hlen : length = 0
  · simp [hlen]
  · simp only [hlen, if_false, Nat.max_assoc, Nat.max_self]


-- @@ L874-874 verbatim
end EvmAsm.Evm64
