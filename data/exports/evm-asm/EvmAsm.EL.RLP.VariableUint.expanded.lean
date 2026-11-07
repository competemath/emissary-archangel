/-
  EvmAsm.EL.RLP.VariableUint

  The unbounded, canonical scalar surface needed by the execution-specs
  ``Uint`` fields.  This is deliberately a pure representation only: no
  emitted routine is routed through it in this step.

  An `RlpUint` stores the prefix-stripped content bytes of one RLP scalar and
  the canonicality fact that `_deserialize_to_uint` requires.  The content is
  a list rather than a fixed 32-byte word, so its value is not silently
  truncated when it is wider than the EVM word used by the existing guest.
  The optional `toU256?` projection is the explicit compatibility boundary for
  callers that have separately established a 32-byte width.
-/

module

public import EvmAsm.EL.RLP.Properties
public import Mathlib.Tactic.NormNum


-- @@ L21-21 verbatim
@[expose] public section


-- @@ L23-23 verbatim
namespace EvmAsm.EL.RLP


-- @@ L25-25 verbatim
/-! ## Canonical variable-width scalar content -/


-- @@ L27-34 verbatim
/-- Canonicality of prefix-stripped RLP scalar content.

    The empty content is the canonical encoding of zero.  A nonempty scalar
    must have a nonzero most-significant byte.  RLP's singleton-prefix rule is
    checked by the surrounding RLP item decoder; this predicate is the
    `_deserialize_to_uint` check on the decoded content itself. -/
def isCanonicalUintContent (content : List Byte) : Prop :=
  content.headD 1 ≠ 0


-- @@ L36-43 verbatim
/-- A decoded RLP scalar with arbitrary-width, canonical content.

    There is intentionally no `content.length ≤ 32` field here.  The pinned
    execution-specs `Uint` type is unbounded; width checks belong only to an
    explicit projection such as `toU256?`. -/
structure RlpUint where
  content : List Byte
  canonical : isCanonicalUintContent content


-- @@ L45-45 verbatim
namespace RlpUint


-- @@ L47-48 verbatim
/-- The arbitrary-precision value represented by the scalar content. -/
def value (u : RlpUint) : Nat := Nat.fromBytesBE u.content


-- @@ L50-51 verbatim
/-- The number of bytes in the variable-width representation. -/
def width (u : RlpUint) : Nat := u.content.length


-- @@ L53-54 verbatim
/-- Whether this scalar can be represented by the existing 256-bit word. -/
def fitsU256 (u : RlpUint) : Prop := u.width ≤ 32


-- @@ L56-61 verbatim
/-- Construct a validated scalar from already-decoded content. -/
def ofContent? (content : List Byte) : Option RlpUint :=
  if h : content.headD 1 ≠ 0 then
    some ⟨content, h⟩
  else
    none


-- @@ L63-71 verbatim
/-- The pure variable-width decoder accepts exactly canonical content. -/
theorem ofContent?_eq_some (content : List Byte)
    (h : isCanonicalUintContent content) :
    ofContent? content = some ⟨content, h⟩ := by
  change content.headD 1 ≠ 0 at h
  unfold ofContent?
  split
  · rfl
  · contradiction


-- @@ L73-76 verbatim
/-- A canonical scalar's content is recovered by re-encoding its value. -/
theorem content_eq_toBytesBE (u : RlpUint) :
    Nat.toBytesBE u.value = u.content := by
  exact Nat.toBytesBE_fromBytesBE_of_canonical u.content u.canonical


-- @@ L78-86 verbatim
/-- Constructing from a natural uses its minimal big-endian representation. -/
def ofNat (n : Nat) : RlpUint :=
  ⟨Nat.toBytesBE n, by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [Nat.toBytesBE_zero]
      simp [isCanonicalUintContent]
    · obtain ⟨b, tl, hbytes, hb⟩ := Nat.toBytesBE_eq_cons_of_pos n hn
      rw [hbytes]
      simpa [isCanonicalUintContent] using hb⟩


-- @@ L88-89 verbatim
@[simp] theorem ofNat_content (n : Nat) : (ofNat n).content = Nat.toBytesBE n :=
  rfl


-- @@ L91-92 verbatim
@[simp] theorem ofNat_value (n : Nat) : (ofNat n).value = n := by
  simp [ofNat, value, Nat.fromBytesBE_toBytesBE]


-- @@ L94-100 verbatim
/-- Decoding canonical content agrees with the unvalidated byte conversion. -/
theorem ofContent?_value (content : List Byte)
    (h : isCanonicalUintContent content) :
    (ofContent? content).map value = some (Nat.fromBytesBE content) := by
  have hs := ofContent?_eq_some content h
  rw [hs]
  rfl


-- @@ L102-105 verbatim
/-- A `k`-byte content value is strictly below `256^k`. -/
theorem value_lt_pow_width (u : RlpUint) :
    u.value < 256 ^ u.width := by
  exact Nat.fromBytesBE_lt u.content


-- @@ L107-117 verbatim
/-- A scalar with at most 32 content bytes is strictly below `2^256`. -/
theorem value_lt_u256_modulus (u : RlpUint) (h : u.fitsU256) :
    u.value < 2 ^ 256 := by
  change Nat.fromBytesBE u.content < 2 ^ 256
  have hlen : u.content.length ≤ 32 := by
    simpa [fitsU256, width] using h
  calc
    Nat.fromBytesBE u.content < 256 ^ u.content.length :=
      Nat.fromBytesBE_lt u.content
    _ ≤ 256 ^ 32 := Nat.pow_le_pow_right (by decide) hlen
    _ = 2 ^ 256 := by norm_num


-- @@ L119-119 verbatim
/-! ## Explicit compatibility projection -/


-- @@ L121-128 verbatim
/-- The existing fixed-width word projection, guarded by an explicit width
    proof.  `BitVec.ofNat` is safe here because `value_lt_u256_modulus` proves
    that no truncation occurs. -/
def toU256 (u : RlpUint) (h : u.fitsU256) : BitVec 256 :=
  if h' : u.width ≤ 32 then
    BitVec.ofNat 256 u.value
  else
    False.elim (h' (by simpa [fitsU256] using h))


-- @@ L130-134 verbatim
@[simp] theorem toU256_toNat (u : RlpUint) (h : u.fitsU256) :
    (u.toU256 h).toNat = u.value := by
  have hlen : u.width ≤ 32 := by simpa [fitsU256] using h
  rw [toU256, dif_pos hlen, BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (value_lt_u256_modulus u h)


-- @@ L136-140 verbatim
/-- An option-valued projection for callers that have not proved the width at
    the call site.  The `none` case is a representation failure, not a
    variable-width decode failure. -/
def toU256? (u : RlpUint) : Option (BitVec 256) :=
  if h : u.width ≤ 32 then some (u.toU256 h) else none


-- @@ L142-145 verbatim
theorem toU256?_eq_some (u : RlpUint) (h : u.fitsU256) :
    u.toU256? = some (BitVec.ofNat 256 u.value) := by
  have hlen : u.width ≤ 32 := by simpa [fitsU256] using h
  simp [toU256?, hlen, toU256]


-- @@ L147-150 verbatim
theorem toU256?_none (u : RlpUint) (h : ¬ u.fitsU256) :
    u.toU256? = none := by
  have hlen : ¬ u.width ≤ 32 := by simpa [fitsU256] using h
  simp [toU256?, hlen]


-- @@ L152-156 verbatim
theorem toU256?_value (u : RlpUint) (h : u.fitsU256) :
    ∃ w, u.toU256? = some w ∧ w.toNat = u.value := by
  have hlen : u.width ≤ 32 := by simpa [fitsU256] using h
  refine ⟨u.toU256 h, ?_, toU256_toNat u h⟩
  simp [toU256?, hlen]


-- @@ L158-158 verbatim
/-! ## Concrete checks for the boundary and canonicality -/


-- @@ L160-161 verbatim
example : (ofNat 0).content = [] := by
  simp [ofNat, Nat.toBytesBE_zero]

-- @@ L162-163 verbatim
example : ofContent? [0x00] = none := by
  simp [ofContent?]

-- @@ L164-165 verbatim
example : (ofContent? [0x01, 0x00]).map value = some 256 := by
  simp [ofContent?, value, Nat.fromBytesBE]


-- @@ L167-167 verbatim
end RlpUint


-- @@ L169-169 verbatim
end EvmAsm.EL.RLP
