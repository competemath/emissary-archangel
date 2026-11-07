/-
  EvmAsm.EL.RLP.FullDecode

  Top-level wrapper for consumers that require an RLP decode to consume the
  whole input.
-/

module

public import EvmAsm.EL.RLP.Decode


-- @@ L12-12 verbatim
@[expose] public section


-- @@ L14-14 verbatim
namespace EvmAsm.EL.RLP


-- @@ L16-21 verbatim
/-- Decode one complete RLP item, rejecting successful prefix decodes that
leave trailing input. -/
def decodeFully (bs : List Byte) : Option RLPItem :=
  match decode bs with
  | some (item, []) => some item
  | _ => none


-- @@ L23-35 verbatim
/-- Distinctive token: FullDecode.decodeFully_eq_some_iff #120. -/
theorem decodeFully_eq_some_iff (bs : List Byte) (item : RLPItem) :
    decodeFully bs = some item ↔ decode bs = some (item, []) := by
  unfold decodeFully
  cases h_decode : decode bs with
  | none =>
      simp
  | some decoded =>
      cases decoded with
      | mk item' leftover =>
          cases leftover with
          | nil => simp
          | cons b rest => simp


-- @@ L37-62 verbatim
/--
Complete-decode success as an existential raw-decoder fact.

Distinctive token: FullDecode.decodeFully_ne_none_iff_exists_decode_empty #120.
-/
theorem decodeFully_ne_none_iff_exists_decode_empty (bs : List Byte) :
    decodeFully bs ≠ none ↔ ∃ item, decode bs = some (item, []) := by
  constructor
  · unfold decodeFully
    cases h_decode : decode bs with
    | none =>
        simp
    | some decoded =>
        cases decoded with
        | mk item leftover =>
            cases leftover with
            | nil =>
                intro _
                exact ⟨item, by simp [h_decode.symm]⟩
            | cons b rest =>
                simp
  · rintro ⟨item, h_decode⟩ h_none
    have h_some : decodeFully bs = some item :=
      (decodeFully_eq_some_iff bs item).2 h_decode
    rw [h_some] at h_none
    contradiction


-- @@ L64-67 verbatim
theorem decodeFully_eq_none_of_decode_none
    {bs : List Byte} (h_decode : decode bs = none) :
    decodeFully bs = none := by
  simp [decodeFully, h_decode]


-- @@ L69-77 verbatim
theorem decodeFully_eq_none_of_decode_leftover
    {bs leftover : List Byte} {item : RLPItem}
    (h_decode : decode bs = some (item, leftover))
    (h_leftover : leftover ≠ []) :
    decodeFully bs = none := by
  unfold decodeFully
  cases leftover with
  | nil => contradiction
  | cons b rest => simp [h_decode]


-- @@ L79-102 verbatim
/--
Complete-decode failure is exactly either decoder failure or successful
prefix decode with trailing bytes left over.

Distinctive token: FullDecode.decodeFully_eq_none_iff #120.
-/
theorem decodeFully_eq_none_iff (bs : List Byte) :
    decodeFully bs = none ↔
      decode bs = none ∨
        ∃ item leftover, decode bs = some (item, leftover) ∧ leftover ≠ [] := by
  unfold decodeFully
  cases h_decode : decode bs with
  | none => simp
  | some decoded =>
      cases decoded with
      | mk item leftover =>
          cases leftover with
          | nil => simp
          | cons b rest =>
              constructor
              · intro _
                exact Or.inr ⟨item, b :: rest, rfl, by simp⟩
              · intro _
                rfl


-- @@ L104-108 verbatim
theorem decodeFully_eq_some_of_decode
    {bs : List Byte} {item : RLPItem}
    (h_decode : decode bs = some (item, [])) :
    decodeFully bs = some item := by
  exact (decodeFully_eq_some_iff bs item).2 h_decode


-- @@ L110-114 verbatim
theorem decodeFully_encode_of_decode_encode
    {item : RLPItem}
    (h_roundtrip : decode (encode item) = some (item, [])) :
    decodeFully (encode item) = some item := by
  exact decodeFully_eq_some_of_decode h_roundtrip


-- @@ L116-116 verbatim
end EvmAsm.EL.RLP
