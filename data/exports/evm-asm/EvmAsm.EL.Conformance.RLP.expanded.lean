/-
  EvmAsm.EL.Conformance.RLP

  Compact Lean-side conformance vectors for the executable RLP decoder
  (GH #125 / GH #120).
-/

module

public import EvmAsm.EL.Conformance
public import EvmAsm.EL.RLP.Decode


-- @@ L13-13 verbatim
@[expose] public section


-- @@ L15-15 verbatim
namespace EvmAsm.EL

-- @@ L16-16 verbatim
namespace Conformance

-- @@ L17-17 verbatim
namespace RLP


-- @@ L19-19 verbatim
abbrev Byte := EvmAsm.EL.RLP.Byte

-- @@ L20-20 verbatim
abbrev RLPItem := EvmAsm.EL.RLP.RLPItem


-- @@ L22-25 verbatim
/-- Input shape for an RLP decode executable-helper conformance vector. -/
structure DecodeInput where
  bytes : List Byte
  deriving Repr


-- @@ L27-31 verbatim
/-- Decode exactly one RLP item and reject leftover bytes. -/
def runDecodeFully (input : DecodeInput) : Option RLPItem :=
  match EvmAsm.EL.RLP.decode input.bytes with
  | some (item, []) => some item
  | _ => none


-- @@ L33-38 verbatim
/-- Nested list decode vector, covering recursive item decoding.
    Distinctive token: rlpNestedListDecodeVector. -/
def rlpNestedListDecodeVector : TestVector DecodeInput RLPItem :=
  { id := "rlp-nested-list-decode"
    input := { bytes := [(0xc3 : Byte), 0x01, 0x02, 0x03] }
    expected := .value (.list [.bytes [0x01], .bytes [0x02], .bytes [0x03]]) }


-- @@ L40-45 verbatim
/-- Non-canonical singleton byte string must be rejected; `0x01` should be
    encoded directly as the single byte `0x01`, not as `0x81 0x01`. -/
def rlpNoncanonicalSingletonVector : TestVector DecodeInput RLPItem :=
  { id := "rlp-noncanonical-singleton"
    input := { bytes := [(0x81 : Byte), 0x01] }
    expected := .error "noncanonical-singleton" }


-- @@ L47-52 verbatim
/-- Empty-list decoding covers the canonical `0xc0` list prefix.
    Distinctive token: RLP.rlpEmptyListDecodeVector #120 #125. -/
def rlpEmptyListDecodeVector : TestVector DecodeInput RLPItem :=
  { id := "rlp-empty-list-decode"
    input := { bytes := [(0xc0 : Byte)] }
    expected := .value (.list []) }


-- @@ L54-59 verbatim
/-- Long-form byte string at the first canonical long-byte boundary.
    Distinctive token: RLP.rlpLongBytesDecodeVector #120 #125. -/
def rlpLongBytesDecodeVector : TestVector DecodeInput RLPItem :=
  { id := "rlp-long-bytes-decode"
    input := { bytes := (0xb8 : Byte) :: 0x38 :: List.replicate 56 (0x7f : Byte) }
    expected := .value (.bytes (List.replicate 56 (0x7f : Byte))) }


-- @@ L61-63 verbatim
theorem runDecodeFully_nestedList :
    runDecodeFully { bytes := [(0xc3 : Byte), 0x01, 0x02, 0x03] } =
      some (.list [.bytes [0x01], .bytes [0x02], .bytes [0x03]]) := rfl


-- @@ L65-66 verbatim
theorem runDecodeFully_reject_noncanonical_singleton :
    runDecodeFully { bytes := [(0x81 : Byte), 0x01] } = none := rfl


-- @@ L68-69 verbatim
theorem runDecodeFully_emptyList :
    runDecodeFully { bytes := [(0xc0 : Byte)] } = some (.list []) := rfl


-- @@ L71-75 verbatim
theorem runDecodeFully_longBytes :
    runDecodeFully
      { bytes := (0xb8 : Byte) :: 0x38 :: List.replicate 56 (0x7f : Byte) } =
      some (.bytes (List.replicate 56 (0x7f : Byte))) := by
  rfl


-- @@ L77-83 verbatim
theorem rlpNestedListDecodeVector_passed :
    checkVector? runDecodeFully rlpNestedListDecodeVector = .passed :=
  checkVector?_some_passed runDecodeFully
    "rlp-nested-list-decode"
    { bytes := [(0xc3 : Byte), 0x01, 0x02, 0x03] }
    (.list [.bytes [0x01], .bytes [0x02], .bytes [0x03]])
    runDecodeFully_nestedList


-- @@ L85-92 verbatim
theorem rlpNoncanonicalSingletonVector_errored :
    checkVector? runDecodeFully rlpNoncanonicalSingletonVector =
      .errored "rlp-noncanonical-singleton" "noncanonical-singleton" :=
  checkVector?_none_error runDecodeFully
    "rlp-noncanonical-singleton"
    "noncanonical-singleton"
    { bytes := [(0x81 : Byte), 0x01] }
    runDecodeFully_reject_noncanonical_singleton


-- @@ L94-100 verbatim
theorem rlpEmptyListDecodeVector_passed :
    checkVector? runDecodeFully rlpEmptyListDecodeVector = .passed :=
  checkVector?_some_passed runDecodeFully
    "rlp-empty-list-decode"
    { bytes := [(0xc0 : Byte)] }
    (.list [])
    runDecodeFully_emptyList


-- @@ L102-108 verbatim
theorem rlpLongBytesDecodeVector_passed :
    checkVector? runDecodeFully rlpLongBytesDecodeVector = .passed :=
  checkVector?_some_passed runDecodeFully
    "rlp-long-bytes-decode"
    { bytes := (0xb8 : Byte) :: 0x38 :: List.replicate 56 (0x7f : Byte) }
    (.bytes (List.replicate 56 (0x7f : Byte)))
    runDecodeFully_longBytes


-- @@ L110-117 verbatim
/-- Vector IDs for RLP executable-decoding conformance coverage.
    Distinctive token: rlpConformanceVectorIds #125 #120. -/
def rlpConformanceVectorIds : List String :=
  [ rlpNestedListDecodeVector.id
  , rlpNoncanonicalSingletonVector.id
  , rlpEmptyListDecodeVector.id
  , rlpLongBytesDecodeVector.id
  ]


-- @@ L119-125 verbatim
theorem rlpConformanceVectorIds_eq :
    rlpConformanceVectorIds =
      [ "rlp-nested-list-decode"
      , "rlp-noncanonical-singleton"
      , "rlp-empty-list-decode"
      , "rlp-long-bytes-decode"
      ] := rfl


-- @@ L127-128 verbatim
theorem rlpConformanceVectorIds_length :
    rlpConformanceVectorIds.length = 4 := rfl


-- @@ L130-132 verbatim
theorem rlpConformanceVectorIds_nodup :
    rlpConformanceVectorIds.Nodup := by
  decide


-- @@ L134-141 verbatim
/-- Compact checked-vector batch for RLP executable decoding.
    Distinctive token: RLP.rlpConformanceVectors #125 #120. -/
def rlpConformanceVectors : List CheckResult :=
  [ checkVector? runDecodeFully rlpNestedListDecodeVector
  , checkVector? runDecodeFully rlpNoncanonicalSingletonVector
  , checkVector? runDecodeFully rlpEmptyListDecodeVector
  , checkVector? runDecodeFully rlpLongBytesDecodeVector
  ]


-- @@ L143-152 verbatim
theorem rlpConformanceVectors_passed :
    rlpConformanceVectors =
      [ .passed
      , .errored "rlp-noncanonical-singleton" "noncanonical-singleton"
      , .passed
      , .passed
      ] := by
  simp [rlpConformanceVectors, rlpNestedListDecodeVector_passed,
    rlpNoncanonicalSingletonVector_errored, rlpEmptyListDecodeVector_passed,
    rlpLongBytesDecodeVector_passed]


-- @@ L154-154 verbatim
end RLP

-- @@ L155-155 verbatim
end Conformance

-- @@ L156-156 verbatim
end EvmAsm.EL
