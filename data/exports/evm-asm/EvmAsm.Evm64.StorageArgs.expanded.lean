/-
  EvmAsm.Evm64.StorageArgs

  Pure stack-argument records and decoder for SLOAD and SSTORE (GH #110).
-/

module

public import EvmAsm.Evm64.EvmWord


-- @@ L11-11 verbatim
@[expose] public section


-- @@ L13-13 verbatim
namespace EvmAsm.Evm64


-- @@ L15-15 verbatim
namespace StorageArgs


-- @@ L17-20 verbatim
/-- SLOAD stack arguments: one storage slot key. -/
structure SLoad where
  slot : EvmWord
  deriving Repr


-- @@ L22-26 verbatim
/-- SSTORE stack arguments: storage slot key and new value. -/
structure SStore where
  slot : EvmWord
  value : EvmWord
  deriving Repr


-- @@ L28-31 verbatim
inductive Kind where
  | sload
  | sstore
  deriving DecidableEq, Repr


-- @@ L33-35 verbatim
/-- The storage opcode kinds covered by GH #110. -/
def allKinds : List Kind :=
  [.sload, .sstore]


-- @@ L37-40 verbatim
inductive Decoded where
  | sload (args : SLoad)
  | sstore (args : SStore)
  deriving Repr


-- @@ L42-44 verbatim
def argumentCount : Kind → Nat
  | .sload => 1
  | .sstore => 2


-- @@ L46-48 verbatim
def resultCount : Kind → Nat
  | .sload => 1
  | .sstore => 0


-- @@ L50-52 verbatim
def writesStorage : Kind → Bool
  | .sload => false
  | .sstore => true


-- @@ L54-56 verbatim
theorem allKinds_nodup :
    allKinds.Nodup := by
  decide


-- @@ L58-60 verbatim
theorem mem_allKinds (kind : Kind) :
    kind ∈ allKinds := by
  cases kind <;> decide


-- @@ L62-63 verbatim
theorem allKinds_argumentCounts :
    allKinds.map argumentCount = [1, 2] := rfl


-- @@ L65-66 verbatim
theorem allKinds_resultCounts :
    allKinds.map resultCount = [1, 0] := rfl


-- @@ L68-69 verbatim
theorem allKinds_writesStorage :
    allKinds.map writesStorage = [false, true] := rfl


-- @@ L71-72 verbatim
def mkSLoad (slot : EvmWord) : SLoad :=
  { slot := slot }


-- @@ L74-75 verbatim
def mkSStore (slot value : EvmWord) : SStore :=
  { slot := slot, value := value }


-- @@ L77-79 verbatim
def decodedKind : Decoded → Kind
  | .sload _ => .sload
  | .sstore _ => .sstore


-- @@ L81-90 verbatim
/--
Decode SLOAD/SSTORE stack arguments from top-of-stack order:
`slot` for SLOAD and `slot, value` for SSTORE.

Distinctive token: StorageArgs.decodeStorageStack? #110.
-/
def decodeStorageStack? : Kind → List EvmWord → Option Decoded
  | .sload, slot :: _ => some (.sload (mkSLoad slot))
  | .sstore, slot :: value :: _ => some (.sstore (mkSStore slot value))
  | _, _ => none


-- @@ L92-95 verbatim
theorem decodeStorageStack?_sload
    (slot : EvmWord) (rest : List EvmWord) :
    decodeStorageStack? .sload (slot :: rest) =
      some (.sload (mkSLoad slot)) := rfl


-- @@ L97-100 verbatim
theorem decodeStorageStack?_sstore
    (slot value : EvmWord) (rest : List EvmWord) :
    decodeStorageStack? .sstore (slot :: value :: rest) =
      some (.sstore (mkSStore slot value)) := rfl


-- @@ L102-120 verbatim
/--
SLOAD stack decoding succeeds exactly when the stack has a top slot word.

Distinctive token: StorageArgs.decodeStorageStack?_sload_eq_some_iff #110.
-/
theorem decodeStorageStack?_sload_eq_some_iff
    (stack : List EvmWord) (decoded : Decoded) :
    decodeStorageStack? .sload stack = some decoded ↔
      ∃ slot rest, stack = slot :: rest ∧ decoded = .sload (mkSLoad slot) := by
  constructor
  · intro h_decode
    cases stack with
    | nil => simp [decodeStorageStack?] at h_decode
    | cons slot rest =>
        simp [decodeStorageStack?] at h_decode
        cases h_decode
        exact ⟨slot, rest, rfl, rfl⟩
  · rintro ⟨slot, rest, rfl, rfl⟩
    rfl


-- @@ L122-139 verbatim
theorem decodeStorageStack?_sstore_eq_some_iff
    (stack : List EvmWord) (decoded : Decoded) :
    decodeStorageStack? .sstore stack = some decoded ↔
      ∃ slot value rest,
        stack = slot :: value :: rest ∧ decoded = .sstore (mkSStore slot value) := by
  constructor
  · intro h_decode
    cases stack with
    | nil => simp [decodeStorageStack?] at h_decode
    | cons slot tail =>
        cases tail with
        | nil => simp [decodeStorageStack?] at h_decode
        | cons value rest =>
            simp [decodeStorageStack?] at h_decode
            cases h_decode
            exact ⟨slot, value, rest, rfl, rfl⟩
  · rintro ⟨slot, value, rest, rfl, rfl⟩
    rfl


-- @@ L141-153 verbatim
theorem decodeStorageStack?_sload_eq_none_iff
    (stack : List EvmWord) :
    decodeStorageStack? .sload stack = none ↔ stack.length < argumentCount .sload := by
  constructor
  · intro h_decode
    cases stack with
    | nil => simp [argumentCount]
    | cons slot rest => simp [decodeStorageStack?] at h_decode
  · intro h_len
    cases stack with
    | nil => rfl
    | cons slot rest =>
        simp [argumentCount] at h_len


-- @@ L155-174 verbatim
theorem decodeStorageStack?_sstore_eq_none_iff
    (stack : List EvmWord) :
    decodeStorageStack? .sstore stack = none ↔ stack.length < argumentCount .sstore := by
  constructor
  · intro h_decode
    cases stack with
    | nil => simp [argumentCount]
    | cons slot tail =>
        cases tail with
        | nil => simp [argumentCount]
        | cons value rest => simp [decodeStorageStack?] at h_decode
  · intro h_len
    cases stack with
    | nil => rfl
    | cons slot tail =>
        cases tail with
        | nil => rfl
        | cons value rest =>
            simp [argumentCount] at h_len
            omega


-- @@ L176-188 verbatim
theorem decodeStorageStack?_eq_some_iff
    (kind : Kind) (stack : List EvmWord) (decoded : Decoded) :
    decodeStorageStack? kind stack = some decoded ↔
      match kind with
      | .sload =>
          ∃ slot rest,
            stack = slot :: rest ∧ decoded = .sload (mkSLoad slot)
      | .sstore =>
          ∃ slot value rest,
            stack = slot :: value :: rest ∧ decoded = .sstore (mkSStore slot value) := by
  cases kind with
  | sload => exact decodeStorageStack?_sload_eq_some_iff stack decoded
  | sstore => exact decodeStorageStack?_sstore_eq_some_iff stack decoded


-- @@ L190-197 verbatim
theorem decodeStorageStack?_sload_kind_of_some
    {stack : List EvmWord} {decoded : Decoded}
    (h_decode : decodeStorageStack? .sload stack = some decoded) :
    decodedKind decoded = .sload := by
  rw [decodeStorageStack?_sload_eq_some_iff] at h_decode
  rcases h_decode with ⟨slot, rest, h_stack, h_decoded⟩
  subst h_decoded
  rfl


-- @@ L199-206 verbatim
theorem decodeStorageStack?_sstore_kind_of_some
    {stack : List EvmWord} {decoded : Decoded}
    (h_decode : decodeStorageStack? .sstore stack = some decoded) :
    decodedKind decoded = .sstore := by
  rw [decodeStorageStack?_sstore_eq_some_iff] at h_decode
  rcases h_decode with ⟨slot, value, rest, h_stack, h_decoded⟩
  subst h_decoded
  rfl


-- @@ L208-214 verbatim
theorem decodeStorageStack?_kind_of_some
    {kind : Kind} {stack : List EvmWord} {decoded : Decoded}
    (h_decode : decodeStorageStack? kind stack = some decoded) :
    decodedKind decoded = kind := by
  cases kind with
  | sload => exact decodeStorageStack?_sload_kind_of_some h_decode
  | sstore => exact decodeStorageStack?_sstore_kind_of_some h_decode


-- @@ L216-220 verbatim
theorem decodeStorageStack?_argumentCount_of_some
    {kind : Kind} {stack : List EvmWord} {decoded : Decoded}
    (h_decode : decodeStorageStack? kind stack = some decoded) :
    argumentCount (decodedKind decoded) = argumentCount kind := by
  rw [decodeStorageStack?_kind_of_some h_decode]


-- @@ L222-226 verbatim
theorem decodeStorageStack?_resultCount_of_some
    {kind : Kind} {stack : List EvmWord} {decoded : Decoded}
    (h_decode : decodeStorageStack? kind stack = some decoded) :
    resultCount (decodedKind decoded) = resultCount kind := by
  rw [decodeStorageStack?_kind_of_some h_decode]


-- @@ L228-232 verbatim
theorem decodeStorageStack?_writesStorage_of_some
    {kind : Kind} {stack : List EvmWord} {decoded : Decoded}
    (h_decode : decodeStorageStack? kind stack = some decoded) :
    writesStorage (decodedKind decoded) = writesStorage kind := by
  rw [decodeStorageStack?_kind_of_some h_decode]


-- @@ L234-239 verbatim
theorem decodeStorageStack?_eq_none_iff
    (kind : Kind) (stack : List EvmWord) :
    decodeStorageStack? kind stack = none ↔ stack.length < argumentCount kind := by
  cases kind with
  | sload => exact decodeStorageStack?_sload_eq_none_iff stack
  | sstore => exact decodeStorageStack?_sstore_eq_none_iff stack


-- @@ L241-242 verbatim
theorem decodeStorageStack?_sload_none_of_empty :
    decodeStorageStack? .sload [] = none := rfl


-- @@ L244-245 verbatim
theorem decodeStorageStack?_sstore_none_of_empty :
    decodeStorageStack? .sstore [] = none := rfl


-- @@ L247-249 verbatim
theorem decodeStorageStack?_sstore_none_of_one
    (slot : EvmWord) :
    decodeStorageStack? .sstore [slot] = none := rfl


-- @@ L251-252 verbatim
theorem decodedKind_sload (slot : EvmWord) :
    decodedKind (.sload (mkSLoad slot)) = .sload := rfl


-- @@ L254-255 verbatim
theorem decodedKind_sstore (slot value : EvmWord) :
    decodedKind (.sstore (mkSStore slot value)) = .sstore := rfl


-- @@ L257-257 verbatim
theorem argumentCount_sload : argumentCount .sload = 1 := rfl


-- @@ L259-259 verbatim
theorem argumentCount_sstore : argumentCount .sstore = 2 := rfl


-- @@ L261-261 verbatim
theorem resultCount_sload : resultCount .sload = 1 := rfl


-- @@ L263-263 verbatim
theorem resultCount_sstore : resultCount .sstore = 0 := rfl


-- @@ L265-265 verbatim
theorem writesStorage_sload : writesStorage .sload = false := rfl


-- @@ L267-267 verbatim
theorem writesStorage_sstore : writesStorage .sstore = true := rfl


-- @@ L269-270 verbatim
theorem decoded_sload_slot (slot : EvmWord) :
    (mkSLoad slot).slot = slot := rfl


-- @@ L272-273 verbatim
theorem decoded_sstore_slot (slot value : EvmWord) :
    (mkSStore slot value).slot = slot := rfl


-- @@ L275-276 verbatim
theorem decoded_sstore_value (slot value : EvmWord) :
    (mkSStore slot value).value = value := rfl


-- @@ L278-278 verbatim
end StorageArgs


-- @@ L280-280 verbatim
end EvmAsm.Evm64
