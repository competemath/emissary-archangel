/-
  EvmAsm.Evm64.Calldata.CopyArgsStackDecode

  Pure top-of-stack decoder for CALLDATACOPY executable-spec bridges
  (GH #104 / GH #107).
-/

module

public import EvmAsm.Evm64.Calldata.CopyArgs


-- @@ L12-12 verbatim
@[expose] public section


-- @@ L14-14 verbatim
namespace EvmAsm.Evm64


-- @@ L16-16 verbatim
namespace CallDataCopyArgsStackDecode


-- @@ L18-28 verbatim
/--
Decode CALLDATACOPY stack arguments from the top-of-stack list order:
`destOffset, dataOffset, size`.

Distinctive token:
CallDataCopyArgsStackDecode.decodeCallDataCopyStack? #104 #107.
-/
def decodeCallDataCopyStack? : List EvmWord → Option CallDataCopyArgs.Args
  | destOffset :: dataOffset :: size :: _ =>
      some (CallDataCopyArgs.copyArgs destOffset dataOffset size)
  | _ => none


-- @@ L30-33 verbatim
theorem decodeCallDataCopyStack?_cons
    (destOffset dataOffset size : EvmWord) (rest : List EvmWord) :
    decodeCallDataCopyStack? (destOffset :: dataOffset :: size :: rest) =
      some (CallDataCopyArgs.copyArgs destOffset dataOffset size) := rfl


-- @@ L35-56 verbatim
theorem decodeCallDataCopyStack?_eq_some_iff
    {stack : List EvmWord} {args : CallDataCopyArgs.Args} :
    decodeCallDataCopyStack? stack = some args ↔
      ∃ destOffset dataOffset size rest,
        stack = destOffset :: dataOffset :: size :: rest ∧
          args = CallDataCopyArgs.copyArgs destOffset dataOffset size := by
  constructor
  · cases stack with
    | nil => simp [decodeCallDataCopyStack?]
    | cons destOffset s1 =>
      cases s1 with
      | nil => simp [decodeCallDataCopyStack?]
      | cons dataOffset s2 =>
        cases s2 with
        | nil => simp [decodeCallDataCopyStack?]
        | cons size rest =>
          intro h
          injection h with h_args
          subst h_args
          exact ⟨destOffset, dataOffset, size, rest, rfl, rfl⟩
  · rintro ⟨destOffset, dataOffset, size, rest, rfl, rfl⟩
    rfl


-- @@ L58-68 verbatim
theorem decodeCallDataCopyStack?_destinationRange_of_some
    {stack : List EvmWord} {args : CallDataCopyArgs.Args}
    (h_decode : decodeCallDataCopyStack? stack = some args) :
    ∃ destOffset dataOffset size rest,
      stack = destOffset :: dataOffset :: size :: rest ∧
        CallDataCopyArgs.destinationRange args =
          { offset := destOffset, size := size } := by
  rw [decodeCallDataCopyStack?_eq_some_iff] at h_decode
  rcases h_decode with ⟨destOffset, dataOffset, size, rest, h_stack, h_args⟩
  subst h_args
  exact ⟨destOffset, dataOffset, size, rest, h_stack, rfl⟩


-- @@ L70-79 verbatim
theorem decodeCallDataCopyStack?_destinationOffsetNat_of_some
    {stack : List EvmWord} {args : CallDataCopyArgs.Args}
    (h_decode : decodeCallDataCopyStack? stack = some args) :
    ∃ destOffset dataOffset size rest,
      stack = destOffset :: dataOffset :: size :: rest ∧
        CallDataCopyArgs.destinationOffsetNat args = destOffset.toNat := by
  rw [decodeCallDataCopyStack?_eq_some_iff] at h_decode
  rcases h_decode with ⟨destOffset, dataOffset, size, rest, h_stack, h_args⟩
  subst h_args
  exact ⟨destOffset, dataOffset, size, rest, h_stack, rfl⟩


-- @@ L81-90 verbatim
theorem decodeCallDataCopyStack?_sourceOffsetNat_of_some
    {stack : List EvmWord} {args : CallDataCopyArgs.Args}
    (h_decode : decodeCallDataCopyStack? stack = some args) :
    ∃ destOffset dataOffset size rest,
      stack = destOffset :: dataOffset :: size :: rest ∧
        CallDataCopyArgs.sourceOffsetNat args = dataOffset.toNat := by
  rw [decodeCallDataCopyStack?_eq_some_iff] at h_decode
  rcases h_decode with ⟨destOffset, dataOffset, size, rest, h_stack, h_args⟩
  subst h_args
  exact ⟨destOffset, dataOffset, size, rest, h_stack, rfl⟩


-- @@ L92-101 verbatim
theorem decodeCallDataCopyStack?_sizeNat_of_some
    {stack : List EvmWord} {args : CallDataCopyArgs.Args}
    (h_decode : decodeCallDataCopyStack? stack = some args) :
    ∃ destOffset dataOffset size rest,
      stack = destOffset :: dataOffset :: size :: rest ∧
        CallDataCopyArgs.sizeNat args = size.toNat := by
  rw [decodeCallDataCopyStack?_eq_some_iff] at h_decode
  rcases h_decode with ⟨destOffset, dataOffset, size, rest, h_stack, h_args⟩
  subst h_args
  exact ⟨destOffset, dataOffset, size, rest, h_stack, rfl⟩


-- @@ L103-121 verbatim
/--
CALLDATACOPY stack decoding fails exactly when fewer than three stack words are
available.

Distinctive token:
CallDataCopyArgsStackDecode.decodeCallDataCopyStack?_eq_none_iff #104 #107.
-/
theorem decodeCallDataCopyStack?_eq_none_iff
    (stack : List EvmWord) :
    decodeCallDataCopyStack? stack = none ↔ stack.length < 3 := by
  cases stack with
  | nil => simp [decodeCallDataCopyStack?]
  | cons destOffset s1 =>
      cases s1 with
      | nil => simp [decodeCallDataCopyStack?]
      | cons dataOffset s2 =>
          cases s2 with
          | nil => simp [decodeCallDataCopyStack?]
          | cons size rest => simp [decodeCallDataCopyStack?]


-- @@ L123-124 verbatim
theorem decodeCallDataCopyStack?_none_of_empty :
    decodeCallDataCopyStack? [] = none := rfl


-- @@ L126-128 verbatim
theorem decodeCallDataCopyStack?_none_of_one
    (destOffset : EvmWord) :
    decodeCallDataCopyStack? [destOffset] = none := rfl


-- @@ L130-132 verbatim
theorem decodeCallDataCopyStack?_none_of_two
    (destOffset dataOffset : EvmWord) :
    decodeCallDataCopyStack? [destOffset, dataOffset] = none := rfl


-- @@ L134-138 verbatim
theorem decodeCallDataCopyStack?_destOffset
    (destOffset dataOffset size : EvmWord) (rest : List EvmWord) :
    Option.map (fun args => args.destOffset)
      (decodeCallDataCopyStack? (destOffset :: dataOffset :: size :: rest)) =
      some destOffset := rfl


-- @@ L140-144 verbatim
theorem decodeCallDataCopyStack?_dataOffset
    (destOffset dataOffset size : EvmWord) (rest : List EvmWord) :
    Option.map (fun args => args.dataOffset)
      (decodeCallDataCopyStack? (destOffset :: dataOffset :: size :: rest)) =
      some dataOffset := rfl


-- @@ L146-150 verbatim
theorem decodeCallDataCopyStack?_size
    (destOffset dataOffset size : EvmWord) (rest : List EvmWord) :
    Option.map (fun args => args.size)
      (decodeCallDataCopyStack? (destOffset :: dataOffset :: size :: rest)) =
      some size := rfl


-- @@ L152-152 verbatim
end CallDataCopyArgsStackDecode


-- @@ L154-154 verbatim
end EvmAsm.Evm64
