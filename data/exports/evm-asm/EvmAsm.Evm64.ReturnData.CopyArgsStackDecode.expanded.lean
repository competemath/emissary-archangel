/-
  EvmAsm.Evm64.ReturnData.CopyArgsStackDecode

  Pure top-of-stack decoder for RETURNDATACOPY executable-spec bridges
  (GH #107 / GH #114).
-/

module

public import EvmAsm.Evm64.ReturnData.CopyArgs


-- @@ L12-12 verbatim
@[expose] public section


-- @@ L14-14 verbatim
namespace EvmAsm.Evm64


-- @@ L16-16 verbatim
namespace ReturnDataCopyArgsStackDecode


-- @@ L18-28 verbatim
/--
Decode RETURNDATACOPY stack arguments from the top-of-stack list order:
`destOffset, dataOffset, size`.

Distinctive token:
ReturnDataCopyArgsStackDecode.decodeReturnDataCopyStack? #107 #114.
-/
def decodeReturnDataCopyStack? : List EvmWord → Option ReturnDataCopyArgs.Args
  | destOffset :: dataOffset :: size :: _ =>
      some (ReturnDataCopyArgs.copyArgs destOffset dataOffset size)
  | _ => none


-- @@ L30-33 verbatim
theorem decodeReturnDataCopyStack?_cons
    (destOffset dataOffset size : EvmWord) (rest : List EvmWord) :
    decodeReturnDataCopyStack? (destOffset :: dataOffset :: size :: rest) =
      some (ReturnDataCopyArgs.copyArgs destOffset dataOffset size) := rfl


-- @@ L35-56 verbatim
theorem decodeReturnDataCopyStack?_eq_some_iff
    {stack : List EvmWord} {args : ReturnDataCopyArgs.Args} :
    decodeReturnDataCopyStack? stack = some args ↔
      ∃ destOffset dataOffset size rest,
        stack = destOffset :: dataOffset :: size :: rest ∧
          args = ReturnDataCopyArgs.copyArgs destOffset dataOffset size := by
  constructor
  · cases stack with
    | nil => simp [decodeReturnDataCopyStack?]
    | cons destOffset s1 =>
      cases s1 with
      | nil => simp [decodeReturnDataCopyStack?]
      | cons dataOffset s2 =>
        cases s2 with
        | nil => simp [decodeReturnDataCopyStack?]
        | cons size rest =>
          intro h
          injection h with h_args
          subst h_args
          exact ⟨destOffset, dataOffset, size, rest, rfl, rfl⟩
  · rintro ⟨destOffset, dataOffset, size, rest, rfl, rfl⟩
    rfl


-- @@ L58-73 verbatim
theorem decodeReturnDataCopyStack?_eq_none_iff (stack : List EvmWord) :
    decodeReturnDataCopyStack? stack = none ↔ stack.length < 3 := by
  constructor
  · intro h_decode
    rcases stack with _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩
    · simp
    · simp
    · simp
    · simp [decodeReturnDataCopyStack?] at h_decode
  · intro h_len
    rcases stack with _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩
    · rfl
    · rfl
    · rfl
    · simp at h_len
      omega


-- @@ L75-76 verbatim
theorem decodeReturnDataCopyStack?_none_of_empty :
    decodeReturnDataCopyStack? [] = none := rfl


-- @@ L78-80 verbatim
theorem decodeReturnDataCopyStack?_none_of_one
    (destOffset : EvmWord) :
    decodeReturnDataCopyStack? [destOffset] = none := rfl


-- @@ L82-84 verbatim
theorem decodeReturnDataCopyStack?_none_of_two
    (destOffset dataOffset : EvmWord) :
    decodeReturnDataCopyStack? [destOffset, dataOffset] = none := rfl


-- @@ L86-90 verbatim
theorem decodeReturnDataCopyStack?_destOffset
    (destOffset dataOffset size : EvmWord) (rest : List EvmWord) :
    Option.map (fun args => args.destOffset)
      (decodeReturnDataCopyStack? (destOffset :: dataOffset :: size :: rest)) =
      some destOffset := rfl


-- @@ L92-96 verbatim
theorem decodeReturnDataCopyStack?_dataOffset
    (destOffset dataOffset size : EvmWord) (rest : List EvmWord) :
    Option.map (fun args => args.dataOffset)
      (decodeReturnDataCopyStack? (destOffset :: dataOffset :: size :: rest)) =
      some dataOffset := rfl


-- @@ L98-102 verbatim
theorem decodeReturnDataCopyStack?_size
    (destOffset dataOffset size : EvmWord) (rest : List EvmWord) :
    Option.map (fun args => args.size)
      (decodeReturnDataCopyStack? (destOffset :: dataOffset :: size :: rest)) =
      some size := rfl


-- @@ L104-104 verbatim
end ReturnDataCopyArgsStackDecode


-- @@ L106-106 verbatim
end EvmAsm.Evm64
