/-
  EvmAsm.Evm64.Code.CopyArgsStackDecode

  Pure top-of-stack decoder for CODECOPY executable-spec bridges
  (GH #107 / GH #118).
-/

module

public import EvmAsm.Evm64.Code.CopyArgs


-- @@ L12-12 verbatim
@[expose] public section


-- @@ L14-14 verbatim
namespace EvmAsm.Evm64


-- @@ L16-16 verbatim
namespace CodeCopyArgsStackDecode


-- @@ L18-27 verbatim
/--
Decode CODECOPY stack arguments from the top-of-stack list order:
`destOffset, codeOffset, size`.

Distinctive token: CodeCopyArgsStackDecode.decodeCodeCopyStack? #107 #118.
-/
def decodeCodeCopyStack? : List EvmWord → Option CodeCopyArgs.Args
  | destOffset :: codeOffset :: size :: _ =>
      some (CodeCopyArgs.copyArgs destOffset codeOffset size)
  | _ => none


-- @@ L29-32 verbatim
theorem decodeCodeCopyStack?_cons
    (destOffset codeOffset size : EvmWord) (rest : List EvmWord) :
    decodeCodeCopyStack? (destOffset :: codeOffset :: size :: rest) =
      some (CodeCopyArgs.copyArgs destOffset codeOffset size) := rfl


-- @@ L34-55 verbatim
theorem decodeCodeCopyStack?_eq_some_iff
    {stack : List EvmWord} {args : CodeCopyArgs.Args} :
    decodeCodeCopyStack? stack = some args ↔
      ∃ destOffset codeOffset size rest,
        stack = destOffset :: codeOffset :: size :: rest ∧
          args = CodeCopyArgs.copyArgs destOffset codeOffset size := by
  constructor
  · cases stack with
    | nil => simp [decodeCodeCopyStack?]
    | cons destOffset s1 =>
      cases s1 with
      | nil => simp [decodeCodeCopyStack?]
      | cons codeOffset s2 =>
        cases s2 with
        | nil => simp [decodeCodeCopyStack?]
        | cons size rest =>
          intro h
          injection h with h_args
          subst h_args
          exact ⟨destOffset, codeOffset, size, rest, rfl, rfl⟩
  · rintro ⟨destOffset, codeOffset, size, rest, rfl, rfl⟩
    rfl


-- @@ L57-72 verbatim
theorem decodeCodeCopyStack?_eq_none_iff (stack : List EvmWord) :
    decodeCodeCopyStack? stack = none ↔ stack.length < 3 := by
  constructor
  · intro h_decode
    rcases stack with _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩
    · simp
    · simp
    · simp
    · simp [decodeCodeCopyStack?] at h_decode
  · intro h_len
    rcases stack with _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩
    · rfl
    · rfl
    · rfl
    · simp at h_len
      omega


-- @@ L74-75 verbatim
theorem decodeCodeCopyStack?_none_of_empty :
    decodeCodeCopyStack? [] = none := rfl


-- @@ L77-79 verbatim
theorem decodeCodeCopyStack?_none_of_one
    (destOffset : EvmWord) :
    decodeCodeCopyStack? [destOffset] = none := rfl


-- @@ L81-83 verbatim
theorem decodeCodeCopyStack?_none_of_two
    (destOffset codeOffset : EvmWord) :
    decodeCodeCopyStack? [destOffset, codeOffset] = none := rfl


-- @@ L85-89 verbatim
theorem decodeCodeCopyStack?_destOffset
    (destOffset codeOffset size : EvmWord) (rest : List EvmWord) :
    Option.map (fun args => args.destOffset)
      (decodeCodeCopyStack? (destOffset :: codeOffset :: size :: rest)) =
      some destOffset := rfl


-- @@ L91-95 verbatim
theorem decodeCodeCopyStack?_codeOffset
    (destOffset codeOffset size : EvmWord) (rest : List EvmWord) :
    Option.map (fun args => args.codeOffset)
      (decodeCodeCopyStack? (destOffset :: codeOffset :: size :: rest)) =
      some codeOffset := rfl


-- @@ L97-101 verbatim
theorem decodeCodeCopyStack?_size
    (destOffset codeOffset size : EvmWord) (rest : List EvmWord) :
    Option.map (fun args => args.size)
      (decodeCodeCopyStack? (destOffset :: codeOffset :: size :: rest)) =
      some size := rfl


-- @@ L103-103 verbatim
end CodeCopyArgsStackDecode


-- @@ L105-105 verbatim
end EvmAsm.Evm64
