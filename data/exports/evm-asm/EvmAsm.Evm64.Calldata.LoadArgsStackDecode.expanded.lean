/-
  EvmAsm.Evm64.Calldata.LoadArgsStackDecode

  Pure top-of-stack decoder for CALLDATALOAD executable-spec bridges
  (GH #104 / GH #107).
-/

module

public import EvmAsm.Evm64.Calldata.LoadArgs


-- @@ L12-12 verbatim
@[expose] public section


-- @@ L14-14 verbatim
namespace EvmAsm.Evm64


-- @@ L16-16 verbatim
namespace CallDataLoadArgsStackDecode


-- @@ L18-27 verbatim
/--
Decode CALLDATALOAD stack arguments from the top-of-stack list order:
`offset`.

Distinctive token:
CallDataLoadArgsStackDecode.decodeCallDataLoadStack? #104 #107.
-/
def decodeCallDataLoadStack? : List EvmWord → Option CallDataLoadArgs.Args
  | offset :: _ => some (CallDataLoadArgs.loadArgs offset)
  | _ => none


-- @@ L29-32 verbatim
theorem decodeCallDataLoadStack?_cons
    (offset : EvmWord) (rest : List EvmWord) :
    decodeCallDataLoadStack? (offset :: rest) =
      some (CallDataLoadArgs.loadArgs offset) := rfl


-- @@ L34-48 verbatim
theorem decodeCallDataLoadStack?_eq_some_iff
    {stack : List EvmWord} {args : CallDataLoadArgs.Args} :
    decodeCallDataLoadStack? stack = some args ↔
      ∃ offset rest,
        stack = offset :: rest ∧ args = CallDataLoadArgs.loadArgs offset := by
  constructor
  · cases stack with
    | nil => simp [decodeCallDataLoadStack?]
    | cons offset rest =>
      intro h
      injection h with h_args
      subst h_args
      exact ⟨offset, rest, rfl, rfl⟩
  · rintro ⟨offset, rest, rfl, rfl⟩
    rfl


-- @@ L50-57 verbatim
theorem decodeCallDataLoadStack?_offset_of_some
    {stack : List EvmWord} {args : CallDataLoadArgs.Args}
    (h : decodeCallDataLoadStack? stack = some args) :
    ∃ rest, stack = args.offset :: rest := by
  obtain ⟨offset, rest, h_stack, h_args⟩ :=
    decodeCallDataLoadStack?_eq_some_iff.mp h
  subst h_args
  exact ⟨rest, h_stack⟩


-- @@ L59-67 verbatim
theorem decodeCallDataLoadStack?_offsetNat_of_some
    {stack : List EvmWord} {args : CallDataLoadArgs.Args}
    (h : decodeCallDataLoadStack? stack = some args) :
    ∃ offset rest,
      stack = offset :: rest ∧ CallDataLoadArgs.offsetNat args = offset.toNat := by
  obtain ⟨offset, rest, h_stack, h_args⟩ :=
    decodeCallDataLoadStack?_eq_some_iff.mp h
  subst h_args
  exact ⟨offset, rest, h_stack, rfl⟩


-- @@ L69-80 verbatim
/--
CALLDATALOAD stack decoding fails exactly when the stack is empty.

Distinctive token:
CallDataLoadArgsStackDecode.decodeCallDataLoadStack?_eq_none_iff #104 #107.
-/
theorem decodeCallDataLoadStack?_eq_none_iff
    (stack : List EvmWord) :
    decodeCallDataLoadStack? stack = none ↔ stack = [] := by
  cases stack with
  | nil => simp [decodeCallDataLoadStack?]
  | cons offset rest => simp [decodeCallDataLoadStack?]


-- @@ L82-83 verbatim
theorem decodeCallDataLoadStack?_none_of_empty :
    decodeCallDataLoadStack? [] = none := rfl


-- @@ L85-89 verbatim
theorem decodeCallDataLoadStack?_offset
    (offset : EvmWord) (rest : List EvmWord) :
    Option.map (fun args => args.offset)
      (decodeCallDataLoadStack? (offset :: rest)) =
      some offset := rfl


-- @@ L91-91 verbatim
end CallDataLoadArgsStackDecode


-- @@ L93-93 verbatim
end EvmAsm.Evm64
