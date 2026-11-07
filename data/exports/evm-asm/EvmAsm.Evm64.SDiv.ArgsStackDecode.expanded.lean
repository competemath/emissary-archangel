/-
  EvmAsm.Evm64.SDiv.ArgsStackDecode

  Pure top-of-stack decoder for SDIV executable-spec bridges (GH #90).
-/

module

public import EvmAsm.Evm64.SDiv.Args


-- @@ L11-11 verbatim
@[expose] public section


-- @@ L13-13 verbatim
namespace EvmAsm.Evm64

-- @@ L14-14 verbatim
namespace SDivArgsStackDecode


-- @@ L16-22 verbatim
/--
Decode SDIV stack arguments from the top-of-stack list order:
`dividend, divisor`.
-/
def decodeSDivStack? : List EvmWord → Option SDivArgs.Args
  | dividend :: divisor :: _ => some (SDivArgs.sdivArgs dividend divisor)
  | _ => none


-- @@ L24-27 verbatim
theorem decodeSDivStack?_cons
    (dividend divisor : EvmWord) (rest : List EvmWord) :
    decodeSDivStack? (dividend :: divisor :: rest) =
      some (SDivArgs.sdivArgs dividend divisor) := rfl


-- @@ L29-47 verbatim
theorem decodeSDivStack?_eq_some_iff
    {stack : List EvmWord} {args : SDivArgs.Args} :
    decodeSDivStack? stack = some args ↔
      ∃ dividend divisor rest,
        stack = dividend :: divisor :: rest ∧
          args = SDivArgs.sdivArgs dividend divisor := by
  constructor
  · cases stack with
    | nil => simp [decodeSDivStack?]
    | cons dividend tail =>
        cases tail with
        | nil => simp [decodeSDivStack?]
        | cons divisor rest =>
            intro h
            injection h with h_args
            subst h_args
            exact ⟨dividend, divisor, rest, rfl, rfl⟩
  · rintro ⟨dividend, divisor, rest, rfl, rfl⟩
    rfl


-- @@ L49-65 verbatim
theorem decodeSDivStack?_eq_none_iff
    {stack : List EvmWord} :
    decodeSDivStack? stack = none ↔
      stack = [] ∨ ∃ dividend, stack = [dividend] := by
  constructor
  · cases stack with
    | nil =>
        intro _h
        exact Or.inl rfl
    | cons dividend tail =>
        cases tail with
        | nil =>
            intro _h
            exact Or.inr ⟨dividend, rfl⟩
        | cons divisor rest =>
            simp [decodeSDivStack?]
  · rintro (rfl | ⟨dividend, rfl⟩) <;> rfl


-- @@ L67-68 verbatim
theorem decodeSDivStack?_none_of_empty :
    decodeSDivStack? [] = none := rfl


-- @@ L70-72 verbatim
theorem decodeSDivStack?_none_of_one
    (dividend : EvmWord) :
    decodeSDivStack? [dividend] = none := rfl


-- @@ L74-78 verbatim
theorem decodeSDivStack?_dividend
    (dividend divisor : EvmWord) (rest : List EvmWord) :
    Option.map (fun args => args.dividend)
      (decodeSDivStack? (dividend :: divisor :: rest)) =
      some dividend := rfl


-- @@ L80-84 verbatim
theorem decodeSDivStack?_divisor
    (dividend divisor : EvmWord) (rest : List EvmWord) :
    Option.map (fun args => args.divisor)
      (decodeSDivStack? (dividend :: divisor :: rest)) =
      some divisor := rfl


-- @@ L86-86 verbatim
end SDivArgsStackDecode

-- @@ L87-87 verbatim
end EvmAsm.Evm64
