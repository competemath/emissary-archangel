/-
  EvmAsm.Evm64.SMod.ArgsStackDecode

  Pure top-of-stack decoder for SMOD executable-spec bridges (GH #90).
-/

module

public import EvmAsm.Evm64.SMod.Args


-- @@ L11-11 verbatim
@[expose] public section


-- @@ L13-13 verbatim
namespace EvmAsm.Evm64

-- @@ L14-14 verbatim
namespace SModArgsStackDecode


-- @@ L16-22 verbatim
/--
Decode SMOD stack arguments from the top-of-stack list order:
`dividend, divisor`.
-/
def decodeSModStack? : List EvmWord → Option SModArgs.Args
  | dividend :: divisor :: _ => some (SModArgs.smodArgs dividend divisor)
  | _ => none


-- @@ L24-27 verbatim
theorem decodeSModStack?_cons
    (dividend divisor : EvmWord) (rest : List EvmWord) :
    decodeSModStack? (dividend :: divisor :: rest) =
      some (SModArgs.smodArgs dividend divisor) := rfl


-- @@ L29-47 verbatim
theorem decodeSModStack?_eq_some_iff
    {stack : List EvmWord} {args : SModArgs.Args} :
    decodeSModStack? stack = some args ↔
      ∃ dividend divisor rest,
        stack = dividend :: divisor :: rest ∧
          args = SModArgs.smodArgs dividend divisor := by
  constructor
  · cases stack with
    | nil => simp [decodeSModStack?]
    | cons dividend tail =>
        cases tail with
        | nil => simp [decodeSModStack?]
        | cons divisor rest =>
            intro h
            injection h with h_args
            subst h_args
            exact ⟨dividend, divisor, rest, rfl, rfl⟩
  · rintro ⟨dividend, divisor, rest, rfl, rfl⟩
    rfl


-- @@ L49-65 verbatim
theorem decodeSModStack?_eq_none_iff
    {stack : List EvmWord} :
    decodeSModStack? stack = none ↔
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
            simp [decodeSModStack?]
  · rintro (rfl | ⟨dividend, rfl⟩) <;> rfl


-- @@ L67-68 verbatim
theorem decodeSModStack?_none_of_empty :
    decodeSModStack? [] = none := rfl


-- @@ L70-72 verbatim
theorem decodeSModStack?_none_of_one
    (dividend : EvmWord) :
    decodeSModStack? [dividend] = none := rfl


-- @@ L74-78 verbatim
theorem decodeSModStack?_dividend
    (dividend divisor : EvmWord) (rest : List EvmWord) :
    Option.map (fun args => args.dividend)
      (decodeSModStack? (dividend :: divisor :: rest)) =
      some dividend := rfl


-- @@ L80-84 verbatim
theorem decodeSModStack?_divisor
    (dividend divisor : EvmWord) (rest : List EvmWord) :
    Option.map (fun args => args.divisor)
      (decodeSModStack? (dividend :: divisor :: rest)) =
      some divisor := rfl


-- @@ L86-86 verbatim
end SModArgsStackDecode

-- @@ L87-87 verbatim
end EvmAsm.Evm64
