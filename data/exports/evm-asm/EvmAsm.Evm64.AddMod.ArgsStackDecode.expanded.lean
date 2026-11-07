/-
  EvmAsm.Evm64.AddMod.ArgsStackDecode

  Pure top-of-stack decoder for ADDMOD executable-spec bridges (GH #91).
-/

module

public import EvmAsm.Evm64.AddMod.Args


-- @@ L11-11 verbatim
@[expose] public section


-- @@ L13-13 verbatim
namespace EvmAsm.Evm64

-- @@ L14-14 verbatim
namespace AddModArgsStackDecode


-- @@ L16-22 verbatim
/--
Decode ADDMOD stack arguments from the top-of-stack list order: first addend,
second addend, modulus.
-/
def decodeAddModStack? : List EvmWord → Option AddModArgs.Args
  | a :: b :: N :: _ => some (AddModArgs.addmodArgs a b N)
  | _ => none


-- @@ L24-27 verbatim
theorem decodeAddModStack?_cons
    (a b N : EvmWord) (rest : List EvmWord) :
    decodeAddModStack? (a :: b :: N :: rest) =
      some (AddModArgs.addmodArgs a b N) := rfl


-- @@ L29-50 verbatim
theorem decodeAddModStack?_eq_some_iff
    {stack : List EvmWord} {args : AddModArgs.Args} :
    decodeAddModStack? stack = some args ↔
      ∃ a b N rest,
        stack = a :: b :: N :: rest ∧
          args = AddModArgs.addmodArgs a b N := by
  constructor
  · cases stack with
    | nil => simp [decodeAddModStack?]
    | cons a s1 =>
        cases s1 with
        | nil => simp [decodeAddModStack?]
        | cons b s2 =>
            cases s2 with
            | nil => simp [decodeAddModStack?]
            | cons N rest =>
                intro h
                injection h with h_args
                subst h_args
                exact ⟨a, b, N, rest, rfl, rfl⟩
  · rintro ⟨a, b, N, rest, rfl, rfl⟩
    rfl


-- @@ L52-73 verbatim
theorem decodeAddModStack?_eq_none_iff
    {stack : List EvmWord} :
    decodeAddModStack? stack = none ↔
      stack = [] ∨ ∃ a, stack = [a] ∨ ∃ b, stack = [a, b] := by
  constructor
  · cases stack with
    | nil =>
        intro _h
        exact Or.inl rfl
    | cons a s1 =>
        cases s1 with
        | nil =>
            intro _h
            exact Or.inr ⟨a, Or.inl rfl⟩
        | cons b s2 =>
            cases s2 with
            | nil =>
                intro _h
                exact Or.inr ⟨a, Or.inr ⟨b, rfl⟩⟩
            | cons N rest =>
                simp [decodeAddModStack?]
  · rintro (rfl | ⟨a, rfl | ⟨b, rfl⟩⟩) <;> rfl


-- @@ L75-76 verbatim
theorem decodeAddModStack?_none_of_empty :
    decodeAddModStack? [] = none := rfl


-- @@ L78-79 verbatim
theorem decodeAddModStack?_none_of_one (a : EvmWord) :
    decodeAddModStack? [a] = none := rfl


-- @@ L81-82 verbatim
theorem decodeAddModStack?_none_of_two (a b : EvmWord) :
    decodeAddModStack? [a, b] = none := rfl


-- @@ L84-88 verbatim
theorem decodeAddModStack?_a
    (a b N : EvmWord) (rest : List EvmWord) :
    Option.map (fun args => args.a)
      (decodeAddModStack? (a :: b :: N :: rest)) =
      some a := rfl


-- @@ L90-94 verbatim
theorem decodeAddModStack?_b
    (a b N : EvmWord) (rest : List EvmWord) :
    Option.map (fun args => args.b)
      (decodeAddModStack? (a :: b :: N :: rest)) =
      some b := rfl


-- @@ L96-100 verbatim
theorem decodeAddModStack?_N
    (a b N : EvmWord) (rest : List EvmWord) :
    Option.map (fun args => args.N)
      (decodeAddModStack? (a :: b :: N :: rest)) =
      some N := rfl


-- @@ L102-102 verbatim
end AddModArgsStackDecode

-- @@ L103-103 verbatim
end EvmAsm.Evm64
