/-
  EvmAsm.Evm64.Exp.ArgsStackDecode

  Pure top-of-stack decoder for EXP executable-spec bridges (GH #92).
-/

module

public import EvmAsm.Evm64.Exp.Args


-- @@ L11-11 verbatim
@[expose] public section


-- @@ L13-13 verbatim
namespace EvmAsm.Evm64


-- @@ L15-15 verbatim
namespace ExpArgsStackDecode


-- @@ L17-25 verbatim
/--
Decode EXP stack arguments from the top-of-stack list order:
`base, exponent`.

Distinctive token: ExpArgsStackDecode.decodeExpStack? #92.
-/
def decodeExpStack? : List EvmWord → Option ExpArgs.Args
  | base :: exponent :: _ => some (ExpArgs.expArgs base exponent)
  | _ => none


-- @@ L27-30 verbatim
theorem decodeExpStack?_cons
    (base exponent : EvmWord) (rest : List EvmWord) :
    decodeExpStack? (base :: exponent :: rest) =
      some (ExpArgs.expArgs base exponent) := rfl


-- @@ L32-50 verbatim
theorem decodeExpStack?_eq_some_iff
    {stack : List EvmWord} {args : ExpArgs.Args} :
    decodeExpStack? stack = some args ↔
      ∃ base exponent rest,
        stack = base :: exponent :: rest ∧
          args = ExpArgs.expArgs base exponent := by
  constructor
  · cases stack with
    | nil => simp [decodeExpStack?]
    | cons base s1 =>
      cases s1 with
      | nil => simp [decodeExpStack?]
      | cons exponent rest =>
        intro h
        injection h with h_args
        subst h_args
        exact ⟨base, exponent, rest, rfl, rfl⟩
  · rintro ⟨base, exponent, rest, rfl, rfl⟩
    rfl


-- @@ L52-66 verbatim
theorem decodeExpStack?_eq_some_expArgs_iff
    {stack : List EvmWord} {base exponent : EvmWord} :
    decodeExpStack? stack = some (ExpArgs.expArgs base exponent) ↔
      ∃ rest, stack = base :: exponent :: rest := by
  constructor
  · intro h
    obtain ⟨base', exponent', rest, h_stack, h_args⟩ :=
      decodeExpStack?_eq_some_iff.mp h
    simp [ExpArgs.expArgs] at h_args
    rcases h_args with ⟨h_base, h_exponent⟩
    subst h_base
    subst h_exponent
    exact ⟨rest, h_stack⟩
  · rintro ⟨rest, rfl⟩
    rfl


-- @@ L68-75 verbatim
theorem decodeExpStack?_base_of_some
    {stack : List EvmWord} {args : ExpArgs.Args}
    (h : decodeExpStack? stack = some args) :
    ∃ exponent rest, stack = args.base :: exponent :: rest := by
  obtain ⟨base, exponent, rest, h_stack, h_args⟩ :=
    decodeExpStack?_eq_some_iff.mp h
  subst h_args
  exact ⟨exponent, rest, h_stack⟩


-- @@ L77-84 verbatim
theorem decodeExpStack?_exponent_of_some
    {stack : List EvmWord} {args : ExpArgs.Args}
    (h : decodeExpStack? stack = some args) :
    ∃ base rest, stack = base :: args.exponent :: rest := by
  obtain ⟨base, exponent, rest, h_stack, h_args⟩ :=
    decodeExpStack?_eq_some_iff.mp h
  subst h_args
  exact ⟨base, rest, h_stack⟩


-- @@ L86-93 verbatim
theorem decodeExpStack?_base_exponent_of_some
    {stack : List EvmWord} {args : ExpArgs.Args}
    (h : decodeExpStack? stack = some args) :
    ∃ rest, stack = args.base :: args.exponent :: rest := by
  obtain ⟨base, exponent, rest, h_stack, h_args⟩ :=
    decodeExpStack?_eq_some_iff.mp h
  subst h_args
  exact ⟨rest, h_stack⟩


-- @@ L95-102 verbatim
theorem decodeExpStack?_length_ge_two_of_some
    {stack : List EvmWord} {args : ExpArgs.Args}
    (h : decodeExpStack? stack = some args) :
    2 ≤ stack.length := by
  obtain ⟨base, exponent, rest, h_stack, _h_args⟩ :=
    decodeExpStack?_eq_some_iff.mp h
  subst h_stack
  simp


-- @@ L104-120 verbatim
theorem decodeExpStack?_eq_none_iff
    {stack : List EvmWord} :
    decodeExpStack? stack = none ↔
      stack = [] ∨ ∃ base, stack = [base] := by
  constructor
  · cases stack with
    | nil =>
        intro _h
        exact Or.inl rfl
    | cons base tail =>
        cases tail with
        | nil =>
            intro _h
            exact Or.inr ⟨base, rfl⟩
        | cons exponent rest =>
            simp [decodeExpStack?]
  · rintro (rfl | ⟨base, rfl⟩) <;> rfl


-- @@ L122-133 verbatim
theorem decodeExpStack?_eq_none_iff_length_lt_two
    {stack : List EvmWord} :
    decodeExpStack? stack = none ↔ stack.length < 2 := by
  cases stack with
  | nil =>
      simp [decodeExpStack?]
  | cons base tail =>
      cases tail with
      | nil =>
          simp [decodeExpStack?]
      | cons exponent rest =>
          simp [decodeExpStack?]


-- @@ L135-139 verbatim
theorem decodeExpStack?_length_lt_two_of_none
    {stack : List EvmWord}
    (h_none : decodeExpStack? stack = none) :
    stack.length < 2 :=
  decodeExpStack?_eq_none_iff_length_lt_two.mp h_none


-- @@ L141-145 verbatim
theorem decodeExpStack?_none_of_length_lt_two
    {stack : List EvmWord}
    (h_len : stack.length < 2) :
    decodeExpStack? stack = none :=
  decodeExpStack?_eq_none_iff_length_lt_two.mpr h_len


-- @@ L147-158 verbatim
theorem decodeExpStack?_isSome_iff_length_ge_two
    {stack : List EvmWord} :
    (decodeExpStack? stack).isSome ↔ 2 ≤ stack.length := by
  cases stack with
  | nil =>
      simp [decodeExpStack?]
  | cons base tail =>
      cases tail with
      | nil =>
          simp [decodeExpStack?]
      | cons exponent rest =>
          simp [decodeExpStack?]


-- @@ L160-164 verbatim
theorem decodeExpStack?_length_ge_two_of_isSome
    {stack : List EvmWord}
    (h_some : (decodeExpStack? stack).isSome) :
    2 ≤ stack.length :=
  decodeExpStack?_isSome_iff_length_ge_two.mp h_some


-- @@ L166-170 verbatim
theorem decodeExpStack?_isSome_of_length_ge_two
    {stack : List EvmWord}
    (h_len : 2 ≤ stack.length) :
    (decodeExpStack? stack).isSome :=
  decodeExpStack?_isSome_iff_length_ge_two.mpr h_len


-- @@ L172-173 verbatim
theorem decodeExpStack?_none_of_empty :
    decodeExpStack? [] = none := rfl


-- @@ L175-177 verbatim
theorem decodeExpStack?_none_of_one
    (base : EvmWord) :
    decodeExpStack? [base] = none := rfl


-- @@ L179-183 verbatim
theorem decodeExpStack?_base
    (base exponent : EvmWord) (rest : List EvmWord) :
    Option.map (fun args => args.base)
      (decodeExpStack? (base :: exponent :: rest)) =
      some base := rfl


-- @@ L185-189 verbatim
theorem decodeExpStack?_exponent
    (base exponent : EvmWord) (rest : List EvmWord) :
    Option.map (fun args => args.exponent)
      (decodeExpStack? (base :: exponent :: rest)) =
      some exponent := rfl


-- @@ L191-202 verbatim
theorem decodeExpStack?_map_base_eq
    (stack : List EvmWord) :
    Option.map (fun args => args.base) (decodeExpStack? stack) =
      match stack with
      | base :: _exponent :: _rest => some base
      | _ => none := by
  cases stack with
  | nil => rfl
  | cons base tail =>
      cases tail with
      | nil => rfl
      | cons exponent rest => rfl


-- @@ L204-215 verbatim
theorem decodeExpStack?_map_exponent_eq
    (stack : List EvmWord) :
    Option.map (fun args => args.exponent) (decodeExpStack? stack) =
      match stack with
      | _base :: exponent :: _rest => some exponent
      | _ => none := by
  cases stack with
  | nil => rfl
  | cons base tail =>
      cases tail with
      | nil => rfl
      | cons exponent rest => rfl


-- @@ L217-230 verbatim
theorem decodeExpStack?_map_result_eq
    (stack : List EvmWord) :
    Option.map (fun args => ExpArgs.expResultFromArgs args)
      (decodeExpStack? stack) =
      match stack with
      | base :: exponent :: _rest =>
          some (ExpArgs.expResultFromArgs (ExpArgs.expArgs base exponent))
      | _ => none := by
  cases stack with
  | nil => rfl
  | cons base tail =>
      cases tail with
      | nil => rfl
      | cons exponent rest => rfl


-- @@ L232-238 verbatim
theorem decodeExpStack?_map_base_of_some
    {stack : List EvmWord} {args : ExpArgs.Args}
    (h : decodeExpStack? stack = some args) :
    Option.map (fun args => args.base) (decodeExpStack? stack) =
      some args.base := by
  rw [h]
  simp


-- @@ L240-246 verbatim
theorem decodeExpStack?_map_exponent_of_some
    {stack : List EvmWord} {args : ExpArgs.Args}
    (h : decodeExpStack? stack = some args) :
    Option.map (fun args => args.exponent) (decodeExpStack? stack) =
      some args.exponent := by
  rw [h]
  simp


-- @@ L248-248 verbatim
end ExpArgsStackDecode


-- @@ L250-250 verbatim
end EvmAsm.Evm64
