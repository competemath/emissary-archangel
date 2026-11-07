/-
  EvmAsm.Evm64.AddMod.StackExecutionBridge

  Pure stack-execution bridge for ADDMOD (GH #91).
-/

module

public import EvmAsm.Evm64.AddMod.ArgsStackDecode


-- @@ L11-11 verbatim
@[expose] public section


-- @@ L13-13 verbatim
namespace EvmAsm.Evm64

-- @@ L14-14 verbatim
namespace AddModStackExecutionBridge


-- @@ L16-19 verbatim
/-- Caller-visible stack effects of ADDMOD at the executable-spec layer. -/
structure AddModVisibleEffects where
  stackWords : List EvmWord
  deriving Repr


-- @@ L21-23 verbatim
structure AddModStackState where
  stack : List EvmWord
  deriving Repr


-- @@ L25-28 verbatim
structure AddModStackResult where
  effects : AddModVisibleEffects
  stack : List EvmWord
  deriving Repr


-- @@ L30-30 verbatim
def argumentCount : Nat := AddModArgs.stackArgumentCount


-- @@ L32-32 verbatim
def resultCount : Nat := AddModArgs.resultCount


-- @@ L34-36 verbatim
def stackRestAfterAddMod? : List EvmWord → Option (List EvmWord)
  | _a :: _b :: _N :: rest => some rest
  | _ => none


-- @@ L38-44 verbatim
/-- Execute the ADDMOD stack transition using the pure argument decoder. -/
def runAddModStack? (state : AddModStackState) : Option AddModStackResult := do
  let args ← AddModArgsStackDecode.decodeAddModStack? state.stack
  let rest ← stackRestAfterAddMod? state.stack
  some
    { effects := { stackWords := [AddModArgs.addmodResultFromArgs args] }
      stack := rest }


-- @@ L46-48 verbatim
theorem stackRestAfterAddMod?_cons
    (a b N : EvmWord) (rest : List EvmWord) :
    stackRestAfterAddMod? (a :: b :: N :: rest) = some rest := rfl


-- @@ L50-57 verbatim
theorem runAddModStack?_cons
    (a b N : EvmWord) (rest : List EvmWord) :
    runAddModStack? { stack := a :: b :: N :: rest } =
      some
        { effects :=
            { stackWords := [AddModArgs.addmodResultFromArgs
                (AddModArgs.addmodArgs a b N)] }
          stack := rest } := rfl


-- @@ L59-64 verbatim
theorem runAddModStack?_semantic_cons
    (a b N : EvmWord) (rest : List EvmWord) :
    runAddModStack? { stack := a :: b :: N :: rest } =
      some
        { effects := { stackWords := [EvmWord.addmod a b N] }
          stack := rest } := rfl


-- @@ L66-67 verbatim
theorem runAddModStack?_underflow_nil :
    runAddModStack? { stack := [] } = none := rfl


-- @@ L69-70 verbatim
theorem runAddModStack?_underflow_one (a : EvmWord) :
    runAddModStack? { stack := [a] } = none := rfl


-- @@ L72-73 verbatim
theorem runAddModStack?_underflow_two (a b : EvmWord) :
    runAddModStack? { stack := [a, b] } = none := rfl


-- @@ L75-76 verbatim
theorem stackRestAfterAddMod?_none_of_empty :
    stackRestAfterAddMod? [] = none := rfl


-- @@ L78-79 verbatim
theorem stackRestAfterAddMod?_none_of_one (a : EvmWord) :
    stackRestAfterAddMod? [a] = none := rfl


-- @@ L81-82 verbatim
theorem stackRestAfterAddMod?_none_of_two (a b : EvmWord) :
    stackRestAfterAddMod? [a, b] = none := rfl


-- @@ L84-105 verbatim
theorem stackRestAfterAddMod?_eq_none_iff
    {stack : List EvmWord} :
    stackRestAfterAddMod? stack = none ↔
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
                simp [stackRestAfterAddMod?]
  · rintro (rfl | ⟨a, rfl | ⟨b, rfl⟩⟩) <;> rfl


-- @@ L107-129 verbatim
theorem runAddModStack?_eq_none_iff
    {state : AddModStackState} :
    runAddModStack? state = none ↔
      state.stack = [] ∨ ∃ a, state.stack = [a] ∨ ∃ b, state.stack = [a, b] := by
  cases state with
  | mk stack =>
      cases stack with
      | nil =>
          simp [runAddModStack?, AddModArgsStackDecode.decodeAddModStack?,
            stackRestAfterAddMod?, Option.bind]
      | cons a s1 =>
          cases s1 with
          | nil =>
              simp [runAddModStack?, AddModArgsStackDecode.decodeAddModStack?,
                stackRestAfterAddMod?, Option.bind]
          | cons b s2 =>
              cases s2 with
              | nil =>
                  simp [runAddModStack?, AddModArgsStackDecode.decodeAddModStack?,
                    stackRestAfterAddMod?, Option.bind]
              | cons N rest =>
                  simp [runAddModStack?, AddModArgsStackDecode.decodeAddModStack?,
                    stackRestAfterAddMod?, Option.bind]


-- @@ L131-170 verbatim
theorem runAddModStack?_eq_some_iff
    {state : AddModStackState} {out : AddModStackResult} :
    runAddModStack? state = some out ↔
      ∃ a b N rest,
        state.stack = a :: b :: N :: rest ∧
          out =
            { effects :=
                { stackWords := [AddModArgs.addmodResultFromArgs
                    (AddModArgs.addmodArgs a b N)] }
              stack := rest } := by
  constructor
  · cases state with
    | mk stack =>
        cases stack with
        | nil =>
            simp [runAddModStack?, AddModArgsStackDecode.decodeAddModStack?,
              stackRestAfterAddMod?, Option.bind]
        | cons a s1 =>
            cases s1 with
            | nil =>
                simp [runAddModStack?, AddModArgsStackDecode.decodeAddModStack?,
                  stackRestAfterAddMod?, Option.bind]
            | cons b s2 =>
                cases s2 with
                | nil =>
                    simp [runAddModStack?, AddModArgsStackDecode.decodeAddModStack?,
                      stackRestAfterAddMod?, Option.bind]
                | cons N rest =>
                    intro h_run
                    simp [runAddModStack?, AddModArgsStackDecode.decodeAddModStack?,
                      stackRestAfterAddMod?, Option.bind] at h_run
                    cases h_run
                    exact ⟨a, b, N, rest, rfl, rfl⟩
  · rintro ⟨a, b, N, rest, h_stack, h_out⟩
    cases state with
    | mk stack =>
        simp at h_stack
        subst h_stack
        subst h_out
        exact runAddModStack?_cons a b N rest


-- @@ L172-192 verbatim
theorem runAddModStack?_stack_length
    {state : AddModStackState} {out : AddModStackResult}
    (h_run : runAddModStack? state = some out) :
    out.stack.length + out.effects.stackWords.length + argumentCount =
      state.stack.length + resultCount := by
  cases state with
  | mk stack =>
      cases stack with
      | nil =>
          simp [runAddModStack?, AddModArgsStackDecode.decodeAddModStack?] at h_run
      | cons a s1 =>
          cases s1 with
          | nil => simp [runAddModStack?, stackRestAfterAddMod?] at h_run
          | cons b s2 =>
              cases s2 with
              | nil => simp [runAddModStack?, stackRestAfterAddMod?] at h_run
              | cons N rest =>
                  simp [runAddModStack?, stackRestAfterAddMod?] at h_run
                  cases h_run
                  simp [argumentCount, resultCount, AddModArgs.stackArgumentCount,
                    AddModArgs.resultCount]


-- @@ L194-199 verbatim
theorem runAddModStack?_head?
    (a b N : EvmWord) (rest : List EvmWord) :
    (runAddModStack? { stack := a :: b :: N :: rest }).map
      (fun out => out.effects.stackWords.head?) =
      some (some (AddModArgs.addmodResultFromArgs
        (AddModArgs.addmodArgs a b N))) := rfl


-- @@ L201-205 verbatim
theorem runAddModStack?_semantic_stack_after
    (a b N : EvmWord) (rest : List EvmWord) :
    (runAddModStack? { stack := a :: b :: N :: rest }).map
      (fun out => out.effects.stackWords ++ out.stack) =
      some (EvmWord.addmod a b N :: rest) := rfl


-- @@ L207-212 verbatim
theorem runAddModStack?_zero_modulus
    (a b : EvmWord) (rest : List EvmWord) :
    runAddModStack? { stack := a :: b :: 0 :: rest } =
      some { effects := { stackWords := [0] }, stack := rest } := by
  rw [runAddModStack?_cons]
  rw [AddModArgs.addmodResultFromArgs_zero_modulus]


-- @@ L214-214 verbatim
end AddModStackExecutionBridge

-- @@ L215-215 verbatim
end EvmAsm.Evm64
