/-
  EvmAsm.Evm64.SMod.StackExecutionBridge

  Pure stack-execution bridge for SMOD (GH #90).
-/

module

public import EvmAsm.Evm64.SMod.ArgsStackDecode


-- @@ L11-11 verbatim
@[expose] public section


-- @@ L13-13 verbatim
namespace EvmAsm.Evm64

-- @@ L14-14 verbatim
namespace SModStackExecutionBridge


-- @@ L16-19 verbatim
/-- Caller-visible stack effects of SMOD at the executable-spec layer. -/
structure SModVisibleEffects where
  stackWords : List EvmWord
  deriving Repr


-- @@ L21-23 verbatim
structure SModStackState where
  stack : List EvmWord
  deriving Repr


-- @@ L25-28 verbatim
structure SModStackResult where
  effects : SModVisibleEffects
  stack : List EvmWord
  deriving Repr


-- @@ L30-30 verbatim
def argumentCount : Nat := SModArgs.stackArgumentCount


-- @@ L32-32 verbatim
def resultCount : Nat := SModArgs.resultCount


-- @@ L34-36 verbatim
def stackRestAfterSMod? : List EvmWord → Option (List EvmWord)
  | _dividend :: _divisor :: rest => some rest
  | _ => none


-- @@ L38-44 verbatim
/-- Execute the SMOD stack transition using the pure argument decoder. -/
def runSModStack? (state : SModStackState) : Option SModStackResult := do
  let args ← SModArgsStackDecode.decodeSModStack? state.stack
  let rest ← stackRestAfterSMod? state.stack
  some
    { effects := { stackWords := [SModArgs.smodResultFromArgs args] }
      stack := rest }


-- @@ L46-48 verbatim
theorem stackRestAfterSMod?_cons
    (dividend divisor : EvmWord) (rest : List EvmWord) :
    stackRestAfterSMod? (dividend :: divisor :: rest) = some rest := rfl


-- @@ L50-57 verbatim
theorem runSModStack?_cons
    (dividend divisor : EvmWord) (rest : List EvmWord) :
    runSModStack? { stack := dividend :: divisor :: rest } =
      some
        { effects :=
            { stackWords := [SModArgs.smodResultFromArgs
                (SModArgs.smodArgs dividend divisor)] }
          stack := rest } := rfl


-- @@ L59-60 verbatim
theorem runSModStack?_underflow_nil :
    runSModStack? { stack := [] } = none := rfl


-- @@ L62-63 verbatim
theorem runSModStack?_underflow_one (dividend : EvmWord) :
    runSModStack? { stack := [dividend] } = none := rfl


-- @@ L65-66 verbatim
theorem stackRestAfterSMod?_none_of_empty :
    stackRestAfterSMod? [] = none := rfl


-- @@ L68-70 verbatim
theorem stackRestAfterSMod?_none_of_one
    (dividend : EvmWord) :
    stackRestAfterSMod? [dividend] = none := rfl


-- @@ L72-88 verbatim
theorem stackRestAfterSMod?_eq_none_iff
    {stack : List EvmWord} :
    stackRestAfterSMod? stack = none ↔
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
            simp [stackRestAfterSMod?]
  · rintro (rfl | ⟨dividend, rfl⟩) <;> rfl


-- @@ L90-107 verbatim
theorem runSModStack?_eq_none_iff
    {state : SModStackState} :
    runSModStack? state = none ↔
      state.stack = [] ∨ ∃ dividend, state.stack = [dividend] := by
  cases state with
  | mk stack =>
      cases stack with
      | nil =>
          simp [runSModStack?, SModArgsStackDecode.decodeSModStack?,
            stackRestAfterSMod?, Option.bind]
      | cons dividend tail =>
          cases tail with
          | nil =>
              simp [runSModStack?, SModArgsStackDecode.decodeSModStack?,
                stackRestAfterSMod?, Option.bind]
          | cons divisor rest =>
              simp [runSModStack?, SModArgsStackDecode.decodeSModStack?,
                stackRestAfterSMod?, Option.bind]


-- @@ L109-143 verbatim
theorem runSModStack?_eq_some_iff
    {state : SModStackState} {out : SModStackResult} :
    runSModStack? state = some out ↔
      ∃ dividend divisor rest,
        state.stack = dividend :: divisor :: rest ∧
          out =
            { effects :=
                { stackWords := [SModArgs.smodResultFromArgs
                    (SModArgs.smodArgs dividend divisor)] }
              stack := rest } := by
  constructor
  · cases state with
    | mk stack =>
        cases stack with
        | nil =>
            simp [runSModStack?, SModArgsStackDecode.decodeSModStack?,
              stackRestAfterSMod?, Option.bind]
        | cons dividend tail =>
            cases tail with
            | nil =>
                simp [runSModStack?, SModArgsStackDecode.decodeSModStack?,
                  stackRestAfterSMod?, Option.bind]
            | cons divisor rest =>
                intro h_run
                simp [runSModStack?, SModArgsStackDecode.decodeSModStack?,
                  stackRestAfterSMod?, Option.bind] at h_run
                cases h_run
                exact ⟨dividend, divisor, rest, rfl, rfl⟩
  · rintro ⟨dividend, divisor, rest, h_stack, h_out⟩
    cases state with
    | mk stack =>
        simp at h_stack
        subst h_stack
        subst h_out
        exact runSModStack?_cons dividend divisor rest


-- @@ L145-162 verbatim
theorem runSModStack?_stack_length
    {state : SModStackState} {out : SModStackResult}
    (h_run : runSModStack? state = some out) :
    out.stack.length + out.effects.stackWords.length + argumentCount =
      state.stack.length + resultCount := by
  cases state with
  | mk stack =>
      cases stack with
      | nil =>
          simp [runSModStack?, SModArgsStackDecode.decodeSModStack?] at h_run
      | cons dividend tail =>
          cases tail with
          | nil => simp [runSModStack?, stackRestAfterSMod?] at h_run
          | cons divisor rest =>
              simp [runSModStack?, stackRestAfterSMod?] at h_run
              cases h_run
              simp [argumentCount, resultCount, SModArgs.stackArgumentCount,
                SModArgs.resultCount]


-- @@ L164-169 verbatim
theorem runSModStack?_head?
    (dividend divisor : EvmWord) (rest : List EvmWord) :
    (runSModStack? { stack := dividend :: divisor :: rest }).map
      (fun out => out.effects.stackWords.head?) =
      some (some (SModArgs.smodResultFromArgs
        (SModArgs.smodArgs dividend divisor))) := rfl


-- @@ L171-176 verbatim
theorem runSModStack?_zero_divisor
    (dividend : EvmWord) (rest : List EvmWord) :
    runSModStack? { stack := dividend :: 0 :: rest } =
      some { effects := { stackWords := [0] }, stack := rest } := by
  rw [runSModStack?_cons]
  rw [SModArgs.smodResultFromArgs_zero_divisor]


-- @@ L178-183 verbatim
theorem runSModStack?_intMin_neg_one
    (rest : List EvmWord) :
    runSModStack? { stack := BitVec.intMin 256 :: (-1 : EvmWord) :: rest } =
      some { effects := { stackWords := [0] }, stack := rest } := by
  rw [runSModStack?_cons]
  rw [SModArgs.smodResultFromArgs_intMin_neg_one]


-- @@ L185-190 verbatim
theorem runSModStack?_neg_pos_sign
    (rest : List EvmWord) :
    runSModStack? { stack := (-3 : EvmWord) :: 2 :: rest } =
      some { effects := { stackWords := [(-1 : EvmWord)] }, stack := rest } := by
  rw [runSModStack?_cons]
  rw [SModArgs.smodResultFromArgs_neg_pos_sign]


-- @@ L192-197 verbatim
theorem runSModStack?_pos_neg_sign
    (rest : List EvmWord) :
    runSModStack? { stack := (3 : EvmWord) :: (-2 : EvmWord) :: rest } =
      some { effects := { stackWords := [(1 : EvmWord)] }, stack := rest } := by
  rw [runSModStack?_cons]
  rw [SModArgs.smodResultFromArgs_pos_neg_sign]


-- @@ L199-204 verbatim
theorem runSModStack?_neg_neg_sign
    (rest : List EvmWord) :
    runSModStack? { stack := (-3 : EvmWord) :: (-2 : EvmWord) :: rest } =
      some { effects := { stackWords := [(-1 : EvmWord)] }, stack := rest } := by
  rw [runSModStack?_cons]
  rw [SModArgs.smodResultFromArgs_neg_neg_sign]


-- @@ L206-206 verbatim
end SModStackExecutionBridge

-- @@ L207-207 verbatim
end EvmAsm.Evm64
