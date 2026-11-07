/-
  EvmAsm.Evm64.Exp.StackExecutionBridge

  Pure stack-execution bridge for EXP (GH #92).
-/

module

public import EvmAsm.Evm64.Exp.ArgsStackDecode


-- @@ L11-11 verbatim
@[expose] public section


-- @@ L13-13 verbatim
namespace EvmAsm.Evm64


-- @@ L15-15 verbatim
namespace ExpStackExecutionBridge


-- @@ L17-22 verbatim
/-- Caller-visible effects of EXP at the executable-spec layer. -/
structure ExpVisibleEffects where
  stackWords : List EvmWord
  dynamicGas : Nat
  totalGas : Nat
  deriving Repr


-- @@ L24-26 verbatim
structure ExpStackState where
  stack : List EvmWord
  deriving Repr


-- @@ L28-31 verbatim
structure ExpStackResult where
  effects : ExpVisibleEffects
  stack : List EvmWord
  deriving Repr


-- @@ L33-33 verbatim
def argumentCount : Nat := ExpArgs.stackArgumentCount


-- @@ L35-35 verbatim
def resultCount : Nat := ExpArgs.resultCount


-- @@ L37-39 verbatim
def stackRestAfterExp? : List EvmWord → Option (List EvmWord)
  | _base :: _exponent :: rest => some rest
  | _ => none


-- @@ L41-55 verbatim
/--
Execute the EXP stack transition using the pure EXP argument decoder and
the existing word-level EXP result/gas bridge.

Distinctive token: ExpStackExecutionBridge.runExpStack? #92.
-/
def runExpStack? (state : ExpStackState) : Option ExpStackResult := do
  let args ← ExpArgsStackDecode.decodeExpStack? state.stack
  let rest ← stackRestAfterExp? state.stack
  some
    { effects :=
        { stackWords := [ExpArgs.expResultFromArgs args]
          dynamicGas := ExpArgs.expDynamicCostFromArgs args
          totalGas := ExpArgs.expTotalGasFromArgs args }
      stack := rest }


-- @@ L57-59 verbatim
theorem stackRestAfterExp?_cons
    (base exponent : EvmWord) (rest : List EvmWord) :
    stackRestAfterExp? (base :: exponent :: rest) = some rest := rfl


-- @@ L61-72 verbatim
theorem runExpStack?_cons
    (base exponent : EvmWord) (rest : List EvmWord) :
    runExpStack? { stack := base :: exponent :: rest } =
      some
        { effects :=
            { stackWords := [ExpArgs.expResultFromArgs
                (ExpArgs.expArgs base exponent)]
              dynamicGas := ExpArgs.expDynamicCostFromArgs
                (ExpArgs.expArgs base exponent)
              totalGas := ExpArgs.expTotalGasFromArgs
                (ExpArgs.expArgs base exponent) }
          stack := rest } := rfl


-- @@ L74-75 verbatim
theorem runExpStack?_underflow_nil :
    runExpStack? { stack := [] } = none := rfl


-- @@ L77-78 verbatim
theorem runExpStack?_underflow_one (base : EvmWord) :
    runExpStack? { stack := [base] } = none := rfl


-- @@ L80-81 verbatim
theorem stackRestAfterExp?_none_of_empty :
    stackRestAfterExp? [] = none := rfl


-- @@ L83-85 verbatim
theorem stackRestAfterExp?_none_of_one
    (base : EvmWord) :
    stackRestAfterExp? [base] = none := rfl


-- @@ L87-103 verbatim
theorem stackRestAfterExp?_eq_none_iff
    {stack : List EvmWord} :
    stackRestAfterExp? stack = none ↔
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
            simp [stackRestAfterExp?]
  · rintro (rfl | ⟨base, rfl⟩) <;> rfl


-- @@ L105-122 verbatim
theorem runExpStack?_eq_none_iff
    {state : ExpStackState} :
    runExpStack? state = none ↔
      state.stack = [] ∨ ∃ base, state.stack = [base] := by
  cases state with
  | mk stack =>
      cases stack with
      | nil =>
          simp [runExpStack?, ExpArgsStackDecode.decodeExpStack?,
            stackRestAfterExp?, Option.bind]
      | cons base tail =>
          cases tail with
          | nil =>
              simp [runExpStack?, ExpArgsStackDecode.decodeExpStack?,
                stackRestAfterExp?, Option.bind]
          | cons exponent rest =>
              simp [runExpStack?, ExpArgsStackDecode.decodeExpStack?,
                stackRestAfterExp?, Option.bind]


-- @@ L124-168 verbatim
/--
EXP stack execution succeeds exactly on a stack with at least two words, and
the output is the decoded EXP result/effects plus the remaining stack tail.

Distinctive token: ExpStackExecutionBridge.runExpStack?_eq_some_iff #92.
-/
theorem runExpStack?_eq_some_iff
    {state : ExpStackState} {out : ExpStackResult} :
    runExpStack? state = some out ↔
      ∃ base exponent rest,
        state.stack = base :: exponent :: rest ∧
          out =
            { effects :=
                { stackWords := [ExpArgs.expResultFromArgs
                    (ExpArgs.expArgs base exponent)]
                  dynamicGas := ExpArgs.expDynamicCostFromArgs
                    (ExpArgs.expArgs base exponent)
                  totalGas := ExpArgs.expTotalGasFromArgs
                    (ExpArgs.expArgs base exponent) }
              stack := rest } := by
  constructor
  · cases state with
    | mk stack =>
        cases stack with
        | nil =>
            simp [runExpStack?, ExpArgsStackDecode.decodeExpStack?,
              stackRestAfterExp?, Option.bind]
        | cons base tail =>
            cases tail with
            | nil =>
                simp [runExpStack?, ExpArgsStackDecode.decodeExpStack?,
                  stackRestAfterExp?, Option.bind]
            | cons exponent rest =>
                intro h_run
                simp [runExpStack?, ExpArgsStackDecode.decodeExpStack?,
                  stackRestAfterExp?, Option.bind] at h_run
                cases h_run
                exact ⟨base, exponent, rest, rfl, rfl⟩
  · rintro ⟨base, exponent, rest, h_stack, h_out⟩
    cases state with
    | mk stack =>
        simp at h_stack
        subst h_stack
        subst h_out
        exact runExpStack?_cons base exponent rest


-- @@ L170-185 verbatim
theorem runExpStack?_effects_stackWords_length
    {state : ExpStackState} {out : ExpStackResult}
    (h_run : runExpStack? state = some out) :
    out.effects.stackWords.length = resultCount := by
  cases state with
  | mk stack =>
      cases stack with
      | nil =>
          simp [runExpStack?, ExpArgsStackDecode.decodeExpStack?] at h_run
      | cons base tail =>
          cases tail with
          | nil => simp [runExpStack?, stackRestAfterExp?] at h_run
          | cons exponent rest =>
              simp [runExpStack?, stackRestAfterExp?] at h_run
              cases h_run
              simp [resultCount, ExpArgs.resultCount]


-- @@ L187-194 verbatim
theorem runExpStack?_effects_stackWords_ne_nil
    {state : ExpStackState} {out : ExpStackResult}
    (h_run : runExpStack? state = some out) :
    out.effects.stackWords ≠ [] := by
  have h_len := runExpStack?_effects_stackWords_length h_run
  intro h_nil
  rw [h_nil] at h_len
  simp [resultCount, ExpArgs.resultCount] at h_len


-- @@ L196-213 verbatim
theorem runExpStack?_stack_length
    {state : ExpStackState} {out : ExpStackResult}
    (h_run : runExpStack? state = some out) :
    out.stack.length + out.effects.stackWords.length + argumentCount =
      state.stack.length + resultCount := by
  cases state with
  | mk stack =>
      cases stack with
      | nil =>
          simp [runExpStack?, ExpArgsStackDecode.decodeExpStack?] at h_run
      | cons base tail =>
          cases tail with
          | nil => simp [runExpStack?, stackRestAfterExp?] at h_run
          | cons exponent rest =>
              simp [runExpStack?, stackRestAfterExp?] at h_run
              cases h_run
              simp [argumentCount, resultCount, ExpArgs.stackArgumentCount,
                ExpArgs.resultCount]


-- @@ L215-220 verbatim
theorem runExpStack?_head?
    (base exponent : EvmWord) (rest : List EvmWord) :
    (runExpStack? { stack := base :: exponent :: rest }).map
      (fun out => out.effects.stackWords.head?) =
      some (some (ExpArgs.expResultFromArgs
        (ExpArgs.expArgs base exponent))) := rfl


-- @@ L222-230 verbatim
theorem runExpStack?_head?_of_some
    {base exponent : EvmWord} {rest : List EvmWord} {out : ExpStackResult}
    (h_run : runExpStack? { stack := base :: exponent :: rest } = some out) :
    out.effects.stackWords.head? =
      some (ExpArgs.expResultFromArgs (ExpArgs.expArgs base exponent)) := by
  rw [runExpStack?_cons] at h_run
  injection h_run with h_out
  subst h_out
  rfl


-- @@ L232-240 verbatim
theorem runExpStack?_stackWords_of_some
    {base exponent : EvmWord} {rest : List EvmWord} {out : ExpStackResult}
    (h_run : runExpStack? { stack := base :: exponent :: rest } = some out) :
    out.effects.stackWords =
      [ExpArgs.expResultFromArgs (ExpArgs.expArgs base exponent)] := by
  rw [runExpStack?_cons] at h_run
  injection h_run with h_out
  subst h_out
  rfl


-- @@ L242-249 verbatim
theorem runExpStack?_tail_of_some
    {base exponent : EvmWord} {rest : List EvmWord} {out : ExpStackResult}
    (h_run : runExpStack? { stack := base :: exponent :: rest } = some out) :
    out.stack = rest := by
  rw [runExpStack?_cons] at h_run
  injection h_run with h_out
  subst h_out
  rfl


-- @@ L251-255 verbatim
theorem runExpStack?_stackAfterExp
    (base exponent : EvmWord) (rest : List EvmWord) :
    (runExpStack? { stack := base :: exponent :: rest }).map
      (fun out => out.effects.stackWords ++ out.stack) =
      some (ExpArgs.stackAfterExp (ExpArgs.expArgs base exponent) rest) := rfl


-- @@ L257-265 verbatim
/-- Semantic stack result for EXP: the executable stack bridge replaces the
    two operands with `EvmWord.exp base exponent`. -/
theorem runExpStack?_semantic_stack_after
    (base exponent : EvmWord) (rest : List EvmWord) :
    (runExpStack? { stack := base :: exponent :: rest }).map
      (fun out => out.effects.stackWords ++ out.stack) =
      some (EvmWord.exp base exponent :: rest) := by
  rw [runExpStack?_stackAfterExp]
  rfl


-- @@ L267-280 verbatim
/-- Semantic success form for EXP on a stack with two operands. -/
theorem runExpStack?_semantic_cons
    (base exponent : EvmWord) (rest : List EvmWord) :
    runExpStack? { stack := base :: exponent :: rest } =
      some
        { effects :=
            { stackWords := [EvmWord.exp base exponent]
              dynamicGas := ExpArgs.expDynamicCostFromArgs
                (ExpArgs.expArgs base exponent)
              totalGas := ExpArgs.expTotalGasFromArgs
                (ExpArgs.expArgs base exponent) }
          stack := rest } := by
  rw [runExpStack?_cons]
  rfl


-- @@ L282-288 verbatim
theorem runExpStack?_gas
    (base exponent : EvmWord) (rest : List EvmWord) :
    (runExpStack? { stack := base :: exponent :: rest }).map
      (fun out => (out.effects.dynamicGas, out.effects.totalGas)) =
      some
        ( ExpArgs.expDynamicCostFromArgs (ExpArgs.expArgs base exponent)
        , ExpArgs.expTotalGasFromArgs (ExpArgs.expArgs base exponent)) := rfl


-- @@ L290-298 verbatim
theorem runExpStack?_dynamicGas_of_some
    {base exponent : EvmWord} {rest : List EvmWord} {out : ExpStackResult}
    (h_run : runExpStack? { stack := base :: exponent :: rest } = some out) :
    out.effects.dynamicGas =
      ExpArgs.expDynamicCostFromArgs (ExpArgs.expArgs base exponent) := by
  rw [runExpStack?_cons] at h_run
  injection h_run with h_out
  subst h_out
  rfl


-- @@ L300-308 verbatim
theorem runExpStack?_totalGas_of_some
    {base exponent : EvmWord} {rest : List EvmWord} {out : ExpStackResult}
    (h_run : runExpStack? { stack := base :: exponent :: rest } = some out) :
    out.effects.totalGas =
      ExpArgs.expTotalGasFromArgs (ExpArgs.expArgs base exponent) := by
  rw [runExpStack?_cons] at h_run
  injection h_run with h_out
  subst h_out
  rfl


-- @@ L310-319 verbatim
theorem runExpStack?_totalGas_eq_dynamicGas_add_static
    {state : ExpStackState} {out : ExpStackResult}
    (h_run : runExpStack? state = some out) :
    out.effects.totalGas =
      out.effects.dynamicGas + EvmOpcode.staticGasCost .EXP := by
  rcases runExpStack?_eq_some_iff.mp h_run with
    ⟨base, exponent, rest, h_stack, h_out⟩
  subst h_out
  simp [ExpArgs.expTotalGasFromArgs, ExpArgs.expDynamicCostFromArgs,
    ExpGas.expTotalGasFromExponent, Nat.add_comm]


-- @@ L321-330 verbatim
theorem runExpStack?_zero_exponent
    (base : EvmWord) (rest : List EvmWord) :
    runExpStack? { stack := base :: 0 :: rest } =
      some
        { effects := { stackWords := [1], dynamicGas := 0, totalGas := 10 }
          stack := rest } := by
  rw [runExpStack?_cons]
  rw [ExpArgs.expResultFromArgs_zero_right]
  rw [ExpArgs.expDynamicCostFromArgs_zero_exponent]
  rw [ExpArgs.expTotalGasFromArgs_zero_exponent]


-- @@ L332-338 verbatim
theorem runExpStack?_zero_zero
    (rest : List EvmWord) :
    runExpStack? { stack := (0 : EvmWord) :: 0 :: rest } =
      some
        { effects := { stackWords := [1], dynamicGas := 0, totalGas := 10 }
          stack := rest } := by
  exact runExpStack?_zero_exponent 0 rest


-- @@ L340-346 verbatim
theorem runExpStack?_max_zero_exponent
    (rest : List EvmWord) :
    runExpStack? { stack := (-1 : EvmWord) :: 0 :: rest } =
      some
        { effects := { stackWords := [1], dynamicGas := 0, totalGas := 10 }
          stack := rest } := by
  exact runExpStack?_zero_exponent (-1 : EvmWord) rest


-- @@ L348-357 verbatim
theorem runExpStack?_one_exponent
    (base : EvmWord) (rest : List EvmWord) :
    runExpStack? { stack := base :: 1 :: rest } =
      some
        { effects := { stackWords := [base], dynamicGas := 50, totalGas := 60 }
          stack := rest } := by
  rw [runExpStack?_cons]
  rw [ExpArgs.expResultFromArgs_one_right]
  rw [ExpArgs.expDynamicCostFromArgs_one_exponent]
  rw [ExpArgs.expTotalGasFromArgs_one_exponent]


-- @@ L359-365 verbatim
theorem runExpStack?_two_one
    (rest : List EvmWord) :
    runExpStack? { stack := (2 : EvmWord) :: 1 :: rest } =
      some
        { effects := { stackWords := [2], dynamicGas := 50, totalGas := 60 }
          stack := rest } := by
  exact runExpStack?_one_exponent 2 rest


-- @@ L367-373 verbatim
theorem runExpStack?_zero_one
    (rest : List EvmWord) :
    runExpStack? { stack := (0 : EvmWord) :: 1 :: rest } =
      some
        { effects := { stackWords := [0], dynamicGas := 50, totalGas := 60 }
          stack := rest } := by
  exact runExpStack?_one_exponent 0 rest


-- @@ L375-381 verbatim
theorem runExpStack?_max_one_exponent
    (rest : List EvmWord) :
    runExpStack? { stack := (-1 : EvmWord) :: 1 :: rest } =
      some
        { effects := { stackWords := [(-1 : EvmWord)], dynamicGas := 50, totalGas := 60 }
          stack := rest } := by
  exact runExpStack?_one_exponent (-1 : EvmWord) rest


-- @@ L383-395 verbatim
theorem runExpStack?_one_left
    (exponent : EvmWord) (rest : List EvmWord) :
    runExpStack? { stack := (1 : EvmWord) :: exponent :: rest } =
      some
        { effects :=
            { stackWords := [1]
              dynamicGas := ExpArgs.expDynamicCostFromArgs
                (ExpArgs.expArgs 1 exponent)
              totalGas := ExpArgs.expTotalGasFromArgs
                (ExpArgs.expArgs 1 exponent) }
          stack := rest } := by
  rw [runExpStack?_cons]
  rw [ExpArgs.expResultFromArgs_one_left]


-- @@ L397-410 verbatim
theorem runExpStack?_zero_left_of_ne_zero
    (exponent : EvmWord) (h_ne : exponent ≠ 0)
    (rest : List EvmWord) :
    runExpStack? { stack := (0 : EvmWord) :: exponent :: rest } =
      some
        { effects :=
            { stackWords := [0]
              dynamicGas := ExpArgs.expDynamicCostFromArgs
                (ExpArgs.expArgs 0 exponent)
              totalGas := ExpArgs.expTotalGasFromArgs
                (ExpArgs.expArgs 0 exponent) }
          stack := rest } := by
  rw [runExpStack?_cons]
  rw [ExpArgs.expResultFromArgs_zero_left_of_ne_zero exponent h_ne]


-- @@ L412-425 verbatim
theorem runExpStack?_zero_left_of_toNat_pos
    (exponent : EvmWord) (h_pos : 0 < exponent.toNat)
    (rest : List EvmWord) :
    runExpStack? { stack := (0 : EvmWord) :: exponent :: rest } =
      some
        { effects :=
            { stackWords := [0]
              dynamicGas := ExpArgs.expDynamicCostFromArgs
                (ExpArgs.expArgs 0 exponent)
              totalGas := ExpArgs.expTotalGasFromArgs
                (ExpArgs.expArgs 0 exponent) }
          stack := rest } := by
  rw [runExpStack?_cons]
  rw [ExpArgs.expResultFromArgs_zero_left_of_toNat_pos exponent h_pos]


-- @@ L427-441 verbatim
theorem runExpStack?_two_64
    (rest : List EvmWord) :
    runExpStack? { stack := (2 : EvmWord) :: 64 :: rest } =
      some
        { effects :=
            { stackWords := [BitVec.ofNat 256 (2^64)]
              dynamicGas := 50
              totalGas := 60 }
          stack := rest } := by
  rw [runExpStack?_cons]
  simp only [ExpArgs.expResultFromArgs, ExpArgs.expArgs,
    ExpArgs.expDynamicCostFromArgs, ExpArgs.expTotalGasFromArgs]
  rw [EvmWord.exp_two_64]
  rw [ExpGas.expDynamicCostFromExponent_of_pos_lt_256 (by decide) (by decide)]
  rw [ExpGas.expTotalGasFromExponent_of_pos_lt_256 (by decide) (by decide)]


-- @@ L443-452 verbatim
theorem runExpStack?_two_256
    (rest : List EvmWord) :
    runExpStack? { stack := (2 : EvmWord) :: 256 :: rest } =
      some
        { effects := { stackWords := [0], dynamicGas := 100, totalGas := 110 }
          stack := rest } := by
  rw [runExpStack?_cons]
  rw [ExpArgs.expResultFromArgs_two_256]
  rw [ExpArgs.expDynamicCostFromArgs_256_exponent]
  rw [ExpArgs.expTotalGasFromArgs_256_exponent]


-- @@ L454-468 verbatim
theorem runExpStack?_two_128
    (rest : List EvmWord) :
    runExpStack? { stack := (2 : EvmWord) :: 128 :: rest } =
      some
        { effects :=
            { stackWords := [BitVec.ofNat 256 (2^128)]
              dynamicGas := 50
              totalGas := 60 }
          stack := rest } := by
  rw [runExpStack?_cons]
  simp only [ExpArgs.expResultFromArgs, ExpArgs.expArgs,
    ExpArgs.expDynamicCostFromArgs, ExpArgs.expTotalGasFromArgs]
  rw [EvmWord.exp_two_128]
  rw [ExpGas.expDynamicCostFromExponent_of_pos_lt_256 (by decide) (by decide)]
  rw [ExpGas.expTotalGasFromExponent_of_pos_lt_256 (by decide) (by decide)]


-- @@ L470-484 verbatim
theorem runExpStack?_two_255
    (rest : List EvmWord) :
    runExpStack? { stack := (2 : EvmWord) :: 255 :: rest } =
      some
        { effects :=
            { stackWords := [BitVec.ofNat 256 (2^255)]
              dynamicGas := 50
              totalGas := 60 }
          stack := rest } := by
  rw [runExpStack?_cons]
  simp only [ExpArgs.expResultFromArgs, ExpArgs.expArgs,
    ExpArgs.expDynamicCostFromArgs, ExpArgs.expTotalGasFromArgs]
  rw [EvmWord.exp_two_255]
  rw [ExpGas.expDynamicCostFromExponent_of_pos_lt_256 (by decide) (by decide)]
  rw [ExpGas.expTotalGasFromExponent_of_pos_lt_256 (by decide) (by decide)]


-- @@ L486-493 verbatim
theorem runExpStack?_max_exponent_gas
    (base : EvmWord) (rest : List EvmWord) :
    (runExpStack? { stack := base :: (-1 : EvmWord) :: rest }).map
      (fun out => (out.effects.dynamicGas, out.effects.totalGas)) =
      some (1600, 1610) := by
  rw [runExpStack?_gas]
  rw [ExpArgs.expDynamicCostFromArgs_max_exponent]
  rw [ExpArgs.expTotalGasFromArgs_max_exponent]


-- @@ L495-505 verbatim
theorem runExpStack?_zero_max_exponent
    (rest : List EvmWord) :
    runExpStack? { stack := (0 : EvmWord) :: (-1 : EvmWord) :: rest } =
      some
        { effects := { stackWords := [0], dynamicGas := 1600, totalGas := 1610 }
          stack := rest } := by
  rw [runExpStack?_cons]
  rw [ExpArgs.expResultFromArgs_zero_left_of_ne_zero]
  rw [ExpArgs.expDynamicCostFromArgs_max_exponent]
  rw [ExpArgs.expTotalGasFromArgs_max_exponent]
  decide


-- @@ L507-507 verbatim
end ExpStackExecutionBridge


-- @@ L509-509 verbatim
end EvmAsm.Evm64
