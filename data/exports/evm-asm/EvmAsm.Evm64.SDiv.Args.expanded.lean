/-
  EvmAsm.Evm64.SDiv.Args

  Pure stack-argument bridge for SDIV (GH #90).
-/

module

public import EvmAsm.Evm64.EvmWordArith.SDiv


-- @@ L11-11 verbatim
@[expose] public section


-- @@ L13-13 verbatim
namespace EvmAsm.Evm64

-- @@ L14-14 verbatim
namespace SDivArgs


-- @@ L16-20 verbatim
/-- SDIV stack arguments: dividend and divisor. -/
structure Args where
  dividend : EvmWord
  divisor : EvmWord
  deriving Repr


-- @@ L22-23 verbatim
/-- SDIV pops two stack words: dividend and divisor. -/
def stackArgumentCount : Nat := 2


-- @@ L25-26 verbatim
/-- SDIV pushes one result word. -/
def resultCount : Nat := 1


-- @@ L28-30 verbatim
/-- Convenience builder for SDIV stack arguments. -/
def sdivArgs (dividend divisor : EvmWord) : Args :=
  { dividend := dividend, divisor := divisor }


-- @@ L32-34 verbatim
/-- SDIV result computed from decoded stack arguments. -/
def sdivResultFromArgs (args : Args) : EvmWord :=
  EvmWord.sdiv args.dividend args.divisor


-- @@ L36-38 verbatim
/-- Stack after the SDIV result replaces the two operands. -/
def stackAfterSDiv (args : Args) (rest : List EvmWord) : List EvmWord :=
  sdivResultFromArgs args :: rest


-- @@ L40-40 verbatim
theorem stackArgumentCount_eq_two : stackArgumentCount = 2 := rfl


-- @@ L42-42 verbatim
theorem resultCount_eq_one : resultCount = 1 := rfl


-- @@ L44-45 verbatim
theorem sdivArgs_dividend (dividend divisor : EvmWord) :
    (sdivArgs dividend divisor).dividend = dividend := rfl


-- @@ L47-48 verbatim
theorem sdivArgs_divisor (dividend divisor : EvmWord) :
    (sdivArgs dividend divisor).divisor = divisor := rfl


-- @@ L50-51 verbatim
theorem sdivResultFromArgs_eq (args : Args) :
    sdivResultFromArgs args = EvmWord.sdiv args.dividend args.divisor := rfl


-- @@ L53-54 verbatim
theorem stackAfterSDiv_eq (args : Args) (rest : List EvmWord) :
    stackAfterSDiv args rest = sdivResultFromArgs args :: rest := rfl


-- @@ L56-58 verbatim
@[simp] theorem stackAfterSDiv_length (args : Args) (rest : List EvmWord) :
    (stackAfterSDiv args rest).length = rest.length + 1 := by
  simp [stackAfterSDiv]


-- @@ L60-62 verbatim
@[simp] theorem sdivResultFromArgs_zero_divisor (dividend : EvmWord) :
    sdivResultFromArgs (sdivArgs dividend 0) = 0 := by
  exact EvmWord.sdiv_zero_right


-- @@ L64-66 verbatim
@[simp] theorem sdivResultFromArgs_zero_dividend (divisor : EvmWord) :
    sdivResultFromArgs (sdivArgs 0 divisor) = 0 := by
  exact EvmWord.zero_sdiv_left


-- @@ L68-71 verbatim
theorem sdivResultFromArgs_intMin_neg_one :
    sdivResultFromArgs (sdivArgs (BitVec.intMin 256) (-1)) =
      BitVec.intMin 256 := by
  exact EvmWord.sdiv_intMin_neg_one


-- @@ L73-75 verbatim
theorem sdivResultFromArgs_neg_one_two :
    sdivResultFromArgs (sdivArgs (-1) 2) = 0 := by
  exact EvmWord.sdiv_neg_one_two


-- @@ L77-79 verbatim
theorem sdivResultFromArgs_pos_neg_trunc :
    sdivResultFromArgs (sdivArgs 7 (-2)) = (-3 : EvmWord) := by
  exact EvmWord.sdiv_pos_neg_trunc


-- @@ L81-83 verbatim
theorem sdivResultFromArgs_neg_pos_trunc :
    sdivResultFromArgs (sdivArgs (-7) 2) = (-3 : EvmWord) := by
  exact EvmWord.sdiv_neg_pos_trunc


-- @@ L85-85 verbatim
end SDivArgs

-- @@ L86-86 verbatim
end EvmAsm.Evm64
