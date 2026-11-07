/-
  EvmAsm.Evm64.SMod.Args

  Pure stack-argument bridge for SMOD (GH #90).
-/

module

public import EvmAsm.Evm64.EvmWordArith.SMod


-- @@ L11-11 verbatim
@[expose] public section


-- @@ L13-13 verbatim
namespace EvmAsm.Evm64

-- @@ L14-14 verbatim
namespace SModArgs


-- @@ L16-20 verbatim
/-- SMOD stack arguments: dividend and divisor. -/
structure Args where
  dividend : EvmWord
  divisor : EvmWord
  deriving Repr


-- @@ L22-23 verbatim
/-- SMOD pops two stack words: dividend and divisor. -/
def stackArgumentCount : Nat := 2


-- @@ L25-26 verbatim
/-- SMOD pushes one result word. -/
def resultCount : Nat := 1


-- @@ L28-30 verbatim
/-- Convenience builder for SMOD stack arguments. -/
def smodArgs (dividend divisor : EvmWord) : Args :=
  { dividend := dividend, divisor := divisor }


-- @@ L32-34 verbatim
/-- SMOD result computed from decoded stack arguments. -/
def smodResultFromArgs (args : Args) : EvmWord :=
  EvmWord.smod args.dividend args.divisor


-- @@ L36-38 verbatim
/-- Stack after the SMOD result replaces the two operands. -/
def stackAfterSMod (args : Args) (rest : List EvmWord) : List EvmWord :=
  smodResultFromArgs args :: rest


-- @@ L40-40 verbatim
theorem stackArgumentCount_eq_two : stackArgumentCount = 2 := rfl


-- @@ L42-42 verbatim
theorem resultCount_eq_one : resultCount = 1 := rfl


-- @@ L44-45 verbatim
theorem smodArgs_dividend (dividend divisor : EvmWord) :
    (smodArgs dividend divisor).dividend = dividend := rfl


-- @@ L47-48 verbatim
theorem smodArgs_divisor (dividend divisor : EvmWord) :
    (smodArgs dividend divisor).divisor = divisor := rfl


-- @@ L50-51 verbatim
theorem smodResultFromArgs_eq (args : Args) :
    smodResultFromArgs args = EvmWord.smod args.dividend args.divisor := rfl


-- @@ L53-54 verbatim
theorem stackAfterSMod_eq (args : Args) (rest : List EvmWord) :
    stackAfterSMod args rest = smodResultFromArgs args :: rest := rfl


-- @@ L56-58 verbatim
@[simp] theorem stackAfterSMod_length (args : Args) (rest : List EvmWord) :
    (stackAfterSMod args rest).length = rest.length + 1 := by
  simp [stackAfterSMod]


-- @@ L60-62 verbatim
@[simp] theorem smodResultFromArgs_zero_divisor (dividend : EvmWord) :
    smodResultFromArgs (smodArgs dividend 0) = 0 := by
  exact EvmWord.smod_zero_right


-- @@ L64-66 verbatim
@[simp] theorem smodResultFromArgs_zero_dividend (divisor : EvmWord) :
    smodResultFromArgs (smodArgs 0 divisor) = 0 := by
  exact EvmWord.zero_smod_left


-- @@ L68-70 verbatim
theorem smodResultFromArgs_intMin_neg_one :
    smodResultFromArgs (smodArgs (BitVec.intMin 256) (-1)) = 0 := by
  exact EvmWord.smod_intMin_neg_one


-- @@ L72-74 verbatim
theorem smodResultFromArgs_neg_pos_sign :
    smodResultFromArgs (smodArgs (-3) 2) = (-1 : EvmWord) := by
  exact EvmWord.smod_neg_pos_sign


-- @@ L76-78 verbatim
theorem smodResultFromArgs_pos_neg_sign :
    smodResultFromArgs (smodArgs 3 (-2)) = (1 : EvmWord) := by
  exact EvmWord.smod_pos_neg_sign


-- @@ L80-82 verbatim
theorem smodResultFromArgs_neg_neg_sign :
    smodResultFromArgs (smodArgs (-3) (-2)) = (-1 : EvmWord) := by
  exact EvmWord.smod_neg_neg_sign


-- @@ L84-84 verbatim
end SModArgs

-- @@ L85-85 verbatim
end EvmAsm.Evm64
