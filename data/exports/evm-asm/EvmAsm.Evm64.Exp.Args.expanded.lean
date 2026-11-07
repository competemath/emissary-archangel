/-
  EvmAsm.Evm64.Exp.Args

  Pure stack-argument bridge for EXP (GH #92).
-/

module

public import EvmAsm.Evm64.EvmWordArith.Exp
public import EvmAsm.Evm64.Exp.Gas


-- @@ L12-12 verbatim
@[expose] public section


-- @@ L14-14 verbatim
namespace EvmAsm.Evm64

-- @@ L15-15 verbatim
namespace ExpArgs


-- @@ L17-21 verbatim
/-- EXP stack arguments: base and exponent. -/
structure Args where
  base : EvmWord
  exponent : EvmWord
  deriving Repr


-- @@ L23-24 verbatim
/-- EXP pops two stack words: base and exponent. -/
def stackArgumentCount : Nat := 2


-- @@ L26-27 verbatim
/-- EXP pushes one result word. -/
def resultCount : Nat := 1


-- @@ L29-31 verbatim
/-- Convenience builder for EXP stack arguments. -/
def expArgs (base exponent : EvmWord) : Args :=
  { base := base, exponent := exponent }


-- @@ L33-36 verbatim
/-- EXP result computed from decoded stack arguments.
    Distinctive token: ExpArgs.expResultFromArgs. -/
def expResultFromArgs (args : Args) : EvmWord :=
  EvmWord.exp args.base args.exponent


-- @@ L38-40 verbatim
/-- Dynamic gas for EXP computed from decoded stack arguments. -/
def expDynamicCostFromArgs (args : Args) : Nat :=
  ExpGas.expDynamicCostFromExponent args.exponent


-- @@ L42-44 verbatim
/-- Total EXP gas computed from decoded stack arguments. -/
def expTotalGasFromArgs (args : Args) : Nat :=
  ExpGas.expTotalGasFromExponent args.exponent


-- @@ L46-48 verbatim
/-- Stack after the EXP result replaces the two operands. -/
def stackAfterExp (args : Args) (rest : List EvmWord) : List EvmWord :=
  expResultFromArgs args :: rest


-- @@ L50-50 verbatim
theorem stackArgumentCount_eq_two : stackArgumentCount = 2 := rfl


-- @@ L52-52 verbatim
theorem resultCount_eq_one : resultCount = 1 := rfl


-- @@ L54-55 verbatim
theorem expArgs_base (base exponent : EvmWord) :
    (expArgs base exponent).base = base := rfl


-- @@ L57-58 verbatim
theorem expArgs_exponent (base exponent : EvmWord) :
    (expArgs base exponent).exponent = exponent := rfl


-- @@ L60-61 verbatim
theorem expResultFromArgs_eq (args : Args) :
    expResultFromArgs args = EvmWord.exp args.base args.exponent := rfl


-- @@ L63-65 verbatim
theorem expDynamicCostFromArgs_eq (args : Args) :
    expDynamicCostFromArgs args =
      ExpGas.expDynamicCostFromExponent args.exponent := rfl


-- @@ L67-69 verbatim
theorem expTotalGasFromArgs_eq (args : Args) :
    expTotalGasFromArgs args =
      ExpGas.expTotalGasFromExponent args.exponent := rfl


-- @@ L71-73 verbatim
theorem expTotalGasFromArgs_eq_static_add_dynamic (args : Args) :
    expTotalGasFromArgs args =
      EvmOpcode.staticGasCost .EXP + expDynamicCostFromArgs args := rfl


-- @@ L75-78 verbatim
theorem expTotalGasFromArgs_eq_dynamic_add_static (args : Args) :
    expTotalGasFromArgs args =
      expDynamicCostFromArgs args + EvmOpcode.staticGasCost .EXP := by
  rw [expTotalGasFromArgs_eq_static_add_dynamic, Nat.add_comm]


-- @@ L80-81 verbatim
theorem stackAfterExp_eq (args : Args) (rest : List EvmWord) :
    stackAfterExp args rest = expResultFromArgs args :: rest := rfl


-- @@ L83-84 verbatim
theorem stackAfterExp_head (args : Args) (rest : List EvmWord) :
    (stackAfterExp args rest).head? = some (expResultFromArgs args) := rfl


-- @@ L86-87 verbatim
theorem stackAfterExp_tail (args : Args) (rest : List EvmWord) :
    (stackAfterExp args rest).tail = rest := rfl


-- @@ L89-91 verbatim
@[simp] theorem stackAfterExp_length (args : Args) (rest : List EvmWord) :
    (stackAfterExp args rest).length = rest.length + 1 := by
  simp [stackAfterExp]


-- @@ L93-95 verbatim
theorem stackAfterExp_length_pos (args : Args) (rest : List EvmWord) :
    0 < (stackAfterExp args rest).length := by
  simp [stackAfterExp]


-- @@ L97-100 verbatim
theorem stackAfterExp_length_eq_counts (args : Args) (rest : List EvmWord) :
    (stackAfterExp args rest).length + stackArgumentCount =
      (args.base :: args.exponent :: rest).length + resultCount := by
  simp [stackAfterExp, stackArgumentCount, resultCount]


-- @@ L102-106 verbatim
theorem stackAfterExp_length_succ_eq_input_length
    (args : Args) (rest : List EvmWord) :
    (stackAfterExp args rest).length + 1 =
      (args.base :: args.exponent :: rest).length := by
  simp [stackAfterExp, Nat.add_comm]


-- @@ L108-110 verbatim
theorem stackAfterExp_ne_nil (args : Args) (rest : List EvmWord) :
    stackAfterExp args rest ≠ [] := by
  simp [stackAfterExp]


-- @@ L112-114 verbatim
theorem expResultFromArgs_zero_zero :
    expResultFromArgs (expArgs 0 0) = 1 := by
  exact EvmWord.exp_zero_zero


-- @@ L116-118 verbatim
theorem expResultFromArgs_zero_right (base : EvmWord) :
    expResultFromArgs (expArgs base 0) = 1 := by
  exact EvmWord.exp_zero_right base


-- @@ L120-122 verbatim
theorem expResultFromArgs_max_zero_right :
    expResultFromArgs (expArgs (-1 : EvmWord) 0) = 1 := by
  exact expResultFromArgs_zero_right (-1 : EvmWord)


-- @@ L124-126 verbatim
theorem expResultFromArgs_one_left (exponent : EvmWord) :
    expResultFromArgs (expArgs 1 exponent) = 1 := by
  exact EvmWord.exp_one_left exponent


-- @@ L128-131 verbatim
theorem expResultFromArgs_zero_left_of_ne_zero (exponent : EvmWord)
    (h : exponent ≠ 0) :
    expResultFromArgs (expArgs 0 exponent) = 0 := by
  exact EvmWord.exp_zero_left_of_ne_zero exponent h


-- @@ L133-139 verbatim
theorem expResultFromArgs_zero_left_of_toNat_pos (exponent : EvmWord)
    (h_pos : 0 < exponent.toNat) :
    expResultFromArgs (expArgs 0 exponent) = 0 := by
  exact expResultFromArgs_zero_left_of_ne_zero exponent (by
    intro h_zero
    rw [h_zero] at h_pos
    simp at h_pos)


-- @@ L141-143 verbatim
theorem expResultFromArgs_one_right (base : EvmWord) :
    expResultFromArgs (expArgs base 1) = base := by
  exact EvmWord.exp_one_right base


-- @@ L145-147 verbatim
theorem expResultFromArgs_zero_one :
    expResultFromArgs (expArgs 0 1) = 0 := by
  exact expResultFromArgs_one_right 0


-- @@ L149-151 verbatim
theorem expResultFromArgs_two_one :
    expResultFromArgs (expArgs 2 1) = 2 := by
  exact EvmWord.exp_two_one


-- @@ L153-155 verbatim
theorem expResultFromArgs_max_one_right :
    expResultFromArgs (expArgs (-1 : EvmWord) 1) = (-1 : EvmWord) := by
  exact expResultFromArgs_one_right (-1 : EvmWord)


-- @@ L157-159 verbatim
theorem expResultFromArgs_two_64 :
    expResultFromArgs (expArgs 2 64) = BitVec.ofNat 256 (2^64) := by
  exact EvmWord.exp_two_64


-- @@ L161-163 verbatim
theorem expResultFromArgs_two_128 :
    expResultFromArgs (expArgs 2 128) = BitVec.ofNat 256 (2^128) := by
  exact EvmWord.exp_two_128


-- @@ L165-167 verbatim
theorem expResultFromArgs_two_255 :
    expResultFromArgs (expArgs 2 255) = BitVec.ofNat 256 (2^255) := by
  exact EvmWord.exp_two_255


-- @@ L169-171 verbatim
theorem expResultFromArgs_two_256 :
    expResultFromArgs (expArgs 2 256) = 0 := by
  exact EvmWord.exp_two_256


-- @@ L173-175 verbatim
theorem expResultFromArgs_zero_left_max :
    expResultFromArgs (expArgs 0 (-1 : EvmWord)) = 0 := by
  exact expResultFromArgs_zero_left_of_ne_zero (-1 : EvmWord) (by decide)


-- @@ L177-179 verbatim
theorem stackAfterExp_zero_exponent (base : EvmWord) (rest : List EvmWord) :
    stackAfterExp (expArgs base 0) rest = 1 :: rest := by
  rw [stackAfterExp, expResultFromArgs_zero_right]


-- @@ L181-183 verbatim
theorem stackAfterExp_max_zero_exponent (rest : List EvmWord) :
    stackAfterExp (expArgs (-1 : EvmWord) 0) rest = 1 :: rest := by
  rw [stackAfterExp, expResultFromArgs_max_zero_right]


-- @@ L185-187 verbatim
theorem stackAfterExp_zero_zero (rest : List EvmWord) :
    stackAfterExp (expArgs 0 0) rest = 1 :: rest := by
  rw [stackAfterExp, expResultFromArgs_zero_zero]


-- @@ L189-192 verbatim
theorem stackAfterExp_zero_left_of_ne_zero
    (exponent : EvmWord) (rest : List EvmWord) (h : exponent ≠ 0) :
    stackAfterExp (expArgs 0 exponent) rest = 0 :: rest := by
  rw [stackAfterExp, expResultFromArgs_zero_left_of_ne_zero exponent h]


-- @@ L194-197 verbatim
theorem stackAfterExp_zero_left_of_toNat_pos
    (exponent : EvmWord) (rest : List EvmWord) (h_pos : 0 < exponent.toNat) :
    stackAfterExp (expArgs 0 exponent) rest = 0 :: rest := by
  rw [stackAfterExp, expResultFromArgs_zero_left_of_toNat_pos exponent h_pos]


-- @@ L199-201 verbatim
theorem stackAfterExp_one_left (exponent : EvmWord) (rest : List EvmWord) :
    stackAfterExp (expArgs 1 exponent) rest = 1 :: rest := by
  rw [stackAfterExp, expResultFromArgs_one_left]


-- @@ L203-205 verbatim
theorem stackAfterExp_one_exponent (base : EvmWord) (rest : List EvmWord) :
    stackAfterExp (expArgs base 1) rest = base :: rest := by
  rw [stackAfterExp, expResultFromArgs_one_right]


-- @@ L207-209 verbatim
theorem stackAfterExp_zero_one (rest : List EvmWord) :
    stackAfterExp (expArgs 0 1) rest = 0 :: rest := by
  rw [stackAfterExp, expResultFromArgs_zero_one]


-- @@ L211-213 verbatim
theorem stackAfterExp_two_one (rest : List EvmWord) :
    stackAfterExp (expArgs 2 1) rest = 2 :: rest := by
  rw [stackAfterExp, expResultFromArgs_two_one]


-- @@ L215-217 verbatim
theorem stackAfterExp_max_one_exponent (rest : List EvmWord) :
    stackAfterExp (expArgs (-1 : EvmWord) 1) rest = (-1 : EvmWord) :: rest := by
  rw [stackAfterExp, expResultFromArgs_max_one_right]


-- @@ L219-222 verbatim
theorem stackAfterExp_two_64 (rest : List EvmWord) :
    stackAfterExp (expArgs 2 64) rest =
      BitVec.ofNat 256 (2^64) :: rest := by
  rw [stackAfterExp, expResultFromArgs_two_64]


-- @@ L224-227 verbatim
theorem stackAfterExp_two_128 (rest : List EvmWord) :
    stackAfterExp (expArgs 2 128) rest =
      BitVec.ofNat 256 (2^128) :: rest := by
  rw [stackAfterExp, expResultFromArgs_two_128]


-- @@ L229-232 verbatim
theorem stackAfterExp_two_255 (rest : List EvmWord) :
    stackAfterExp (expArgs 2 255) rest =
      BitVec.ofNat 256 (2^255) :: rest := by
  rw [stackAfterExp, expResultFromArgs_two_255]


-- @@ L234-236 verbatim
theorem stackAfterExp_two_256 (rest : List EvmWord) :
    stackAfterExp (expArgs 2 256) rest = 0 :: rest := by
  rw [stackAfterExp, expResultFromArgs_two_256]


-- @@ L238-240 verbatim
theorem stackAfterExp_zero_left_max (rest : List EvmWord) :
    stackAfterExp (expArgs 0 (-1 : EvmWord)) rest = 0 :: rest := by
  rw [stackAfterExp, expResultFromArgs_zero_left_max]


-- @@ L242-246 verbatim
theorem expDynamicCostFromArgs_one_exponent (base : EvmWord) :
    expDynamicCostFromArgs (expArgs base 1) = 50 := by
  unfold expDynamicCostFromArgs expArgs
  change ExpGas.expDynamicCostFromExponent (1 : EvmWord) = 50
  exact ExpGas.expDynamicCostFromExponent_of_pos_lt_256 (by decide) (by decide)


-- @@ L248-252 verbatim
theorem expTotalGasFromArgs_one_exponent (base : EvmWord) :
    expTotalGasFromArgs (expArgs base 1) = 60 := by
  unfold expTotalGasFromArgs expArgs
  change ExpGas.expTotalGasFromExponent (1 : EvmWord) = 60
  exact ExpGas.expTotalGasFromExponent_of_pos_lt_256 (by decide) (by decide)


-- @@ L254-258 verbatim
theorem expTotalGasFromArgs_255_exponent (base : EvmWord) :
    expTotalGasFromArgs (expArgs base 255) = 60 := by
  unfold expTotalGasFromArgs expArgs
  change ExpGas.expTotalGasFromExponent (255 : EvmWord) = 60
  exact ExpGas.expTotalGasFromExponent_of_pos_lt_256 (by decide) (by decide)


-- @@ L260-264 verbatim
theorem expDynamicCostFromArgs_255_exponent (base : EvmWord) :
    expDynamicCostFromArgs (expArgs base 255) = 50 := by
  unfold expDynamicCostFromArgs expArgs
  change ExpGas.expDynamicCostFromExponent (255 : EvmWord) = 50
  exact ExpGas.expDynamicCostFromExponent_of_pos_lt_256 (by decide) (by decide)


-- @@ L266-268 verbatim
@[simp] theorem expDynamicCostFromArgs_zero_exponent (base : EvmWord) :
    expDynamicCostFromArgs (expArgs base 0) = 0 := by
  exact ExpGas.expDynamicCostFromExponent_zero


-- @@ L270-272 verbatim
theorem expTotalGasFromArgs_zero_exponent (base : EvmWord) :
    expTotalGasFromArgs (expArgs base 0) = 10 := by
  exact ExpGas.expTotalGasFromExponent_zero


-- @@ L274-278 verbatim
theorem expDynamicCostFromArgs_256_exponent (base : EvmWord) :
    expDynamicCostFromArgs (expArgs base 256) = 100 := by
  unfold expDynamicCostFromArgs expArgs
  change ExpGas.expDynamicCostFromExponent (256 : EvmWord) = 100
  exact ExpGas.expDynamicCostFromExponent_256


-- @@ L280-282 verbatim
theorem expTotalGasFromArgs_256_exponent (base : EvmWord) :
    expTotalGasFromArgs (expArgs base 256) = 110 := by
  exact ExpGas.expTotalGasFromExponent_256


-- @@ L284-286 verbatim
theorem expDynamicCostFromArgs_65535_exponent (base : EvmWord) :
    expDynamicCostFromArgs (expArgs base 65535) = 100 := by
  exact ExpGas.expDynamicCostFromExponent_65535


-- @@ L288-290 verbatim
theorem expTotalGasFromArgs_65535_exponent (base : EvmWord) :
    expTotalGasFromArgs (expArgs base 65535) = 110 := by
  exact ExpGas.expTotalGasFromExponent_65535


-- @@ L292-294 verbatim
theorem expDynamicCostFromArgs_65536_exponent (base : EvmWord) :
    expDynamicCostFromArgs (expArgs base 65536) = 150 := by
  exact ExpGas.expDynamicCostFromExponent_65536


-- @@ L296-298 verbatim
theorem expTotalGasFromArgs_65536_exponent (base : EvmWord) :
    expTotalGasFromArgs (expArgs base 65536) = 160 := by
  exact ExpGas.expTotalGasFromExponent_65536


-- @@ L300-302 verbatim
theorem expDynamicCostFromArgs_max_exponent (base : EvmWord) :
    expDynamicCostFromArgs (expArgs base (-1)) = 1600 := by
  exact ExpGas.expDynamicCostFromExponent_max


-- @@ L304-306 verbatim
theorem expTotalGasFromArgs_max_exponent (base : EvmWord) :
    expTotalGasFromArgs (expArgs base (-1)) = 1610 := by
  exact ExpGas.expTotalGasFromExponent_max


-- @@ L308-308 verbatim
end ExpArgs

-- @@ L309-309 verbatim
end EvmAsm.Evm64
