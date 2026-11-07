/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN1V5Digits

  Irreducible aliases for the v5 n=1 final quotient digits, remainder limbs, and
  top-borrow `c3` — the values the denorm epilogue reads out of the q-cells
  (`sp+4088..4064`), u-cells (`sp+4056..4032`) and `x10`.  Each is the all-call
  schoolbook projection `(fullDivN1R{0,1,2,3}V5 true … true …).proj`.

  **Why irreducible:** the loop-post → denorm-epilogue bridge must match a 25-atom
  separating-conjunction whose cell values are 4-deep `iterN1Call_v5 → div128Quot_v5
  → val256` chains.  Any whole-assertion tactic (`simp`, even `sep_perm`) that
  traverses those values blows `maxRecDepth`.  Hiding each cell value behind an
  irreducible atom makes the assertion SHALLOW, so address normalization + `sep_perm`
  run in the bridge.  See `feedback_irreducible_for_let_bindings`.  Bead
  `evm-asm-wbc4i.9.1`.
-/

module

public import EvmAsm.Evm64.DivMod.Compose.FullPathN1V5Defs


-- @@ L22-22 verbatim
@[expose] public section


-- @@ L24-24 verbatim
namespace EvmAsm.Evm64


-- @@ L26-26 verbatim
open EvmAsm.Rv64


-- @@ L28-30 verbatim
/-- n=1 quotient digit q0 (cell `sp+4088`): `(fullDivN1R0V5 …).1`. -/
@[irreducible] def n1QuotDigit0V5 (a0 a1 a2 a3 b0 b1 b2 b3 : Word) : Word :=
  (fullDivN1R0V5 true true true true a0 a1 a2 a3 b0 b1 b2 b3).1

-- @@ L31-33 verbatim
/-- n=1 quotient digit q1 (cell `sp+4080`): `(fullDivN1R1V5 …).1`. -/
@[irreducible] def n1QuotDigit1V5 (a0 a1 a2 a3 b0 b1 b2 b3 : Word) : Word :=
  (fullDivN1R1V5 true true true a0 a1 a2 a3 b0 b1 b2 b3).1

-- @@ L34-36 verbatim
/-- n=1 quotient digit q2 (cell `sp+4072`): `(fullDivN1R2V5 …).1`. -/
@[irreducible] def n1QuotDigit2V5 (a0 a1 a2 a3 b0 b1 b2 b3 : Word) : Word :=
  (fullDivN1R2V5 true true a0 a1 a2 a3 b0 b1 b2 b3).1

-- @@ L37-39 verbatim
/-- n=1 quotient digit q3 (cell `sp+4064`): `(fullDivN1R3V5 …).1`. -/
@[irreducible] def n1QuotDigit3V5 (a0 a1 a2 a3 b0 b1 b2 b3 : Word) : Word :=
  (fullDivN1R3V5 true a0 a1 a2 a3 b0 b1 b2 b3).1


-- @@ L41-43 verbatim
/-- n=1 normalized remainder limb 0 (cell `sp+4056`): `(fullDivN1R0V5 …).2.1`. -/
@[irreducible] def n1RemLimb0V5 (a0 a1 a2 a3 b0 b1 b2 b3 : Word) : Word :=
  (fullDivN1R0V5 true true true true a0 a1 a2 a3 b0 b1 b2 b3).2.1

-- @@ L44-46 verbatim
/-- n=1 normalized remainder limb 1 (cell `sp+4048`): `(fullDivN1R0V5 …).2.2.1`. -/
@[irreducible] def n1RemLimb1V5 (a0 a1 a2 a3 b0 b1 b2 b3 : Word) : Word :=
  (fullDivN1R0V5 true true true true a0 a1 a2 a3 b0 b1 b2 b3).2.2.1

-- @@ L47-49 verbatim
/-- n=1 normalized remainder limb 2 (cell `sp+4040`): `(fullDivN1R0V5 …).2.2.2.1`. -/
@[irreducible] def n1RemLimb2V5 (a0 a1 a2 a3 b0 b1 b2 b3 : Word) : Word :=
  (fullDivN1R0V5 true true true true a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1

-- @@ L50-52 verbatim
/-- n=1 normalized remainder limb 3 (cell `sp+4032`, also `x2`): `(fullDivN1R0V5 …).2.2.2.2.1`. -/
@[irreducible] def n1RemLimb3V5 (a0 a1 a2 a3 b0 b1 b2 b3 : Word) : Word :=
  (fullDivN1R0V5 true true true true a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1


-- @@ L54-56 verbatim
/-- n=1 final top-borrow `c3` (register `x10`): `fullDivN1C3V5 …`. -/
@[irreducible] def n1FinalC3V5 (a0 a1 a2 a3 b0 b1 b2 b3 : Word) : Word :=
  fullDivN1C3V5 true true true true a0 a1 a2 a3 b0 b1 b2 b3


-- @@ L58-61 verbatim
@[simp] theorem n1QuotDigit0V5_eq {a0 a1 a2 a3 b0 b1 b2 b3 : Word} :
    n1QuotDigit0V5 a0 a1 a2 a3 b0 b1 b2 b3 =
      (fullDivN1R0V5 true true true true a0 a1 a2 a3 b0 b1 b2 b3).1 := by
  unfold n1QuotDigit0V5; rfl

-- @@ L62-65 verbatim
@[simp] theorem n1QuotDigit1V5_eq {a0 a1 a2 a3 b0 b1 b2 b3 : Word} :
    n1QuotDigit1V5 a0 a1 a2 a3 b0 b1 b2 b3 =
      (fullDivN1R1V5 true true true a0 a1 a2 a3 b0 b1 b2 b3).1 := by
  unfold n1QuotDigit1V5; rfl

-- @@ L66-69 verbatim
@[simp] theorem n1QuotDigit2V5_eq {a0 a1 a2 a3 b0 b1 b2 b3 : Word} :
    n1QuotDigit2V5 a0 a1 a2 a3 b0 b1 b2 b3 =
      (fullDivN1R2V5 true true a0 a1 a2 a3 b0 b1 b2 b3).1 := by
  unfold n1QuotDigit2V5; rfl

-- @@ L70-73 verbatim
@[simp] theorem n1QuotDigit3V5_eq {a0 a1 a2 a3 b0 b1 b2 b3 : Word} :
    n1QuotDigit3V5 a0 a1 a2 a3 b0 b1 b2 b3 =
      (fullDivN1R3V5 true a0 a1 a2 a3 b0 b1 b2 b3).1 := by
  unfold n1QuotDigit3V5; rfl

-- @@ L74-77 verbatim
@[simp] theorem n1RemLimb0V5_eq {a0 a1 a2 a3 b0 b1 b2 b3 : Word} :
    n1RemLimb0V5 a0 a1 a2 a3 b0 b1 b2 b3 =
      (fullDivN1R0V5 true true true true a0 a1 a2 a3 b0 b1 b2 b3).2.1 := by
  unfold n1RemLimb0V5; rfl

-- @@ L78-81 verbatim
@[simp] theorem n1RemLimb1V5_eq {a0 a1 a2 a3 b0 b1 b2 b3 : Word} :
    n1RemLimb1V5 a0 a1 a2 a3 b0 b1 b2 b3 =
      (fullDivN1R0V5 true true true true a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 := by
  unfold n1RemLimb1V5; rfl

-- @@ L82-85 verbatim
@[simp] theorem n1RemLimb2V5_eq {a0 a1 a2 a3 b0 b1 b2 b3 : Word} :
    n1RemLimb2V5 a0 a1 a2 a3 b0 b1 b2 b3 =
      (fullDivN1R0V5 true true true true a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1 := by
  unfold n1RemLimb2V5; rfl

-- @@ L86-89 verbatim
@[simp] theorem n1RemLimb3V5_eq {a0 a1 a2 a3 b0 b1 b2 b3 : Word} :
    n1RemLimb3V5 a0 a1 a2 a3 b0 b1 b2 b3 =
      (fullDivN1R0V5 true true true true a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 := by
  unfold n1RemLimb3V5; rfl

-- @@ L90-93 verbatim
@[simp] theorem n1FinalC3V5_eq {a0 a1 a2 a3 b0 b1 b2 b3 : Word} :
    n1FinalC3V5 a0 a1 a2 a3 b0 b1 b2 b3 =
      fullDivN1C3V5 true true true true a0 a1 a2 a3 b0 b1 b2 b3 := by
  unfold n1FinalC3V5; rfl


-- @@ L95-95 verbatim
end EvmAsm.Evm64
