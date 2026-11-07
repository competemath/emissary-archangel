/-
  EvmAsm.Evm64.Exp.Compose.SavedBitFixedIterStateLoopReloadLimbFrames

  Opaque continuation-frame definitions for reload-limb direct adapters.
-/

module

public import EvmAsm.Evm64.Exp.Compose.SavedBitFixedControlFrame


-- @@ L11-11 verbatim
@[expose] public section


-- @@ L13-13 verbatim
namespace EvmAsm.Evm64.Exp.Compose


-- @@ L15-15 verbatim
open EvmAsm.Rv64


-- @@ L17-21 verbatim
@[irreducible]
def expReloadLimbDirectTailFrame
    (ptr nextNextLimb : Word) : Assertion :=
  (((ptr + signExtend12 (-8 : BitVec 12)) +
    signExtend12 (0 : BitVec 12)) ↦ₘ nextNextLimb)


-- @@ L23-29 verbatim
theorem expReloadLimbDirectTailFrame_unfold
    {ptr nextNextLimb : Word} :
    expReloadLimbDirectTailFrame ptr nextNextLimb =
      (((ptr + signExtend12 (-8 : BitVec 12)) +
        signExtend12 (0 : BitVec 12)) ↦ₘ nextNextLimb) := by
  delta expReloadLimbDirectTailFrame
  rfl


-- @@ L31-34 verbatim
@[irreducible]
def expReloadDirectTailFrame
    (ptr nextNextLimb : Word) (frame : Assertion) : Assertion :=
  expReloadLimbDirectTailFrame ptr nextNextLimb ** frame


-- @@ L36-41 verbatim
theorem expReloadDirectTailFrame_unfold
    {ptr nextNextLimb : Word} {frame : Assertion} :
    expReloadDirectTailFrame ptr nextNextLimb frame =
      ((((ptr + signExtend12 (-8 : BitVec 12)) +
        signExtend12 (0 : BitVec 12)) ↦ₘ nextNextLimb) ** frame) := by
  rw [expReloadDirectTailFrame, expReloadLimbDirectTailFrame_unfold]


-- @@ L43-47 verbatim
theorem expReloadDirectTailFrame_emp
    {ptr nextNextLimb : Word} :
    expReloadDirectTailFrame ptr nextNextLimb empAssertion =
      expReloadLimbDirectTailFrame ptr nextNextLimb := by
  rw [expReloadDirectTailFrame, sepConj_emp_right']


-- @@ L49-56 verbatim
@[irreducible]
def expReloadLimbDirectFalseFrame
    (controlC6 e iterCount ptr nextLimb : Word) : Assertion :=
  (((ptr + signExtend12 (0 : BitVec 12)) ↦ₘ nextLimb) **
    ⌜expTwoMulIterCountNew iterCount ≠ 0⌝ **
    ⌜controlC6 + signExtend12 (-1 : BitVec 12) = 0⌝ **
    ⌜(e >>> (63 : BitVec 6).toNat) +
      signExtend12 (0 : BitVec 12) = 0⌝)


-- @@ L58-67 verbatim
theorem expReloadLimbDirectFalseFrame_unfold
    {controlC6 e iterCount ptr nextLimb : Word} :
    expReloadLimbDirectFalseFrame controlC6 e iterCount ptr nextLimb =
      (((ptr + signExtend12 (0 : BitVec 12)) ↦ₘ nextLimb) **
        ⌜expTwoMulIterCountNew iterCount ≠ 0⌝ **
        ⌜controlC6 + signExtend12 (-1 : BitVec 12) = 0⌝ **
        ⌜(e >>> (63 : BitVec 6).toNat) +
          signExtend12 (0 : BitVec 12) = 0⌝) := by
  delta expReloadLimbDirectFalseFrame
  rfl


-- @@ L69-78 verbatim
@[irreducible]
def expReloadDirectFalseFrame
    (controlC6 e iterCount ptr nextLimb : Word)
    (frame : Assertion) : Assertion :=
  (((ptr + signExtend12 (0 : BitVec 12)) ↦ₘ nextLimb) **
    ⌜expTwoMulIterCountNew iterCount ≠ 0⌝ **
    ⌜controlC6 + signExtend12 (-1 : BitVec 12) = 0⌝ **
    ⌜(e >>> (63 : BitVec 6).toNat) +
      signExtend12 (0 : BitVec 12) = 0⌝ **
    frame)


-- @@ L80-90 verbatim
theorem expReloadDirectFalseFrame_unfold
    {controlC6 e iterCount ptr nextLimb : Word} {frame : Assertion} :
    expReloadDirectFalseFrame controlC6 e iterCount ptr nextLimb frame =
      (((ptr + signExtend12 (0 : BitVec 12)) ↦ₘ nextLimb) **
        ⌜expTwoMulIterCountNew iterCount ≠ 0⌝ **
        ⌜controlC6 + signExtend12 (-1 : BitVec 12) = 0⌝ **
        ⌜(e >>> (63 : BitVec 6).toNat) +
          signExtend12 (0 : BitVec 12) = 0⌝ **
        frame) := by
  delta expReloadDirectFalseFrame
  rfl


-- @@ L92-98 verbatim
theorem expReloadDirectFalseFrame_emp
    {controlC6 e iterCount ptr nextLimb : Word} :
    expReloadDirectFalseFrame controlC6 e iterCount ptr nextLimb
        empAssertion =
      expReloadLimbDirectFalseFrame controlC6 e iterCount ptr nextLimb := by
  rw [expReloadDirectFalseFrame_unfold, expReloadLimbDirectFalseFrame_unfold,
    sepConj_emp_right']


-- @@ L100-107 verbatim
@[irreducible]
def expReloadLimbDirectTrueFrame
    (controlC6 e iterCount ptr nextLimb : Word) : Assertion :=
  (((ptr + signExtend12 (0 : BitVec 12)) ↦ₘ nextLimb) **
    ⌜expTwoMulIterCountNew iterCount ≠ 0⌝ **
    ⌜controlC6 + signExtend12 (-1 : BitVec 12) = 0⌝ **
    ⌜(e >>> (63 : BitVec 6).toNat) +
      signExtend12 (0 : BitVec 12) ≠ 0⌝)


-- @@ L109-118 verbatim
theorem expReloadLimbDirectTrueFrame_unfold
    {controlC6 e iterCount ptr nextLimb : Word} :
    expReloadLimbDirectTrueFrame controlC6 e iterCount ptr nextLimb =
      (((ptr + signExtend12 (0 : BitVec 12)) ↦ₘ nextLimb) **
        ⌜expTwoMulIterCountNew iterCount ≠ 0⌝ **
        ⌜controlC6 + signExtend12 (-1 : BitVec 12) = 0⌝ **
        ⌜(e >>> (63 : BitVec 6).toNat) +
          signExtend12 (0 : BitVec 12) ≠ 0⌝) := by
  delta expReloadLimbDirectTrueFrame
  rfl


-- @@ L120-129 verbatim
@[irreducible]
def expReloadDirectTrueFrame
    (controlC6 e iterCount ptr nextLimb : Word)
    (frame : Assertion) : Assertion :=
  (((ptr + signExtend12 (0 : BitVec 12)) ↦ₘ nextLimb) **
    ⌜expTwoMulIterCountNew iterCount ≠ 0⌝ **
    ⌜controlC6 + signExtend12 (-1 : BitVec 12) = 0⌝ **
    ⌜(e >>> (63 : BitVec 6).toNat) +
      signExtend12 (0 : BitVec 12) ≠ 0⌝ **
    frame)


-- @@ L131-141 verbatim
theorem expReloadDirectTrueFrame_unfold
    {controlC6 e iterCount ptr nextLimb : Word} {frame : Assertion} :
    expReloadDirectTrueFrame controlC6 e iterCount ptr nextLimb frame =
      (((ptr + signExtend12 (0 : BitVec 12)) ↦ₘ nextLimb) **
        ⌜expTwoMulIterCountNew iterCount ≠ 0⌝ **
        ⌜controlC6 + signExtend12 (-1 : BitVec 12) = 0⌝ **
        ⌜(e >>> (63 : BitVec 6).toNat) +
          signExtend12 (0 : BitVec 12) ≠ 0⌝ **
        frame) := by
  delta expReloadDirectTrueFrame
  rfl


-- @@ L143-149 verbatim
theorem expReloadDirectTrueFrame_emp
    {controlC6 e iterCount ptr nextLimb : Word} :
    expReloadDirectTrueFrame controlC6 e iterCount ptr nextLimb
        empAssertion =
      expReloadLimbDirectTrueFrame controlC6 e iterCount ptr nextLimb := by
  rw [expReloadDirectTrueFrame_unfold, expReloadLimbDirectTrueFrame_unfold,
    sepConj_emp_right']


-- @@ L151-151 verbatim
end EvmAsm.Evm64.Exp.Compose
