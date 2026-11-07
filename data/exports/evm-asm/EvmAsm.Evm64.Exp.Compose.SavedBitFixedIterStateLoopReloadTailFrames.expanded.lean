/-
  EvmAsm.Evm64.Exp.Compose.SavedBitFixedIterStateLoopReloadTailFrames

  Opaque continuation-frame definitions for reload-tail direct adapters.
-/

module

public import EvmAsm.Evm64.Exp.Compose.SavedBitFixedIterStateLoopReloadLimbFrames


-- @@ L11-11 verbatim
@[expose] public section


-- @@ L13-13 verbatim
namespace EvmAsm.Evm64.Exp.Compose


-- @@ L15-15 verbatim
open EvmAsm.Rv64


-- @@ L17-23 verbatim
@[irreducible]
def expReloadTailDirectTailFrameN
    (exponentWord : EvmWord) (k : Nat) (ptr nextNextLimb : Word) :
    Assertion :=
  expReloadDirectTailFrame ptr nextNextLimb
    (expTwoMulFixedReloadLimbFrameN exponentWord (k + 1)
      (ptr + signExtend12 (-8 : BitVec 12)))


-- @@ L25-32 verbatim
theorem expReloadTailDirectTailFrameN_unfold
    {exponentWord : EvmWord} {k : Nat} {ptr nextNextLimb : Word} :
    expReloadTailDirectTailFrameN exponentWord k ptr nextNextLimb =
      (((((ptr + signExtend12 (-8 : BitVec 12)) +
        signExtend12 (0 : BitVec 12)) ↦ₘ nextNextLimb) **
        expTwoMulFixedReloadLimbFrameN exponentWord (k + 1)
          (ptr + signExtend12 (-8 : BitVec 12)))) := by
  rw [expReloadTailDirectTailFrameN, expReloadDirectTailFrame_unfold]


-- @@ L34-40 verbatim
@[irreducible]
def expReloadTailDirectFalseFrameN
    (exponentWord : EvmWord) (k : Nat)
    (controlC6 e iterCount ptr nextLimb : Word) : Assertion :=
  expReloadDirectFalseFrame controlC6 e iterCount ptr nextLimb
    (expTwoMulFixedReloadLimbFrameN exponentWord (k + 1)
      (ptr + signExtend12 (-8 : BitVec 12)))


-- @@ L42-54 verbatim
theorem expReloadTailDirectFalseFrameN_unfold
    {exponentWord : EvmWord} {k : Nat}
    {controlC6 e iterCount ptr nextLimb : Word} :
    expReloadTailDirectFalseFrameN exponentWord k
      controlC6 e iterCount ptr nextLimb =
      (((ptr + signExtend12 (0 : BitVec 12)) ↦ₘ nextLimb) **
        ⌜expTwoMulIterCountNew iterCount ≠ 0⌝ **
        ⌜controlC6 + signExtend12 (-1 : BitVec 12) = 0⌝ **
        ⌜(e >>> (63 : BitVec 6).toNat) +
          signExtend12 (0 : BitVec 12) = 0⌝ **
        expTwoMulFixedReloadLimbFrameN exponentWord (k + 1)
          (ptr + signExtend12 (-8 : BitVec 12))) := by
  rw [expReloadTailDirectFalseFrameN, expReloadDirectFalseFrame_unfold]


-- @@ L56-62 verbatim
@[irreducible]
def expReloadTailDirectTrueFrameN
    (exponentWord : EvmWord) (k : Nat)
    (controlC6 e iterCount ptr nextLimb : Word) : Assertion :=
  expReloadDirectTrueFrame controlC6 e iterCount ptr nextLimb
    (expTwoMulFixedReloadLimbFrameN exponentWord (k + 1)
      (ptr + signExtend12 (-8 : BitVec 12)))


-- @@ L64-76 verbatim
theorem expReloadTailDirectTrueFrameN_unfold
    {exponentWord : EvmWord} {k : Nat}
    {controlC6 e iterCount ptr nextLimb : Word} :
    expReloadTailDirectTrueFrameN exponentWord k
      controlC6 e iterCount ptr nextLimb =
      (((ptr + signExtend12 (0 : BitVec 12)) ↦ₘ nextLimb) **
        ⌜expTwoMulIterCountNew iterCount ≠ 0⌝ **
        ⌜controlC6 + signExtend12 (-1 : BitVec 12) = 0⌝ **
        ⌜(e >>> (63 : BitVec 6).toNat) +
          signExtend12 (0 : BitVec 12) ≠ 0⌝ **
        expTwoMulFixedReloadLimbFrameN exponentWord (k + 1)
          (ptr + signExtend12 (-8 : BitVec 12))) := by
  rw [expReloadTailDirectTrueFrameN, expReloadDirectTrueFrame_unfold]


-- @@ L78-78 verbatim
end EvmAsm.Evm64.Exp.Compose
