/-
  EvmAsm.Evm64.Exp.Compose.SavedBitFixedControlFrame

  Small control-invariant helpers for the fixed-loop induction frame.
-/

module

public import EvmAsm.Evm64.Exp.Compose.SavedBitFixedLoopInvariant


-- @@ L11-11 verbatim
@[expose] public section


-- @@ L13-13 verbatim
namespace EvmAsm.Evm64.Exp.Compose


-- @@ L15-15 verbatim
open EvmAsm.Rv64


-- @@ L17-19 verbatim
private theorem controlFrame_signExtend12_neg1_toNat :
    (signExtend12 (-1 : BitVec 12)).toNat = 2^64 - 1 := by
  decide


-- @@ L21-29 verbatim
private theorem controlFrame_word_add_neg1_toNat
    {w : Word} (hPos : 1 ≤ w.toNat) :
    (w + signExtend12 (-1 : BitVec 12)).toNat = w.toNat - 1 := by
  rw [BitVec.toNat_add, controlFrame_signExtend12_neg1_toNat]
  rw [show w.toNat + (2^64 - 1) = (w.toNat - 1) + 2^64 from by
    have := w.isLt
    omega]
  rw [Nat.add_mod_right]
  exact Nat.mod_eq_of_lt (by have := w.isLt; omega)


-- @@ L31-35 verbatim
@[irreducible]
def expTwoMulFixedSavedNextLimbFrame
    (ptr nextNextLimb : Word) : Assertion :=
  (((ptr + signExtend12 (-8 : BitVec 12)) +
    signExtend12 (0 : BitVec 12)) ↦ₘ nextNextLimb)


-- @@ L37-43 verbatim
theorem expTwoMulFixedSavedNextLimbFrame_unfold
    {ptr nextNextLimb : Word} :
    expTwoMulFixedSavedNextLimbFrame ptr nextNextLimb =
      ((((ptr + signExtend12 (-8 : BitVec 12)) +
        signExtend12 (0 : BitVec 12)) ↦ₘ nextNextLimb)) := by
  delta expTwoMulFixedSavedNextLimbFrame
  rfl


-- @@ L45-49 verbatim
theorem expTwoMulFixedSavedNextLimbFrame_pcFree
    (ptr nextNextLimb : Word) :
    (expTwoMulFixedSavedNextLimbFrame ptr nextNextLimb).pcFree := by
  rw [expTwoMulFixedSavedNextLimbFrame_unfold]
  pcFree


-- @@ L51-55 verbatim
instance pcFreeInst_expTwoMulFixedSavedNextLimbFrame
    (ptr nextNextLimb : Word) :
    Assertion.PCFree
      (expTwoMulFixedSavedNextLimbFrame ptr nextNextLimb) :=
  ⟨expTwoMulFixedSavedNextLimbFrame_pcFree ptr nextNextLimb⟩


-- @@ L57-61 verbatim
@[irreducible]
def expTwoMulFixedSavedNextLimbFrameN
    (exponentWord : EvmWord) (k : Nat) (ptr : Word) : Assertion :=
  expTwoMulFixedSavedNextLimbFrame ptr
    (exponentWord.getLimbN (2 - (k + 1) / 64))


-- @@ L63-69 verbatim
theorem expTwoMulFixedSavedNextLimbFrameN_unfold
    {exponentWord : EvmWord} {k : Nat} {ptr : Word} :
    expTwoMulFixedSavedNextLimbFrameN exponentWord k ptr =
      expTwoMulFixedSavedNextLimbFrame ptr
        (exponentWord.getLimbN (2 - (k + 1) / 64)) := by
  delta expTwoMulFixedSavedNextLimbFrameN
  rfl


-- @@ L71-77 verbatim
theorem expTwoMulFixedSavedNextLimbFrameN_eq_of_nextNext
    {exponentWord : EvmWord} {k : Nat} {ptr nextNextLimb : Word}
    (hNextNext :
      nextNextLimb = exponentWord.getLimbN (2 - (k + 1) / 64)) :
    expTwoMulFixedSavedNextLimbFrame ptr nextNextLimb =
      expTwoMulFixedSavedNextLimbFrameN exponentWord k ptr := by
  rw [expTwoMulFixedSavedNextLimbFrameN_unfold, hNextNext]


-- @@ L79-84 verbatim
theorem expTwoMulFixedSavedNextLimbFrameN_pcFree
    (exponentWord : EvmWord) (k : Nat) (ptr : Word) :
    (expTwoMulFixedSavedNextLimbFrameN exponentWord k ptr).pcFree := by
  rw [expTwoMulFixedSavedNextLimbFrameN_unfold,
    expTwoMulFixedSavedNextLimbFrame_unfold]
  pcFree


-- @@ L86-90 verbatim
instance pcFreeInst_expTwoMulFixedSavedNextLimbFrameN
    (exponentWord : EvmWord) (k : Nat) (ptr : Word) :
    Assertion.PCFree
      (expTwoMulFixedSavedNextLimbFrameN exponentWord k ptr) :=
  ⟨expTwoMulFixedSavedNextLimbFrameN_pcFree exponentWord k ptr⟩


-- @@ L92-104 verbatim
theorem expTwoMulFixedSavedNextLimbFrameN_succ_no_reload
    {exponentWord : EvmWord} {k : Nat} {ptr : Word}
    (hMod : k % 64 < 62) :
    expTwoMulFixedSavedNextLimbFrameN exponentWord k ptr =
      expTwoMulFixedSavedNextLimbFrameN exponentWord (k + 1) ptr := by
  rw [expTwoMulFixedSavedNextLimbFrameN_unfold,
    expTwoMulFixedSavedNextLimbFrameN_unfold]
  rw [expTwoMulFixedSavedNextLimbFrame_unfold,
    expTwoMulFixedSavedNextLimbFrame_unfold]
  congr 1
  have hdiv : (k + 2) / 64 = (k + 1) / 64 := by
    omega
  rw [show (k + 1 + 1) / 64 = (k + 2) / 64 by ring, hdiv]


-- @@ L106-110 verbatim
@[irreducible]
def expTwoMulFixedReloadLimbFrameN
    (exponentWord : EvmWord) (k : Nat) (ptr : Word) : Assertion :=
  expTwoMulFixedSavedNextLimbFrame ptr
    (exponentWord.getLimbN (1 - k / 64))


-- @@ L112-118 verbatim
theorem expTwoMulFixedReloadLimbFrameN_unfold
    {exponentWord : EvmWord} {k : Nat} {ptr : Word} :
    expTwoMulFixedReloadLimbFrameN exponentWord k ptr =
      expTwoMulFixedSavedNextLimbFrame ptr
        (exponentWord.getLimbN (1 - k / 64)) := by
  delta expTwoMulFixedReloadLimbFrameN
  rfl


-- @@ L120-131 verbatim
theorem expTwoMulFixedReloadLimbFrameN_succ_no_reload
    {exponentWord : EvmWord} {k : Nat} {ptr : Word}
    (hMod : k % 64 < 63) :
    expTwoMulFixedReloadLimbFrameN exponentWord k ptr =
      expTwoMulFixedReloadLimbFrameN exponentWord (k + 1) ptr := by
  rw [expTwoMulFixedReloadLimbFrameN_unfold,
    expTwoMulFixedReloadLimbFrameN_unfold]
  congr 1
  congr 1
  have hdiv : (k + 1) / 64 = k / 64 := by
    omega
  rw [hdiv]


-- @@ L133-142 verbatim
theorem expTwoMulFixedReloadLimbFrameN_succ_of_control_no_reload
    {exponentWord : EvmWord} {k : Nat}
    {c6 ptr nextLimb evmSp : Word}
    (hControl :
      expTwoMulFixedControlInvariant exponentWord k c6 ptr nextLimb evmSp)
    (hC6 : c6 + signExtend12 (-1 : BitVec 12) ≠ 0) :
    expTwoMulFixedReloadLimbFrameN exponentWord k ptr =
      expTwoMulFixedReloadLimbFrameN exponentWord (k + 1) ptr :=
  expTwoMulFixedReloadLimbFrameN_succ_no_reload
    (expTwoMulFixedControlInvariant_no_reload_mod hControl hC6)


-- @@ L144-160 verbatim
theorem expTwoMulFixedControlInvariant_pre_reload_mod
    {exponentWord : EvmWord} {k : Nat}
    {c6 ptr nextLimb evmSp : Word}
    (hControl :
      expTwoMulFixedControlInvariant exponentWord k c6 ptr nextLimb evmSp)
    (hC6 : (c6 + signExtend12 (-1 : BitVec 12)).toNat = 1) :
    k % 64 = 62 := by
  unfold expTwoMulFixedControlInvariant at hControl
  rcases hControl with ⟨hNat, _⟩
  have hPos : 1 ≤ c6.toNat := by
    rw [hNat]
    have hr : k % 64 < 64 := Nat.mod_lt _ (by decide)
    omega
  have hDec := controlFrame_word_add_neg1_toNat (w := c6) hPos
  rw [hDec, hNat] at hC6
  have hr : k % 64 < 64 := Nat.mod_lt _ (by decide)
  omega


-- @@ L162-182 verbatim
theorem expTwoMulFixedControlInvariant_ordinary_no_reload_mod
    {exponentWord : EvmWord} {k : Nat}
    {c6 ptr nextLimb evmSp : Word}
    (hControl :
      expTwoMulFixedControlInvariant exponentWord k c6 ptr nextLimb evmSp)
    (hC6 : c6 + signExtend12 (-1 : BitVec 12) ≠ 0)
    (hNotPre :
      (c6 + signExtend12 (-1 : BitVec 12)).toNat ≠ 1) :
    k % 64 < 62 := by
  have hNoReload :=
    expTwoMulFixedControlInvariant_no_reload_mod hControl hC6
  by_contra hNot
  have hMod : k % 64 = 62 := by omega
  unfold expTwoMulFixedControlInvariant at hControl
  rcases hControl with ⟨hNat, _⟩
  have hPos : 1 ≤ c6.toNat := by
    rw [hNat]
    omega
  have hDec := controlFrame_word_add_neg1_toNat (w := c6) hPos
  apply hNotPre
  rw [hDec, hNat, hMod]


-- @@ L184-202 verbatim
theorem expTwoMulFixedControlInvariant_step_cases
    {exponentWord : EvmWord} {k : Nat}
    {c6 ptr nextLimb evmSp : Word}
    (hControl :
      expTwoMulFixedControlInvariant exponentWord k c6 ptr nextLimb evmSp) :
    c6 + signExtend12 (-1 : BitVec 12) = 0 ∨
      (c6 + signExtend12 (-1 : BitVec 12)).toNat = 1 ∨
      (c6 + signExtend12 (-1 : BitVec 12) ≠ 0 ∧
        (c6 + signExtend12 (-1 : BitVec 12)).toNat ≠ 1 ∧
        k % 64 < 62) := by
  by_cases hZero : c6 + signExtend12 (-1 : BitVec 12) = 0
  · exact Or.inl hZero
  · by_cases hPre :
        (c6 + signExtend12 (-1 : BitVec 12)).toNat = 1
    · exact Or.inr (Or.inl hPre)
    · exact Or.inr (Or.inr
        ⟨hZero, hPre,
          expTwoMulFixedControlInvariant_ordinary_no_reload_mod
            hControl hZero hPre⟩)


-- @@ L204-222 verbatim
theorem expTwoMulFixedSavedNextLimbFrameN_eq_succ_reload_limb_of_pre_reload
    {exponentWord : EvmWord} {k : Nat} {ptr : Word}
    (hMod : k % 64 = 62) :
    expTwoMulFixedSavedNextLimbFrameN exponentWord (k + 1) ptr =
      expTwoMulFixedReloadLimbFrameN exponentWord (k + 1) ptr := by
  rw [expTwoMulFixedSavedNextLimbFrameN_unfold,
    expTwoMulFixedReloadLimbFrameN_unfold]
  rw [expTwoMulFixedSavedNextLimbFrame_unfold,
    expTwoMulFixedSavedNextLimbFrame_unfold]
  congr 1
  have hdiv : (k + 1 + 1) / 64 = (k + 1) / 64 + 1 := by
    omega
  rw [hdiv]
  have hCases : (k + 1) / 64 = 0 ∨ 1 ≤ (k + 1) / 64 := by
    omega
  rcases hCases with hZero | hGe
  · rw [hZero]
  · rw [Nat.sub_eq_zero_of_le (by omega : 2 ≤ (k + 1) / 64 + 1),
      Nat.sub_eq_zero_of_le hGe]


-- @@ L224-233 verbatim
theorem expTwoMulFixedSavedNextLimbFrameN_eq_succ_reload_limb_of_control_pre_reload
    {exponentWord : EvmWord} {k : Nat}
    {c6 ptr nextLimb evmSp : Word}
    (hControl :
      expTwoMulFixedControlInvariant exponentWord k c6 ptr nextLimb evmSp)
    (hC6 : (c6 + signExtend12 (-1 : BitVec 12)).toNat = 1) :
    expTwoMulFixedSavedNextLimbFrameN exponentWord (k + 1) ptr =
      expTwoMulFixedReloadLimbFrameN exponentWord (k + 1) ptr := by
  apply expTwoMulFixedSavedNextLimbFrameN_eq_succ_reload_limb_of_pre_reload
  exact expTwoMulFixedControlInvariant_pre_reload_mod hControl hC6


-- @@ L235-240 verbatim
@[irreducible]
def expTwoMulFixedPreReloadFrameN
    (exponentWord : EvmWord) (k : Nat) (ptr : Word) : Assertion :=
  expTwoMulFixedSavedNextLimbFrameN exponentWord k ptr **
  expTwoMulFixedSavedNextLimbFrameN exponentWord (k + 1)
    (ptr + signExtend12 (-8 : BitVec 12))


-- @@ L242-249 verbatim
theorem expTwoMulFixedPreReloadFrameN_unfold
    {exponentWord : EvmWord} {k : Nat} {ptr : Word} :
    expTwoMulFixedPreReloadFrameN exponentWord k ptr =
      (expTwoMulFixedSavedNextLimbFrameN exponentWord k ptr **
      expTwoMulFixedSavedNextLimbFrameN exponentWord (k + 1)
        (ptr + signExtend12 (-8 : BitVec 12))) := by
  delta expTwoMulFixedPreReloadFrameN
  rfl


-- @@ L251-259 verbatim
theorem expTwoMulFixedPreReloadFrameN_pcFree
    (exponentWord : EvmWord) (k : Nat) (ptr : Word) :
    (expTwoMulFixedPreReloadFrameN exponentWord k ptr).pcFree := by
  rw [expTwoMulFixedPreReloadFrameN_unfold,
    expTwoMulFixedSavedNextLimbFrameN_unfold,
    expTwoMulFixedSavedNextLimbFrameN_unfold,
    expTwoMulFixedSavedNextLimbFrame_unfold,
    expTwoMulFixedSavedNextLimbFrame_unfold]
  pcFree


-- @@ L261-265 verbatim
instance pcFreeInst_expTwoMulFixedPreReloadFrameN
    (exponentWord : EvmWord) (k : Nat) (ptr : Word) :
    Assertion.PCFree
      (expTwoMulFixedPreReloadFrameN exponentWord k ptr) :=
  ⟨expTwoMulFixedPreReloadFrameN_pcFree exponentWord k ptr⟩


-- @@ L267-284 verbatim
theorem expTwoMulFixedPreReloadFrameN_handoff_of_control
    {exponentWord : EvmWord} {k : Nat}
    {c6 ptr nextLimb evmSp : Word}
    (hControl :
      expTwoMulFixedControlInvariant exponentWord k c6 ptr nextLimb evmSp)
    (hC6 : (c6 + signExtend12 (-1 : BitVec 12)).toNat = 1) :
    expTwoMulFixedPreReloadFrameN exponentWord k ptr =
      (expTwoMulFixedSavedNextLimbFrameN exponentWord k ptr **
        expTwoMulFixedReloadLimbFrameN exponentWord (k + 1)
          (ptr + signExtend12 (-8 : BitVec 12))) := by
  -- Use the address-parametric value lemma keyed on `k % 64 = 62`, extracted
  -- from the control invariant — avoids juggling `hControl`'s pointer argument
  -- (which would trigger a non-matching-atom def-eq blowup).
  have hMod : k % 64 = 62 :=
    expTwoMulFixedControlInvariant_pre_reload_mod hControl hC6
  rw [expTwoMulFixedPreReloadFrameN_unfold,
    expTwoMulFixedSavedNextLimbFrameN_eq_succ_reload_limb_of_pre_reload
      (ptr := ptr + signExtend12 (-8 : BitVec 12)) hMod]


-- @@ L286-304 verbatim
theorem expTwoMulFixedReloadLimbFrameN_eq_of_reload_nextNext
    {exponentWord : EvmWord} {k : Nat} {ptr nextNextLimb : Word}
    (hMod : k % 64 = 63)
    (hNextNext :
      nextNextLimb = exponentWord.getLimbN (2 - (k + 1) / 64)) :
    expTwoMulFixedSavedNextLimbFrame ptr nextNextLimb =
      expTwoMulFixedReloadLimbFrameN exponentWord k ptr := by
  rw [expTwoMulFixedReloadLimbFrameN_unfold, hNextNext]
  congr 1
  have hdiv : (k + 1) / 64 = k / 64 + 1 := by
    omega
  rw [hdiv]
  have hCases : k / 64 = 0 ∨ k / 64 = 1 ∨ 2 ≤ k / 64 := by
    omega
  rcases hCases with hZero | hOne | hGe
  · rw [hZero]
  · rw [hOne]
  · rw [Nat.sub_eq_zero_of_le (by omega : 2 ≤ k / 64 + 1),
      Nat.sub_eq_zero_of_le (by omega : 1 ≤ k / 64)]


-- @@ L306-318 verbatim
theorem expTwoMulFixedReloadLimbFrameN_eq_of_control_reload_nextNext
    {exponentWord : EvmWord} {k : Nat}
    {c6 ptr nextLimb nextNextLimb evmSp : Word}
    (hControl :
      expTwoMulFixedControlInvariant exponentWord k c6 ptr nextLimb evmSp)
    (hC6 : c6 + signExtend12 (-1 : BitVec 12) = 0)
    (hNextNext :
      nextNextLimb = exponentWord.getLimbN (2 - (k + 1) / 64)) :
    expTwoMulFixedSavedNextLimbFrame ptr nextNextLimb =
      expTwoMulFixedReloadLimbFrameN exponentWord k ptr :=
  expTwoMulFixedReloadLimbFrameN_eq_of_reload_nextNext
    (expTwoMulFixedControlInvariant_reload_mod hControl hC6)
    hNextNext


-- @@ L320-325 verbatim
@[irreducible]
def expTwoMulFixedReloadTailFrameN
    (exponentWord : EvmWord) (k : Nat) (ptr : Word) : Assertion :=
  expTwoMulFixedReloadLimbFrameN exponentWord k ptr **
  expTwoMulFixedSavedNextLimbFrame (ptr + signExtend12 (-8 : BitVec 12))
    (exponentWord.getLimbN (0 - k / 64))


-- @@ L327-335 verbatim
theorem expTwoMulFixedReloadTailFrameN_unfold
    {exponentWord : EvmWord} {k : Nat} {ptr : Word} :
    expTwoMulFixedReloadTailFrameN exponentWord k ptr =
      (expTwoMulFixedReloadLimbFrameN exponentWord k ptr **
      expTwoMulFixedSavedNextLimbFrame
        (ptr + signExtend12 (-8 : BitVec 12))
        (exponentWord.getLimbN (0 - k / 64))) := by
  delta expTwoMulFixedReloadTailFrameN
  rfl


-- @@ L337-344 verbatim
theorem expTwoMulFixedReloadTailFrameN_pcFree
    (exponentWord : EvmWord) (k : Nat) (ptr : Word) :
    (expTwoMulFixedReloadTailFrameN exponentWord k ptr).pcFree := by
  rw [expTwoMulFixedReloadTailFrameN_unfold,
    expTwoMulFixedReloadLimbFrameN_unfold,
    expTwoMulFixedSavedNextLimbFrame_unfold,
    expTwoMulFixedSavedNextLimbFrame_unfold]
  pcFree


-- @@ L346-350 verbatim
instance pcFreeInst_expTwoMulFixedReloadTailFrameN
    (exponentWord : EvmWord) (k : Nat) (ptr : Word) :
    Assertion.PCFree
      (expTwoMulFixedReloadTailFrameN exponentWord k ptr) :=
  ⟨expTwoMulFixedReloadTailFrameN_pcFree exponentWord k ptr⟩


-- @@ L352-366 verbatim
theorem expTwoMulFixedReloadTailFrameN_succ_no_reload
    {exponentWord : EvmWord} {k : Nat} {ptr : Word}
    (hMod : k % 64 < 63) :
    expTwoMulFixedReloadTailFrameN exponentWord k ptr =
      expTwoMulFixedReloadTailFrameN exponentWord (k + 1) ptr := by
  rw [expTwoMulFixedReloadTailFrameN_unfold,
    expTwoMulFixedReloadTailFrameN_unfold,
    expTwoMulFixedReloadLimbFrameN_succ_no_reload hMod]
  congr 1
  rw [expTwoMulFixedSavedNextLimbFrame_unfold,
    expTwoMulFixedSavedNextLimbFrame_unfold]
  congr 1
  have hdiv : (k + 1) / 64 = k / 64 := by
    omega
  rw [hdiv]


-- @@ L368-377 verbatim
theorem expTwoMulFixedReloadTailFrameN_succ_of_control_no_reload
    {exponentWord : EvmWord} {k : Nat}
    {c6 ptr nextLimb evmSp : Word}
    (hControl :
      expTwoMulFixedControlInvariant exponentWord k c6 ptr nextLimb evmSp)
    (hC6 : c6 + signExtend12 (-1 : BitVec 12) ≠ 0) :
    expTwoMulFixedReloadTailFrameN exponentWord k ptr =
      expTwoMulFixedReloadTailFrameN exponentWord (k + 1) ptr :=
  expTwoMulFixedReloadTailFrameN_succ_no_reload
    (expTwoMulFixedControlInvariant_no_reload_mod hControl hC6)


-- @@ L379-397 verbatim
theorem expTwoMulFixedReloadTailFrameN_second_eq_succ_reload_limb
    {exponentWord : EvmWord} {k : Nat} {ptr : Word}
    (hMod : k % 64 = 63) :
    expTwoMulFixedSavedNextLimbFrame
        (ptr + signExtend12 (-8 : BitVec 12))
        (exponentWord.getLimbN (0 - k / 64)) =
      expTwoMulFixedReloadLimbFrameN exponentWord (k + 1)
        (ptr + signExtend12 (-8 : BitVec 12)) := by
  rw [expTwoMulFixedReloadLimbFrameN_unfold]
  congr 1
  have hdiv : (k + 1) / 64 = k / 64 + 1 := by
    omega
  rw [hdiv]
  have hCases : k / 64 = 0 ∨ 1 ≤ k / 64 := by
    omega
  rcases hCases with hZero | hGe
  · rw [hZero]
  · rw [Nat.sub_eq_zero_of_le (Nat.zero_le (k / 64)),
      Nat.sub_eq_zero_of_le (by omega : 1 ≤ k / 64 + 1)]


-- @@ L399-407 verbatim
theorem expTwoMulFixedReloadTailFrameN_handoff
    {exponentWord : EvmWord} {k : Nat} {ptr : Word}
    (hMod : k % 64 = 63) :
    expTwoMulFixedReloadTailFrameN exponentWord k ptr =
      (expTwoMulFixedReloadLimbFrameN exponentWord k ptr **
        expTwoMulFixedReloadLimbFrameN exponentWord (k + 1)
          (ptr + signExtend12 (-8 : BitVec 12))) := by
  rw [expTwoMulFixedReloadTailFrameN_unfold,
    expTwoMulFixedReloadTailFrameN_second_eq_succ_reload_limb hMod]


-- @@ L409-420 verbatim
theorem expTwoMulFixedReloadTailFrameN_handoff_of_control
    {exponentWord : EvmWord} {k : Nat}
    {c6 ptr nextLimb evmSp : Word}
    (hControl :
      expTwoMulFixedControlInvariant exponentWord k c6 ptr nextLimb evmSp)
    (hC6 : c6 + signExtend12 (-1 : BitVec 12) = 0) :
    expTwoMulFixedReloadTailFrameN exponentWord k ptr =
      (expTwoMulFixedReloadLimbFrameN exponentWord k ptr **
        expTwoMulFixedReloadLimbFrameN exponentWord (k + 1)
          (ptr + signExtend12 (-8 : BitVec 12))) :=
  expTwoMulFixedReloadTailFrameN_handoff
    (expTwoMulFixedControlInvariant_reload_mod hControl hC6)


-- @@ L422-424 verbatim
@[irreducible]
def expTwoMulFixedControlDec (c6 : Word) : Word :=
  c6 + signExtend12 (-1 : BitVec 12)


-- @@ L426-430 verbatim
theorem expTwoMulFixedControlDec_unfold {c6 : Word} :
    expTwoMulFixedControlDec c6 =
      c6 + signExtend12 (-1 : BitVec 12) := by
  delta expTwoMulFixedControlDec
  rfl


-- @@ L432-440 verbatim
@[irreducible]
def expTwoMulFixedInductionFrameN
    (exponentWord : EvmWord) (k : Nat) (c6 ptr : Word) : Assertion :=
  if expTwoMulFixedControlDec c6 = (0 : Word) then
    expTwoMulFixedReloadTailFrameN exponentWord k ptr
  else if (expTwoMulFixedControlDec c6).toNat = 1 then
    expTwoMulFixedPreReloadFrameN exponentWord k ptr
  else
    expTwoMulFixedSavedNextLimbFrameN exponentWord k ptr


-- @@ L442-448 verbatim
theorem expTwoMulFixedInductionFrameN_reload
    {exponentWord : EvmWord} {k : Nat} {c6 ptr : Word}
    (hC6 : expTwoMulFixedControlDec c6 = (0 : Word)) :
    expTwoMulFixedInductionFrameN exponentWord k c6 ptr =
      expTwoMulFixedReloadTailFrameN exponentWord k ptr := by
  rw [expTwoMulFixedInductionFrameN]
  simp [hC6]


-- @@ L450-463 verbatim
theorem expTwoMulFixedInductionFrameN_pre_reload
    {exponentWord : EvmWord} {k : Nat} {c6 ptr : Word}
    (hC6 : (expTwoMulFixedControlDec c6).toNat = 1) :
    expTwoMulFixedInductionFrameN exponentWord k c6 ptr =
      expTwoMulFixedPreReloadFrameN exponentWord k ptr := by
  rw [expTwoMulFixedInductionFrameN]
  split
  · rename_i hZero
    have hNatZero :
        (expTwoMulFixedControlDec c6).toNat = 0 := by
      rw [hZero]
      decide
    omega
  · rfl


-- @@ L465-475 verbatim
theorem expTwoMulFixedInductionFrameN_ordinary
    {exponentWord : EvmWord} {k : Nat} {c6 ptr : Word}
    (hC6 : expTwoMulFixedControlDec c6 ≠ (0 : Word))
    (hNotPre : (expTwoMulFixedControlDec c6).toNat ≠ 1) :
    expTwoMulFixedInductionFrameN exponentWord k c6 ptr =
      expTwoMulFixedSavedNextLimbFrameN exponentWord k ptr := by
  rw [expTwoMulFixedInductionFrameN]
  split
  · rename_i hZero
    exact False.elim (hC6 hZero)
  · rfl


-- @@ L477-484 verbatim
theorem expTwoMulFixedInductionFrameN_reload_of_control
    {exponentWord : EvmWord} {k : Nat} {c6 ptr : Word}
    (hC6 : c6 + signExtend12 (-1 : BitVec 12) = 0) :
    expTwoMulFixedInductionFrameN exponentWord k c6 ptr =
      expTwoMulFixedReloadTailFrameN exponentWord k ptr :=
  expTwoMulFixedInductionFrameN_reload (by
    rw [expTwoMulFixedControlDec_unfold]
    exact hC6)


-- @@ L486-493 verbatim
theorem expTwoMulFixedInductionFrameN_pre_reload_of_control
    {exponentWord : EvmWord} {k : Nat} {c6 ptr : Word}
    (hC6 : (c6 + signExtend12 (-1 : BitVec 12)).toNat = 1) :
    expTwoMulFixedInductionFrameN exponentWord k c6 ptr =
      expTwoMulFixedPreReloadFrameN exponentWord k ptr :=
  expTwoMulFixedInductionFrameN_pre_reload (by
    rw [expTwoMulFixedControlDec_unfold]
    exact hC6)


-- @@ L495-507 verbatim
theorem expTwoMulFixedInductionFrameN_ordinary_of_control
    {exponentWord : EvmWord} {k : Nat} {c6 ptr : Word}
    (hC6 : c6 + signExtend12 (-1 : BitVec 12) ≠ 0)
    (hNotPre : (c6 + signExtend12 (-1 : BitVec 12)).toNat ≠ 1) :
    expTwoMulFixedInductionFrameN exponentWord k c6 ptr =
      expTwoMulFixedSavedNextLimbFrameN exponentWord k ptr :=
  expTwoMulFixedInductionFrameN_ordinary
    (by
      rw [expTwoMulFixedControlDec_unfold]
      exact hC6)
    (by
      rw [expTwoMulFixedControlDec_unfold]
      exact hNotPre)


-- @@ L509-517 verbatim
theorem expTwoMulFixedInductionFrameN_succ_reload
    {exponentWord : EvmWord} {k : Nat} {ptr : Word} :
    expTwoMulFixedInductionFrameN exponentWord (k + 1) 64
        (ptr + signExtend12 (-8 : BitVec 12)) =
      expTwoMulFixedSavedNextLimbFrameN exponentWord (k + 1)
        (ptr + signExtend12 (-8 : BitVec 12)) := by
  apply expTwoMulFixedInductionFrameN_ordinary_of_control
  · decide
  · decide


-- @@ L519-534 verbatim
theorem expTwoMulFixedControlInvariant_succ_reload_with_induction_frame
    {exponentWord : EvmWord} {k : Nat}
    {c6 ptr loadedLimb nextNextLimb evmSp : Word}
    (hControl :
      expTwoMulFixedControlInvariant exponentWord k c6 ptr loadedLimb evmSp)
    (hC6 : c6 + signExtend12 (-1 : BitVec 12) = 0)
    (hNext :
      nextNextLimb = exponentWord.getLimbN (2 - (k + 1) / 64)) :
    expTwoMulFixedControlInvariant exponentWord (k + 1) 64
        (ptr + signExtend12 (-8 : BitVec 12)) nextNextLimb evmSp ∧
      expTwoMulFixedInductionFrameN exponentWord (k + 1) 64
          (ptr + signExtend12 (-8 : BitVec 12)) =
        expTwoMulFixedSavedNextLimbFrameN exponentWord (k + 1)
          (ptr + signExtend12 (-8 : BitVec 12)) := by
  exact ⟨expTwoMulFixedControlInvariant_succ_reload hControl hC6 hNext,
    expTwoMulFixedInductionFrameN_succ_reload⟩


-- @@ L536-556 verbatim
theorem expTwoMulFixedInductionFrameN_step_cases_of_control
    {exponentWord : EvmWord} {k : Nat}
    {c6 ptr nextLimb evmSp : Word}
    (hControl :
      expTwoMulFixedControlInvariant exponentWord k c6 ptr nextLimb evmSp) :
    expTwoMulFixedInductionFrameN exponentWord k c6 ptr =
        expTwoMulFixedReloadTailFrameN exponentWord k ptr ∨
      expTwoMulFixedInductionFrameN exponentWord k c6 ptr =
        expTwoMulFixedPreReloadFrameN exponentWord k ptr ∨
      (expTwoMulFixedInductionFrameN exponentWord k c6 ptr =
          expTwoMulFixedSavedNextLimbFrameN exponentWord k ptr ∧
        k % 64 < 62) := by
  rcases expTwoMulFixedControlInvariant_step_cases hControl with
    hReload | hPre | ⟨hOrd, hNotPre, hMod⟩
  · exact Or.inl
      (expTwoMulFixedInductionFrameN_reload_of_control hReload)
  · exact Or.inr (Or.inl
      (expTwoMulFixedInductionFrameN_pre_reload_of_control hPre))
  · exact Or.inr (Or.inr
      ⟨expTwoMulFixedInductionFrameN_ordinary_of_control hOrd hNotPre,
        hMod⟩)


-- @@ L558-588 verbatim
theorem expTwoMulFixedControlInvariant_succ_ordinary_with_induction_frame
    {exponentWord : EvmWord} {k : Nat}
    {c6 ptr nextLimb evmSp : Word}
    (hControl :
      expTwoMulFixedControlInvariant exponentWord k c6 ptr nextLimb evmSp)
    (hC6 : c6 + signExtend12 (-1 : BitVec 12) ≠ 0)
    (hSuccOrd : (k + 1) % 64 < 62) :
    expTwoMulFixedControlInvariant exponentWord (k + 1)
        (c6 + signExtend12 (-1 : BitVec 12)) ptr nextLimb evmSp ∧
      expTwoMulFixedInductionFrameN exponentWord (k + 1)
          (c6 + signExtend12 (-1 : BitVec 12)) ptr =
        expTwoMulFixedSavedNextLimbFrameN exponentWord (k + 1) ptr := by
  have hControlSucc :=
    expTwoMulFixedControlInvariant_succ_no_reload hControl hC6
  have hSuccNotReload :
      c6 + signExtend12 (-1 : BitVec 12) +
          signExtend12 (-1 : BitVec 12) ≠ 0 := by
    intro hReload
    have hMod :=
      expTwoMulFixedControlInvariant_reload_mod hControlSucc hReload
    omega
  have hSuccNotPre :
      (c6 + signExtend12 (-1 : BitVec 12) +
          signExtend12 (-1 : BitVec 12)).toNat ≠ 1 := by
    intro hPre
    have hMod :=
      expTwoMulFixedControlInvariant_pre_reload_mod hControlSucc hPre
    omega
  exact ⟨hControlSucc,
    expTwoMulFixedInductionFrameN_ordinary_of_control
      hSuccNotReload hSuccNotPre⟩


-- @@ L590-616 verbatim
theorem expTwoMulFixedControlInvariant_succ_pre_reload_with_induction_frame
    {exponentWord : EvmWord} {k : Nat}
    {c6 ptr nextLimb evmSp : Word}
    (hControl :
      expTwoMulFixedControlInvariant exponentWord k c6 ptr nextLimb evmSp)
    (hC6 : (c6 + signExtend12 (-1 : BitVec 12)).toNat = 1) :
    expTwoMulFixedControlInvariant exponentWord (k + 1)
        (c6 + signExtend12 (-1 : BitVec 12)) ptr nextLimb evmSp ∧
      expTwoMulFixedInductionFrameN exponentWord (k + 1)
          (c6 + signExtend12 (-1 : BitVec 12)) ptr =
        expTwoMulFixedReloadTailFrameN exponentWord (k + 1) ptr := by
  have hNonzero : c6 + signExtend12 (-1 : BitVec 12) ≠ 0 := by
    intro hZero
    have hNatZero : (c6 + signExtend12 (-1 : BitVec 12)).toNat = 0 := by
      rw [hZero]
      decide
    omega
  have hControlSucc :=
    expTwoMulFixedControlInvariant_succ_no_reload hControl hNonzero
  have hReload :
      c6 + signExtend12 (-1 : BitVec 12) +
          signExtend12 (-1 : BitVec 12) = 0 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, controlFrame_signExtend12_neg1_toNat, hC6]
    decide
  exact ⟨hControlSucc,
    expTwoMulFixedInductionFrameN_reload_of_control hReload⟩


-- @@ L618-635 verbatim
theorem expTwoMulFixedControlInvariant_succ_to_pre_reload_with_induction_frame
    {exponentWord : EvmWord} {k : Nat}
    {c6 ptr nextLimb evmSp : Word}
    (hControl :
      expTwoMulFixedControlInvariant exponentWord k c6 ptr nextLimb evmSp)
    (hC6 : c6 + signExtend12 (-1 : BitVec 12) ≠ 0)
    (hSuccPre :
      (c6 + signExtend12 (-1 : BitVec 12) +
          signExtend12 (-1 : BitVec 12)).toNat = 1) :
    expTwoMulFixedControlInvariant exponentWord (k + 1)
        (c6 + signExtend12 (-1 : BitVec 12)) ptr nextLimb evmSp ∧
      expTwoMulFixedInductionFrameN exponentWord (k + 1)
          (c6 + signExtend12 (-1 : BitVec 12)) ptr =
        expTwoMulFixedPreReloadFrameN exponentWord (k + 1) ptr := by
  have hControlSucc :=
    expTwoMulFixedControlInvariant_succ_no_reload hControl hC6
  exact ⟨hControlSucc,
    expTwoMulFixedInductionFrameN_pre_reload_of_control hSuccPre⟩


-- @@ L637-680 verbatim
theorem expTwoMulFixedControlInvariant_succ_no_reload_induction_frame_cases
    {exponentWord : EvmWord} {k : Nat}
    {c6 ptr nextLimb evmSp : Word}
    (hControl :
      expTwoMulFixedControlInvariant exponentWord k c6 ptr nextLimb evmSp)
    (hC6 : c6 + signExtend12 (-1 : BitVec 12) ≠ 0) :
    (expTwoMulFixedControlInvariant exponentWord (k + 1)
        (c6 + signExtend12 (-1 : BitVec 12)) ptr nextLimb evmSp ∧
      expTwoMulFixedInductionFrameN exponentWord (k + 1)
          (c6 + signExtend12 (-1 : BitVec 12)) ptr =
        expTwoMulFixedReloadTailFrameN exponentWord (k + 1) ptr) ∨
      (expTwoMulFixedControlInvariant exponentWord (k + 1)
          (c6 + signExtend12 (-1 : BitVec 12)) ptr nextLimb evmSp ∧
        expTwoMulFixedInductionFrameN exponentWord (k + 1)
            (c6 + signExtend12 (-1 : BitVec 12)) ptr =
          expTwoMulFixedPreReloadFrameN exponentWord (k + 1) ptr) ∨
      (expTwoMulFixedControlInvariant exponentWord (k + 1)
          (c6 + signExtend12 (-1 : BitVec 12)) ptr nextLimb evmSp ∧
        expTwoMulFixedInductionFrameN exponentWord (k + 1)
            (c6 + signExtend12 (-1 : BitVec 12)) ptr =
          expTwoMulFixedSavedNextLimbFrameN exponentWord (k + 1) ptr ∧
        (k + 1) % 64 < 62) := by
  by_cases hReload :
      c6 + signExtend12 (-1 : BitVec 12) +
          signExtend12 (-1 : BitVec 12) = 0
  · have hControlSucc :=
      expTwoMulFixedControlInvariant_succ_no_reload hControl hC6
    exact Or.inl
      ⟨hControlSucc, expTwoMulFixedInductionFrameN_reload_of_control hReload⟩
  · by_cases hSuccPre :
        (c6 + signExtend12 (-1 : BitVec 12) +
            signExtend12 (-1 : BitVec 12)).toNat = 1
    · exact Or.inr (Or.inl
        (expTwoMulFixedControlInvariant_succ_to_pre_reload_with_induction_frame
          hControl hC6 hSuccPre))
    · have hControlSucc :=
        expTwoMulFixedControlInvariant_succ_no_reload hControl hC6
      have hSuccOrd : (k + 1) % 64 < 62 :=
        expTwoMulFixedControlInvariant_ordinary_no_reload_mod
          hControlSucc hReload hSuccPre
      have hOrd :=
        expTwoMulFixedControlInvariant_succ_ordinary_with_induction_frame
          hControl hC6 hSuccOrd
      exact Or.inr (Or.inr ⟨hOrd.1, hOrd.2, hSuccOrd⟩)


-- @@ L682-690 verbatim
theorem expTwoMulFixedInductionFrameN_pcFree
    (exponentWord : EvmWord) (k : Nat) (c6 ptr : Word) :
    (expTwoMulFixedInductionFrameN exponentWord k c6 ptr).pcFree := by
  rw [expTwoMulFixedInductionFrameN]
  split
  · exact expTwoMulFixedReloadTailFrameN_pcFree exponentWord k ptr
  · split
    · exact expTwoMulFixedPreReloadFrameN_pcFree exponentWord k ptr
    · exact expTwoMulFixedSavedNextLimbFrameN_pcFree exponentWord k ptr


-- @@ L692-696 verbatim
instance pcFreeInst_expTwoMulFixedInductionFrameN
    (exponentWord : EvmWord) (k : Nat) (c6 ptr : Word) :
    Assertion.PCFree
      (expTwoMulFixedInductionFrameN exponentWord k c6 ptr) :=
  ⟨expTwoMulFixedInductionFrameN_pcFree exponentWord k c6 ptr⟩


-- @@ L698-706 verbatim
@[irreducible]
def expTwoMulFixedDirectHeadFrameN
    (exponentWord : EvmWord) (k : Nat) (c6 ptr : Word) : Assertion :=
  if expTwoMulFixedControlDec c6 = (0 : Word) then
    expTwoMulFixedReloadTailFrameN exponentWord k ptr
  else if (expTwoMulFixedControlDec c6).toNat = 1 then
    expTwoMulFixedPreReloadFrameN exponentWord k ptr
  else
    expTwoMulFixedSavedNextLimbFrameN exponentWord (k + 1) ptr


-- @@ L708-714 verbatim
theorem expTwoMulFixedDirectHeadFrameN_reload
    {exponentWord : EvmWord} {k : Nat} {c6 ptr : Word}
    (hC6 : expTwoMulFixedControlDec c6 = (0 : Word)) :
    expTwoMulFixedDirectHeadFrameN exponentWord k c6 ptr =
      expTwoMulFixedReloadTailFrameN exponentWord k ptr := by
  rw [expTwoMulFixedDirectHeadFrameN]
  simp [hC6]


-- @@ L716-729 verbatim
theorem expTwoMulFixedDirectHeadFrameN_pre_reload
    {exponentWord : EvmWord} {k : Nat} {c6 ptr : Word}
    (hC6 : (expTwoMulFixedControlDec c6).toNat = 1) :
    expTwoMulFixedDirectHeadFrameN exponentWord k c6 ptr =
      expTwoMulFixedPreReloadFrameN exponentWord k ptr := by
  rw [expTwoMulFixedDirectHeadFrameN]
  split
  · rename_i hZero
    have hNatZero :
        (expTwoMulFixedControlDec c6).toNat = 0 := by
      rw [hZero]
      decide
    omega
  · rfl


-- @@ L731-741 verbatim
theorem expTwoMulFixedDirectHeadFrameN_ordinary
    {exponentWord : EvmWord} {k : Nat} {c6 ptr : Word}
    (hC6 : expTwoMulFixedControlDec c6 ≠ (0 : Word))
    (hNotPre : (expTwoMulFixedControlDec c6).toNat ≠ 1) :
    expTwoMulFixedDirectHeadFrameN exponentWord k c6 ptr =
      expTwoMulFixedSavedNextLimbFrameN exponentWord (k + 1) ptr := by
  rw [expTwoMulFixedDirectHeadFrameN]
  split
  · rename_i hZero
    exact False.elim (hC6 hZero)
  · rfl


-- @@ L743-750 verbatim
theorem expTwoMulFixedDirectHeadFrameN_reload_of_control
    {exponentWord : EvmWord} {k : Nat} {c6 ptr : Word}
    (hC6 : c6 + signExtend12 (-1 : BitVec 12) = 0) :
    expTwoMulFixedDirectHeadFrameN exponentWord k c6 ptr =
      expTwoMulFixedReloadTailFrameN exponentWord k ptr :=
  expTwoMulFixedDirectHeadFrameN_reload (by
    rw [expTwoMulFixedControlDec_unfold]
    exact hC6)


-- @@ L752-759 verbatim
theorem expTwoMulFixedDirectHeadFrameN_pre_reload_of_control
    {exponentWord : EvmWord} {k : Nat} {c6 ptr : Word}
    (hC6 : (c6 + signExtend12 (-1 : BitVec 12)).toNat = 1) :
    expTwoMulFixedDirectHeadFrameN exponentWord k c6 ptr =
      expTwoMulFixedPreReloadFrameN exponentWord k ptr :=
  expTwoMulFixedDirectHeadFrameN_pre_reload (by
    rw [expTwoMulFixedControlDec_unfold]
    exact hC6)


-- @@ L761-773 verbatim
theorem expTwoMulFixedDirectHeadFrameN_ordinary_of_control
    {exponentWord : EvmWord} {k : Nat} {c6 ptr : Word}
    (hC6 : c6 + signExtend12 (-1 : BitVec 12) ≠ 0)
    (hNotPre : (c6 + signExtend12 (-1 : BitVec 12)).toNat ≠ 1) :
    expTwoMulFixedDirectHeadFrameN exponentWord k c6 ptr =
      expTwoMulFixedSavedNextLimbFrameN exponentWord (k + 1) ptr :=
  expTwoMulFixedDirectHeadFrameN_ordinary
    (by
      rw [expTwoMulFixedControlDec_unfold]
      exact hC6)
    (by
      rw [expTwoMulFixedControlDec_unfold]
      exact hNotPre)


-- @@ L775-783 verbatim
theorem expTwoMulFixedDirectHeadFrameN_pcFree
    (exponentWord : EvmWord) (k : Nat) (c6 ptr : Word) :
    (expTwoMulFixedDirectHeadFrameN exponentWord k c6 ptr).pcFree := by
  rw [expTwoMulFixedDirectHeadFrameN]
  split
  · exact expTwoMulFixedReloadTailFrameN_pcFree exponentWord k ptr
  · split
    · exact expTwoMulFixedPreReloadFrameN_pcFree exponentWord k ptr
    · exact expTwoMulFixedSavedNextLimbFrameN_pcFree exponentWord (k + 1) ptr


-- @@ L785-789 verbatim
instance pcFreeInst_expTwoMulFixedDirectHeadFrameN
    (exponentWord : EvmWord) (k : Nat) (c6 ptr : Word) :
    Assertion.PCFree
      (expTwoMulFixedDirectHeadFrameN exponentWord k c6 ptr) :=
  ⟨expTwoMulFixedDirectHeadFrameN_pcFree exponentWord k c6 ptr⟩


-- @@ L791-797 verbatim
theorem expTwoMulFixedControlInvariant_nextLimb
    {exponentWord : EvmWord} {k : Nat}
    {c6 ptr nextLimb evmSp : Word}
    (hControl :
      expTwoMulFixedControlInvariant exponentWord k c6 ptr nextLimb evmSp) :
    nextLimb = exponentWord.getLimbN (2 - k / 64) := by
  exact hControl.2


-- @@ L799-811 verbatim
theorem expTwoMulFixedControlInvariant_nextLimb_succ_no_reload
    {exponentWord : EvmWord} {k : Nat}
    {c6 ptr nextLimb evmSp : Word}
    (hControl :
      expTwoMulFixedControlInvariant exponentWord k c6 ptr nextLimb evmSp)
    (hC6 : c6 + signExtend12 (-1 : BitVec 12) ≠ 0) :
    nextLimb = exponentWord.getLimbN (2 - (k + 1) / 64) := by
  have hMod :=
    expTwoMulFixedControlInvariant_no_reload_mod hControl hC6
  rw [expTwoMulFixedControlInvariant_nextLimb hControl]
  have hdiv : (k + 1) / 64 = k / 64 := by
    omega
  rw [hdiv]


-- @@ L813-813 verbatim
end EvmAsm.Evm64.Exp.Compose
