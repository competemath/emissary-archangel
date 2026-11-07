/-
  EvmAsm.Evm64.DivMod.SpecPredicates

  EvmWord-level wrappers around the Word-tuple runtime condition predicates
  used by the n=4 stack-level DIV/MOD specs.

  Each definition is a thin shim over a Word-level predicate plus a `_def`
  `rfl` lemma. Extracted from `Spec.lean` to keep that file under the file-size
  guardrail. No content changes — every definition / `_def` lemma here is
  byte-identical to its previous home in `Spec.lean`.
-/

module

public import EvmAsm.Evm64.DivMod.Compose.FullPathN4
public import EvmAsm.Evm64.DivMod.Compose.FullPathN4Beq
public import EvmAsm.Evm64.DivMod.Compose.FullPathN4CallV4NoNop
public import EvmAsm.Evm64.DivMod.Compose.FullPathN4BeqV4NoNop
public import EvmAsm.Evm64.EvmWordArith.MaxTrialVacuity


-- @@ L21-21 verbatim
@[expose] public section


-- @@ L23-23 verbatim
namespace EvmAsm.Evm64


-- @@ L25-35 verbatim
open EvmAsm.Rv64

-- ============================================================================
-- EvmWord-level runtime condition predicates for the n=4 max path
-- ============================================================================

-- The full-path DIV spec `evm_div_n4_full_max_skip_spec` takes runtime
-- conditions (`isMaxTrialN4`, `isSkipBorrowN4Max`) keyed off eight Word
-- limbs. For the EvmWord-level stack spec, it's more natural to express
-- these on `a b : EvmWord` directly — the wrappers below defer to the
-- Word-level predicates via `a.getLimbN k` / `b.getLimbN k`.


-- @@ L37-41 verbatim
/-- Max trial quotient condition at n=4 in EvmWord form: `u4 ≥ b3'` after
    normalization, i.e., the algorithm uses the maximum trial quotient
    (`signExtend12 4095 = 2^64 - 1`). -/
def isMaxTrialN4Evm (a b : EvmWord) : Prop :=
  isMaxTrialN4 (a.getLimbN 3) (b.getLimbN 2) (b.getLimbN 3)


-- @@ L43-48 verbatim
/-- Skip-addback condition at n=4 max in EvmWord form: the runtime borrow
    check `u4 < mulsubN4_c3` does not fire, so the algorithm skips the
    addback step and uses `qHat` as the quotient digit. -/
def isSkipBorrowN4MaxEvm (a b : EvmWord) : Prop :=
  isSkipBorrowN4Max (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
                    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)


-- @@ L50-54 verbatim
/-- Call trial condition at n=4 in EvmWord form: `u4 < b3'` after
    normalization, i.e., the max trial is too large so the algorithm falls
    through to `div128` for a tighter quotient. -/
def isCallTrialN4Evm (a b : EvmWord) : Prop :=
  isCallTrialN4 (a.getLimbN 3) (b.getLimbN 2) (b.getLimbN 3)


-- @@ L56-61 verbatim
/-- Skip-addback condition at n=4 call path in EvmWord form: the runtime
    borrow check does not fire, so the algorithm skips addback after the
    `div128`-computed trial quotient. -/
def isSkipBorrowN4CallEvm (a b : EvmWord) : Prop :=
  isSkipBorrowN4Call (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
                     (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)


-- @@ L63-68 verbatim
/-- Addback-needed condition at n=4 call path in EvmWord form: the runtime
    borrow check fires, so the algorithm decrements the trial quotient and
    adds back `v` to the partial remainder. -/
def isAddbackBorrowN4CallEvm (a b : EvmWord) : Prop :=
  isAddbackBorrowN4Call (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
                        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)


-- @@ L70-72 verbatim
theorem isCallTrialN4Evm_def {a b : EvmWord} :
    isCallTrialN4Evm a b =
    isCallTrialN4 (a.getLimbN 3) (b.getLimbN 2) (b.getLimbN 3) := rfl


-- @@ L74-90 verbatim
/-- **Call-trial holds automatically at n=4 under `hshift_nz`** — EvmWord form.

    Direct corollary of the Word-level `isCallTrialN4_of_shift_nz`
    (`EvmWordArith.MaxTrialVacuity`). Under shift-normalization (`shift ≠ 0`),
    `u4 < b3'` always, so the BLTU runtime check picks the `div128` call path
    rather than the max-trial path.

    Dispatcher trivializer: `evm_div_n4_shift_nz_stack_spec` and
    `evm_mod_n4_shift_nz_stack_spec` use this to discharge the max branch via
    `exfalso`. See `memory/project_n4_shift_nz_dispatcher_plan.md`. -/
theorem isCallTrialN4Evm_of_shift_nz (a b : EvmWord)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0) :
    isCallTrialN4Evm a b := by
  rw [isCallTrialN4Evm_def]
  exact isCallTrialN4_of_shift_nz (a.getLimbN 3) (b.getLimbN 2) (b.getLimbN 3)
    hb3nz hshift_nz


-- @@ L92-95 verbatim
theorem isSkipBorrowN4CallEvm_def {a b : EvmWord} :
    isSkipBorrowN4CallEvm a b =
    isSkipBorrowN4Call (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
                       (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) := rfl


-- @@ L97-100 verbatim
theorem isAddbackBorrowN4CallEvm_def {a b : EvmWord} :
    isAddbackBorrowN4CallEvm a b =
    isAddbackBorrowN4Call (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
                          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) := rfl


-- @@ L102-107 verbatim
/-- Carry-2-non-zero condition at n=4 call path in EvmWord form: the
    double-addback branch indicator used by the BEQ variant. Wraps the
    raw-limb form `isAddbackCarry2NzN4CallAb`. -/
def isAddbackCarry2NzN4CallEvm (a b : EvmWord) : Prop :=
  isAddbackCarry2NzN4CallAb (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
                            (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)


-- @@ L109-116 verbatim
theorem isAddbackCarry2NzN4CallEvm_def {a b : EvmWord} :
    isAddbackCarry2NzN4CallEvm a b =
    isAddbackCarry2NzN4CallAb (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
                              (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) := rfl

-- ============================================================================
-- EvmWord-level runtime condition predicates for the n=4 v4 call path
-- ============================================================================


-- @@ L118-121 verbatim
/-- Skip-addback condition at n=4 v4 call path in EvmWord form. -/
def isSkipBorrowN4CallV4Evm (a b : EvmWord) : Prop :=
  isSkipBorrowN4CallV4Ab (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
                         (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)


-- @@ L123-126 verbatim
/-- Addback-needed condition at n=4 v4 call path in EvmWord form. -/
def isAddbackBorrowN4CallV4Evm (a b : EvmWord) : Prop :=
  isAddbackBorrowN4CallV4Ab (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
                            (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)


-- @@ L128-131 verbatim
/-- Carry-2-non-zero condition at n=4 v4 call path in EvmWord form. -/
def isAddbackCarry2NzN4CallV4Evm (a b : EvmWord) : Prop :=
  isAddbackCarry2NzN4CallV4Ab (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
                              (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)


-- @@ L133-136 verbatim
theorem isSkipBorrowN4CallV4Evm_def {a b : EvmWord} :
    isSkipBorrowN4CallV4Evm a b =
    isSkipBorrowN4CallV4Ab (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
                           (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) := rfl


-- @@ L138-141 verbatim
theorem isAddbackBorrowN4CallV4Evm_def {a b : EvmWord} :
    isAddbackBorrowN4CallV4Evm a b =
    isAddbackBorrowN4CallV4Ab (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
                              (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) := rfl


-- @@ L143-146 verbatim
theorem isAddbackCarry2NzN4CallV4Evm_def {a b : EvmWord} :
    isAddbackCarry2NzN4CallV4Evm a b =
    isAddbackCarry2NzN4CallV4Ab (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
                                (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) := rfl


-- @@ L148-177 verbatim
/-- Eliminate the packaged EvmWord v4 n=4 call-addback carry2 predicate to
    the raw implication consumed by double-addback loop-body proofs. -/
theorem isAddbackCarry2NzN4CallV4Evm_raw {a b : EvmWord}
    (hcarry2_nz : isAddbackCarry2NzN4CallV4Evm a b) :
    let shift := (clzResult (b.getLimbN 3)).1
    let antiShift := signExtend12 (0 : BitVec 12) - shift
    let b3' := ((b.getLimbN 3) <<< (shift.toNat % 64)) |||
      ((b.getLimbN 2) >>> (antiShift.toNat % 64))
    let b2' := ((b.getLimbN 2) <<< (shift.toNat % 64)) |||
      ((b.getLimbN 1) >>> (antiShift.toNat % 64))
    let b1' := ((b.getLimbN 1) <<< (shift.toNat % 64)) |||
      ((b.getLimbN 0) >>> (antiShift.toNat % 64))
    let b0' := (b.getLimbN 0) <<< (shift.toNat % 64)
    let u4 := (a.getLimbN 3) >>> (antiShift.toNat % 64)
    let u3 := ((a.getLimbN 3) <<< (shift.toNat % 64)) |||
      ((a.getLimbN 2) >>> (antiShift.toNat % 64))
    let u2 := ((a.getLimbN 2) <<< (shift.toNat % 64)) |||
      ((a.getLimbN 1) >>> (antiShift.toNat % 64))
    let u1 := ((a.getLimbN 1) <<< (shift.toNat % 64)) |||
      ((a.getLimbN 0) >>> (antiShift.toNat % 64))
    let u0 := (a.getLimbN 0) <<< (shift.toNat % 64)
    let qHat := divKTrialCallV4QHat u4 u3 b3'
    let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
    let c3 := ms.2.2.2.2
    let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 b0' b1' b2' b3'
    let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 (u4 - c3) b0' b1' b2' b3'
    carry = 0 →
      addbackN4_carry ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 b0' b1' b2' b3' ≠ 0 := by
  rw [isAddbackCarry2NzN4CallV4Evm_def] at hcarry2_nz
  exact isAddbackCarry2NzN4CallV4Ab_raw hcarry2_nz


-- @@ L179-205 verbatim
/-- If the first v4 call-addback carry is already nonzero, the carry2
    predicate holds vacuously: the double-addback premise `carry = 0` is false. -/
theorem isAddbackCarry2NzN4CallV4Evm_of_first_carry_ne_zero {a b : EvmWord}
    (hcarry_nz :
      let shift := (clzResult (b.getLimbN 3)).1
      let antiShift := signExtend12 (0 : BitVec 12) - shift
      let b3' := ((b.getLimbN 3) <<< (shift.toNat % 64)) |||
        ((b.getLimbN 2) >>> (antiShift.toNat % 64))
      let b2' := ((b.getLimbN 2) <<< (shift.toNat % 64)) |||
        ((b.getLimbN 1) >>> (antiShift.toNat % 64))
      let b1' := ((b.getLimbN 1) <<< (shift.toNat % 64)) |||
        ((b.getLimbN 0) >>> (antiShift.toNat % 64))
      let b0' := (b.getLimbN 0) <<< (shift.toNat % 64)
      let u4 := (a.getLimbN 3) >>> (antiShift.toNat % 64)
      let u3 := ((a.getLimbN 3) <<< (shift.toNat % 64)) |||
        ((a.getLimbN 2) >>> (antiShift.toNat % 64))
      let u2 := ((a.getLimbN 2) <<< (shift.toNat % 64)) |||
        ((a.getLimbN 1) >>> (antiShift.toNat % 64))
      let u1 := ((a.getLimbN 1) <<< (shift.toNat % 64)) |||
        ((a.getLimbN 0) >>> (antiShift.toNat % 64))
      let u0 := (a.getLimbN 0) <<< (shift.toNat % 64)
      let qHat := divKTrialCallV4QHat u4 u3 b3'
      let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
      addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 b0' b1' b2' b3' ≠ 0) :
    isAddbackCarry2NzN4CallV4Evm a b := by
  rw [isAddbackCarry2NzN4CallV4Evm_def]
  exact isAddbackCarry2NzN4CallV4Ab_of_first_carry_ne_zero hcarry_nz


-- @@ L207-207 verbatim
end EvmAsm.Evm64
