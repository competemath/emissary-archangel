/-
  EvmAsm.Evm64.DivMod.Spec.CallAddback

  Call+addback BEQ semantic predicate marker (n=4, shift ≠ 0).

  Contents:
  - the predicate below, retained only as the Phase 2a algorithm-fix target
    marker.
  - a small rfl unfolding theorem.

  The former stack specs, qHat sub-stubs, and Word-level Euclideans were
  deleted after they were found to depend transitively on the false n=4 addback
  semantic premise.
-/

module

public import EvmAsm.Evm64.DivMod.Spec.CallSkip
public import EvmAsm.Evm64.DivMod.Spec.CallSkipUnconditional
public import EvmAsm.Evm64.DivMod.LoopBody.TrialCallBounds
public import EvmAsm.Evm64.DivMod.LoopDefs.IterV4


-- @@ L23-23 verbatim
@[expose] public section


-- @@ L25-25 verbatim
namespace EvmAsm.Evm64


-- @@ L27-27 verbatim
open EvmAsm.Rv64

-- @@ L28-28 verbatim
open EvmAsm.Rv64.AddrNorm (word_add_zero)

-- @@ L29-29 verbatim
open EvmWord (val256)

-- @@ L30-34 verbatim
open EvmAsm.Rv64.Tactics

-- ============================================================================
-- Call+addback BEQ semantic predicate marker (n=4, shift ≠ 0)
-- ============================================================================


-- @@ L36-79 verbatim
/-- Semantic-correctness precondition for the n=4 call+addback-BEQ sub-path
    under the repaired v4 trial quotient: the final `q_out`
    (= `qHat - 1` single-addback or `qHat - 2` double-addback) equals
    `⌊val256(a)/val256(b)⌋`.

    Unlike `n4CallSkipSemanticHolds`, which states a lower-bound on the raw
    trial quotient, this predicate directly states that the post-addback
    corrected quotient is the true quotient. The old v1 marker used
    `div128Quot`; that version was false on runtime-reachable inputs because
    the one-correction quotient could overshoot by a 2^32-scale amount. The
    executable DIV/MOD paths now use `div128Quot_v4`, which performs the
    repaired two-correction trial quotient. The runtime-condition closure is
    `n4CallAddbackBeqSemanticHolds_of_runtime_conditions` in
    `CallAddbackRuntime.lean`: it routes through the v4 predicate, combines
    the v4 quotient-overestimate bound with the addback-borrow/carry facts and
    the normalized remainder bound, then transports the result back to this
    historical predicate spelling via `n4CallAddbackBeqSemanticHolds_eq_v4`. -/
def n4CallAddbackBeqSemanticHolds (a b : EvmWord) : Prop :=
  let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
  let antiShift := (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
  let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
  let b2' := ((b.getLimbN 2) <<< shift) ||| ((b.getLimbN 1) >>> antiShift)
  let b1' := ((b.getLimbN 1) <<< shift) ||| ((b.getLimbN 0) >>> antiShift)
  let b0' := (b.getLimbN 0) <<< shift
  let u4 := (a.getLimbN 3) >>> antiShift
  let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
  let u2 := ((a.getLimbN 2) <<< shift) ||| ((a.getLimbN 1) >>> antiShift)
  let u1 := ((a.getLimbN 1) <<< shift) ||| ((a.getLimbN 0) >>> antiShift)
  let u0 := (a.getLimbN 0) <<< shift
  let qHat := div128Quot_v4 u4 u3 b3'
  let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
  let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 b0' b1' b2' b3'
  let q_out : Word :=
    if carry = 0 then qHat + signExtend12 4095 + signExtend12 4095
    else qHat + signExtend12 4095
  q_out.toNat =
    val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) /
      val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)

-- The v1 counterexample, v2 fix-verification, v2-buggy-confirmation and
-- the v2 mirror predicate (plus its
-- sanity check on the v1 counterexample input) live in
-- `EvmAsm/Evm64/DivMod/Spec/CallAddbackCounterexamples.lean` (extracted
-- 2026 toward the #1078 file-size cap; see beads evm-asm-b5i).





-- @@ L84-107 verbatim
theorem n4CallAddbackBeqSemantic_unfold {a b : EvmWord} :
    n4CallAddbackBeqSemanticHolds a b =
    (let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
     let antiShift :=
       (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
     let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
     let b2' := ((b.getLimbN 2) <<< shift) ||| ((b.getLimbN 1) >>> antiShift)
     let b1' := ((b.getLimbN 1) <<< shift) ||| ((b.getLimbN 0) >>> antiShift)
     let b0' := (b.getLimbN 0) <<< shift
     let u4 := (a.getLimbN 3) >>> antiShift
     let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
     let u2 := ((a.getLimbN 2) <<< shift) ||| ((a.getLimbN 1) >>> antiShift)
     let u1 := ((a.getLimbN 1) <<< shift) ||| ((a.getLimbN 0) >>> antiShift)
     let u0 := (a.getLimbN 0) <<< shift
     let qHat := div128Quot_v4 u4 u3 b3'
     let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
     let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 b0' b1' b2' b3'
     let q_out : Word :=
       if carry = 0 then qHat + signExtend12 4095 + signExtend12 4095
       else qHat + signExtend12 4095
     q_out.toNat =
       val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) /
         val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) :=
  rfl


-- @@ L109-111 verbatim
/-- CLZ normalization shift used by the n=4 v4 call+addback-BEQ marker. -/
def n4CallAddbackBeqShift (b : EvmWord) : Nat :=
  (clzResult (b.getLimbN 3)).1.toNat % 64


-- @@ L113-115 verbatim
theorem n4CallAddbackBeqShift_unfold {b : EvmWord} :
    n4CallAddbackBeqShift b = (clzResult (b.getLimbN 3)).1.toNat % 64 :=
  rfl


-- @@ L117-120 verbatim
theorem n4CallAddbackBeqShift_raw_lt_64 {b : EvmWord} :
    (clzResult (b.getLimbN 3)).1.toNat < 64 := by
  have h_le := clzResult_fst_toNat_le (b.getLimbN 3)
  omega


-- @@ L122-125 verbatim
theorem n4CallAddbackBeqShift_eq_raw {b : EvmWord} :
    n4CallAddbackBeqShift b = (clzResult (b.getLimbN 3)).1.toNat := by
  rw [n4CallAddbackBeqShift_unfold]
  exact Nat.mod_eq_of_lt n4CallAddbackBeqShift_raw_lt_64


-- @@ L127-135 verbatim
theorem n4CallAddbackBeqShift_pos_of_ne_zero {b : EvmWord}
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0) :
    0 < n4CallAddbackBeqShift b := by
  rw [n4CallAddbackBeqShift_eq_raw]
  rcases Nat.eq_zero_or_pos (clzResult (b.getLimbN 3)).1.toNat with h_zero | h_pos
  · exfalso
    apply hshift_nz
    exact BitVec.eq_of_toNat_eq (by simp [h_zero])
  · exact h_pos


-- @@ L137-139 verbatim
/-- Anti-shift used by the n=4 v4 call+addback-BEQ marker. -/
def n4CallAddbackBeqAntiShift (b : EvmWord) : Nat :=
  (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64


-- @@ L141-144 verbatim
theorem n4CallAddbackBeqAntiShift_unfold {b : EvmWord} :
    n4CallAddbackBeqAntiShift b =
      (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64 :=
  rfl


-- @@ L146-155 verbatim
theorem n4CallAddbackBeqAntiShift_eq_sub_shift {b : EvmWord}
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0) :
    n4CallAddbackBeqAntiShift b = 64 - n4CallAddbackBeqShift b := by
  have h_pos_raw : 1 ≤ (clzResult (b.getLimbN 3)).1.toNat := by
    rw [← n4CallAddbackBeqShift_eq_raw]
    exact n4CallAddbackBeqShift_pos_of_ne_zero hshift_nz
  rw [n4CallAddbackBeqAntiShift_unfold, n4CallAddbackBeqShift_eq_raw]
  exact antiShift_toNat_mod_eq
    h_pos_raw
    (clzResult_fst_toNat_le (b.getLimbN 3))


-- @@ L157-160 verbatim
/-- Normalized top divisor limb used by the n=4 v4 call+addback-BEQ marker. -/
def n4CallAddbackBeqB3Prime (b : EvmWord) : Word :=
  ((b.getLimbN 3) <<< n4CallAddbackBeqShift b) |||
    ((b.getLimbN 2) >>> n4CallAddbackBeqAntiShift b)


-- @@ L162-166 verbatim
theorem n4CallAddbackBeqB3Prime_unfold {b : EvmWord} :
    n4CallAddbackBeqB3Prime b =
      ((b.getLimbN 3) <<< n4CallAddbackBeqShift b) |||
        ((b.getLimbN 2) >>> n4CallAddbackBeqAntiShift b) :=
  rfl


-- @@ L168-175 verbatim
theorem n4CallAddbackBeqB3Prime_eq_direct {b : EvmWord}
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0) :
    n4CallAddbackBeqB3Prime b =
      ((b.getLimbN 3) <<< (clzResult (b.getLimbN 3)).1.toNat) |||
        ((b.getLimbN 2) >>> (64 - (clzResult (b.getLimbN 3)).1.toNat)) := by
  rw [n4CallAddbackBeqB3Prime_unfold]
  rw [n4CallAddbackBeqShift_eq_raw, n4CallAddbackBeqAntiShift_eq_sub_shift hshift_nz]
  rw [n4CallAddbackBeqShift_eq_raw]


-- @@ L177-191 verbatim
theorem n4CallAddbackBeqB3Prime_ge_pow63 {b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0) :
    (n4CallAddbackBeqB3Prime b).toNat ≥ 2^63 := by
  rw [n4CallAddbackBeqB3Prime_unfold]
  rw [n4CallAddbackBeqShift_unfold, n4CallAddbackBeqAntiShift_unfold]
  have h_shifted := b3_shifted_ge_pow63 hb3nz
  have h_or_ge :
      ((((b.getLimbN 3) <<< ((clzResult (b.getLimbN 3)).1.toNat % 64))) |||
        ((b.getLimbN 2) >>>
          ((signExtend12 (0 : BitVec 12) -
            (clzResult (b.getLimbN 3)).1).toNat % 64))).toNat ≥
        ((b.getLimbN 3) <<< ((clzResult (b.getLimbN 3)).1.toNat % 64)).toNat := by
    rw [BitVec.toNat_or]
    exact Nat.left_le_or
  exact le_trans h_shifted h_or_ge


-- @@ L193-199 verbatim
theorem n4CallAddbackBeqDHi_ge_pow31 {b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0) :
    (divKTrialCallV4DHi (n4CallAddbackBeqB3Prime b)).toNat ≥ 2^31 := by
  rw [divKTrialCallV4DHi_eq]
  exact div128Quot_shift0_dHi_ge
    (n4CallAddbackBeqB3Prime b)
    (n4CallAddbackBeqB3Prime_ge_pow63 hb3nz)


-- @@ L201-204 verbatim
theorem n4CallAddbackBeqDHi_lt_pow32 {b : EvmWord} :
    (divKTrialCallV4DHi (n4CallAddbackBeqB3Prime b)).toNat < 2^32 := by
  rw [divKTrialCallV4DHi_eq]
  exact hi32_toNat_lt_pow32 (n4CallAddbackBeqB3Prime b)


-- @@ L206-209 verbatim
theorem n4CallAddbackBeqDLo_lt_pow32 {b : EvmWord} :
    (divKTrialCallV4DLo (n4CallAddbackBeqB3Prime b)).toNat < 2^32 := by
  rw [divKTrialCallV4DLo_eq]
  exact lo32_toNat_lt_pow32 (n4CallAddbackBeqB3Prime b)


-- @@ L211-214 verbatim
/-- Normalized divisor limb 2 used by the n=4 v4 call+addback-BEQ marker. -/
def n4CallAddbackBeqB2Prime (b : EvmWord) : Word :=
  ((b.getLimbN 2) <<< n4CallAddbackBeqShift b) |||
    ((b.getLimbN 1) >>> n4CallAddbackBeqAntiShift b)


-- @@ L216-220 verbatim
theorem n4CallAddbackBeqB2Prime_unfold {b : EvmWord} :
    n4CallAddbackBeqB2Prime b =
      ((b.getLimbN 2) <<< n4CallAddbackBeqShift b) |||
        ((b.getLimbN 1) >>> n4CallAddbackBeqAntiShift b) :=
  rfl


-- @@ L222-229 verbatim
theorem n4CallAddbackBeqB2Prime_eq_direct {b : EvmWord}
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0) :
    n4CallAddbackBeqB2Prime b =
      ((b.getLimbN 2) <<< (clzResult (b.getLimbN 3)).1.toNat) |||
        ((b.getLimbN 1) >>> (64 - (clzResult (b.getLimbN 3)).1.toNat)) := by
  rw [n4CallAddbackBeqB2Prime_unfold]
  rw [n4CallAddbackBeqShift_eq_raw, n4CallAddbackBeqAntiShift_eq_sub_shift hshift_nz]
  rw [n4CallAddbackBeqShift_eq_raw]


-- @@ L231-234 verbatim
/-- Normalized divisor limb 1 used by the n=4 v4 call+addback-BEQ marker. -/
def n4CallAddbackBeqB1Prime (b : EvmWord) : Word :=
  ((b.getLimbN 1) <<< n4CallAddbackBeqShift b) |||
    ((b.getLimbN 0) >>> n4CallAddbackBeqAntiShift b)


-- @@ L236-240 verbatim
theorem n4CallAddbackBeqB1Prime_unfold {b : EvmWord} :
    n4CallAddbackBeqB1Prime b =
      ((b.getLimbN 1) <<< n4CallAddbackBeqShift b) |||
        ((b.getLimbN 0) >>> n4CallAddbackBeqAntiShift b) :=
  rfl


-- @@ L242-249 verbatim
theorem n4CallAddbackBeqB1Prime_eq_direct {b : EvmWord}
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0) :
    n4CallAddbackBeqB1Prime b =
      ((b.getLimbN 1) <<< (clzResult (b.getLimbN 3)).1.toNat) |||
        ((b.getLimbN 0) >>> (64 - (clzResult (b.getLimbN 3)).1.toNat)) := by
  rw [n4CallAddbackBeqB1Prime_unfold]
  rw [n4CallAddbackBeqShift_eq_raw, n4CallAddbackBeqAntiShift_eq_sub_shift hshift_nz]
  rw [n4CallAddbackBeqShift_eq_raw]


-- @@ L251-253 verbatim
/-- Normalized divisor limb 0 used by the n=4 v4 call+addback-BEQ marker. -/
def n4CallAddbackBeqB0Prime (b : EvmWord) : Word :=
  (b.getLimbN 0) <<< n4CallAddbackBeqShift b


-- @@ L255-258 verbatim
theorem n4CallAddbackBeqB0Prime_unfold {b : EvmWord} :
    n4CallAddbackBeqB0Prime b =
      (b.getLimbN 0) <<< n4CallAddbackBeqShift b :=
  rfl


-- @@ L260-265 verbatim
theorem n4CallAddbackBeqB0Prime_eq_direct {b : EvmWord}
    (_hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0) :
    n4CallAddbackBeqB0Prime b =
      (b.getLimbN 0) <<< (clzResult (b.getLimbN 3)).1.toNat := by
  rw [n4CallAddbackBeqB0Prime_unfold]
  rw [n4CallAddbackBeqShift_eq_raw]


-- @@ L267-269 verbatim
/-- Normalized overflow dividend limb used by the n=4 v4 call+addback-BEQ marker. -/
def n4CallAddbackBeqU4 (a b : EvmWord) : Word :=
  (a.getLimbN 3) >>> n4CallAddbackBeqAntiShift b


-- @@ L271-274 verbatim
theorem n4CallAddbackBeqU4_unfold {a b : EvmWord} :
    n4CallAddbackBeqU4 a b =
      (a.getLimbN 3) >>> n4CallAddbackBeqAntiShift b :=
  rfl


-- @@ L276-282 verbatim
theorem n4CallAddbackBeqU4_eq_direct {a b : EvmWord}
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0) :
    n4CallAddbackBeqU4 a b =
      (a.getLimbN 3) >>> (64 - (clzResult (b.getLimbN 3)).1.toNat) := by
  rw [n4CallAddbackBeqU4_unfold]
  rw [n4CallAddbackBeqAntiShift_eq_sub_shift hshift_nz]
  rw [n4CallAddbackBeqShift_eq_raw]


-- @@ L284-296 verbatim
theorem n4CallAddbackBeqU4_lt_vTop_of_call {a b : EvmWord}
    (hcall : isCallTrialN4 (a.getLimbN 3) (b.getLimbN 2) (b.getLimbN 3)) :
    (n4CallAddbackBeqU4 a b).toNat <
      (divKTrialCallV4DHi (n4CallAddbackBeqB3Prime b)).toNat * 2^32 +
        (divKTrialCallV4DLo (n4CallAddbackBeqB3Prime b)).toNat := by
  have h_u4_lt_b3' :=
    isCallTrialN4_toNat_lt (a.getLimbN 3) (b.getLimbN 2) (b.getLimbN 3) hcall
  rw [divKTrialCallV4DHi_eq, divKTrialCallV4DLo_eq]
  rw [← div128Quot_vTop_decomp (n4CallAddbackBeqB3Prime b)]
  rw [n4CallAddbackBeqU4_unfold, n4CallAddbackBeqAntiShift_unfold,
    n4CallAddbackBeqB3Prime_unfold, n4CallAddbackBeqShift_unfold,
    n4CallAddbackBeqAntiShift_unfold]
  exact h_u4_lt_b3'


-- @@ L298-301 verbatim
/-- Normalized top in-range dividend limb used by the n=4 v4 call+addback-BEQ marker. -/
def n4CallAddbackBeqU3 (a b : EvmWord) : Word :=
  ((a.getLimbN 3) <<< n4CallAddbackBeqShift b) |||
    ((a.getLimbN 2) >>> n4CallAddbackBeqAntiShift b)


-- @@ L303-307 verbatim
theorem n4CallAddbackBeqU3_unfold {a b : EvmWord} :
    n4CallAddbackBeqU3 a b =
      ((a.getLimbN 3) <<< n4CallAddbackBeqShift b) |||
        ((a.getLimbN 2) >>> n4CallAddbackBeqAntiShift b) :=
  rfl


-- @@ L309-316 verbatim
theorem n4CallAddbackBeqU3_eq_direct {a b : EvmWord}
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0) :
    n4CallAddbackBeqU3 a b =
      ((a.getLimbN 3) <<< (clzResult (b.getLimbN 3)).1.toNat) |||
        ((a.getLimbN 2) >>> (64 - (clzResult (b.getLimbN 3)).1.toNat)) := by
  rw [n4CallAddbackBeqU3_unfold]
  rw [n4CallAddbackBeqShift_eq_raw, n4CallAddbackBeqAntiShift_eq_sub_shift hshift_nz]
  rw [n4CallAddbackBeqShift_eq_raw]


-- @@ L318-321 verbatim
/-- Normalized dividend limb 2 used by the n=4 v4 call+addback-BEQ marker. -/
def n4CallAddbackBeqU2 (a b : EvmWord) : Word :=
  ((a.getLimbN 2) <<< n4CallAddbackBeqShift b) |||
    ((a.getLimbN 1) >>> n4CallAddbackBeqAntiShift b)


-- @@ L323-327 verbatim
theorem n4CallAddbackBeqU2_unfold {a b : EvmWord} :
    n4CallAddbackBeqU2 a b =
      ((a.getLimbN 2) <<< n4CallAddbackBeqShift b) |||
        ((a.getLimbN 1) >>> n4CallAddbackBeqAntiShift b) :=
  rfl


-- @@ L329-336 verbatim
theorem n4CallAddbackBeqU2_eq_direct {a b : EvmWord}
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0) :
    n4CallAddbackBeqU2 a b =
      ((a.getLimbN 2) <<< (clzResult (b.getLimbN 3)).1.toNat) |||
        ((a.getLimbN 1) >>> (64 - (clzResult (b.getLimbN 3)).1.toNat)) := by
  rw [n4CallAddbackBeqU2_unfold]
  rw [n4CallAddbackBeqShift_eq_raw, n4CallAddbackBeqAntiShift_eq_sub_shift hshift_nz]
  rw [n4CallAddbackBeqShift_eq_raw]


-- @@ L338-341 verbatim
/-- Normalized dividend limb 1 used by the n=4 v4 call+addback-BEQ marker. -/
def n4CallAddbackBeqU1 (a b : EvmWord) : Word :=
  ((a.getLimbN 1) <<< n4CallAddbackBeqShift b) |||
    ((a.getLimbN 0) >>> n4CallAddbackBeqAntiShift b)


-- @@ L343-347 verbatim
theorem n4CallAddbackBeqU1_unfold {a b : EvmWord} :
    n4CallAddbackBeqU1 a b =
      ((a.getLimbN 1) <<< n4CallAddbackBeqShift b) |||
        ((a.getLimbN 0) >>> n4CallAddbackBeqAntiShift b) :=
  rfl


-- @@ L349-356 verbatim
theorem n4CallAddbackBeqU1_eq_direct {a b : EvmWord}
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0) :
    n4CallAddbackBeqU1 a b =
      ((a.getLimbN 1) <<< (clzResult (b.getLimbN 3)).1.toNat) |||
        ((a.getLimbN 0) >>> (64 - (clzResult (b.getLimbN 3)).1.toNat)) := by
  rw [n4CallAddbackBeqU1_unfold]
  rw [n4CallAddbackBeqShift_eq_raw, n4CallAddbackBeqAntiShift_eq_sub_shift hshift_nz]
  rw [n4CallAddbackBeqShift_eq_raw]


-- @@ L358-360 verbatim
/-- Normalized dividend limb 0 used by the n=4 v4 call+addback-BEQ marker. -/
def n4CallAddbackBeqU0 (a b : EvmWord) : Word :=
  (a.getLimbN 0) <<< n4CallAddbackBeqShift b


-- @@ L362-365 verbatim
theorem n4CallAddbackBeqU0_unfold {a b : EvmWord} :
    n4CallAddbackBeqU0 a b =
      (a.getLimbN 0) <<< n4CallAddbackBeqShift b :=
  rfl


-- @@ L367-372 verbatim
theorem n4CallAddbackBeqU0_eq_direct {a b : EvmWord}
    (_hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0) :
    n4CallAddbackBeqU0 a b =
      (a.getLimbN 0) <<< (clzResult (b.getLimbN 3)).1.toNat := by
  rw [n4CallAddbackBeqU0_unfold]
  rw [n4CallAddbackBeqShift_eq_raw]


-- @@ L374-381 verbatim
/-- Trial quotient used by the n=4 v4 call+addback-BEQ semantic marker. -/
def n4CallAddbackBeqQHatV4 (a b : EvmWord) : Word :=
  let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
  let antiShift := (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
  let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
  let u4 := (a.getLimbN 3) >>> antiShift
  let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
  div128Quot_v4 u4 u3 b3'


-- @@ L383-392 verbatim
theorem n4CallAddbackBeqQHatV4_unfold {a b : EvmWord} :
    n4CallAddbackBeqQHatV4 a b =
      (let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
       let antiShift :=
         (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
       let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
       let u4 := (a.getLimbN 3) >>> antiShift
       let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
       div128Quot_v4 u4 u3 b3') :=
  rfl


-- @@ L394-400 verbatim
theorem n4CallAddbackBeqQHatV4_eq_normalized {a b : EvmWord} :
    n4CallAddbackBeqQHatV4 a b =
      div128Quot_v4
        (n4CallAddbackBeqU4 a b)
        (n4CallAddbackBeqU3 a b)
        (n4CallAddbackBeqB3Prime b) :=
  rfl


-- @@ L402-414 verbatim
theorem n4CallAddbackBeqQHatV4_eq_direct {a b : EvmWord}
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0) :
    n4CallAddbackBeqQHatV4 a b =
      div128Quot_v4
        ((a.getLimbN 3) >>> (64 - (clzResult (b.getLimbN 3)).1.toNat))
        (((a.getLimbN 3) <<< (clzResult (b.getLimbN 3)).1.toNat) |||
          ((a.getLimbN 2) >>> (64 - (clzResult (b.getLimbN 3)).1.toNat)))
        (((b.getLimbN 3) <<< (clzResult (b.getLimbN 3)).1.toNat) |||
          ((b.getLimbN 2) >>> (64 - (clzResult (b.getLimbN 3)).1.toNat))) := by
  rw [n4CallAddbackBeqQHatV4_eq_normalized]
  rw [n4CallAddbackBeqU4_eq_direct hshift_nz]
  rw [n4CallAddbackBeqU3_eq_direct hshift_nz]
  rw [n4CallAddbackBeqB3Prime_eq_direct hshift_nz]


-- @@ L416-423 verbatim
theorem n4CallAddbackBeqQHatV4_eq_trialCallQHat {a b : EvmWord} :
    n4CallAddbackBeqQHatV4 a b =
      divKTrialCallV4QHat
        (n4CallAddbackBeqU4 a b)
        (n4CallAddbackBeqU3 a b)
        (n4CallAddbackBeqB3Prime b) := by
  rw [n4CallAddbackBeqQHatV4_eq_normalized]
  rw [divKTrialCallV4QHat_eq_div128Quot_v4]


-- @@ L425-455 verbatim
theorem n4CallAddbackBeqQHatV4_toNat_eq_trialCall_halves_of_un21_lt
    {a b : EvmWord}
    (hdHi_ge : (divKTrialCallV4DHi (n4CallAddbackBeqB3Prime b)).toNat ≥ 2^31)
    (hdHi_lt : (divKTrialCallV4DHi (n4CallAddbackBeqB3Prime b)).toNat < 2^32)
    (hdLo_lt : (divKTrialCallV4DLo (n4CallAddbackBeqB3Prime b)).toNat < 2^32)
    (hu4_lt_vTop :
      (n4CallAddbackBeqU4 a b).toNat <
        (divKTrialCallV4DHi (n4CallAddbackBeqB3Prime b)).toNat * 2^32 +
          (divKTrialCallV4DLo (n4CallAddbackBeqB3Prime b)).toNat)
    (hUn21_lt_vTop :
      (divKTrialCallV4Un21
        (n4CallAddbackBeqU4 a b)
        (n4CallAddbackBeqU3 a b)
        (n4CallAddbackBeqB3Prime b)).toNat <
        (divKTrialCallV4DHi (n4CallAddbackBeqB3Prime b)).toNat * 2^32 +
          (divKTrialCallV4DLo (n4CallAddbackBeqB3Prime b)).toNat) :
    (n4CallAddbackBeqQHatV4 a b).toNat =
      (divKTrialCallV4Q1dd
        (n4CallAddbackBeqU4 a b)
        (n4CallAddbackBeqU3 a b)
        (n4CallAddbackBeqB3Prime b)).toNat * 2^32 +
        (divKTrialCallV4Q0dd
          (n4CallAddbackBeqU4 a b)
          (n4CallAddbackBeqU3 a b)
          (n4CallAddbackBeqB3Prime b)).toNat := by
  rw [n4CallAddbackBeqQHatV4_eq_normalized]
  exact div128Quot_v4_toNat_eq_trialCall_halves_of_un21_lt
    (n4CallAddbackBeqU4 a b)
    (n4CallAddbackBeqU3 a b)
    (n4CallAddbackBeqB3Prime b)
    hdHi_ge hdHi_lt hdLo_lt hu4_lt_vTop hUn21_lt_vTop


-- @@ L457-484 verbatim
theorem n4CallAddbackBeqQHatV4_toNat_eq_trialCall_halves_of_runtime_bounds
    {a b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hu4_lt_vTop :
      (n4CallAddbackBeqU4 a b).toNat <
        (divKTrialCallV4DHi (n4CallAddbackBeqB3Prime b)).toNat * 2^32 +
          (divKTrialCallV4DLo (n4CallAddbackBeqB3Prime b)).toNat)
    (hUn21_lt_vTop :
      (divKTrialCallV4Un21
        (n4CallAddbackBeqU4 a b)
        (n4CallAddbackBeqU3 a b)
        (n4CallAddbackBeqB3Prime b)).toNat <
        (divKTrialCallV4DHi (n4CallAddbackBeqB3Prime b)).toNat * 2^32 +
          (divKTrialCallV4DLo (n4CallAddbackBeqB3Prime b)).toNat) :
    (n4CallAddbackBeqQHatV4 a b).toNat =
      (divKTrialCallV4Q1dd
        (n4CallAddbackBeqU4 a b)
        (n4CallAddbackBeqU3 a b)
        (n4CallAddbackBeqB3Prime b)).toNat * 2^32 +
        (divKTrialCallV4Q0dd
          (n4CallAddbackBeqU4 a b)
          (n4CallAddbackBeqU3 a b)
          (n4CallAddbackBeqB3Prime b)).toNat := by
  exact n4CallAddbackBeqQHatV4_toNat_eq_trialCall_halves_of_un21_lt
    (n4CallAddbackBeqDHi_ge_pow31 hb3nz)
    n4CallAddbackBeqDHi_lt_pow32
    n4CallAddbackBeqDLo_lt_pow32
    hu4_lt_vTop hUn21_lt_vTop


-- @@ L486-509 verbatim
theorem n4CallAddbackBeqQHatV4_toNat_eq_trialCall_halves_of_call
    {a b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hcall : isCallTrialN4 (a.getLimbN 3) (b.getLimbN 2) (b.getLimbN 3))
    (hUn21_lt_vTop :
      (divKTrialCallV4Un21
        (n4CallAddbackBeqU4 a b)
        (n4CallAddbackBeqU3 a b)
        (n4CallAddbackBeqB3Prime b)).toNat <
        (divKTrialCallV4DHi (n4CallAddbackBeqB3Prime b)).toNat * 2^32 +
          (divKTrialCallV4DLo (n4CallAddbackBeqB3Prime b)).toNat) :
    (n4CallAddbackBeqQHatV4 a b).toNat =
      (divKTrialCallV4Q1dd
        (n4CallAddbackBeqU4 a b)
        (n4CallAddbackBeqU3 a b)
        (n4CallAddbackBeqB3Prime b)).toNat * 2^32 +
        (divKTrialCallV4Q0dd
          (n4CallAddbackBeqU4 a b)
          (n4CallAddbackBeqU3 a b)
          (n4CallAddbackBeqB3Prime b)).toNat := by
  exact n4CallAddbackBeqQHatV4_toNat_eq_trialCall_halves_of_runtime_bounds
    hb3nz
    (n4CallAddbackBeqU4_lt_vTop_of_call hcall)
    hUn21_lt_vTop


-- @@ L511-526 verbatim
theorem n4CallAddbackBeqUn21_lt_vTop_of_lt_b3prime {a b : EvmWord}
    (hUn21_lt_b3prime :
      (divKTrialCallV4Un21
        (n4CallAddbackBeqU4 a b)
        (n4CallAddbackBeqU3 a b)
        (n4CallAddbackBeqB3Prime b)).toNat <
        (n4CallAddbackBeqB3Prime b).toNat) :
    (divKTrialCallV4Un21
      (n4CallAddbackBeqU4 a b)
      (n4CallAddbackBeqU3 a b)
      (n4CallAddbackBeqB3Prime b)).toNat <
      (divKTrialCallV4DHi (n4CallAddbackBeqB3Prime b)).toNat * 2^32 +
        (divKTrialCallV4DLo (n4CallAddbackBeqB3Prime b)).toNat := by
  rw [divKTrialCallV4DHi_eq, divKTrialCallV4DLo_eq]
  rw [← div128Quot_vTop_decomp (n4CallAddbackBeqB3Prime b)]
  exact hUn21_lt_b3prime


-- @@ L528-550 verbatim
theorem n4CallAddbackBeqQHatV4_toNat_eq_trialCall_halves_of_call_un21_lt_b3prime
    {a b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hcall : isCallTrialN4 (a.getLimbN 3) (b.getLimbN 2) (b.getLimbN 3))
    (hUn21_lt_b3prime :
      (divKTrialCallV4Un21
        (n4CallAddbackBeqU4 a b)
        (n4CallAddbackBeqU3 a b)
        (n4CallAddbackBeqB3Prime b)).toNat <
        (n4CallAddbackBeqB3Prime b).toNat) :
    (n4CallAddbackBeqQHatV4 a b).toNat =
      (divKTrialCallV4Q1dd
        (n4CallAddbackBeqU4 a b)
        (n4CallAddbackBeqU3 a b)
        (n4CallAddbackBeqB3Prime b)).toNat * 2^32 +
        (divKTrialCallV4Q0dd
          (n4CallAddbackBeqU4 a b)
          (n4CallAddbackBeqU3 a b)
          (n4CallAddbackBeqB3Prime b)).toNat := by
  exact n4CallAddbackBeqQHatV4_toNat_eq_trialCall_halves_of_call
    hb3nz
    hcall
    (n4CallAddbackBeqUn21_lt_vTop_of_lt_b3prime hUn21_lt_b3prime)


-- @@ L552-579 verbatim
theorem n4CallAddbackBeqRawTrialBound_direct {a b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hcall : isCallTrialN4 (a.getLimbN 3) (b.getLimbN 2) (b.getLimbN 3)) :
    (((a.getLimbN 3) >>> (64 - (clzResult (b.getLimbN 3)).1.toNat)).toNat * 2^64 +
        (((a.getLimbN 3) <<< (clzResult (b.getLimbN 3)).1.toNat) |||
          ((a.getLimbN 2) >>> (64 - (clzResult (b.getLimbN 3)).1.toNat))).toNat) /
      (((b.getLimbN 3) <<< (clzResult (b.getLimbN 3)).1.toNat) |||
        ((b.getLimbN 2) >>> (64 - (clzResult (b.getLimbN 3)).1.toNat))).toNat ≤
    val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) /
      val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) + 2 := by
  have h_shift_pos : 1 ≤ (clzResult (b.getLimbN 3)).1.toNat := by
    rw [← n4CallAddbackBeqShift_eq_raw]
    exact n4CallAddbackBeqShift_pos_of_ne_zero hshift_nz
  have hsmod :
      (clzResult (b.getLimbN 3)).1.toNat % 64 =
        (clzResult (b.getLimbN 3)).1.toNat :=
    Nat.mod_eq_of_lt (by have := clzResult_fst_toNat_le (b.getLimbN 3); omega)
  have hasmod :
      (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64 =
        64 - (clzResult (b.getLimbN 3)).1.toNat :=
    antiShift_toNat_mod_eq h_shift_pos (clzResult_fst_toNat_le (b.getLimbN 3))
  have h := knuth_theorem_b_from_clz
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    hb3nz hshift_nz hcall
  rw [hsmod, hasmod] at h
  exact h


-- @@ L581-597 verbatim
theorem n4CallAddbackBeqQHatV4_le_val256_div_plus_two_of_le_rawTrial
    {a b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hcall : isCallTrialN4 (a.getLimbN 3) (b.getLimbN 2) (b.getLimbN 3))
    (hq_le_raw :
      (n4CallAddbackBeqQHatV4 a b).toNat ≤
        (((a.getLimbN 3) >>> (64 - (clzResult (b.getLimbN 3)).1.toNat)).toNat * 2^64 +
            (((a.getLimbN 3) <<< (clzResult (b.getLimbN 3)).1.toNat) |||
              ((a.getLimbN 2) >>> (64 - (clzResult (b.getLimbN 3)).1.toNat))).toNat) /
          (((b.getLimbN 3) <<< (clzResult (b.getLimbN 3)).1.toNat) |||
            ((b.getLimbN 2) >>> (64 - (clzResult (b.getLimbN 3)).1.toNat))).toNat) :
    (n4CallAddbackBeqQHatV4 a b).toNat ≤
      val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) /
        val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) + 2 := by
  exact le_trans hq_le_raw
    (n4CallAddbackBeqRawTrialBound_direct hb3nz hshift_nz hcall)


-- @@ L599-613 verbatim
/-- First addback carry used by the n=4 v4 call+addback-BEQ semantic marker. -/
def n4CallAddbackBeqCarryV4 (a b : EvmWord) : Word :=
  let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
  let antiShift := (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
  let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
  let b2' := ((b.getLimbN 2) <<< shift) ||| ((b.getLimbN 1) >>> antiShift)
  let b1' := ((b.getLimbN 1) <<< shift) ||| ((b.getLimbN 0) >>> antiShift)
  let b0' := (b.getLimbN 0) <<< shift
  let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
  let u2 := ((a.getLimbN 2) <<< shift) ||| ((a.getLimbN 1) >>> antiShift)
  let u1 := ((a.getLimbN 1) <<< shift) ||| ((a.getLimbN 0) >>> antiShift)
  let u0 := (a.getLimbN 0) <<< shift
  let qHat := n4CallAddbackBeqQHatV4 a b
  let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
  addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 b0' b1' b2' b3'


-- @@ L615-631 verbatim
theorem n4CallAddbackBeqCarryV4_unfold {a b : EvmWord} :
    n4CallAddbackBeqCarryV4 a b =
      (let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
       let antiShift :=
         (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
       let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
       let b2' := ((b.getLimbN 2) <<< shift) ||| ((b.getLimbN 1) >>> antiShift)
       let b1' := ((b.getLimbN 1) <<< shift) ||| ((b.getLimbN 0) >>> antiShift)
       let b0' := (b.getLimbN 0) <<< shift
       let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
       let u2 := ((a.getLimbN 2) <<< shift) ||| ((a.getLimbN 1) >>> antiShift)
       let u1 := ((a.getLimbN 1) <<< shift) ||| ((a.getLimbN 0) >>> antiShift)
       let u0 := (a.getLimbN 0) <<< shift
       let qHat := n4CallAddbackBeqQHatV4 a b
       let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
       addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 b0' b1' b2' b3') :=
  rfl


-- @@ L633-650 verbatim
theorem n4CallAddbackBeqCarryV4_eq_normalized {a b : EvmWord} :
    n4CallAddbackBeqCarryV4 a b =
      (let qHat := n4CallAddbackBeqQHatV4 a b
       let ms := mulsubN4 qHat
        (n4CallAddbackBeqB0Prime b)
        (n4CallAddbackBeqB1Prime b)
        (n4CallAddbackBeqB2Prime b)
        (n4CallAddbackBeqB3Prime b)
        (n4CallAddbackBeqU0 a b)
        (n4CallAddbackBeqU1 a b)
        (n4CallAddbackBeqU2 a b)
        (n4CallAddbackBeqU3 a b)
       addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1
        (n4CallAddbackBeqB0Prime b)
        (n4CallAddbackBeqB1Prime b)
        (n4CallAddbackBeqB2Prime b)
        (n4CallAddbackBeqB3Prime b)) :=
  rfl


-- @@ L652-691 verbatim
theorem n4CallAddbackBeqCarryV4_eq_direct {a b : EvmWord}
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0) :
    n4CallAddbackBeqCarryV4 a b =
      (let b3' :=
        ((b.getLimbN 3) <<< (clzResult (b.getLimbN 3)).1.toNat) |||
          ((b.getLimbN 2) >>> (64 - (clzResult (b.getLimbN 3)).1.toNat))
       let b2' :=
        ((b.getLimbN 2) <<< (clzResult (b.getLimbN 3)).1.toNat) |||
          ((b.getLimbN 1) >>> (64 - (clzResult (b.getLimbN 3)).1.toNat))
       let b1' :=
        ((b.getLimbN 1) <<< (clzResult (b.getLimbN 3)).1.toNat) |||
          ((b.getLimbN 0) >>> (64 - (clzResult (b.getLimbN 3)).1.toNat))
       let b0' := (b.getLimbN 0) <<< (clzResult (b.getLimbN 3)).1.toNat
       let u3 :=
        ((a.getLimbN 3) <<< (clzResult (b.getLimbN 3)).1.toNat) |||
          ((a.getLimbN 2) >>> (64 - (clzResult (b.getLimbN 3)).1.toNat))
       let u2 :=
        ((a.getLimbN 2) <<< (clzResult (b.getLimbN 3)).1.toNat) |||
          ((a.getLimbN 1) >>> (64 - (clzResult (b.getLimbN 3)).1.toNat))
       let u1 :=
        ((a.getLimbN 1) <<< (clzResult (b.getLimbN 3)).1.toNat) |||
          ((a.getLimbN 0) >>> (64 - (clzResult (b.getLimbN 3)).1.toNat))
       let u0 := (a.getLimbN 0) <<< (clzResult (b.getLimbN 3)).1.toNat
       let qHat :=
        div128Quot_v4
          ((a.getLimbN 3) >>> (64 - (clzResult (b.getLimbN 3)).1.toNat))
          u3
          b3'
       let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
       addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 b0' b1' b2' b3') := by
  rw [n4CallAddbackBeqCarryV4_eq_normalized]
  rw [n4CallAddbackBeqQHatV4_eq_direct hshift_nz]
  rw [n4CallAddbackBeqB0Prime_eq_direct hshift_nz]
  rw [n4CallAddbackBeqB1Prime_eq_direct hshift_nz]
  rw [n4CallAddbackBeqB2Prime_eq_direct hshift_nz]
  rw [n4CallAddbackBeqB3Prime_eq_direct hshift_nz]
  rw [n4CallAddbackBeqU0_eq_direct hshift_nz]
  rw [n4CallAddbackBeqU1_eq_direct hshift_nz]
  rw [n4CallAddbackBeqU2_eq_direct hshift_nz]
  rw [n4CallAddbackBeqU3_eq_direct hshift_nz]


-- @@ L693-698 verbatim
/-- Corrected quotient produced by the n=4 v4 call+addback-BEQ semantic marker. -/
def n4CallAddbackBeqQOutV4 (a b : EvmWord) : Word :=
  let qHat := n4CallAddbackBeqQHatV4 a b
  let carry := n4CallAddbackBeqCarryV4 a b
  if carry = 0 then qHat + signExtend12 4095 + signExtend12 4095
  else qHat + signExtend12 4095


-- @@ L700-706 verbatim
theorem n4CallAddbackBeqQOutV4_unfold {a b : EvmWord} :
    n4CallAddbackBeqQOutV4 a b =
      (let qHat := n4CallAddbackBeqQHatV4 a b
       let carry := n4CallAddbackBeqCarryV4 a b
       if carry = 0 then qHat + signExtend12 4095 + signExtend12 4095
       else qHat + signExtend12 4095) :=
  rfl


-- @@ L708-727 verbatim
theorem n4CallAddbackBeqQOutV4_raw_unfold {a b : EvmWord} :
    n4CallAddbackBeqQOutV4 a b =
      (let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
       let antiShift :=
         (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
       let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
       let b2' := ((b.getLimbN 2) <<< shift) ||| ((b.getLimbN 1) >>> antiShift)
       let b1' := ((b.getLimbN 1) <<< shift) ||| ((b.getLimbN 0) >>> antiShift)
       let b0' := (b.getLimbN 0) <<< shift
       let u4 := (a.getLimbN 3) >>> antiShift
       let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
       let u2 := ((a.getLimbN 2) <<< shift) ||| ((a.getLimbN 1) >>> antiShift)
       let u1 := ((a.getLimbN 1) <<< shift) ||| ((a.getLimbN 0) >>> antiShift)
       let u0 := (a.getLimbN 0) <<< shift
       let qHat := div128Quot_v4 u4 u3 b3'
       let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
       let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 b0' b1' b2' b3'
       if carry = 0 then qHat + signExtend12 4095 + signExtend12 4095
       else qHat + signExtend12 4095) :=
  rfl


-- @@ L729-763 verbatim
theorem n4CallAddbackBeqQOutV4_eq_direct {a b : EvmWord}
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0) :
    n4CallAddbackBeqQOutV4 a b =
      (let b3' :=
        ((b.getLimbN 3) <<< (clzResult (b.getLimbN 3)).1.toNat) |||
          ((b.getLimbN 2) >>> (64 - (clzResult (b.getLimbN 3)).1.toNat))
       let b2' :=
        ((b.getLimbN 2) <<< (clzResult (b.getLimbN 3)).1.toNat) |||
          ((b.getLimbN 1) >>> (64 - (clzResult (b.getLimbN 3)).1.toNat))
       let b1' :=
        ((b.getLimbN 1) <<< (clzResult (b.getLimbN 3)).1.toNat) |||
          ((b.getLimbN 0) >>> (64 - (clzResult (b.getLimbN 3)).1.toNat))
       let b0' := (b.getLimbN 0) <<< (clzResult (b.getLimbN 3)).1.toNat
       let u3 :=
        ((a.getLimbN 3) <<< (clzResult (b.getLimbN 3)).1.toNat) |||
          ((a.getLimbN 2) >>> (64 - (clzResult (b.getLimbN 3)).1.toNat))
       let u2 :=
        ((a.getLimbN 2) <<< (clzResult (b.getLimbN 3)).1.toNat) |||
          ((a.getLimbN 1) >>> (64 - (clzResult (b.getLimbN 3)).1.toNat))
       let u1 :=
        ((a.getLimbN 1) <<< (clzResult (b.getLimbN 3)).1.toNat) |||
          ((a.getLimbN 0) >>> (64 - (clzResult (b.getLimbN 3)).1.toNat))
       let u0 := (a.getLimbN 0) <<< (clzResult (b.getLimbN 3)).1.toNat
       let qHat :=
        div128Quot_v4
          ((a.getLimbN 3) >>> (64 - (clzResult (b.getLimbN 3)).1.toNat))
          u3
          b3'
       let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
       let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 b0' b1' b2' b3'
       if carry = 0 then qHat + signExtend12 4095 + signExtend12 4095
       else qHat + signExtend12 4095) := by
  rw [n4CallAddbackBeqQOutV4_unfold]
  rw [n4CallAddbackBeqQHatV4_eq_direct hshift_nz]
  rw [n4CallAddbackBeqCarryV4_eq_direct hshift_nz]


-- @@ L765-814 verbatim
/-- On the addback branch, the loop iterator's quotient output agrees with the
    v4 call+addback-BEQ marker quotient. -/
theorem n4CallAddbackBeqIterWithDoubleAddback_qOutV4_of_borrow {a b : EvmWord}
    (h_borrow :
      BitVec.ult (n4CallAddbackBeqU4 a b)
        (mulsubN4
          (n4CallAddbackBeqQHatV4 a b)
          (n4CallAddbackBeqB0Prime b)
          (n4CallAddbackBeqB1Prime b)
          (n4CallAddbackBeqB2Prime b)
          (n4CallAddbackBeqB3Prime b)
          (n4CallAddbackBeqU0 a b)
          (n4CallAddbackBeqU1 a b)
          (n4CallAddbackBeqU2 a b)
          (n4CallAddbackBeqU3 a b)).2.2.2.2) :
    (iterWithDoubleAddback
      (n4CallAddbackBeqQHatV4 a b)
      (n4CallAddbackBeqB0Prime b)
      (n4CallAddbackBeqB1Prime b)
      (n4CallAddbackBeqB2Prime b)
      (n4CallAddbackBeqB3Prime b)
      (n4CallAddbackBeqU0 a b)
      (n4CallAddbackBeqU1 a b)
      (n4CallAddbackBeqU2 a b)
      (n4CallAddbackBeqU3 a b)
      (n4CallAddbackBeqU4 a b)).1 =
      n4CallAddbackBeqQOutV4 a b := by
  have h_iter := iterWithDoubleAddback_borrow h_borrow
  have h_fst := congrArg Prod.fst h_iter
  have h_carry_eq := n4CallAddbackBeqCarryV4_eq_normalized (a := a) (b := b)
  by_cases h_carry : n4CallAddbackBeqCarryV4 a b = 0
  · rw [← h_carry_eq] at h_fst
    rw [if_pos h_carry] at h_fst
    rw [n4CallAddbackBeqQOutV4_unfold, h_carry]
    exact h_fst
  · have h_carry_norm : ¬
        (let qHat := n4CallAddbackBeqQHatV4 a b
         let ms := mulsubN4 qHat
          (n4CallAddbackBeqB0Prime b) (n4CallAddbackBeqB1Prime b)
          (n4CallAddbackBeqB2Prime b) (n4CallAddbackBeqB3Prime b)
          (n4CallAddbackBeqU0 a b) (n4CallAddbackBeqU1 a b)
          (n4CallAddbackBeqU2 a b) (n4CallAddbackBeqU3 a b)
         addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1
          (n4CallAddbackBeqB0Prime b) (n4CallAddbackBeqB1Prime b)
          (n4CallAddbackBeqB2Prime b) (n4CallAddbackBeqB3Prime b)) = 0 := by
      intro h_norm
      exact h_carry (h_carry_eq.trans h_norm)
    rw [if_neg h_carry_norm] at h_fst
    rw [n4CallAddbackBeqQOutV4_unfold, if_neg h_carry]
    exact h_fst


-- @@ L816-821 verbatim
/-- The zero-carry call+addback-BEQ case decrements the trial quotient twice. -/
theorem n4CallAddbackBeqQOutV4_of_carry_eq_zero {a b : EvmWord}
    (h_carry : n4CallAddbackBeqCarryV4 a b = 0) :
    n4CallAddbackBeqQOutV4 a b =
      n4CallAddbackBeqQHatV4 a b + signExtend12 4095 + signExtend12 4095 := by
  simp [n4CallAddbackBeqQOutV4, h_carry]


-- @@ L823-829 verbatim
/-- The nonzero-carry call+addback-BEQ case decrements the trial quotient once. -/
theorem n4CallAddbackBeqQOutV4_of_carry_ne_zero {a b : EvmWord}
    (h_carry : n4CallAddbackBeqCarryV4 a b ≠ 0) :
    n4CallAddbackBeqQOutV4 a b =
      n4CallAddbackBeqQHatV4 a b + signExtend12 4095 := by
  rw [n4CallAddbackBeqQOutV4]
  rw [if_neg h_carry]


-- @@ L831-836 verbatim
/-- `toNat` form of the zero-carry double-decrement qOut case. -/
theorem n4CallAddbackBeqQOutV4_toNat_of_carry_eq_zero {a b : EvmWord}
    (h_carry : n4CallAddbackBeqCarryV4 a b = 0) :
    (n4CallAddbackBeqQOutV4 a b).toNat =
      (n4CallAddbackBeqQHatV4 a b + signExtend12 4095 + signExtend12 4095).toNat := by
  rw [n4CallAddbackBeqQOutV4_of_carry_eq_zero h_carry]


-- @@ L838-843 verbatim
/-- `toNat` form of the nonzero-carry single-decrement qOut case. -/
theorem n4CallAddbackBeqQOutV4_toNat_of_carry_ne_zero {a b : EvmWord}
    (h_carry : n4CallAddbackBeqCarryV4 a b ≠ 0) :
    (n4CallAddbackBeqQOutV4 a b).toNat =
      (n4CallAddbackBeqQHatV4 a b + signExtend12 4095).toNat := by
  rw [n4CallAddbackBeqQOutV4_of_carry_ne_zero h_carry]


-- @@ L845-848 verbatim
/-- True 256-bit quotient targeted by the n=4 v4 call+addback-BEQ marker. -/
def n4CallAddbackBeqQTrue (a b : EvmWord) : Nat :=
  val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) /
    val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)


-- @@ L850-854 verbatim
theorem n4CallAddbackBeqQTrue_unfold {a b : EvmWord} :
    n4CallAddbackBeqQTrue a b =
      val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) /
        val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) :=
  rfl


-- @@ L856-861 verbatim
theorem eq_n4CallAddbackBeqQTrue_iff {a b : EvmWord} {q : Nat} :
    q = n4CallAddbackBeqQTrue a b ↔
      q =
        val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) /
          val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) :=
  Iff.rfl


-- @@ L863-868 verbatim
theorem n4CallAddbackBeqQTrue_eq_iff {a b : EvmWord} {q : Nat} :
    n4CallAddbackBeqQTrue a b = q ↔
      val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) /
          val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) =
        q :=
  Iff.rfl


-- @@ L870-877 verbatim
/-- Carry-selected qHat equality targeted by the v4 n=4 call+addback-BEQ marker. -/
def n4CallAddbackBeqQHatBranchEqQTrue (a b : EvmWord) : Prop :=
  if n4CallAddbackBeqCarryV4 a b = 0 then
    (n4CallAddbackBeqQHatV4 a b + signExtend12 4095 + signExtend12 4095).toNat =
      n4CallAddbackBeqQTrue a b
  else
    (n4CallAddbackBeqQHatV4 a b + signExtend12 4095).toNat =
      n4CallAddbackBeqQTrue a b


-- @@ L879-887 verbatim
theorem n4CallAddbackBeqQHatBranchEqQTrue_unfold {a b : EvmWord} :
    n4CallAddbackBeqQHatBranchEqQTrue a b =
      if n4CallAddbackBeqCarryV4 a b = 0 then
        (n4CallAddbackBeqQHatV4 a b + signExtend12 4095 + signExtend12 4095).toNat =
          n4CallAddbackBeqQTrue a b
      else
        (n4CallAddbackBeqQHatV4 a b + signExtend12 4095).toNat =
          n4CallAddbackBeqQTrue a b :=
  rfl


-- @@ L889-894 verbatim
theorem n4CallAddbackBeqQHatBranchEqQTrue_carry_eq_zero_iff {a b : EvmWord}
    (h_carry : n4CallAddbackBeqCarryV4 a b = 0) :
    n4CallAddbackBeqQHatBranchEqQTrue a b ↔
      (n4CallAddbackBeqQHatV4 a b + signExtend12 4095 + signExtend12 4095).toNat =
        n4CallAddbackBeqQTrue a b := by
  rw [n4CallAddbackBeqQHatBranchEqQTrue, if_pos h_carry]


-- @@ L896-901 verbatim
theorem n4CallAddbackBeqQHatBranchEqQTrue_carry_ne_zero_iff {a b : EvmWord}
    (h_carry : n4CallAddbackBeqCarryV4 a b ≠ 0) :
    n4CallAddbackBeqQHatBranchEqQTrue a b ↔
      (n4CallAddbackBeqQHatV4 a b + signExtend12 4095).toNat =
        n4CallAddbackBeqQTrue a b := by
  rw [n4CallAddbackBeqQHatBranchEqQTrue, if_neg h_carry]


-- @@ L903-909 verbatim
theorem n4CallAddbackBeqQHatBranchEqQTrue_of_carry_eq_zero {a b : EvmWord}
    (h_carry : n4CallAddbackBeqCarryV4 a b = 0)
    (h_qHat :
      (n4CallAddbackBeqQHatV4 a b + signExtend12 4095 + signExtend12 4095).toNat =
        n4CallAddbackBeqQTrue a b) :
    n4CallAddbackBeqQHatBranchEqQTrue a b :=
  (n4CallAddbackBeqQHatBranchEqQTrue_carry_eq_zero_iff h_carry).2 h_qHat


-- @@ L911-916 verbatim
theorem n4CallAddbackBeqQHatBranchEqQTrue_carry_eq_zero {a b : EvmWord}
    (h_carry : n4CallAddbackBeqCarryV4 a b = 0)
    (h_qHat : n4CallAddbackBeqQHatBranchEqQTrue a b) :
    (n4CallAddbackBeqQHatV4 a b + signExtend12 4095 + signExtend12 4095).toNat =
      n4CallAddbackBeqQTrue a b :=
  (n4CallAddbackBeqQHatBranchEqQTrue_carry_eq_zero_iff h_carry).1 h_qHat


-- @@ L918-924 verbatim
theorem n4CallAddbackBeqQHatBranchEqQTrue_of_carry_ne_zero {a b : EvmWord}
    (h_carry : n4CallAddbackBeqCarryV4 a b ≠ 0)
    (h_qHat :
      (n4CallAddbackBeqQHatV4 a b + signExtend12 4095).toNat =
        n4CallAddbackBeqQTrue a b) :
    n4CallAddbackBeqQHatBranchEqQTrue a b :=
  (n4CallAddbackBeqQHatBranchEqQTrue_carry_ne_zero_iff h_carry).2 h_qHat


-- @@ L926-931 verbatim
theorem n4CallAddbackBeqQHatBranchEqQTrue_carry_ne_zero {a b : EvmWord}
    (h_carry : n4CallAddbackBeqCarryV4 a b ≠ 0)
    (h_qHat : n4CallAddbackBeqQHatBranchEqQTrue a b) :
    (n4CallAddbackBeqQHatV4 a b + signExtend12 4095).toNat =
      n4CallAddbackBeqQTrue a b :=
  (n4CallAddbackBeqQHatBranchEqQTrue_carry_ne_zero_iff h_carry).1 h_qHat


-- @@ L933-938 verbatim
theorem n4CallAddbackBeqQOutV4_toNat_eq_qTrue_carry_eq_zero_iff {a b : EvmWord}
    (h_carry : n4CallAddbackBeqCarryV4 a b = 0) :
    (n4CallAddbackBeqQOutV4 a b).toNat = n4CallAddbackBeqQTrue a b ↔
      (n4CallAddbackBeqQHatV4 a b + signExtend12 4095 + signExtend12 4095).toNat =
        n4CallAddbackBeqQTrue a b := by
  rw [n4CallAddbackBeqQOutV4_toNat_of_carry_eq_zero h_carry]


-- @@ L940-945 verbatim
theorem n4CallAddbackBeqQOutV4_toNat_eq_qTrue_carry_ne_zero_iff {a b : EvmWord}
    (h_carry : n4CallAddbackBeqCarryV4 a b ≠ 0) :
    (n4CallAddbackBeqQOutV4 a b).toNat = n4CallAddbackBeqQTrue a b ↔
      (n4CallAddbackBeqQHatV4 a b + signExtend12 4095).toNat =
        n4CallAddbackBeqQTrue a b := by
  rw [n4CallAddbackBeqQOutV4_toNat_of_carry_ne_zero h_carry]


-- @@ L947-959 verbatim
theorem n4CallAddbackBeqQOutV4_toNat_eq_qTrue_qHat_branch_iff {a b : EvmWord} :
    (n4CallAddbackBeqQOutV4 a b).toNat = n4CallAddbackBeqQTrue a b ↔
      if n4CallAddbackBeqCarryV4 a b = 0 then
        (n4CallAddbackBeqQHatV4 a b + signExtend12 4095 + signExtend12 4095).toNat =
          n4CallAddbackBeqQTrue a b
      else
        (n4CallAddbackBeqQHatV4 a b + signExtend12 4095).toNat =
          n4CallAddbackBeqQTrue a b := by
  by_cases h_carry : n4CallAddbackBeqCarryV4 a b = 0
  · rw [if_pos h_carry]
    exact n4CallAddbackBeqQOutV4_toNat_eq_qTrue_carry_eq_zero_iff h_carry
  · rw [if_neg h_carry]
    exact n4CallAddbackBeqQOutV4_toNat_eq_qTrue_carry_ne_zero_iff h_carry


-- @@ L961-971 verbatim
/-- Introduce `qOut = qTrue` from the carry-selected qHat equality. -/
theorem n4CallAddbackBeqQOutV4_toNat_eq_qTrue_of_qHat_branch {a b : EvmWord}
    (h_qHat :
      if n4CallAddbackBeqCarryV4 a b = 0 then
        (n4CallAddbackBeqQHatV4 a b + signExtend12 4095 + signExtend12 4095).toNat =
          n4CallAddbackBeqQTrue a b
      else
        (n4CallAddbackBeqQHatV4 a b + signExtend12 4095).toNat =
          n4CallAddbackBeqQTrue a b) :
    (n4CallAddbackBeqQOutV4 a b).toNat = n4CallAddbackBeqQTrue a b :=
  (n4CallAddbackBeqQOutV4_toNat_eq_qTrue_qHat_branch_iff).2 h_qHat


-- @@ L973-982 verbatim
/-- Eliminate `qOut = qTrue` to the carry-selected qHat equality. -/
theorem n4CallAddbackBeqQOutV4_toNat_eq_qTrue_qHat_branch {a b : EvmWord}
    (h_qOut : (n4CallAddbackBeqQOutV4 a b).toNat = n4CallAddbackBeqQTrue a b) :
    if n4CallAddbackBeqCarryV4 a b = 0 then
      (n4CallAddbackBeqQHatV4 a b + signExtend12 4095 + signExtend12 4095).toNat =
        n4CallAddbackBeqQTrue a b
    else
      (n4CallAddbackBeqQHatV4 a b + signExtend12 4095).toNat =
        n4CallAddbackBeqQTrue a b :=
  (n4CallAddbackBeqQOutV4_toNat_eq_qTrue_qHat_branch_iff).1 h_qOut


-- @@ L984-987 verbatim
theorem n4CallAddbackBeqQOutV4_toNat_eq_qTrue_qHatBranchEqQTrue_iff {a b : EvmWord} :
    (n4CallAddbackBeqQOutV4 a b).toNat = n4CallAddbackBeqQTrue a b ↔
      n4CallAddbackBeqQHatBranchEqQTrue a b := by
  exact n4CallAddbackBeqQOutV4_toNat_eq_qTrue_qHat_branch_iff


-- @@ L989-993 verbatim
/-- Introduce `qOut = qTrue` from the named carry-selected qHat predicate. -/
theorem n4CallAddbackBeqQOutV4_toNat_eq_qTrue_of_qHatBranchEqQTrue {a b : EvmWord}
    (h_qHat : n4CallAddbackBeqQHatBranchEqQTrue a b) :
    (n4CallAddbackBeqQOutV4 a b).toNat = n4CallAddbackBeqQTrue a b :=
  (n4CallAddbackBeqQOutV4_toNat_eq_qTrue_qHatBranchEqQTrue_iff).2 h_qHat


-- @@ L995-999 verbatim
/-- Eliminate `qOut = qTrue` to the named carry-selected qHat predicate. -/
theorem n4CallAddbackBeqQOutV4_toNat_eq_qTrue_qHatBranchEqQTrue {a b : EvmWord}
    (h_qOut : (n4CallAddbackBeqQOutV4 a b).toNat = n4CallAddbackBeqQTrue a b) :
    n4CallAddbackBeqQHatBranchEqQTrue a b :=
  (n4CallAddbackBeqQOutV4_toNat_eq_qTrue_qHatBranchEqQTrue_iff).1 h_qOut


-- @@ L1001-1009 verbatim
/-- V4 semantic-correctness precondition for the n=4 call+addback-BEQ sub-path.

    This is the v4 migration target for `n4CallAddbackBeqSemanticHolds`: it uses
    the fully corrected `div128Quot_v4` trial quotient. The runtime bridge
    `n4CallAddbackBeqSemanticHolds_of_runtime_conditions` targets this quotient
    surface from the compact `n4CallAddbackBeqRuntimeBounds` arithmetic bundle;
    the legacy v1 marker remains only as the documented counterexample surface. -/
def n4CallAddbackBeqSemanticHoldsV4 (a b : EvmWord) : Prop :=
  (n4CallAddbackBeqQOutV4 a b).toNat = n4CallAddbackBeqQTrue a b


-- @@ L1011-1034 verbatim
theorem n4CallAddbackBeqSemanticV4_unfold {a b : EvmWord} :
    n4CallAddbackBeqSemanticHoldsV4 a b =
    (let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
     let antiShift :=
       (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
     let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
     let b2' := ((b.getLimbN 2) <<< shift) ||| ((b.getLimbN 1) >>> antiShift)
     let b1' := ((b.getLimbN 1) <<< shift) ||| ((b.getLimbN 0) >>> antiShift)
     let b0' := (b.getLimbN 0) <<< shift
     let u4 := (a.getLimbN 3) >>> antiShift
     let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
     let u2 := ((a.getLimbN 2) <<< shift) ||| ((a.getLimbN 1) >>> antiShift)
     let u1 := ((a.getLimbN 1) <<< shift) ||| ((a.getLimbN 0) >>> antiShift)
     let u0 := (a.getLimbN 0) <<< shift
     let qHat := div128Quot_v4 u4 u3 b3'
     let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
     let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 b0' b1' b2' b3'
     let q_out : Word :=
       if carry = 0 then qHat + signExtend12 4095 + signExtend12 4095
       else qHat + signExtend12 4095
     q_out.toNat =
         val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) /
           val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) :=
  rfl


-- @@ L1036-1038 verbatim
theorem n4CallAddbackBeqSemanticHolds_eq_v4 {a b : EvmWord} :
    n4CallAddbackBeqSemanticHolds a b = n4CallAddbackBeqSemanticHoldsV4 a b := by
  rw [n4CallAddbackBeqSemantic_unfold, n4CallAddbackBeqSemanticV4_unfold]


-- @@ L1040-1042 verbatim
theorem n4CallAddbackBeqSemanticHolds_iff_v4 {a b : EvmWord} :
    n4CallAddbackBeqSemanticHolds a b ↔ n4CallAddbackBeqSemanticHoldsV4 a b := by
  rw [n4CallAddbackBeqSemanticHolds_eq_v4]


-- @@ L1044-1047 verbatim
theorem n4CallAddbackBeqSemanticHolds_of_v4 {a b : EvmWord}
    (hsem : n4CallAddbackBeqSemanticHoldsV4 a b) :
    n4CallAddbackBeqSemanticHolds a b :=
  n4CallAddbackBeqSemanticHolds_iff_v4.2 hsem


-- @@ L1049-1052 verbatim
theorem n4CallAddbackBeqSemanticHolds_v4 {a b : EvmWord}
    (hsem : n4CallAddbackBeqSemanticHolds a b) :
    n4CallAddbackBeqSemanticHoldsV4 a b :=
  n4CallAddbackBeqSemanticHolds_iff_v4.1 hsem


-- @@ L1054-1092 verbatim
theorem n4CallAddbackBeqSemanticHoldsV4_eq_direct {a b : EvmWord}
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0) :
    n4CallAddbackBeqSemanticHoldsV4 a b =
      (let b3' :=
        ((b.getLimbN 3) <<< (clzResult (b.getLimbN 3)).1.toNat) |||
          ((b.getLimbN 2) >>> (64 - (clzResult (b.getLimbN 3)).1.toNat))
       let b2' :=
        ((b.getLimbN 2) <<< (clzResult (b.getLimbN 3)).1.toNat) |||
          ((b.getLimbN 1) >>> (64 - (clzResult (b.getLimbN 3)).1.toNat))
       let b1' :=
        ((b.getLimbN 1) <<< (clzResult (b.getLimbN 3)).1.toNat) |||
          ((b.getLimbN 0) >>> (64 - (clzResult (b.getLimbN 3)).1.toNat))
       let b0' := (b.getLimbN 0) <<< (clzResult (b.getLimbN 3)).1.toNat
       let u3 :=
        ((a.getLimbN 3) <<< (clzResult (b.getLimbN 3)).1.toNat) |||
          ((a.getLimbN 2) >>> (64 - (clzResult (b.getLimbN 3)).1.toNat))
       let u2 :=
        ((a.getLimbN 2) <<< (clzResult (b.getLimbN 3)).1.toNat) |||
          ((a.getLimbN 1) >>> (64 - (clzResult (b.getLimbN 3)).1.toNat))
       let u1 :=
        ((a.getLimbN 1) <<< (clzResult (b.getLimbN 3)).1.toNat) |||
          ((a.getLimbN 0) >>> (64 - (clzResult (b.getLimbN 3)).1.toNat))
       let u0 := (a.getLimbN 0) <<< (clzResult (b.getLimbN 3)).1.toNat
       let qHat :=
        div128Quot_v4
          ((a.getLimbN 3) >>> (64 - (clzResult (b.getLimbN 3)).1.toNat))
          u3
          b3'
       let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
       let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 b0' b1' b2' b3'
       let qOut : Word :=
        if carry = 0 then qHat + signExtend12 4095 + signExtend12 4095
        else qHat + signExtend12 4095
       qOut.toNat =
        val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) /
          val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) := by
  rw [n4CallAddbackBeqSemanticHoldsV4]
  rw [n4CallAddbackBeqQOutV4_eq_direct hshift_nz]
  rw [n4CallAddbackBeqQTrue_unfold]


-- @@ L1094-1132 verbatim
theorem n4CallAddbackBeqSemanticHoldsV4_of_direct {a b : EvmWord}
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (h_direct :
      let b3' :=
        ((b.getLimbN 3) <<< (clzResult (b.getLimbN 3)).1.toNat) |||
          ((b.getLimbN 2) >>> (64 - (clzResult (b.getLimbN 3)).1.toNat))
      let b2' :=
        ((b.getLimbN 2) <<< (clzResult (b.getLimbN 3)).1.toNat) |||
          ((b.getLimbN 1) >>> (64 - (clzResult (b.getLimbN 3)).1.toNat))
      let b1' :=
        ((b.getLimbN 1) <<< (clzResult (b.getLimbN 3)).1.toNat) |||
          ((b.getLimbN 0) >>> (64 - (clzResult (b.getLimbN 3)).1.toNat))
      let b0' := (b.getLimbN 0) <<< (clzResult (b.getLimbN 3)).1.toNat
      let u3 :=
        ((a.getLimbN 3) <<< (clzResult (b.getLimbN 3)).1.toNat) |||
          ((a.getLimbN 2) >>> (64 - (clzResult (b.getLimbN 3)).1.toNat))
      let u2 :=
        ((a.getLimbN 2) <<< (clzResult (b.getLimbN 3)).1.toNat) |||
          ((a.getLimbN 1) >>> (64 - (clzResult (b.getLimbN 3)).1.toNat))
      let u1 :=
        ((a.getLimbN 1) <<< (clzResult (b.getLimbN 3)).1.toNat) |||
          ((a.getLimbN 0) >>> (64 - (clzResult (b.getLimbN 3)).1.toNat))
      let u0 := (a.getLimbN 0) <<< (clzResult (b.getLimbN 3)).1.toNat
      let qHat :=
        div128Quot_v4
          ((a.getLimbN 3) >>> (64 - (clzResult (b.getLimbN 3)).1.toNat))
          u3
          b3'
      let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
      let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 b0' b1' b2' b3'
      let qOut : Word :=
        if carry = 0 then qHat + signExtend12 4095 + signExtend12 4095
        else qHat + signExtend12 4095
      qOut.toNat =
        val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) /
          val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) :
    n4CallAddbackBeqSemanticHoldsV4 a b := by
  rw [n4CallAddbackBeqSemanticHoldsV4_eq_direct hshift_nz]
  exact h_direct


-- @@ L1134-1171 verbatim
theorem n4CallAddbackBeqSemanticHoldsV4_direct {a b : EvmWord}
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hsem : n4CallAddbackBeqSemanticHoldsV4 a b) :
    let b3' :=
      ((b.getLimbN 3) <<< (clzResult (b.getLimbN 3)).1.toNat) |||
        ((b.getLimbN 2) >>> (64 - (clzResult (b.getLimbN 3)).1.toNat))
    let b2' :=
      ((b.getLimbN 2) <<< (clzResult (b.getLimbN 3)).1.toNat) |||
        ((b.getLimbN 1) >>> (64 - (clzResult (b.getLimbN 3)).1.toNat))
    let b1' :=
      ((b.getLimbN 1) <<< (clzResult (b.getLimbN 3)).1.toNat) |||
        ((b.getLimbN 0) >>> (64 - (clzResult (b.getLimbN 3)).1.toNat))
    let b0' := (b.getLimbN 0) <<< (clzResult (b.getLimbN 3)).1.toNat
    let u3 :=
      ((a.getLimbN 3) <<< (clzResult (b.getLimbN 3)).1.toNat) |||
        ((a.getLimbN 2) >>> (64 - (clzResult (b.getLimbN 3)).1.toNat))
    let u2 :=
      ((a.getLimbN 2) <<< (clzResult (b.getLimbN 3)).1.toNat) |||
        ((a.getLimbN 1) >>> (64 - (clzResult (b.getLimbN 3)).1.toNat))
    let u1 :=
      ((a.getLimbN 1) <<< (clzResult (b.getLimbN 3)).1.toNat) |||
        ((a.getLimbN 0) >>> (64 - (clzResult (b.getLimbN 3)).1.toNat))
    let u0 := (a.getLimbN 0) <<< (clzResult (b.getLimbN 3)).1.toNat
    let qHat :=
      div128Quot_v4
        ((a.getLimbN 3) >>> (64 - (clzResult (b.getLimbN 3)).1.toNat))
        u3
        b3'
    let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
    let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 b0' b1' b2' b3'
    let qOut : Word :=
      if carry = 0 then qHat + signExtend12 4095 + signExtend12 4095
      else qHat + signExtend12 4095
    qOut.toNat =
        val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) /
          val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) := by
  rw [n4CallAddbackBeqSemanticHoldsV4_eq_direct hshift_nz] at hsem
  exact hsem


-- @@ L1173-1209 verbatim
theorem n4CallAddbackBeqSemanticHoldsV4_direct_iff {a b : EvmWord}
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0) :
    n4CallAddbackBeqSemanticHoldsV4 a b ↔
      (let b3' :=
        ((b.getLimbN 3) <<< (clzResult (b.getLimbN 3)).1.toNat) |||
          ((b.getLimbN 2) >>> (64 - (clzResult (b.getLimbN 3)).1.toNat))
       let b2' :=
        ((b.getLimbN 2) <<< (clzResult (b.getLimbN 3)).1.toNat) |||
          ((b.getLimbN 1) >>> (64 - (clzResult (b.getLimbN 3)).1.toNat))
       let b1' :=
        ((b.getLimbN 1) <<< (clzResult (b.getLimbN 3)).1.toNat) |||
          ((b.getLimbN 0) >>> (64 - (clzResult (b.getLimbN 3)).1.toNat))
       let b0' := (b.getLimbN 0) <<< (clzResult (b.getLimbN 3)).1.toNat
       let u3 :=
        ((a.getLimbN 3) <<< (clzResult (b.getLimbN 3)).1.toNat) |||
          ((a.getLimbN 2) >>> (64 - (clzResult (b.getLimbN 3)).1.toNat))
       let u2 :=
        ((a.getLimbN 2) <<< (clzResult (b.getLimbN 3)).1.toNat) |||
          ((a.getLimbN 1) >>> (64 - (clzResult (b.getLimbN 3)).1.toNat))
       let u1 :=
        ((a.getLimbN 1) <<< (clzResult (b.getLimbN 3)).1.toNat) |||
          ((a.getLimbN 0) >>> (64 - (clzResult (b.getLimbN 3)).1.toNat))
       let u0 := (a.getLimbN 0) <<< (clzResult (b.getLimbN 3)).1.toNat
       let qHat :=
        div128Quot_v4
          ((a.getLimbN 3) >>> (64 - (clzResult (b.getLimbN 3)).1.toNat))
          u3
          b3'
       let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
       let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 b0' b1' b2' b3'
       let qOut : Word :=
        if carry = 0 then qHat + signExtend12 4095 + signExtend12 4095
        else qHat + signExtend12 4095
       qOut.toNat =
        val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) /
          val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) := by
  rw [n4CallAddbackBeqSemanticHoldsV4_eq_direct hshift_nz]


-- @@ L1211-1216 verbatim
theorem n4CallAddbackBeqSemanticHoldsV4_qOutV4_eq {a b : EvmWord} :
    n4CallAddbackBeqSemanticHoldsV4 a b =
      ((n4CallAddbackBeqQOutV4 a b).toNat =
        val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) /
          val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) :=
  rfl


-- @@ L1218-1221 verbatim
theorem n4CallAddbackBeqSemanticHoldsV4_qOutV4_qTrue_eq {a b : EvmWord} :
    n4CallAddbackBeqSemanticHoldsV4 a b =
      ((n4CallAddbackBeqQOutV4 a b).toNat = n4CallAddbackBeqQTrue a b) :=
  rfl


-- @@ L1223-1228 verbatim
/-- Introduce the v4 n=4 call+addback-BEQ semantic predicate from the compact
    `qOut = qTrue` equality. -/
theorem n4CallAddbackBeqSemanticHoldsV4_of_qOutV4_toNat_eq_qTrue {a b : EvmWord}
    (h_qOut : (n4CallAddbackBeqQOutV4 a b).toNat = n4CallAddbackBeqQTrue a b) :
    n4CallAddbackBeqSemanticHoldsV4 a b :=
  h_qOut


-- @@ L1230-1235 verbatim
/-- Eliminate the v4 n=4 call+addback-BEQ semantic predicate to the compact
    `qOut = qTrue` equality. -/
theorem n4CallAddbackBeqSemanticHoldsV4_qOutV4_toNat_eq_qTrue {a b : EvmWord}
    (hsem : n4CallAddbackBeqSemanticHoldsV4 a b) :
    (n4CallAddbackBeqQOutV4 a b).toNat = n4CallAddbackBeqQTrue a b :=
  hsem


-- @@ L1237-1245 verbatim
/-- Introduce the v4 n=4 call+addback-BEQ semantic predicate from the named
    corrected quotient equality. -/
theorem n4CallAddbackBeqSemanticHoldsV4_of_qOutV4_toNat_eq {a b : EvmWord}
    (h_qOut :
      (n4CallAddbackBeqQOutV4 a b).toNat =
        val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) /
          val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) :
    n4CallAddbackBeqSemanticHoldsV4 a b :=
  h_qOut


-- @@ L1247-1254 verbatim
/-- Eliminate the v4 n=4 call+addback-BEQ semantic predicate to the named
    corrected quotient equality. -/
theorem n4CallAddbackBeqSemanticHoldsV4_qOutV4_toNat_eq {a b : EvmWord}
    (hsem : n4CallAddbackBeqSemanticHoldsV4 a b) :
    (n4CallAddbackBeqQOutV4 a b).toNat =
      val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) /
        val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) :=
  hsem


-- @@ L1256-1266 verbatim
/-- Introduce the v4 semantic predicate from the zero-carry qHat equality. -/
theorem n4CallAddbackBeqSemanticHoldsV4_of_carry_eq_zero_qHat {a b : EvmWord}
    (h_carry : n4CallAddbackBeqCarryV4 a b = 0)
    (h_qHat :
      (n4CallAddbackBeqQHatV4 a b + signExtend12 4095 + signExtend12 4095).toNat =
        val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) /
          val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) :
    n4CallAddbackBeqSemanticHoldsV4 a b := by
  apply n4CallAddbackBeqSemanticHoldsV4_of_qOutV4_toNat_eq
  rw [n4CallAddbackBeqQOutV4_toNat_of_carry_eq_zero h_carry]
  exact h_qHat


-- @@ L1268-1278 verbatim
/-- Introduce the v4 semantic predicate from the nonzero-carry qHat equality. -/
theorem n4CallAddbackBeqSemanticHoldsV4_of_carry_ne_zero_qHat {a b : EvmWord}
    (h_carry : n4CallAddbackBeqCarryV4 a b ≠ 0)
    (h_qHat :
      (n4CallAddbackBeqQHatV4 a b + signExtend12 4095).toNat =
        val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) /
          val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) :
    n4CallAddbackBeqSemanticHoldsV4 a b := by
  apply n4CallAddbackBeqSemanticHoldsV4_of_qOutV4_toNat_eq
  rw [n4CallAddbackBeqQOutV4_toNat_of_carry_ne_zero h_carry]
  exact h_qHat


-- @@ L1280-1288 verbatim
/-- Eliminate the v4 semantic predicate to the zero-carry qHat equality. -/
theorem n4CallAddbackBeqSemanticHoldsV4_carry_eq_zero_qHat {a b : EvmWord}
    (h_carry : n4CallAddbackBeqCarryV4 a b = 0)
    (hsem : n4CallAddbackBeqSemanticHoldsV4 a b) :
    (n4CallAddbackBeqQHatV4 a b + signExtend12 4095 + signExtend12 4095).toNat =
      val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) /
        val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) := by
  rw [← n4CallAddbackBeqQOutV4_toNat_of_carry_eq_zero h_carry]
  exact n4CallAddbackBeqSemanticHoldsV4_qOutV4_toNat_eq hsem


-- @@ L1290-1298 verbatim
/-- Eliminate the v4 semantic predicate to the nonzero-carry qHat equality. -/
theorem n4CallAddbackBeqSemanticHoldsV4_carry_ne_zero_qHat {a b : EvmWord}
    (h_carry : n4CallAddbackBeqCarryV4 a b ≠ 0)
    (hsem : n4CallAddbackBeqSemanticHoldsV4 a b) :
    (n4CallAddbackBeqQHatV4 a b + signExtend12 4095).toNat =
      val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) /
        val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) := by
  rw [← n4CallAddbackBeqQOutV4_toNat_of_carry_ne_zero h_carry]
  exact n4CallAddbackBeqSemanticHoldsV4_qOutV4_toNat_eq hsem


-- @@ L1300-1310 verbatim
/-- Introduce the v4 semantic predicate from the zero-carry qHat equality to
    the compact qTrue target. -/
theorem n4CallAddbackBeqSemanticHoldsV4_of_carry_eq_zero_qHat_qTrue {a b : EvmWord}
    (h_carry : n4CallAddbackBeqCarryV4 a b = 0)
    (h_qHat :
      (n4CallAddbackBeqQHatV4 a b + signExtend12 4095 + signExtend12 4095).toNat =
        n4CallAddbackBeqQTrue a b) :
    n4CallAddbackBeqSemanticHoldsV4 a b := by
  apply n4CallAddbackBeqSemanticHoldsV4_of_qOutV4_toNat_eq_qTrue
  rw [n4CallAddbackBeqQOutV4_toNat_of_carry_eq_zero h_carry]
  exact h_qHat


-- @@ L1312-1322 verbatim
/-- Introduce the v4 semantic predicate from the nonzero-carry qHat equality to
    the compact qTrue target. -/
theorem n4CallAddbackBeqSemanticHoldsV4_of_carry_ne_zero_qHat_qTrue {a b : EvmWord}
    (h_carry : n4CallAddbackBeqCarryV4 a b ≠ 0)
    (h_qHat :
      (n4CallAddbackBeqQHatV4 a b + signExtend12 4095).toNat =
        n4CallAddbackBeqQTrue a b) :
    n4CallAddbackBeqSemanticHoldsV4 a b := by
  apply n4CallAddbackBeqSemanticHoldsV4_of_qOutV4_toNat_eq_qTrue
  rw [n4CallAddbackBeqQOutV4_toNat_of_carry_ne_zero h_carry]
  exact h_qHat


-- @@ L1324-1332 verbatim
/-- Eliminate the v4 semantic predicate to the zero-carry qHat equality against
    the compact qTrue target. -/
theorem n4CallAddbackBeqSemanticHoldsV4_carry_eq_zero_qHat_qTrue {a b : EvmWord}
    (h_carry : n4CallAddbackBeqCarryV4 a b = 0)
    (hsem : n4CallAddbackBeqSemanticHoldsV4 a b) :
    (n4CallAddbackBeqQHatV4 a b + signExtend12 4095 + signExtend12 4095).toNat =
      n4CallAddbackBeqQTrue a b := by
  rw [← n4CallAddbackBeqQOutV4_toNat_of_carry_eq_zero h_carry]
  exact n4CallAddbackBeqSemanticHoldsV4_qOutV4_toNat_eq_qTrue hsem


-- @@ L1334-1342 verbatim
/-- Eliminate the v4 semantic predicate to the nonzero-carry qHat equality
    against the compact qTrue target. -/
theorem n4CallAddbackBeqSemanticHoldsV4_carry_ne_zero_qHat_qTrue {a b : EvmWord}
    (h_carry : n4CallAddbackBeqCarryV4 a b ≠ 0)
    (hsem : n4CallAddbackBeqSemanticHoldsV4 a b) :
    (n4CallAddbackBeqQHatV4 a b + signExtend12 4095).toNat =
      n4CallAddbackBeqQTrue a b := by
  rw [← n4CallAddbackBeqQOutV4_toNat_of_carry_ne_zero h_carry]
  exact n4CallAddbackBeqSemanticHoldsV4_qOutV4_toNat_eq_qTrue hsem


-- @@ L1344-1352 verbatim
/-- Zero-carry branch-local qHat characterization of the v4 semantic predicate. -/
theorem n4CallAddbackBeqSemanticHoldsV4_carry_eq_zero_qHat_qTrue_iff {a b : EvmWord}
    (h_carry : n4CallAddbackBeqCarryV4 a b = 0) :
    n4CallAddbackBeqSemanticHoldsV4 a b ↔
      (n4CallAddbackBeqQHatV4 a b + signExtend12 4095 + signExtend12 4095).toNat =
        n4CallAddbackBeqQTrue a b := by
  constructor
  · exact n4CallAddbackBeqSemanticHoldsV4_carry_eq_zero_qHat_qTrue h_carry
  · exact n4CallAddbackBeqSemanticHoldsV4_of_carry_eq_zero_qHat_qTrue h_carry


-- @@ L1354-1362 verbatim
/-- Nonzero-carry branch-local qHat characterization of the v4 semantic predicate. -/
theorem n4CallAddbackBeqSemanticHoldsV4_carry_ne_zero_qHat_qTrue_iff {a b : EvmWord}
    (h_carry : n4CallAddbackBeqCarryV4 a b ≠ 0) :
    n4CallAddbackBeqSemanticHoldsV4 a b ↔
      (n4CallAddbackBeqQHatV4 a b + signExtend12 4095).toNat =
        n4CallAddbackBeqQTrue a b := by
  constructor
  · exact n4CallAddbackBeqSemanticHoldsV4_carry_ne_zero_qHat_qTrue h_carry
  · exact n4CallAddbackBeqSemanticHoldsV4_of_carry_ne_zero_qHat_qTrue h_carry


-- @@ L1364-1376 verbatim
theorem n4CallAddbackBeqSemanticHoldsV4_qHat_branch_iff {a b : EvmWord} :
    n4CallAddbackBeqSemanticHoldsV4 a b ↔
      if n4CallAddbackBeqCarryV4 a b = 0 then
        (n4CallAddbackBeqQHatV4 a b + signExtend12 4095 + signExtend12 4095).toNat =
          n4CallAddbackBeqQTrue a b
      else
        (n4CallAddbackBeqQHatV4 a b + signExtend12 4095).toNat =
          n4CallAddbackBeqQTrue a b := by
  by_cases h_carry : n4CallAddbackBeqCarryV4 a b = 0
  · rw [if_pos h_carry]
    exact n4CallAddbackBeqSemanticHoldsV4_carry_eq_zero_qHat_qTrue_iff h_carry
  · rw [if_neg h_carry]
    exact n4CallAddbackBeqSemanticHoldsV4_carry_ne_zero_qHat_qTrue_iff h_carry


-- @@ L1378-1388 verbatim
/-- Introduce the v4 semantic predicate from the carry-selected qHat equality. -/
theorem n4CallAddbackBeqSemanticHoldsV4_of_qHat_branch {a b : EvmWord}
    (h_qHat :
      if n4CallAddbackBeqCarryV4 a b = 0 then
        (n4CallAddbackBeqQHatV4 a b + signExtend12 4095 + signExtend12 4095).toNat =
          n4CallAddbackBeqQTrue a b
      else
        (n4CallAddbackBeqQHatV4 a b + signExtend12 4095).toNat =
          n4CallAddbackBeqQTrue a b) :
    n4CallAddbackBeqSemanticHoldsV4 a b :=
  (n4CallAddbackBeqSemanticHoldsV4_qHat_branch_iff).2 h_qHat


-- @@ L1390-1399 verbatim
/-- Eliminate the v4 semantic predicate to the carry-selected qHat equality. -/
theorem n4CallAddbackBeqSemanticHoldsV4_qHat_branch {a b : EvmWord}
    (hsem : n4CallAddbackBeqSemanticHoldsV4 a b) :
    if n4CallAddbackBeqCarryV4 a b = 0 then
      (n4CallAddbackBeqQHatV4 a b + signExtend12 4095 + signExtend12 4095).toNat =
        n4CallAddbackBeqQTrue a b
    else
      (n4CallAddbackBeqQHatV4 a b + signExtend12 4095).toNat =
        n4CallAddbackBeqQTrue a b :=
  (n4CallAddbackBeqSemanticHoldsV4_qHat_branch_iff).1 hsem


-- @@ L1401-1404 verbatim
theorem n4CallAddbackBeqSemanticHoldsV4_qHatBranchEqQTrue_iff {a b : EvmWord} :
    n4CallAddbackBeqSemanticHoldsV4 a b ↔
      n4CallAddbackBeqQHatBranchEqQTrue a b := by
  exact n4CallAddbackBeqSemanticHoldsV4_qHat_branch_iff


-- @@ L1406-1410 verbatim
/-- Introduce the v4 semantic predicate from the named carry-selected qHat predicate. -/
theorem n4CallAddbackBeqSemanticHoldsV4_of_qHatBranchEqQTrue {a b : EvmWord}
    (h_qHat : n4CallAddbackBeqQHatBranchEqQTrue a b) :
    n4CallAddbackBeqSemanticHoldsV4 a b :=
  (n4CallAddbackBeqSemanticHoldsV4_qHatBranchEqQTrue_iff).2 h_qHat


-- @@ L1412-1416 verbatim
/-- Eliminate the v4 semantic predicate to the named carry-selected qHat predicate. -/
theorem n4CallAddbackBeqSemanticHoldsV4_qHatBranchEqQTrue {a b : EvmWord}
    (hsem : n4CallAddbackBeqSemanticHoldsV4 a b) :
    n4CallAddbackBeqQHatBranchEqQTrue a b :=
  (n4CallAddbackBeqSemanticHoldsV4_qHatBranchEqQTrue_iff).1 hsem


-- @@ L1418-1445 verbatim
/-- Introduce the v4 n=4 call+addback-BEQ semantic predicate from the raw
    normalized `q_out` equality. -/
theorem n4CallAddbackBeqSemanticHoldsV4_of_qOut_toNat_eq {a b : EvmWord}
    (h_qOut :
      let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
      let antiShift :=
        (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
      let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
      let b2' := ((b.getLimbN 2) <<< shift) ||| ((b.getLimbN 1) >>> antiShift)
      let b1' := ((b.getLimbN 1) <<< shift) ||| ((b.getLimbN 0) >>> antiShift)
      let b0' := (b.getLimbN 0) <<< shift
      let u4 := (a.getLimbN 3) >>> antiShift
      let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
      let u2 := ((a.getLimbN 2) <<< shift) ||| ((a.getLimbN 1) >>> antiShift)
      let u1 := ((a.getLimbN 1) <<< shift) ||| ((a.getLimbN 0) >>> antiShift)
      let u0 := (a.getLimbN 0) <<< shift
      let qHat := div128Quot_v4 u4 u3 b3'
      let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
      let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 b0' b1' b2' b3'
      let q_out : Word :=
        if carry = 0 then qHat + signExtend12 4095 + signExtend12 4095
        else qHat + signExtend12 4095
      q_out.toNat =
        val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) /
          val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) :
    n4CallAddbackBeqSemanticHoldsV4 a b := by
  rw [n4CallAddbackBeqSemanticV4_unfold]
  exact h_qOut


-- @@ L1447-1473 verbatim
/-- Eliminate the v4 n=4 call+addback-BEQ semantic predicate to the raw
    normalized `q_out` equality. -/
theorem n4CallAddbackBeqSemanticHoldsV4_qOut_toNat_eq {a b : EvmWord}
    (hsem : n4CallAddbackBeqSemanticHoldsV4 a b) :
    let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
    let antiShift :=
      (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
    let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
    let b2' := ((b.getLimbN 2) <<< shift) ||| ((b.getLimbN 1) >>> antiShift)
    let b1' := ((b.getLimbN 1) <<< shift) ||| ((b.getLimbN 0) >>> antiShift)
    let b0' := (b.getLimbN 0) <<< shift
    let u4 := (a.getLimbN 3) >>> antiShift
    let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
    let u2 := ((a.getLimbN 2) <<< shift) ||| ((a.getLimbN 1) >>> antiShift)
    let u1 := ((a.getLimbN 1) <<< shift) ||| ((a.getLimbN 0) >>> antiShift)
    let u0 := (a.getLimbN 0) <<< shift
    let qHat := div128Quot_v4 u4 u3 b3'
    let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
    let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 b0' b1' b2' b3'
    let q_out : Word :=
      if carry = 0 then qHat + signExtend12 4095 + signExtend12 4095
      else qHat + signExtend12 4095
    q_out.toNat =
      val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) /
        val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) := by
  rw [n4CallAddbackBeqSemanticV4_unfold] at hsem
  exact hsem


-- @@ L1475-1475 verbatim
end EvmAsm.Evm64
