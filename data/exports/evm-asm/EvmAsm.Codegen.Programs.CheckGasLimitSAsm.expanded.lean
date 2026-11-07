/-
  EvmAsm.Codegen.Programs.CheckGasLimitSAsm

  `check_gas_limit` via the **continuation forward-join**
  (`EvmAsm/Rv64/SAsm/ContForwardJoin.lean`, bead evm-asm-4ch8f.33.2) —
  the acceptance consumer.

  The routine (Ethereum `check_gas_limit`, gas-limit elasticity):

  ```
        lui  t0, 1 ; addiw t0, t0, 904     -- GAS_LIMIT_MINIMUM = 5000
        bltu a0, t0, .low                  -- new < 5000 → status 1
        srli t1, a1, 10                    -- max_delta = parent / 1024
        bltu a1, a0, .grow
        sub  t2, a1, a0                    -- shrink: delta = parent - new
        j    .join
  .grow: sub t2, a0, a1                    -- grow:   delta = new - parent
  .join: bgeu t2, t1, .far                 -- delta ≥ max_delta → status 2
        li a0, 0 ; ret
  .low:  li a0, 1 ; ret
  .far:  li a0, 2 ; ret
  ```

  The abs-delta if/else is one `contJoinStation_spec` (both arms
  reconverge at `.join` with `t2 = |new − parent|` as the if-value); the
  three return tails are `sharedRetTail_spec` (#10041) instances.

  **Genuine post** (`checkGasLimit_spec`): `a0 = cglStatus new parent` —
  `1` when `new < 5000`, else `0` when `|new − parent| < parent >>> 10`,
  else `2`; the parent input preserved.  Byte-transparent: stated at the
  `#guard`-tied `GuestAddrs.check_gas_limit` directly over the emitted
  `checkGasLimit_prog` (no byte change, no A/B).
-/

import EvmAsm.Codegen.Programs.Header
import EvmAsm.Rv64.SAsm.ContForwardJoin
import EvmAsm.Rv64.SAsm.FnFlat


-- @@ L39-39 verbatim
namespace EvmAsm.Codegen


-- @@ L41-41 verbatim
open EvmAsm.Rv64 EvmAsm.Rv64.SAsm


-- @@ L43-43 verbatim
namespace CheckGasLimitSAsm


-- @@ L45-45 verbatim
/-! ## The routine's semantics -/


-- @@ L47-50 verbatim
/-- `|new − parent|` — the gas-limit adjustment magnitude (the if-value
    established at the forward join). -/
def cglDelta (nl pl : Word) : Word :=
  if BitVec.ult pl nl then nl - pl else pl - nl


-- @@ L52-57 verbatim
/-- The `check_gas_limit` verdict: `1` below the 5000 minimum, `0` when
    the adjustment is strictly inside `parent / 1024`, else `2`. -/
def cglStatus (nl pl : Word) : Word :=
  if BitVec.ult nl (5000 : Word) then 1
  else if BitVec.ult (cglDelta nl pl) (pl >>> 10) then 0
  else 2


-- @@ L59-62 verbatim
/-! A zero check-gas status supplies the positivity needed by the K73
    base-fee divider.  This is deliberately weaker than the minimum-gas
    branch: `cglStatus nl pl = 0` only says that the adjustment is below the
    parent allowance, and the parent may be below 5000 when `nl = pl`. -/

-- @@ L63-81 verbatim
theorem cglStatus_zero_implies_parent_target_pos
    (nl pl : Word) (hzero : cglStatus nl pl = 0) :
    0 < (pl >>> 1).toNat := by
  unfold cglStatus at hzero
  split at hzero
  · simp_all
  · split at hzero
    · have hlt : (cglDelta nl pl).toNat < (pl >>> 10).toNat := by
        apply (BitVec.ult_iff_toNat_lt).mp
        assumption
      have hallow : 0 < (pl >>> 10).toNat := by
        by_contra hnot
        have hz : (pl >>> 10).toNat = 0 := Nat.eq_zero_of_not_pos hnot
        simp [hz] at hlt
      rw [BitVec.toNat_ushiftRight] at hallow
      have hpl : 1024 ≤ pl.toNat := by omega
      rw [BitVec.toNat_ushiftRight]
      omega
    · simp_all


-- @@ L83-83 verbatim
/-! ## The whole routine -/


-- @@ L85-423 expanded
/-- **`check_gas_limit` at its linked address** (genuine post):
    `a0 = cglStatus new parent`, the parent input untouched. -/
theorem checkGasLimit_spec (nl pl ret : Word) (halignRet : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin 10 (GuestAddrs.check_gas_limit : Word) ret
      (CodeReq.ofProg (GuestAddrs.check_gas_limit : Word) checkGasLimit_prog)
      (((.x10 : Reg) ↦ᵣ nl) **
        ((.x11 : Reg) ↦ᵣ pl) ** ((.x1 : Reg) ↦ᵣ ret) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7)
      (((.x10 : Reg) ↦ᵣ cglStatus nl pl) **
        ((.x11 : Reg) ↦ᵣ pl) ** ((.x1 : Reg) ↦ᵣ ret) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7) :=
  by
  set CR := CodeReq.ofProg (GuestAddrs.check_gas_limit : Word) checkGasLimit_prog with hCR
  refine
    cpsTripleWithin_weaken
      (fun h hp => by
        simp only [regOwns_cons, regOwns_nil, sepConj_emp_right']
        xperm_hyp hp)
      (fun _ hq => hq)
      (cpsTripleWithin_peel_regOwns [.x5, .x6, .x7] (by decide) (P :=
        ((.x10 : Reg) ↦ᵣ nl) ** ((.x11 : Reg) ↦ᵣ pl) ** ((.x1 : Reg) ↦ᵣ ret)) (fun vf => ?_))
  simp only [regAtomsOf_cons, regAtomsOf_nil, sepConj_emp_right']
    -- ---- materialize GAS_LIMIT_MINIMUM = 5000 ----
    
  have hlui :=
    liftCode (cr' := CR)
      (lui_spec_gen_within .x5 (vf .x5) (1 : BitVec 20) (GuestAddrs.check_gas_limit : Word)
        (by decide))
      (by rw [hCR];
        first
        | (with_reducible exact fun a i h => h)
        | ((with_reducible refine CodeReq.singleton_mono ?_); decide)
        | ((with_reducible refine CodeReq.sub_ofProg_of_lookup _ _ ?_ ?_) <;> decide))
  rw [show
      ((((1 : BitVec 20).zeroExtend 32 : BitVec 32) <<< 12).signExtend 64 : Word) = (4096 : Word)
      from by decide,
    show (GuestAddrs.check_gas_limit : Word) + 4 = ((GuestAddrs.check_gas_limit + 4) : Word) from by
      decide] at hlui
  have haddiw :=
    liftCode (cr' := CR)
      (addiw_spec_gen_same_within .x5 (4096 : Word) (904 : BitVec 12)
        ((GuestAddrs.check_gas_limit + 4) : Word) (by decide))
      (by rw [hCR];
        first
        | (with_reducible exact fun a i h => h)
        | ((with_reducible refine CodeReq.singleton_mono ?_); decide)
        | ((with_reducible refine CodeReq.sub_ofProg_of_lookup _ _ ?_ ?_) <;> decide))
  rw [show
      ((((4096 : Word).truncate 32 : BitVec 32) +
                  ((signExtend12 (904 : BitVec 12)).truncate 32 : BitVec 32) :
                BitVec 32).signExtend
            64 :
          Word) =
        (5000 : Word)
      from by decide,
    show ((GuestAddrs.check_gas_limit + 4) : Word) + 4 = ((GuestAddrs.check_gas_limit + 8) : Word)
      from by decide] at haddiw
  have hbrMin :=
    cpsBranchWithin_frameR
      (((.x11 : Reg) ↦ᵣ pl) **
        ((.x1 : Reg) ↦ᵣ ret) ** ((.x6 : Reg) ↦ᵣ vf .x6) ** ((.x7 : Reg) ↦ᵣ vf .x7))
      (by
        repeat
          first
          | apply pcFree_sepConj
          | exact pcFree_regIs
          | exact pcFree_regOwn
          | exact pcFree_memIs
          | exact pcFree_memOwn
          | exact pcFree_emp
          | exact pcFree_pure
          | exact pcFree_instrAt
          | exact bytesRegion_pcFree _ _
          | exact pcFree_stackFree _ _
          | exact pcFree_dwordsIs _ _
          | exact pcFree_regsAt _ _
          | exact pcFree_frameSlotsOwn _ _
          | exact pcFree_frameSlotsSaved _ _ _
          | exact pcFree_regFileIs _)
      (cpsBranchWithin_extend_code (cr' := CR) (h :=
        bltu_spec_gen_within .x10 .x5 (36 : BitVec 13) nl (5000 : Word)
          ((GuestAddrs.check_gas_limit + 8) : Word))
        (hmono := by rw [hCR];
        first
        | (with_reducible exact fun a i h => h)
        | ((with_reducible refine CodeReq.singleton_mono ?_); decide)
        | ((with_reducible refine CodeReq.sub_ofProg_of_lookup _ _ ?_ ?_) <;> decide)))
  rw [show
      ((GuestAddrs.check_gas_limit + 8) : Word) + signExtend13 (36 : BitVec 13) =
        ((GuestAddrs.check_gas_limit + 44) : Word)
      from by decide,
    show ((GuestAddrs.check_gas_limit + 8) : Word) + 4 = ((GuestAddrs.check_gas_limit + 12) : Word)
      from by decide] at hbrMin
  have htail1 :
    BitVec.ult nl (5000 : Word) →
      cpsTripleWithin 7 ((GuestAddrs.check_gas_limit + 44) : Word) ret CR
        (((.x10 : Reg) ↦ᵣ nl) **
          ((.x5 : Reg) ↦ᵣ (5000 : Word)) **
            (((.x11 : Reg) ↦ᵣ pl) **
              ((.x1 : Reg) ↦ᵣ ret) ** ((.x6 : Reg) ↦ᵣ vf .x6) ** ((.x7 : Reg) ↦ᵣ vf .x7)))
        (((.x10 : Reg) ↦ᵣ cglStatus nl pl) **
          ((.x11 : Reg) ↦ᵣ pl) ** ((.x1 : Reg) ↦ᵣ ret) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7) :=
    by
    intro h1
    have h :=
      sharedRetTail_spec CR ((GuestAddrs.check_gas_limit + 44) : Word) ret .x10 (1 : Word) nl
        (((.x11 : Reg) ↦ᵣ pl) **
          ((.x5 : Reg) ↦ᵣ (5000 : Word)) ** ((.x6 : Reg) ↦ᵣ vf .x6) ** ((.x7 : Reg) ↦ᵣ vf .x7))
        (by
          repeat
            first
            | apply pcFree_sepConj
            | exact pcFree_regIs
            | exact pcFree_regOwn
            | exact pcFree_memIs
            | exact pcFree_memOwn
            | exact pcFree_emp
            | exact pcFree_pure
            | exact pcFree_instrAt
            | exact bytesRegion_pcFree _ _
            | exact pcFree_stackFree _ _
            | exact pcFree_dwordsIs _ _
            | exact pcFree_regsAt _ _
            | exact pcFree_frameSlotsOwn _ _
            | exact pcFree_frameSlotsSaved _ _ _
            | exact pcFree_regFileIs _)
        (by decide) halignRet
        (by rw [hCR];
          first
          | (with_reducible exact fun a i h => h)
          | ((with_reducible refine CodeReq.singleton_mono ?_); decide)
          | ((with_reducible refine CodeReq.sub_ofProg_of_lookup _ _ ?_ ?_) <;> decide))
        (by rw [hCR];
          first
          | (with_reducible exact fun a i h => h)
          | ((with_reducible refine CodeReq.singleton_mono ?_); decide)
          | ((with_reducible refine CodeReq.sub_ofProg_of_lookup _ _ ?_ ?_) <;> decide))
    refine
      cpsTripleWithin_mono_nSteps (by omega)
        (cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hq => ?_) h)
    unfold cglStatus
    rw [if_pos h1]
    have hq1 :
      (((.x5 : Reg) ↦ᵣ (5000 : Word)) **
          (((.x6 : Reg) ↦ᵣ vf .x6) **
            (((.x7 : Reg) ↦ᵣ vf .x7) **
              (((.x10 : Reg) ↦ᵣ (1 : Word)) ** ((.x11 : Reg) ↦ᵣ pl) ** ((.x1 : Reg) ↦ᵣ ret)))))
        h :=
      by xperm_hyp hq
    have hq2 :=
      sepConj_mono (regIs_to_regOwn .x5 _)
        (sepConj_mono (regIs_to_regOwn .x6 _)
          (sepConj_mono (regIs_to_regOwn .x7 _) (fun _ hh => hh)))
        h hq1
    xperm_hyp hq2
  have hfallMin :
    ¬BitVec.ult nl (5000 : Word) →
      cpsTripleWithin 7 ((GuestAddrs.check_gas_limit + 12) : Word) ret CR
        (((.x10 : Reg) ↦ᵣ nl) **
          ((.x5 : Reg) ↦ᵣ (5000 : Word)) **
            (((.x11 : Reg) ↦ᵣ pl) **
              ((.x1 : Reg) ↦ᵣ ret) ** ((.x6 : Reg) ↦ᵣ vf .x6) ** ((.x7 : Reg) ↦ᵣ vf .x7)))
        (((.x10 : Reg) ↦ᵣ cglStatus nl pl) **
          ((.x11 : Reg) ↦ᵣ pl) ** ((.x1 : Reg) ↦ᵣ ret) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7) :=
    by
    intro hn1
    have hsrli :=
      liftCode (cr' := CR)
        (srli_spec_gen_within .x6 .x11 (vf .x6) pl (10 : BitVec 6)
          ((GuestAddrs.check_gas_limit + 12) : Word) (by decide))
        (by rw [hCR];
          first
          | (with_reducible exact fun a i h => h)
          | ((with_reducible refine CodeReq.singleton_mono ?_); decide)
          | ((with_reducible refine CodeReq.sub_ofProg_of_lookup _ _ ?_ ?_) <;> decide))
    rw [show ((10 : BitVec 6)).toNat = 10 from rfl,
      show
        ((GuestAddrs.check_gas_limit + 12) : Word) + 4 = ((GuestAddrs.check_gas_limit + 16) : Word)
        from by decide] at hsrli
    have hsrliF :=
      cpsTripleWithin_frameR
        (((.x10 : Reg) ↦ᵣ nl) **
          ((.x5 : Reg) ↦ᵣ (5000 : Word)) ** ((.x1 : Reg) ↦ᵣ ret) ** ((.x7 : Reg) ↦ᵣ vf .x7))
        (by
          repeat
            first
            | apply pcFree_sepConj
            | exact pcFree_regIs
            | exact pcFree_regOwn
            | exact pcFree_memIs
            | exact pcFree_memOwn
            | exact pcFree_emp
            | exact pcFree_pure
            | exact pcFree_instrAt
            | exact bytesRegion_pcFree _ _
            | exact pcFree_stackFree _ _
            | exact pcFree_dwordsIs _ _
            | exact pcFree_regsAt _ _
            | exact pcFree_frameSlotsOwn _ _
            | exact pcFree_frameSlotsSaved _ _ _
            | exact pcFree_regFileIs _)
        hsrli
    have hbrAbs :=
      cpsBranchWithin_frameR
        (((.x5 : Reg) ↦ᵣ (5000 : Word)) **
          ((.x6 : Reg) ↦ᵣ (pl >>> 10)) ** ((.x7 : Reg) ↦ᵣ vf .x7) ** ((.x1 : Reg) ↦ᵣ ret))
        (by
          repeat
            first
            | apply pcFree_sepConj
            | exact pcFree_regIs
            | exact pcFree_regOwn
            | exact pcFree_memIs
            | exact pcFree_memOwn
            | exact pcFree_emp
            | exact pcFree_pure
            | exact pcFree_instrAt
            | exact bytesRegion_pcFree _ _
            | exact pcFree_stackFree _ _
            | exact pcFree_dwordsIs _ _
            | exact pcFree_regsAt _ _
            | exact pcFree_frameSlotsOwn _ _
            | exact pcFree_frameSlotsSaved _ _ _
            | exact pcFree_regFileIs _)
        (cpsBranchWithin_extend_code (cr' := CR) (h :=
          bltu_spec_gen_within .x11 .x10 (12 : BitVec 13) pl nl
            ((GuestAddrs.check_gas_limit + 16) : Word))
          (hmono := by rw [hCR];
          first
          | (with_reducible exact fun a i h => h)
          | ((with_reducible refine CodeReq.singleton_mono ?_); decide)
          | ((with_reducible refine CodeReq.sub_ofProg_of_lookup _ _ ?_ ?_) <;> decide)))
    rw [show
        ((GuestAddrs.check_gas_limit + 16) : Word) + signExtend13 (12 : BitVec 13) =
          ((GuestAddrs.check_gas_limit + 28) : Word)
        from by decide,
      show
        ((GuestAddrs.check_gas_limit + 16) : Word) + 4 = ((GuestAddrs.check_gas_limit + 20) : Word)
        from by decide] at hbrAbs
    have hgrow :
      BitVec.ult pl nl →
        cpsTripleWithin 2 ((GuestAddrs.check_gas_limit + 28) : Word)
          ((GuestAddrs.check_gas_limit + 32) : Word) CR
          (((.x10 : Reg) ↦ᵣ nl) **
            ((.x11 : Reg) ↦ᵣ pl) **
              (((.x5 : Reg) ↦ᵣ (5000 : Word)) **
                ((.x6 : Reg) ↦ᵣ (pl >>> 10)) ** ((.x7 : Reg) ↦ᵣ vf .x7) ** ((.x1 : Reg) ↦ᵣ ret)))
          (((.x10 : Reg) ↦ᵣ nl) **
            ((.x11 : Reg) ↦ᵣ pl) **
              ((.x5 : Reg) ↦ᵣ (5000 : Word)) **
                ((.x6 : Reg) ↦ᵣ (pl >>> 10)) **
                  ((.x7 : Reg) ↦ᵣ cglDelta nl pl) ** ((.x1 : Reg) ↦ᵣ ret)) :=
      by
      intro hc
      have hsub :=
        liftCode (cr' := CR)
          (sub_spec_gen_within .x7 .x10 .x11 nl pl (vf .x7)
            ((GuestAddrs.check_gas_limit + 28) : Word) (by decide))
          (by rw [hCR];
            first
            | (with_reducible exact fun a i h => h)
            | ((with_reducible refine CodeReq.singleton_mono ?_); decide)
            | ((with_reducible refine CodeReq.sub_ofProg_of_lookup _ _ ?_ ?_) <;> decide))
      rw [show
          ((GuestAddrs.check_gas_limit + 28) : Word) + 4 =
            ((GuestAddrs.check_gas_limit + 32) : Word)
          from by decide] at hsub
      have hsubF :=
        cpsTripleWithin_frameR
          (((.x5 : Reg) ↦ᵣ (5000 : Word)) ** ((.x6 : Reg) ↦ᵣ (pl >>> 10)) ** ((.x1 : Reg) ↦ᵣ ret))
          (by
            repeat
              first
              | apply pcFree_sepConj
              | exact pcFree_regIs
              | exact pcFree_regOwn
              | exact pcFree_memIs
              | exact pcFree_memOwn
              | exact pcFree_emp
              | exact pcFree_pure
              | exact pcFree_instrAt
              | exact bytesRegion_pcFree _ _
              | exact pcFree_stackFree _ _
              | exact pcFree_dwordsIs _ _
              | exact pcFree_regsAt _ _
              | exact pcFree_frameSlotsOwn _ _
              | exact pcFree_frameSlotsSaved _ _ _
              | exact pcFree_regFileIs _)
          hsub
      refine
        cpsTripleWithin_mono_nSteps (by omega)
          (cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun h hq => ?_) hsubF)
      rw [show cglDelta nl pl = nl - pl from by unfold cglDelta; rw [if_pos hc]]
      xperm_hyp hq
    have hshrink :
      ¬BitVec.ult pl nl →
        cpsTripleWithin 2 ((GuestAddrs.check_gas_limit + 20) : Word)
          ((GuestAddrs.check_gas_limit + 32) : Word) CR
          (((.x10 : Reg) ↦ᵣ nl) **
            ((.x11 : Reg) ↦ᵣ pl) **
              (((.x5 : Reg) ↦ᵣ (5000 : Word)) **
                ((.x6 : Reg) ↦ᵣ (pl >>> 10)) ** ((.x7 : Reg) ↦ᵣ vf .x7) ** ((.x1 : Reg) ↦ᵣ ret)))
          (((.x10 : Reg) ↦ᵣ nl) **
            ((.x11 : Reg) ↦ᵣ pl) **
              ((.x5 : Reg) ↦ᵣ (5000 : Word)) **
                ((.x6 : Reg) ↦ᵣ (pl >>> 10)) **
                  ((.x7 : Reg) ↦ᵣ cglDelta nl pl) ** ((.x1 : Reg) ↦ᵣ ret)) :=
      by
      intro hnc
      have hsub :=
        liftCode (cr' := CR)
          (sub_spec_gen_within .x7 .x11 .x10 pl nl (vf .x7)
            ((GuestAddrs.check_gas_limit + 20) : Word) (by decide))
          (by rw [hCR];
            first
            | (with_reducible exact fun a i h => h)
            | ((with_reducible refine CodeReq.singleton_mono ?_); decide)
            | ((with_reducible refine CodeReq.sub_ofProg_of_lookup _ _ ?_ ?_) <;> decide))
      rw [show
          ((GuestAddrs.check_gas_limit + 20) : Word) + 4 =
            ((GuestAddrs.check_gas_limit + 24) : Word)
          from by decide] at hsub
      have hjal :=
        liftCode (cr' := CR)
          (jal_x0_spec_gen_within (8 : BitVec 21) ((GuestAddrs.check_gas_limit + 24) : Word))
          (by rw [hCR];
            first
            | (with_reducible exact fun a i h => h)
            | ((with_reducible refine CodeReq.singleton_mono ?_); decide)
            | ((with_reducible refine CodeReq.sub_ofProg_of_lookup _ _ ?_ ?_) <;> decide))
      rw [show
          ((GuestAddrs.check_gas_limit + 24) : Word) + signExtend21 (8 : BitVec 21) =
            ((GuestAddrs.check_gas_limit + 32) : Word)
          from by decide] at hjal
      have hsubF :=
        cpsTripleWithin_frameR
          (((.x5 : Reg) ↦ᵣ (5000 : Word)) ** ((.x6 : Reg) ↦ᵣ (pl >>> 10)) ** ((.x1 : Reg) ↦ᵣ ret))
          (by
            repeat
              first
              | apply pcFree_sepConj
              | exact pcFree_regIs
              | exact pcFree_regOwn
              | exact pcFree_memIs
              | exact pcFree_memOwn
              | exact pcFree_emp
              | exact pcFree_pure
              | exact pcFree_instrAt
              | exact bytesRegion_pcFree _ _
              | exact pcFree_stackFree _ _
              | exact pcFree_dwordsIs _ _
              | exact pcFree_regsAt _ _
              | exact pcFree_frameSlotsOwn _ _
              | exact pcFree_frameSlotsSaved _ _ _
              | exact pcFree_regFileIs _)
          hsub
      have hjalF :=
        cpsTripleWithin_frameR
          (((.x11 : Reg) ↦ᵣ pl) **
            ((.x10 : Reg) ↦ᵣ nl) **
              ((.x7 : Reg) ↦ᵣ (pl - nl)) **
                ((.x5 : Reg) ↦ᵣ (5000 : Word)) **
                  ((.x6 : Reg) ↦ᵣ (pl >>> 10)) ** ((.x1 : Reg) ↦ᵣ ret))
          (by
            repeat
              first
              | apply pcFree_sepConj
              | exact pcFree_regIs
              | exact pcFree_regOwn
              | exact pcFree_memIs
              | exact pcFree_memOwn
              | exact pcFree_emp
              | exact pcFree_pure
              | exact pcFree_instrAt
              | exact bytesRegion_pcFree _ _
              | exact pcFree_stackFree _ _
              | exact pcFree_dwordsIs _ _
              | exact pcFree_regsAt _ _
              | exact pcFree_frameSlotsOwn _ _
              | exact pcFree_frameSlotsSaved _ _ _
              | exact pcFree_regFileIs _)
          hjal
      have hc :=
        cpsTripleWithin_seq_perm_same_cr
          (fun _ hp => by
            rw [sepConj_emp_left']
            xperm_hyp hp)
          hsubF hjalF
      refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun h hq => ?_) hc
      rw [sepConj_emp_left'] at hq
      rw [show cglDelta nl pl = pl - nl from by unfold cglDelta; rw [if_neg hnc]]
      xperm_hyp hq
    have hjoin :=
      contJoinStation_spec (cond := BitVec.ult pl nl) (PT :=
        ((.x10 : Reg) ↦ᵣ nl) **
          ((.x11 : Reg) ↦ᵣ pl) **
            (((.x5 : Reg) ↦ᵣ (5000 : Word)) **
              ((.x6 : Reg) ↦ᵣ (pl >>> 10)) ** ((.x7 : Reg) ↦ᵣ vf .x7) ** ((.x1 : Reg) ↦ᵣ ret)))
        (PF :=
        ((.x10 : Reg) ↦ᵣ nl) **
          ((.x11 : Reg) ↦ᵣ pl) **
            (((.x5 : Reg) ↦ᵣ (5000 : Word)) **
              ((.x6 : Reg) ↦ᵣ (pl >>> 10)) ** ((.x7 : Reg) ↦ᵣ vf .x7) ** ((.x1 : Reg) ↦ᵣ ret)))
        hbrAbs (fun h hq => by xperm_hyp hq) (fun h hq => by xperm_hyp hq) (fun hc => hgrow hc)
        (fun hnc => hshrink hnc)
          -- ---- the delta guard (BGEU t2, t1 at +32) into the tails ----
          
    have hbrGe :=
      cpsBranchWithin_frameR
        (((.x10 : Reg) ↦ᵣ nl) **
          ((.x11 : Reg) ↦ᵣ pl) ** ((.x5 : Reg) ↦ᵣ (5000 : Word)) ** ((.x1 : Reg) ↦ᵣ ret))
        (by
          repeat
            first
            | apply pcFree_sepConj
            | exact pcFree_regIs
            | exact pcFree_regOwn
            | exact pcFree_memIs
            | exact pcFree_memOwn
            | exact pcFree_emp
            | exact pcFree_pure
            | exact pcFree_instrAt
            | exact bytesRegion_pcFree _ _
            | exact pcFree_stackFree _ _
            | exact pcFree_dwordsIs _ _
            | exact pcFree_regsAt _ _
            | exact pcFree_frameSlotsOwn _ _
            | exact pcFree_frameSlotsSaved _ _ _
            | exact pcFree_regFileIs _)
        (cpsBranchWithin_extend_code (cr' := CR) (h :=
          bgeu_spec_gen_within .x7 .x6 (20 : BitVec 13) (cglDelta nl pl) (pl >>> 10)
            ((GuestAddrs.check_gas_limit + 32) : Word))
          (hmono := by rw [hCR];
          first
          | (with_reducible exact fun a i h => h)
          | ((with_reducible refine CodeReq.singleton_mono ?_); decide)
          | ((with_reducible refine CodeReq.sub_ofProg_of_lookup _ _ ?_ ?_) <;> decide)))
    rw [show
        ((GuestAddrs.check_gas_limit + 32) : Word) + signExtend13 (20 : BitVec 13) =
          ((GuestAddrs.check_gas_limit + 52) : Word)
        from by decide,
      show
        ((GuestAddrs.check_gas_limit + 32) : Word) + 4 = ((GuestAddrs.check_gas_limit + 36) : Word)
        from by decide] at hbrGe
    have htail2 :
      ¬BitVec.ult (cglDelta nl pl) (pl >>> 10) →
        cpsTripleWithin 2 ((GuestAddrs.check_gas_limit + 52) : Word) ret CR
          (((.x7 : Reg) ↦ᵣ cglDelta nl pl) **
            ((.x6 : Reg) ↦ᵣ (pl >>> 10)) **
              (((.x10 : Reg) ↦ᵣ nl) **
                ((.x11 : Reg) ↦ᵣ pl) ** ((.x5 : Reg) ↦ᵣ (5000 : Word)) ** ((.x1 : Reg) ↦ᵣ ret)))
          (((.x10 : Reg) ↦ᵣ cglStatus nl pl) **
            ((.x11 : Reg) ↦ᵣ pl) **
              ((.x1 : Reg) ↦ᵣ ret) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7) :=
      by
      intro hge
      have h :=
        sharedRetTail_spec CR ((GuestAddrs.check_gas_limit + 52) : Word) ret .x10 (2 : Word) nl
          (((.x11 : Reg) ↦ᵣ pl) **
            ((.x5 : Reg) ↦ᵣ (5000 : Word)) **
              ((.x6 : Reg) ↦ᵣ (pl >>> 10)) ** ((.x7 : Reg) ↦ᵣ cglDelta nl pl))
          (by
            repeat
              first
              | apply pcFree_sepConj
              | exact pcFree_regIs
              | exact pcFree_regOwn
              | exact pcFree_memIs
              | exact pcFree_memOwn
              | exact pcFree_emp
              | exact pcFree_pure
              | exact pcFree_instrAt
              | exact bytesRegion_pcFree _ _
              | exact pcFree_stackFree _ _
              | exact pcFree_dwordsIs _ _
              | exact pcFree_regsAt _ _
              | exact pcFree_frameSlotsOwn _ _
              | exact pcFree_frameSlotsSaved _ _ _
              | exact pcFree_regFileIs _)
          (by decide) halignRet
          (by rw [hCR];
            first
            | (with_reducible exact fun a i h => h)
            | ((with_reducible refine CodeReq.singleton_mono ?_); decide)
            | ((with_reducible refine CodeReq.sub_ofProg_of_lookup _ _ ?_ ?_) <;> decide))
          (by rw [hCR];
            first
            | (with_reducible exact fun a i h => h)
            | ((with_reducible refine CodeReq.singleton_mono ?_); decide)
            | ((with_reducible refine CodeReq.sub_ofProg_of_lookup _ _ ?_ ?_) <;> decide))
      refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hq => ?_) h
      unfold cglStatus
      rw [if_neg hn1, if_neg hge]
      have hq1 :
        (((.x5 : Reg) ↦ᵣ (5000 : Word)) **
            (((.x6 : Reg) ↦ᵣ (pl >>> 10)) **
              (((.x7 : Reg) ↦ᵣ cglDelta nl pl) **
                (((.x10 : Reg) ↦ᵣ (2 : Word)) ** ((.x11 : Reg) ↦ᵣ pl) ** ((.x1 : Reg) ↦ᵣ ret)))))
          h :=
        by xperm_hyp hq
      have hq2 :=
        sepConj_mono (regIs_to_regOwn .x5 _)
          (sepConj_mono (regIs_to_regOwn .x6 _)
            (sepConj_mono (regIs_to_regOwn .x7 _) (fun _ hh => hh)))
          h hq1
      xperm_hyp hq2
    have hsucc :
      BitVec.ult (cglDelta nl pl) (pl >>> 10) →
        cpsTripleWithin 2 ((GuestAddrs.check_gas_limit + 36) : Word) ret CR
          (((.x7 : Reg) ↦ᵣ cglDelta nl pl) **
            ((.x6 : Reg) ↦ᵣ (pl >>> 10)) **
              (((.x10 : Reg) ↦ᵣ nl) **
                ((.x11 : Reg) ↦ᵣ pl) ** ((.x5 : Reg) ↦ᵣ (5000 : Word)) ** ((.x1 : Reg) ↦ᵣ ret)))
          (((.x10 : Reg) ↦ᵣ cglStatus nl pl) **
            ((.x11 : Reg) ↦ᵣ pl) **
              ((.x1 : Reg) ↦ᵣ ret) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7) :=
      by
      intro hlt
      have h :=
        sharedRetTail_spec CR ((GuestAddrs.check_gas_limit + 36) : Word) ret .x10 (0 : Word) nl
          (((.x11 : Reg) ↦ᵣ pl) **
            ((.x5 : Reg) ↦ᵣ (5000 : Word)) **
              ((.x6 : Reg) ↦ᵣ (pl >>> 10)) ** ((.x7 : Reg) ↦ᵣ cglDelta nl pl))
          (by
            repeat
              first
              | apply pcFree_sepConj
              | exact pcFree_regIs
              | exact pcFree_regOwn
              | exact pcFree_memIs
              | exact pcFree_memOwn
              | exact pcFree_emp
              | exact pcFree_pure
              | exact pcFree_instrAt
              | exact bytesRegion_pcFree _ _
              | exact pcFree_stackFree _ _
              | exact pcFree_dwordsIs _ _
              | exact pcFree_regsAt _ _
              | exact pcFree_frameSlotsOwn _ _
              | exact pcFree_frameSlotsSaved _ _ _
              | exact pcFree_regFileIs _)
          (by decide) halignRet
          (by rw [hCR];
            first
            | (with_reducible exact fun a i h => h)
            | ((with_reducible refine CodeReq.singleton_mono ?_); decide)
            | ((with_reducible refine CodeReq.sub_ofProg_of_lookup _ _ ?_ ?_) <;> decide))
          (by rw [hCR];
            first
            | (with_reducible exact fun a i h => h)
            | ((with_reducible refine CodeReq.singleton_mono ?_); decide)
            | ((with_reducible refine CodeReq.sub_ofProg_of_lookup _ _ ?_ ?_) <;> decide))
      refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hq => ?_) h
      unfold cglStatus
      rw [if_neg hn1, if_pos hlt]
      have hq1 :
        (((.x5 : Reg) ↦ᵣ (5000 : Word)) **
            (((.x6 : Reg) ↦ᵣ (pl >>> 10)) **
              (((.x7 : Reg) ↦ᵣ cglDelta nl pl) **
                (((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ pl) ** ((.x1 : Reg) ↦ᵣ ret)))))
          h :=
        by xperm_hyp hq
      have hq2 :=
        sepConj_mono (regIs_to_regOwn .x5 _)
          (sepConj_mono (regIs_to_regOwn .x6 _)
            (sepConj_mono (regIs_to_regOwn .x7 _) (fun _ hh => hh)))
          h hq1
      xperm_hyp hq2
    have hstGe :=
      retJoinStation_spec (cond := ¬BitVec.ult (cglDelta nl pl) (pl >>> 10)) (PT :=
        ((.x7 : Reg) ↦ᵣ cglDelta nl pl) **
          ((.x6 : Reg) ↦ᵣ (pl >>> 10)) **
            (((.x10 : Reg) ↦ᵣ nl) **
              ((.x11 : Reg) ↦ᵣ pl) ** ((.x5 : Reg) ↦ᵣ (5000 : Word)) ** ((.x1 : Reg) ↦ᵣ ret)))
        (PF :=
        ((.x7 : Reg) ↦ᵣ cglDelta nl pl) **
          ((.x6 : Reg) ↦ᵣ (pl >>> 10)) **
            (((.x10 : Reg) ↦ᵣ nl) **
              ((.x11 : Reg) ↦ᵣ pl) ** ((.x5 : Reg) ↦ᵣ (5000 : Word)) ** ((.x1 : Reg) ↦ᵣ ret)))
        hbrGe (fun h hq => by xperm_hyp hq)
        (fun h hq =>
          by
          have hq1 :
            (⌜BitVec.ult (cglDelta nl pl) (pl >>> 10)⌝ **
                (((.x7 : Reg) ↦ᵣ cglDelta nl pl) **
                  ((.x6 : Reg) ↦ᵣ (pl >>> 10)) **
                    ((.x10 : Reg) ↦ᵣ nl) **
                      ((.x11 : Reg) ↦ᵣ pl) **
                        ((.x5 : Reg) ↦ᵣ (5000 : Word)) ** ((.x1 : Reg) ↦ᵣ ret)))
              h :=
            by xperm_hyp hq
          obtain ⟨hlt, hrest⟩ := (sepConj_pure_left h).1 hq1
          exact (sepConj_pure_left h).2 ⟨fun hn => hn hlt, hrest⟩)
        (fun hge => htail2 hge)
        (fun hnge => hsucc (not_not.mp hnge))
          -- srli ; join ; guard station
          
    have hc1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hsrliF hjoin
    have hc2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc1 hstGe
    exact
      cpsTripleWithin_mono_nSteps (by omega)
        (cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => hq) hc2)
          -- ---- assemble: lui ; addiw ; minimum station ----
          
  have hluiF :=
    cpsTripleWithin_frameR
      (((.x10 : Reg) ↦ᵣ nl) **
        ((.x11 : Reg) ↦ᵣ pl) **
          ((.x1 : Reg) ↦ᵣ ret) ** ((.x6 : Reg) ↦ᵣ vf .x6) ** ((.x7 : Reg) ↦ᵣ vf .x7))
      (by
        repeat
          first
          | apply pcFree_sepConj
          | exact pcFree_regIs
          | exact pcFree_regOwn
          | exact pcFree_memIs
          | exact pcFree_memOwn
          | exact pcFree_emp
          | exact pcFree_pure
          | exact pcFree_instrAt
          | exact bytesRegion_pcFree _ _
          | exact pcFree_stackFree _ _
          | exact pcFree_dwordsIs _ _
          | exact pcFree_regsAt _ _
          | exact pcFree_frameSlotsOwn _ _
          | exact pcFree_frameSlotsSaved _ _ _
          | exact pcFree_regFileIs _)
      hlui
  have haddiwF :=
    cpsTripleWithin_frameR
      (((.x10 : Reg) ↦ᵣ nl) **
        ((.x11 : Reg) ↦ᵣ pl) **
          ((.x1 : Reg) ↦ᵣ ret) ** ((.x6 : Reg) ↦ᵣ vf .x6) ** ((.x7 : Reg) ↦ᵣ vf .x7))
      (by
        repeat
          first
          | apply pcFree_sepConj
          | exact pcFree_regIs
          | exact pcFree_regOwn
          | exact pcFree_memIs
          | exact pcFree_memOwn
          | exact pcFree_emp
          | exact pcFree_pure
          | exact pcFree_instrAt
          | exact bytesRegion_pcFree _ _
          | exact pcFree_stackFree _ _
          | exact pcFree_dwordsIs _ _
          | exact pcFree_regsAt _ _
          | exact pcFree_frameSlotsOwn _ _
          | exact pcFree_frameSlotsSaved _ _ _
          | exact pcFree_regFileIs _)
      haddiw
  have hstMin :=
    retJoinStation_spec (cond := BitVec.ult nl (5000 : Word)) (PT :=
      ((.x10 : Reg) ↦ᵣ nl) **
        ((.x5 : Reg) ↦ᵣ (5000 : Word)) **
          (((.x11 : Reg) ↦ᵣ pl) **
            ((.x1 : Reg) ↦ᵣ ret) ** ((.x6 : Reg) ↦ᵣ vf .x6) ** ((.x7 : Reg) ↦ᵣ vf .x7)))
      (PF :=
      ((.x10 : Reg) ↦ᵣ nl) **
        ((.x5 : Reg) ↦ᵣ (5000 : Word)) **
          (((.x11 : Reg) ↦ᵣ pl) **
            ((.x1 : Reg) ↦ᵣ ret) ** ((.x6 : Reg) ↦ᵣ vf .x6) ** ((.x7 : Reg) ↦ᵣ vf .x7)))
      hbrMin (fun h hq => by xperm_hyp hq) (fun h hq => by xperm_hyp hq) (fun h1 => htail1 h1)
      (fun hn1 => hfallMin hn1)
  have hc1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hluiF haddiwF
  have hc2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc1 hstMin
  exact
    cpsTripleWithin_mono_nSteps (by omega)
      (cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => hq) hc2)


-- @@ L426-426 verbatim
end CheckGasLimitSAsm


-- @@ L428-428 verbatim
end EvmAsm.Codegen
