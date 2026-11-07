/-
  Full typed-tx paths for `tx_type_dispatch` (type 1..4).
  Split from TxTypeDispatchSpec for Codegen/Programs 1500-line cap.
-/

import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.ControlFlow
import EvmAsm.Rv64.MemRegion
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.SAsm.DualReadByteScan
import EvmAsm.Rv64.SAsm.LoopFuel
import EvmAsm.Codegen.Programs.TxTypeDispatchSpec
import EvmAsm.Codegen.GuestAddrs


-- @@ L17-17 verbatim
namespace EvmAsm.Codegen.TxTypeDispatchSpec


-- @@ L19-19 verbatim
open EvmAsm.Rv64

-- @@ L20-20 verbatim
open EvmAsm.Codegen


-- @@ L22-34 verbatim
local macro "pcf" : tactic =>
  `(tactic| repeat
      first
      | apply pcFree_sepConj
      | exact pcFree_regIs
      | exact pcFree_regOwn
      | exact pcFree_memIs
      | exact pcFree_memOwn
      | exact bytesRegion_pcFree _ _
      | exact pcFree_emp
      | exact pcFree_pure)

-- Re-export private helpers needed by full typed paths.

-- @@ L35-41 verbatim
private theorem ofNat_ne_zero {a : Nat} (h0 : a ≠ 0) (hlt : a < 2 ^ 64) :
    BitVec.ofNat 64 a ≠ (0 : Word) := by
  intro h
  have h2 := congrArg BitVec.toNat h
  simp only [BitVec.toNat_ofNat] at h2
  have hz : ((0 : Word).toNat) = 0 := by decide
  omega


-- @@ L43-49 verbatim
private theorem ult_zx_192 (b : BitVec 8) (h : b.toNat < 192) :
    BitVec.ult (b.zeroExtend 64 : Word) (192 : Word) := by
  have hlt : (b.zeroExtend 64 : Word).toNat < (192 : Word).toNat := by
    have hz := SAsm.toNat_zeroExtend_byte b
    have h192 : (192 : Word).toNat = 192 := by decide
    omega
  rwa [BitVec.ult_iff_toNat_lt]


-- @@ L51-52 verbatim
private theorem base_add_zero (base : Word) :
    base + BitVec.ofNat 64 0 = base := BitVec.add_zero base


-- @@ L54-55 verbatim
private theorem type_bound : 4 * typeProg.length < 2 ^ 64 := by
  simp only [type_length]; decide


-- @@ L57-58 verbatim
private theorem D4 : D + 4 = D + BitVec.ofNat 64 (4 * 1) := by
  simp only [D, GuestAddrs.tx_type_dispatch]; decide

-- @@ L59-60 verbatim
private theorem D8 : D + 8 = D + BitVec.ofNat 64 (4 * 2) := by
  simp only [D, GuestAddrs.tx_type_dispatch]; decide

-- @@ L61-62 verbatim
private theorem D12 : D + 12 = D + BitVec.ofNat 64 (4 * 3) := by
  simp only [D, GuestAddrs.tx_type_dispatch]; decide


-- @@ L64-65 verbatim
private theorem D16 : D + 16 = D + BitVec.ofNat 64 (4 * 4) := by
  simp only [D, GuestAddrs.tx_type_dispatch]; decide

-- @@ L66-69 verbatim
private theorem D20 : D + 20 = D + BitVec.ofNat 64 (4 * 5) := by
  simp only [D, GuestAddrs.tx_type_dispatch]; decide

-- Full type-1 path: non-empty, first byte = 1 → type=1, inner=1, a0=0 (12 steps).

-- @@ L70-229 expanded
set_option maxRecDepth 8000 in
theorem txTypeDispatch_type1_spec_within (raIn txBase typePtr innerPtr oldT oldI v5 v6 : Word)
    (txBytes : List (BitVec 8)) (rest : List (BitVec 8)) (hret : (raIn &&& ~~~(1 : Word)) = raIn)
    (hbytes : txBytes = (1 : BitVec 8) :: rest) (halign : txBase.toNat % 8 = 0)
    (hover : txBase.toNat + txBytes.length < 2 ^ 64)
    (hvalid0 : isValidByteAccess (txBase + BitVec.ofNat 64 0) = true) :
    cpsTripleWithin 12 D raIn typeCode
      ((.x1 ↦ᵣ raIn) **
        (.x10 ↦ᵣ txBase) **
          (.x11 ↦ᵣ BitVec.ofNat 64 txBytes.length) **
            (.x12 ↦ᵣ typePtr) **
              (.x13 ↦ᵣ innerPtr) **
                bytesRegion txBase txBytes **
                  (typePtr ↦ₘ oldT) **
                    (innerPtr ↦ₘ oldI) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x1 ↦ᵣ raIn) **
        (.x10 ↦ᵣ (0 : Word)) **
          (.x11 ↦ᵣ BitVec.ofNat 64 txBytes.length) **
            (.x12 ↦ᵣ typePtr) **
              (.x13 ↦ᵣ innerPtr) **
                bytesRegion txBase txBytes **
                  (typePtr ↦ₘ (1 : Word)) **
                    (innerPtr ↦ₘ (1 : Word)) **
                      (.x5 ↦ᵣ (1 : Word)) ** (.x6 ↦ᵣ (1 : Word)) ** (.x0 ↦ᵣ (0 : Word))) :=
  by
  have hlen_pos : 0 < txBytes.length := by simp only [hbytes, List.length_cons]; omega
  have hlen_ne : BitVec.ofNat 64 txBytes.length ≠ (0 : Word) :=
    ofNat_ne_zero (Nat.ne_of_gt hlen_pos) (by omega)
  have hb1 : (1 : BitVec 8).toNat < 192 := by decide
  have hzx1 : (((1 : BitVec 8).zeroExtend 64) : Word) = (1 : Word) := by
    decide
      -- [0] BEQ empty ntaken
      
  have hbr0 :=
    cpsBranchWithin_extend_code
      (CodeReq.ofProg_mem_at D D typeProg 0 (.BEQ .x11 .x0 (164 : BitVec 13)) (by decide)
        (by rw [type_length]; decide) rfl type_bound)
      (beq_spec_gen_within .x11 .x0 (164 : BitVec 13) (BitVec.ofNat 64 txBytes.length) (0 : Word) D)
  have hnt0 :=
    cpsBranchWithin_ntakenStripPure2 hbr0
      (fun _ hq => by
        obtain ⟨_, _, _, _, _, hrest⟩ := hq
        exact absurd ((sepConj_pure_right _).1 hrest).2 hlen_ne)
  have hnt0F :=
    cpsTripleWithin_frameR
      ((.x1 ↦ᵣ raIn) **
        (.x10 ↦ᵣ txBase) **
          (.x12 ↦ᵣ typePtr) **
            (.x13 ↦ᵣ innerPtr) **
              bytesRegion txBase txBytes **
                (typePtr ↦ₘ oldT) ** (innerPtr ↦ₘ oldI) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6))
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
      hnt0
  have hover0 : txBase.toNat + 0 < 2 ^ 64 := by omega
  have hlbu0 :=
    bytesRegion_lbu_within .x5 .x10 txBase v5 (D + 4) txBytes 0 (by decide) halign hlen_pos hover0
      hvalid0
  have hptr : txBase + BitVec.ofNat 64 0 = txBase := base_add_zero txBase
  have hbyte : (txBytes[0]'hlen_pos).zeroExtend 64 = ((1 : BitVec 8).zeroExtend 64) := by
    simp only [hbytes, List.getElem_cons_zero]
  have hlbu0' :
    cpsTripleWithin 1 (D + 4) (D + 8) (CodeReq.singleton (D + 4) (.LBU .x5 .x10 (0 : BitVec 12)))
      ((.x10 ↦ᵣ txBase) ** (.x5 ↦ᵣ v5) ** bytesRegion txBase txBytes)
      ((.x10 ↦ᵣ txBase) ** (.x5 ↦ᵣ ((1 : BitVec 8).zeroExtend 64)) ** bytesRegion txBase txBytes) :=
    by
    have hpc : (D + 4) + 4 = D + 8 := by simp only [D, GuestAddrs.tx_type_dispatch]; decide
    rw [← hpc]
    refine
      cpsTripleWithin_weaken (fun _ hp => by rwa [hptr]) (fun _ hq => by rwa [hptr, hbyte] at hq)
        hlbu0
  have hlbuE :=
    cpsTripleWithin_extend_code
      (CodeReq.ofProg_mem_at D (D + 4) typeProg 1 (.LBU .x5 .x10 (0 : BitVec 12)) D4
        (by rw [type_length]; decide) rfl type_bound)
      hlbu0'
  have hlbuF :=
    cpsTripleWithin_frameR
      ((.x1 ↦ᵣ raIn) **
        (.x11 ↦ᵣ BitVec.ofNat 64 txBytes.length) **
          (.x12 ↦ᵣ typePtr) **
            (.x13 ↦ᵣ innerPtr) **
              (typePtr ↦ₘ oldT) ** (innerPtr ↦ₘ oldI) ** (.x6 ↦ᵣ v6) ** (.x0 ↦ᵣ (0 : Word)))
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
      hlbuE
  have hli192 := li_spec_gen_within .x6 v6 (192 : Word) (D + 8) (by decide)
  have hli192E :=
    cpsTripleWithin_extend_code
      (CodeReq.ofProg_mem_at D (D + 8) typeProg 2 (.LI .x6 (192 : Word)) D8
        (by rw [type_length]; decide) rfl type_bound)
      hli192
  have hli192F :=
    cpsTripleWithin_frameR
      ((.x1 ↦ᵣ raIn) **
        (.x10 ↦ᵣ txBase) **
          (.x11 ↦ᵣ BitVec.ofNat 64 txBytes.length) **
            (.x12 ↦ᵣ typePtr) **
              (.x13 ↦ᵣ innerPtr) **
                bytesRegion txBase txBytes **
                  (typePtr ↦ₘ oldT) **
                    (innerPtr ↦ₘ oldI) **
                      (.x5 ↦ᵣ ((1 : BitVec 8).zeroExtend 64)) ** (.x0 ↦ᵣ (0 : Word)))
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
      hli192E
  have hbr3 :=
    cpsBranchWithin_extend_code
      (CodeReq.ofProg_mem_at D (D + 12) typeProg 3 (.BGEU .x5 .x6 (168 : BitVec 13)) D12
        (by rw [type_length]; decide) rfl type_bound)
      (bgeu_spec_gen_within .x5 .x6 (168 : BitVec 13) ((1 : BitVec 8).zeroExtend 64) (192 : Word)
        (D + 12))
  have hnt3 :=
    cpsBranchWithin_ntakenStripPure2 hbr3
      (fun _ hq => by
        obtain ⟨_, _, _, _, _, hrest⟩ := hq
        exact ((sepConj_pure_right _).1 hrest).2 (ult_zx_192 _ hb1))
  have hnt3F :=
    cpsTripleWithin_frameR
      ((.x1 ↦ᵣ raIn) **
        (.x10 ↦ᵣ txBase) **
          (.x11 ↦ᵣ BitVec.ofNat 64 txBytes.length) **
            (.x12 ↦ᵣ typePtr) **
              (.x13 ↦ᵣ innerPtr) **
                bytesRegion txBase txBytes **
                  (typePtr ↦ₘ oldT) ** (innerPtr ↦ₘ oldI) ** (.x0 ↦ᵣ (0 : Word)))
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
      hnt3
  have hli1 := li_spec_gen_within .x6 (192 : Word) (1 : Word) (D + 16) (by decide)
  have hli1E :=
    cpsTripleWithin_extend_code
      (CodeReq.ofProg_mem_at D (D + 16) typeProg 4 (.LI .x6 (1 : Word)) D16
        (by rw [type_length]; decide) rfl type_bound)
      hli1
  have hli1F :=
    cpsTripleWithin_frameR
      ((.x1 ↦ᵣ raIn) **
        (.x10 ↦ᵣ txBase) **
          (.x11 ↦ᵣ BitVec.ofNat 64 txBytes.length) **
            (.x12 ↦ᵣ typePtr) **
              (.x13 ↦ᵣ innerPtr) **
                bytesRegion txBase txBytes **
                  (typePtr ↦ₘ oldT) **
                    (innerPtr ↦ₘ oldI) **
                      (.x5 ↦ᵣ ((1 : BitVec 8).zeroExtend 64)) ** (.x0 ↦ᵣ (0 : Word)))
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
      hli1E
  have hbr5 :=
    cpsBranchWithin_extend_code
      (CodeReq.ofProg_mem_at D (D + 20) typeProg 5 (.BEQ .x5 .x6 (48 : BitVec 13)) D20
        (by rw [type_length]; decide) rfl type_bound)
      (beq_spec_gen_within .x5 .x6 (48 : BitVec 13) ((1 : BitVec 8).zeroExtend 64) (1 : Word)
        (D + 20))
  have hpc5 : (D + 20) + signExtend13 (48 : BitVec 13) = Type1Li := by
    simp only [Type1Li, D, GuestAddrs.tx_type_dispatch]; decide
  rw [hpc5] at hbr5
  have htk5 :=
    cpsBranchWithin_takenStripPure2 hbr5
      (fun _ hq => by
        obtain ⟨_, _, _, _, _, hrest⟩ := hq
        exact absurd hzx1 ((sepConj_pure_right _).1 hrest).2)
  have htk5F :=
    cpsTripleWithin_frameR
      ((.x1 ↦ᵣ raIn) **
        (.x10 ↦ᵣ txBase) **
          (.x11 ↦ᵣ BitVec.ofNat 64 txBytes.length) **
            (.x12 ↦ᵣ typePtr) **
              (.x13 ↦ᵣ innerPtr) **
                bytesRegion txBase txBytes **
                  (typePtr ↦ₘ oldT) ** (innerPtr ↦ₘ oldI) ** (.x0 ↦ᵣ (0 : Word)))
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
      htk5
  have hret1 :=
    type1OkRet_spec raIn txBase typePtr innerPtr oldT oldI txBase (BitVec.ofNat 64 txBytes.length)
      ((1 : BitVec 8).zeroExtend 64) (1 : Word) txBytes hret
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hnt0F hlbuF
  have c02 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c01 hli192F
  have c03 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c02 hnt3F
  have c04 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c03 hli1F
  have c05 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c04 htk5F
  have c06 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c05 hret1
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => by xperm_hyp hq) c06


-- @@ L231-232 verbatim
private theorem D24 : D + 24 = D + BitVec.ofNat 64 (4 * 6) := by
  simp only [D, GuestAddrs.tx_type_dispatch]; decide

-- @@ L233-236 verbatim
private theorem D28 : D + 28 = D + BitVec.ofNat 64 (4 * 7) := by
  simp only [D, GuestAddrs.tx_type_dispatch]; decide

-- Full type-2 path (14 steps): prefix + LI1/BEQ-ntaken + LI2/BEQ-taken + type2OkRet.

-- @@ L237-431 expanded
set_option maxRecDepth 8000 in
theorem txTypeDispatch_type2_spec_within (raIn txBase typePtr innerPtr oldT oldI v5 v6 : Word)
    (txBytes : List (BitVec 8)) (rest : List (BitVec 8)) (hret : (raIn &&& ~~~(1 : Word)) = raIn)
    (hbytes : txBytes = (2 : BitVec 8) :: rest) (halign : txBase.toNat % 8 = 0)
    (hover : txBase.toNat + txBytes.length < 2 ^ 64)
    (hvalid0 : isValidByteAccess (txBase + BitVec.ofNat 64 0) = true) :
    cpsTripleWithin 14 D raIn typeCode
      ((.x1 ↦ᵣ raIn) **
        (.x10 ↦ᵣ txBase) **
          (.x11 ↦ᵣ BitVec.ofNat 64 txBytes.length) **
            (.x12 ↦ᵣ typePtr) **
              (.x13 ↦ᵣ innerPtr) **
                bytesRegion txBase txBytes **
                  (typePtr ↦ₘ oldT) **
                    (innerPtr ↦ₘ oldI) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x1 ↦ᵣ raIn) **
        (.x10 ↦ᵣ (0 : Word)) **
          (.x11 ↦ᵣ BitVec.ofNat 64 txBytes.length) **
            (.x12 ↦ᵣ typePtr) **
              (.x13 ↦ᵣ innerPtr) **
                bytesRegion txBase txBytes **
                  (typePtr ↦ₘ (2 : Word)) **
                    (innerPtr ↦ₘ (1 : Word)) **
                      (.x5 ↦ᵣ (2 : Word)) ** (.x6 ↦ᵣ (1 : Word)) ** (.x0 ↦ᵣ (0 : Word))) :=
  by
  have hlen_pos : 0 < txBytes.length := by simp only [hbytes, List.length_cons]; omega
  have hlen_ne : BitVec.ofNat 64 txBytes.length ≠ (0 : Word) :=
    ofNat_ne_zero (Nat.ne_of_gt hlen_pos) (by omega)
  have hb2 : (2 : BitVec 8).toNat < 192 := by decide
  have hzx2 : (((2 : BitVec 8).zeroExtend 64) : Word) = (2 : Word) := by decide
  have hne21 : (((2 : BitVec 8).zeroExtend 64) : Word) ≠ (1 : Word) := by
    decide
      -- [0] BEQ empty ntaken
      
  have hbr0 :=
    cpsBranchWithin_extend_code
      (CodeReq.ofProg_mem_at D D typeProg 0 (.BEQ .x11 .x0 (164 : BitVec 13)) (by decide)
        (by rw [type_length]; decide) rfl type_bound)
      (beq_spec_gen_within .x11 .x0 (164 : BitVec 13) (BitVec.ofNat 64 txBytes.length) (0 : Word) D)
  have hnt0 :=
    cpsBranchWithin_ntakenStripPure2 hbr0
      (fun _ hq => by
        obtain ⟨_, _, _, _, _, hrest⟩ := hq
        exact absurd ((sepConj_pure_right _).1 hrest).2 hlen_ne)
  have hnt0F :=
    cpsTripleWithin_frameR
      ((.x1 ↦ᵣ raIn) **
        (.x10 ↦ᵣ txBase) **
          (.x12 ↦ᵣ typePtr) **
            (.x13 ↦ᵣ innerPtr) **
              bytesRegion txBase txBytes **
                (typePtr ↦ₘ oldT) ** (innerPtr ↦ₘ oldI) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6))
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
      hnt0
  have hover0 : txBase.toNat + 0 < 2 ^ 64 := by omega
  have hlbu0 :=
    bytesRegion_lbu_within .x5 .x10 txBase v5 (D + 4) txBytes 0 (by decide) halign hlen_pos hover0
      hvalid0
  have hptr : txBase + BitVec.ofNat 64 0 = txBase := base_add_zero txBase
  have hbyte : (txBytes[0]'hlen_pos).zeroExtend 64 = ((2 : BitVec 8).zeroExtend 64) := by
    simp only [hbytes, List.getElem_cons_zero]
  have hlbu0' :
    cpsTripleWithin 1 (D + 4) (D + 8) (CodeReq.singleton (D + 4) (.LBU .x5 .x10 (0 : BitVec 12)))
      ((.x10 ↦ᵣ txBase) ** (.x5 ↦ᵣ v5) ** bytesRegion txBase txBytes)
      ((.x10 ↦ᵣ txBase) ** (.x5 ↦ᵣ ((2 : BitVec 8).zeroExtend 64)) ** bytesRegion txBase txBytes) :=
    by
    have hpc : (D + 4) + 4 = D + 8 := by simp only [D, GuestAddrs.tx_type_dispatch]; decide
    rw [← hpc]
    refine
      cpsTripleWithin_weaken (fun _ hp => by rwa [hptr]) (fun _ hq => by rwa [hptr, hbyte] at hq)
        hlbu0
  have hlbuE :=
    cpsTripleWithin_extend_code
      (CodeReq.ofProg_mem_at D (D + 4) typeProg 1 (.LBU .x5 .x10 (0 : BitVec 12)) D4
        (by rw [type_length]; decide) rfl type_bound)
      hlbu0'
  have hlbuF :=
    cpsTripleWithin_frameR
      ((.x1 ↦ᵣ raIn) **
        (.x11 ↦ᵣ BitVec.ofNat 64 txBytes.length) **
          (.x12 ↦ᵣ typePtr) **
            (.x13 ↦ᵣ innerPtr) **
              (typePtr ↦ₘ oldT) ** (innerPtr ↦ₘ oldI) ** (.x6 ↦ᵣ v6) ** (.x0 ↦ᵣ (0 : Word)))
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
      hlbuE
  have hli192 := li_spec_gen_within .x6 v6 (192 : Word) (D + 8) (by decide)
  have hli192E :=
    cpsTripleWithin_extend_code
      (CodeReq.ofProg_mem_at D (D + 8) typeProg 2 (.LI .x6 (192 : Word)) D8
        (by rw [type_length]; decide) rfl type_bound)
      hli192
  have hli192F :=
    cpsTripleWithin_frameR
      ((.x1 ↦ᵣ raIn) **
        (.x10 ↦ᵣ txBase) **
          (.x11 ↦ᵣ BitVec.ofNat 64 txBytes.length) **
            (.x12 ↦ᵣ typePtr) **
              (.x13 ↦ᵣ innerPtr) **
                bytesRegion txBase txBytes **
                  (typePtr ↦ₘ oldT) **
                    (innerPtr ↦ₘ oldI) **
                      (.x5 ↦ᵣ ((2 : BitVec 8).zeroExtend 64)) ** (.x0 ↦ᵣ (0 : Word)))
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
      hli192E
  have hbr3 :=
    cpsBranchWithin_extend_code
      (CodeReq.ofProg_mem_at D (D + 12) typeProg 3 (.BGEU .x5 .x6 (168 : BitVec 13)) D12
        (by rw [type_length]; decide) rfl type_bound)
      (bgeu_spec_gen_within .x5 .x6 (168 : BitVec 13) ((2 : BitVec 8).zeroExtend 64) (192 : Word)
        (D + 12))
  have hnt3 :=
    cpsBranchWithin_ntakenStripPure2 hbr3
      (fun _ hq => by
        obtain ⟨_, _, _, _, _, hrest⟩ := hq
        exact ((sepConj_pure_right _).1 hrest).2 (ult_zx_192 _ hb2))
  have hnt3F :=
    cpsTripleWithin_frameR
      ((.x1 ↦ᵣ raIn) **
        (.x10 ↦ᵣ txBase) **
          (.x11 ↦ᵣ BitVec.ofNat 64 txBytes.length) **
            (.x12 ↦ᵣ typePtr) **
              (.x13 ↦ᵣ innerPtr) **
                bytesRegion txBase txBytes **
                  (typePtr ↦ₘ oldT) ** (innerPtr ↦ₘ oldI) ** (.x0 ↦ᵣ (0 : Word)))
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
      hnt3
  have hli1 := li_spec_gen_within .x6 (192 : Word) (1 : Word) (D + 16) (by decide)
  have hli1E :=
    cpsTripleWithin_extend_code
      (CodeReq.ofProg_mem_at D (D + 16) typeProg 4 (.LI .x6 (1 : Word)) D16
        (by rw [type_length]; decide) rfl type_bound)
      hli1
  have hli1F :=
    cpsTripleWithin_frameR
      ((.x1 ↦ᵣ raIn) **
        (.x10 ↦ᵣ txBase) **
          (.x11 ↦ᵣ BitVec.ofNat 64 txBytes.length) **
            (.x12 ↦ᵣ typePtr) **
              (.x13 ↦ᵣ innerPtr) **
                bytesRegion txBase txBytes **
                  (typePtr ↦ₘ oldT) **
                    (innerPtr ↦ₘ oldI) **
                      (.x5 ↦ᵣ ((2 : BitVec 8).zeroExtend 64)) ** (.x0 ↦ᵣ (0 : Word)))
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
      hli1E
  have hbr5 :=
    cpsBranchWithin_extend_code
      (CodeReq.ofProg_mem_at D (D + 20) typeProg 5 (.BEQ .x5 .x6 (48 : BitVec 13)) D20
        (by rw [type_length]; decide) rfl type_bound)
      (beq_spec_gen_within .x5 .x6 (48 : BitVec 13) ((2 : BitVec 8).zeroExtend 64) (1 : Word)
        (D + 20))
  have hnt5 :=
    cpsBranchWithin_ntakenStripPure2 hbr5
      (fun _ hq => by
        obtain ⟨_, _, _, _, _, hrest⟩ := hq
        exact absurd ((sepConj_pure_right _).1 hrest).2 hne21)
  have hnt5F :=
    cpsTripleWithin_frameR
      ((.x1 ↦ᵣ raIn) **
        (.x10 ↦ᵣ txBase) **
          (.x11 ↦ᵣ BitVec.ofNat 64 txBytes.length) **
            (.x12 ↦ᵣ typePtr) **
              (.x13 ↦ᵣ innerPtr) **
                bytesRegion txBase txBytes **
                  (typePtr ↦ₘ oldT) ** (innerPtr ↦ₘ oldI) ** (.x0 ↦ᵣ (0 : Word)))
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
      hnt5
  have hli2 := li_spec_gen_within .x6 (1 : Word) (2 : Word) (D + 24) (by decide)
  have hli2E :=
    cpsTripleWithin_extend_code
      (CodeReq.ofProg_mem_at D (D + 24) typeProg 6 (.LI .x6 (2 : Word)) D24
        (by rw [type_length]; decide) rfl type_bound)
      hli2
  have hli2F :=
    cpsTripleWithin_frameR
      ((.x1 ↦ᵣ raIn) **
        (.x10 ↦ᵣ txBase) **
          (.x11 ↦ᵣ BitVec.ofNat 64 txBytes.length) **
            (.x12 ↦ᵣ typePtr) **
              (.x13 ↦ᵣ innerPtr) **
                bytesRegion txBase txBytes **
                  (typePtr ↦ₘ oldT) **
                    (innerPtr ↦ₘ oldI) **
                      (.x5 ↦ᵣ ((2 : BitVec 8).zeroExtend 64)) ** (.x0 ↦ᵣ (0 : Word)))
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
      hli2E
  have hbr7 :=
    cpsBranchWithin_extend_code
      (CodeReq.ofProg_mem_at D (D + 28) typeProg 7 (.BEQ .x5 .x6 (64 : BitVec 13)) D28
        (by rw [type_length]; decide) rfl type_bound)
      (beq_spec_gen_within .x5 .x6 (64 : BitVec 13) ((2 : BitVec 8).zeroExtend 64) (2 : Word)
        (D + 28))
  have hpc7 : (D + 28) + signExtend13 (64 : BitVec 13) = Type2Li := by
    simp only [Type2Li, D, GuestAddrs.tx_type_dispatch]; decide
  rw [hpc7] at hbr7
  have htk7 :=
    cpsBranchWithin_takenStripPure2 hbr7
      (fun _ hq => by
        obtain ⟨_, _, _, _, _, hrest⟩ := hq
        exact absurd hzx2 ((sepConj_pure_right _).1 hrest).2)
  have htk7F :=
    cpsTripleWithin_frameR
      ((.x1 ↦ᵣ raIn) **
        (.x10 ↦ᵣ txBase) **
          (.x11 ↦ᵣ BitVec.ofNat 64 txBytes.length) **
            (.x12 ↦ᵣ typePtr) **
              (.x13 ↦ᵣ innerPtr) **
                bytesRegion txBase txBytes **
                  (typePtr ↦ₘ oldT) ** (innerPtr ↦ₘ oldI) ** (.x0 ↦ᵣ (0 : Word)))
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
      htk7
  have hret2 :=
    type2OkRet_spec raIn txBase typePtr innerPtr oldT oldI txBase (BitVec.ofNat 64 txBytes.length)
      ((2 : BitVec 8).zeroExtend 64) (2 : Word) txBytes hret
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hnt0F hlbuF
  have c02 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c01 hli192F
  have c03 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c02 hnt3F
  have c04 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c03 hli1F
  have c05 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c04 hnt5F
  have c06 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c05 hli2F
  have c07 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c06 htk7F
  have c08 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c07 hret2
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => by xperm_hyp hq) c08


-- @@ L433-434 verbatim
private theorem D32 : D + 32 = D + BitVec.ofNat 64 (4 * 8) := by
  simp only [D, GuestAddrs.tx_type_dispatch]; decide

-- @@ L435-436 verbatim
private theorem D36 : D + 36 = D + BitVec.ofNat 64 (4 * 9) := by
  simp only [D, GuestAddrs.tx_type_dispatch]; decide

-- @@ L437-438 verbatim
private theorem D40 : D + 40 = D + BitVec.ofNat 64 (4 * 10) := by
  simp only [D, GuestAddrs.tx_type_dispatch]; decide

-- @@ L439-442 verbatim
private theorem D44 : D + 44 = D + BitVec.ofNat 64 (4 * 11) := by
  simp only [D, GuestAddrs.tx_type_dispatch]; decide

-- Full type-3 path (16 steps): type2 prefix + LI2/BEQ-ntaken + LI3/BEQ-taken + type3OkRet.

-- @@ L443-676 expanded
set_option maxRecDepth 8000 in
theorem txTypeDispatch_type3_spec_within (raIn txBase typePtr innerPtr oldT oldI v5 v6 : Word)
    (txBytes : List (BitVec 8)) (rest : List (BitVec 8)) (hret : (raIn &&& ~~~(1 : Word)) = raIn)
    (hbytes : txBytes = (3 : BitVec 8) :: rest) (halign : txBase.toNat % 8 = 0)
    (hover : txBase.toNat + txBytes.length < 2 ^ 64)
    (hvalid0 : isValidByteAccess (txBase + BitVec.ofNat 64 0) = true) :
    cpsTripleWithin 16 D raIn typeCode
      ((.x1 ↦ᵣ raIn) **
        (.x10 ↦ᵣ txBase) **
          (.x11 ↦ᵣ BitVec.ofNat 64 txBytes.length) **
            (.x12 ↦ᵣ typePtr) **
              (.x13 ↦ᵣ innerPtr) **
                bytesRegion txBase txBytes **
                  (typePtr ↦ₘ oldT) **
                    (innerPtr ↦ₘ oldI) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x1 ↦ᵣ raIn) **
        (.x10 ↦ᵣ (0 : Word)) **
          (.x11 ↦ᵣ BitVec.ofNat 64 txBytes.length) **
            (.x12 ↦ᵣ typePtr) **
              (.x13 ↦ᵣ innerPtr) **
                bytesRegion txBase txBytes **
                  (typePtr ↦ₘ (3 : Word)) **
                    (innerPtr ↦ₘ (1 : Word)) **
                      (.x5 ↦ᵣ (3 : Word)) ** (.x6 ↦ᵣ (1 : Word)) ** (.x0 ↦ᵣ (0 : Word))) :=
  by
  have hlen_pos : 0 < txBytes.length := by simp only [hbytes, List.length_cons]; omega
  have hlen_ne : BitVec.ofNat 64 txBytes.length ≠ (0 : Word) :=
    ofNat_ne_zero (Nat.ne_of_gt hlen_pos) (by omega)
  have hb3 : (3 : BitVec 8).toNat < 192 := by decide
  have hzx3 : (((3 : BitVec 8).zeroExtend 64) : Word) = (3 : Word) := by decide
  have hne31 : (((3 : BitVec 8).zeroExtend 64) : Word) ≠ (1 : Word) := by decide
  have hne32 : (((3 : BitVec 8).zeroExtend 64) : Word) ≠ (2 : Word) := by
    decide
      -- [0] BEQ empty ntaken
      
  have hbr0 :=
    cpsBranchWithin_extend_code
      (CodeReq.ofProg_mem_at D D typeProg 0 (.BEQ .x11 .x0 (164 : BitVec 13)) (by decide)
        (by rw [type_length]; decide) rfl type_bound)
      (beq_spec_gen_within .x11 .x0 (164 : BitVec 13) (BitVec.ofNat 64 txBytes.length) (0 : Word) D)
  have hnt0 :=
    cpsBranchWithin_ntakenStripPure2 hbr0
      (fun _ hq => by
        obtain ⟨_, _, _, _, _, hrest⟩ := hq
        exact absurd ((sepConj_pure_right _).1 hrest).2 hlen_ne)
  have hnt0F :=
    cpsTripleWithin_frameR
      ((.x1 ↦ᵣ raIn) **
        (.x10 ↦ᵣ txBase) **
          (.x12 ↦ᵣ typePtr) **
            (.x13 ↦ᵣ innerPtr) **
              bytesRegion txBase txBytes **
                (typePtr ↦ₘ oldT) ** (innerPtr ↦ₘ oldI) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6))
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
      hnt0
  have hover0 : txBase.toNat + 0 < 2 ^ 64 := by omega
  have hlbu0 :=
    bytesRegion_lbu_within .x5 .x10 txBase v5 (D + 4) txBytes 0 (by decide) halign hlen_pos hover0
      hvalid0
  have hptr : txBase + BitVec.ofNat 64 0 = txBase := base_add_zero txBase
  have hbyte : (txBytes[0]'hlen_pos).zeroExtend 64 = ((3 : BitVec 8).zeroExtend 64) := by
    simp only [hbytes, List.getElem_cons_zero]
  have hlbu0' :
    cpsTripleWithin 1 (D + 4) (D + 8) (CodeReq.singleton (D + 4) (.LBU .x5 .x10 (0 : BitVec 12)))
      ((.x10 ↦ᵣ txBase) ** (.x5 ↦ᵣ v5) ** bytesRegion txBase txBytes)
      ((.x10 ↦ᵣ txBase) ** (.x5 ↦ᵣ ((3 : BitVec 8).zeroExtend 64)) ** bytesRegion txBase txBytes) :=
    by
    have hpc : (D + 4) + 4 = D + 8 := by simp only [D, GuestAddrs.tx_type_dispatch]; decide
    rw [← hpc]
    refine
      cpsTripleWithin_weaken (fun _ hp => by rwa [hptr]) (fun _ hq => by rwa [hptr, hbyte] at hq)
        hlbu0
  have hlbuE :=
    cpsTripleWithin_extend_code
      (CodeReq.ofProg_mem_at D (D + 4) typeProg 1 (.LBU .x5 .x10 (0 : BitVec 12)) D4
        (by rw [type_length]; decide) rfl type_bound)
      hlbu0'
  have hlbuF :=
    cpsTripleWithin_frameR
      ((.x1 ↦ᵣ raIn) **
        (.x11 ↦ᵣ BitVec.ofNat 64 txBytes.length) **
          (.x12 ↦ᵣ typePtr) **
            (.x13 ↦ᵣ innerPtr) **
              (typePtr ↦ₘ oldT) ** (innerPtr ↦ₘ oldI) ** (.x6 ↦ᵣ v6) ** (.x0 ↦ᵣ (0 : Word)))
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
      hlbuE
  have hli192 := li_spec_gen_within .x6 v6 (192 : Word) (D + 8) (by decide)
  have hli192E :=
    cpsTripleWithin_extend_code
      (CodeReq.ofProg_mem_at D (D + 8) typeProg 2 (.LI .x6 (192 : Word)) D8
        (by rw [type_length]; decide) rfl type_bound)
      hli192
  have hli192F :=
    cpsTripleWithin_frameR
      ((.x1 ↦ᵣ raIn) **
        (.x10 ↦ᵣ txBase) **
          (.x11 ↦ᵣ BitVec.ofNat 64 txBytes.length) **
            (.x12 ↦ᵣ typePtr) **
              (.x13 ↦ᵣ innerPtr) **
                bytesRegion txBase txBytes **
                  (typePtr ↦ₘ oldT) **
                    (innerPtr ↦ₘ oldI) **
                      (.x5 ↦ᵣ ((3 : BitVec 8).zeroExtend 64)) ** (.x0 ↦ᵣ (0 : Word)))
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
      hli192E
  have hbr3 :=
    cpsBranchWithin_extend_code
      (CodeReq.ofProg_mem_at D (D + 12) typeProg 3 (.BGEU .x5 .x6 (168 : BitVec 13)) D12
        (by rw [type_length]; decide) rfl type_bound)
      (bgeu_spec_gen_within .x5 .x6 (168 : BitVec 13) ((3 : BitVec 8).zeroExtend 64) (192 : Word)
        (D + 12))
  have hnt3 :=
    cpsBranchWithin_ntakenStripPure2 hbr3
      (fun _ hq => by
        obtain ⟨_, _, _, _, _, hrest⟩ := hq
        exact ((sepConj_pure_right _).1 hrest).2 (ult_zx_192 _ hb3))
  have hnt3F :=
    cpsTripleWithin_frameR
      ((.x1 ↦ᵣ raIn) **
        (.x10 ↦ᵣ txBase) **
          (.x11 ↦ᵣ BitVec.ofNat 64 txBytes.length) **
            (.x12 ↦ᵣ typePtr) **
              (.x13 ↦ᵣ innerPtr) **
                bytesRegion txBase txBytes **
                  (typePtr ↦ₘ oldT) ** (innerPtr ↦ₘ oldI) ** (.x0 ↦ᵣ (0 : Word)))
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
      hnt3
  have hli1 := li_spec_gen_within .x6 (192 : Word) (1 : Word) (D + 16) (by decide)
  have hli1E :=
    cpsTripleWithin_extend_code
      (CodeReq.ofProg_mem_at D (D + 16) typeProg 4 (.LI .x6 (1 : Word)) D16
        (by rw [type_length]; decide) rfl type_bound)
      hli1
  have hli1F :=
    cpsTripleWithin_frameR
      ((.x1 ↦ᵣ raIn) **
        (.x10 ↦ᵣ txBase) **
          (.x11 ↦ᵣ BitVec.ofNat 64 txBytes.length) **
            (.x12 ↦ᵣ typePtr) **
              (.x13 ↦ᵣ innerPtr) **
                bytesRegion txBase txBytes **
                  (typePtr ↦ₘ oldT) **
                    (innerPtr ↦ₘ oldI) **
                      (.x5 ↦ᵣ ((3 : BitVec 8).zeroExtend 64)) ** (.x0 ↦ᵣ (0 : Word)))
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
      hli1E
  have hbr5 :=
    cpsBranchWithin_extend_code
      (CodeReq.ofProg_mem_at D (D + 20) typeProg 5 (.BEQ .x5 .x6 (48 : BitVec 13)) D20
        (by rw [type_length]; decide) rfl type_bound)
      (beq_spec_gen_within .x5 .x6 (48 : BitVec 13) ((3 : BitVec 8).zeroExtend 64) (1 : Word)
        (D + 20))
  have hnt5 :=
    cpsBranchWithin_ntakenStripPure2 hbr5
      (fun _ hq => by
        obtain ⟨_, _, _, _, _, hrest⟩ := hq
        exact absurd ((sepConj_pure_right _).1 hrest).2 hne31)
  have hnt5F :=
    cpsTripleWithin_frameR
      ((.x1 ↦ᵣ raIn) **
        (.x10 ↦ᵣ txBase) **
          (.x11 ↦ᵣ BitVec.ofNat 64 txBytes.length) **
            (.x12 ↦ᵣ typePtr) **
              (.x13 ↦ᵣ innerPtr) **
                bytesRegion txBase txBytes **
                  (typePtr ↦ₘ oldT) ** (innerPtr ↦ₘ oldI) ** (.x0 ↦ᵣ (0 : Word)))
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
      hnt5
  have hli2 := li_spec_gen_within .x6 (1 : Word) (2 : Word) (D + 24) (by decide)
  have hli2E :=
    cpsTripleWithin_extend_code
      (CodeReq.ofProg_mem_at D (D + 24) typeProg 6 (.LI .x6 (2 : Word)) D24
        (by rw [type_length]; decide) rfl type_bound)
      hli2
  have hli2F :=
    cpsTripleWithin_frameR
      ((.x1 ↦ᵣ raIn) **
        (.x10 ↦ᵣ txBase) **
          (.x11 ↦ᵣ BitVec.ofNat 64 txBytes.length) **
            (.x12 ↦ᵣ typePtr) **
              (.x13 ↦ᵣ innerPtr) **
                bytesRegion txBase txBytes **
                  (typePtr ↦ₘ oldT) **
                    (innerPtr ↦ₘ oldI) **
                      (.x5 ↦ᵣ ((3 : BitVec 8).zeroExtend 64)) ** (.x0 ↦ᵣ (0 : Word)))
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
      hli2E
  have hbr7 :=
    cpsBranchWithin_extend_code
      (CodeReq.ofProg_mem_at D (D + 28) typeProg 7 (.BEQ .x5 .x6 (64 : BitVec 13)) D28
        (by rw [type_length]; decide) rfl type_bound)
      (beq_spec_gen_within .x5 .x6 (64 : BitVec 13) ((3 : BitVec 8).zeroExtend 64) (2 : Word)
        (D + 28))
  have hnt7 :=
    cpsBranchWithin_ntakenStripPure2 hbr7
      (fun _ hq => by
        obtain ⟨_, _, _, _, _, hrest⟩ := hq
        exact absurd ((sepConj_pure_right _).1 hrest).2 hne32)
  have hnt7F :=
    cpsTripleWithin_frameR
      ((.x1 ↦ᵣ raIn) **
        (.x10 ↦ᵣ txBase) **
          (.x11 ↦ᵣ BitVec.ofNat 64 txBytes.length) **
            (.x12 ↦ᵣ typePtr) **
              (.x13 ↦ᵣ innerPtr) **
                bytesRegion txBase txBytes **
                  (typePtr ↦ₘ oldT) ** (innerPtr ↦ₘ oldI) ** (.x0 ↦ᵣ (0 : Word)))
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
      hnt7
  have hli3 := li_spec_gen_within .x6 (2 : Word) (3 : Word) (D + 32) (by decide)
  have hli3E :=
    cpsTripleWithin_extend_code
      (CodeReq.ofProg_mem_at D (D + 32) typeProg 8 (.LI .x6 (3 : Word)) D32
        (by rw [type_length]; decide) rfl type_bound)
      hli3
  have hli3F :=
    cpsTripleWithin_frameR
      ((.x1 ↦ᵣ raIn) **
        (.x10 ↦ᵣ txBase) **
          (.x11 ↦ᵣ BitVec.ofNat 64 txBytes.length) **
            (.x12 ↦ᵣ typePtr) **
              (.x13 ↦ᵣ innerPtr) **
                bytesRegion txBase txBytes **
                  (typePtr ↦ₘ oldT) **
                    (innerPtr ↦ₘ oldI) **
                      (.x5 ↦ᵣ ((3 : BitVec 8).zeroExtend 64)) ** (.x0 ↦ᵣ (0 : Word)))
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
      hli3E
  have hbr9 :=
    cpsBranchWithin_extend_code
      (CodeReq.ofProg_mem_at D (D + 36) typeProg 9 (.BEQ .x5 .x6 (80 : BitVec 13)) D36
        (by rw [type_length]; decide) rfl type_bound)
      (beq_spec_gen_within .x5 .x6 (80 : BitVec 13) ((3 : BitVec 8).zeroExtend 64) (3 : Word)
        (D + 36))
  have hpc9 : (D + 36) + signExtend13 (80 : BitVec 13) = Type3Li := by
    simp only [Type3Li, D, GuestAddrs.tx_type_dispatch]; decide
  rw [hpc9] at hbr9
  have htk9 :=
    cpsBranchWithin_takenStripPure2 hbr9
      (fun _ hq => by
        obtain ⟨_, _, _, _, _, hrest⟩ := hq
        exact absurd hzx3 ((sepConj_pure_right _).1 hrest).2)
  have htk9F :=
    cpsTripleWithin_frameR
      ((.x1 ↦ᵣ raIn) **
        (.x10 ↦ᵣ txBase) **
          (.x11 ↦ᵣ BitVec.ofNat 64 txBytes.length) **
            (.x12 ↦ᵣ typePtr) **
              (.x13 ↦ᵣ innerPtr) **
                bytesRegion txBase txBytes **
                  (typePtr ↦ₘ oldT) ** (innerPtr ↦ₘ oldI) ** (.x0 ↦ᵣ (0 : Word)))
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
      htk9
  have hret3 :=
    type3OkRet_spec raIn txBase typePtr innerPtr oldT oldI txBase (BitVec.ofNat 64 txBytes.length)
      ((3 : BitVec 8).zeroExtend 64) (3 : Word) txBytes hret
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hnt0F hlbuF
  have c02 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c01 hli192F
  have c03 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c02 hnt3F
  have c04 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c03 hli1F
  have c05 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c04 hnt5F
  have c06 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c05 hli2F
  have c07 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c06 hnt7F
  have c08 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c07 hli3F
  have c09 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c08 htk9F
  have c10 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c09 hret3
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => by xperm_hyp hq) c10


-- @@ L677-945 expanded
set_option maxRecDepth 8000 in
theorem txTypeDispatch_type4_spec_within (raIn txBase typePtr innerPtr oldT oldI v5 v6 : Word)
    (txBytes : List (BitVec 8)) (rest : List (BitVec 8)) (hret : (raIn &&& ~~~(1 : Word)) = raIn)
    (hbytes : txBytes = (4 : BitVec 8) :: rest) (halign : txBase.toNat % 8 = 0)
    (hover : txBase.toNat + txBytes.length < 2 ^ 64)
    (hvalid0 : isValidByteAccess (txBase + BitVec.ofNat 64 0) = true) :
    cpsTripleWithin 18 D raIn typeCode
      ((.x1 ↦ᵣ raIn) **
        (.x10 ↦ᵣ txBase) **
          (.x11 ↦ᵣ BitVec.ofNat 64 txBytes.length) **
            (.x12 ↦ᵣ typePtr) **
              (.x13 ↦ᵣ innerPtr) **
                bytesRegion txBase txBytes **
                  (typePtr ↦ₘ oldT) **
                    (innerPtr ↦ₘ oldI) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x1 ↦ᵣ raIn) **
        (.x10 ↦ᵣ (0 : Word)) **
          (.x11 ↦ᵣ BitVec.ofNat 64 txBytes.length) **
            (.x12 ↦ᵣ typePtr) **
              (.x13 ↦ᵣ innerPtr) **
                bytesRegion txBase txBytes **
                  (typePtr ↦ₘ (4 : Word)) **
                    (innerPtr ↦ₘ (1 : Word)) **
                      (.x5 ↦ᵣ (4 : Word)) ** (.x6 ↦ᵣ (1 : Word)) ** (.x0 ↦ᵣ (0 : Word))) :=
  by
  have hlen_pos : 0 < txBytes.length := by simp only [hbytes, List.length_cons]; omega
  have hlen_ne : BitVec.ofNat 64 txBytes.length ≠ (0 : Word) :=
    ofNat_ne_zero (Nat.ne_of_gt hlen_pos) (by omega)
  have hb4 : (4 : BitVec 8).toNat < 192 := by decide
  have hzx4 : (((4 : BitVec 8).zeroExtend 64) : Word) = (4 : Word) := by decide
  have hne41 : (((4 : BitVec 8).zeroExtend 64) : Word) ≠ (1 : Word) := by decide
  have hne42 : (((4 : BitVec 8).zeroExtend 64) : Word) ≠ (2 : Word) := by decide
  have hne43 : (((4 : BitVec 8).zeroExtend 64) : Word) ≠ (3 : Word) := by
    decide
      -- [0] BEQ empty ntaken
      
  have hbr0 :=
    cpsBranchWithin_extend_code
      (CodeReq.ofProg_mem_at D D typeProg 0 (.BEQ .x11 .x0 (164 : BitVec 13)) (by decide)
        (by rw [type_length]; decide) rfl type_bound)
      (beq_spec_gen_within .x11 .x0 (164 : BitVec 13) (BitVec.ofNat 64 txBytes.length) (0 : Word) D)
  have hnt0 :=
    cpsBranchWithin_ntakenStripPure2 hbr0
      (fun _ hq => by
        obtain ⟨_, _, _, _, _, hrest⟩ := hq
        exact absurd ((sepConj_pure_right _).1 hrest).2 hlen_ne)
  have hnt0F :=
    cpsTripleWithin_frameR
      ((.x1 ↦ᵣ raIn) **
        (.x10 ↦ᵣ txBase) **
          (.x12 ↦ᵣ typePtr) **
            (.x13 ↦ᵣ innerPtr) **
              bytesRegion txBase txBytes **
                (typePtr ↦ₘ oldT) ** (innerPtr ↦ₘ oldI) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6))
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
      hnt0
  have hover0 : txBase.toNat + 0 < 2 ^ 64 := by omega
  have hlbu0 :=
    bytesRegion_lbu_within .x5 .x10 txBase v5 (D + 4) txBytes 0 (by decide) halign hlen_pos hover0
      hvalid0
  have hptr : txBase + BitVec.ofNat 64 0 = txBase := base_add_zero txBase
  have hbyte : (txBytes[0]'hlen_pos).zeroExtend 64 = ((4 : BitVec 8).zeroExtend 64) := by
    simp only [hbytes, List.getElem_cons_zero]
  have hlbu0' :
    cpsTripleWithin 1 (D + 4) (D + 8) (CodeReq.singleton (D + 4) (.LBU .x5 .x10 (0 : BitVec 12)))
      ((.x10 ↦ᵣ txBase) ** (.x5 ↦ᵣ v5) ** bytesRegion txBase txBytes)
      ((.x10 ↦ᵣ txBase) ** (.x5 ↦ᵣ ((4 : BitVec 8).zeroExtend 64)) ** bytesRegion txBase txBytes) :=
    by
    have hpc : (D + 4) + 4 = D + 8 := by simp only [D, GuestAddrs.tx_type_dispatch]; decide
    rw [← hpc]
    refine
      cpsTripleWithin_weaken (fun _ hp => by rwa [hptr]) (fun _ hq => by rwa [hptr, hbyte] at hq)
        hlbu0
  have hlbuE :=
    cpsTripleWithin_extend_code
      (CodeReq.ofProg_mem_at D (D + 4) typeProg 1 (.LBU .x5 .x10 (0 : BitVec 12)) D4
        (by rw [type_length]; decide) rfl type_bound)
      hlbu0'
  have hlbuF :=
    cpsTripleWithin_frameR
      ((.x1 ↦ᵣ raIn) **
        (.x11 ↦ᵣ BitVec.ofNat 64 txBytes.length) **
          (.x12 ↦ᵣ typePtr) **
            (.x13 ↦ᵣ innerPtr) **
              (typePtr ↦ₘ oldT) ** (innerPtr ↦ₘ oldI) ** (.x6 ↦ᵣ v6) ** (.x0 ↦ᵣ (0 : Word)))
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
      hlbuE
  have hli192 := li_spec_gen_within .x6 v6 (192 : Word) (D + 8) (by decide)
  have hli192E :=
    cpsTripleWithin_extend_code
      (CodeReq.ofProg_mem_at D (D + 8) typeProg 2 (.LI .x6 (192 : Word)) D8
        (by rw [type_length]; decide) rfl type_bound)
      hli192
  have hli192F :=
    cpsTripleWithin_frameR
      ((.x1 ↦ᵣ raIn) **
        (.x10 ↦ᵣ txBase) **
          (.x11 ↦ᵣ BitVec.ofNat 64 txBytes.length) **
            (.x12 ↦ᵣ typePtr) **
              (.x13 ↦ᵣ innerPtr) **
                bytesRegion txBase txBytes **
                  (typePtr ↦ₘ oldT) **
                    (innerPtr ↦ₘ oldI) **
                      (.x5 ↦ᵣ ((4 : BitVec 8).zeroExtend 64)) ** (.x0 ↦ᵣ (0 : Word)))
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
      hli192E
  have hbr3 :=
    cpsBranchWithin_extend_code
      (CodeReq.ofProg_mem_at D (D + 12) typeProg 3 (.BGEU .x5 .x6 (168 : BitVec 13)) D12
        (by rw [type_length]; decide) rfl type_bound)
      (bgeu_spec_gen_within .x5 .x6 (168 : BitVec 13) ((4 : BitVec 8).zeroExtend 64) (192 : Word)
        (D + 12))
  have hnt3 :=
    cpsBranchWithin_ntakenStripPure2 hbr3
      (fun _ hq => by
        obtain ⟨_, _, _, _, _, hrest⟩ := hq
        exact ((sepConj_pure_right _).1 hrest).2 (ult_zx_192 _ hb4))
  have hnt3F :=
    cpsTripleWithin_frameR
      ((.x1 ↦ᵣ raIn) **
        (.x10 ↦ᵣ txBase) **
          (.x11 ↦ᵣ BitVec.ofNat 64 txBytes.length) **
            (.x12 ↦ᵣ typePtr) **
              (.x13 ↦ᵣ innerPtr) **
                bytesRegion txBase txBytes **
                  (typePtr ↦ₘ oldT) ** (innerPtr ↦ₘ oldI) ** (.x0 ↦ᵣ (0 : Word)))
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
      hnt3
  have hli1 := li_spec_gen_within .x6 (192 : Word) (1 : Word) (D + 16) (by decide)
  have hli1E :=
    cpsTripleWithin_extend_code
      (CodeReq.ofProg_mem_at D (D + 16) typeProg 4 (.LI .x6 (1 : Word)) D16
        (by rw [type_length]; decide) rfl type_bound)
      hli1
  have hli1F :=
    cpsTripleWithin_frameR
      ((.x1 ↦ᵣ raIn) **
        (.x10 ↦ᵣ txBase) **
          (.x11 ↦ᵣ BitVec.ofNat 64 txBytes.length) **
            (.x12 ↦ᵣ typePtr) **
              (.x13 ↦ᵣ innerPtr) **
                bytesRegion txBase txBytes **
                  (typePtr ↦ₘ oldT) **
                    (innerPtr ↦ₘ oldI) **
                      (.x5 ↦ᵣ ((4 : BitVec 8).zeroExtend 64)) ** (.x0 ↦ᵣ (0 : Word)))
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
      hli1E
  have hbr5 :=
    cpsBranchWithin_extend_code
      (CodeReq.ofProg_mem_at D (D + 20) typeProg 5 (.BEQ .x5 .x6 (48 : BitVec 13)) D20
        (by rw [type_length]; decide) rfl type_bound)
      (beq_spec_gen_within .x5 .x6 (48 : BitVec 13) ((4 : BitVec 8).zeroExtend 64) (1 : Word)
        (D + 20))
  have hnt5 :=
    cpsBranchWithin_ntakenStripPure2 hbr5
      (fun _ hq => by
        obtain ⟨_, _, _, _, _, hrest⟩ := hq
        exact absurd ((sepConj_pure_right _).1 hrest).2 hne41)
  have hnt5F :=
    cpsTripleWithin_frameR
      ((.x1 ↦ᵣ raIn) **
        (.x10 ↦ᵣ txBase) **
          (.x11 ↦ᵣ BitVec.ofNat 64 txBytes.length) **
            (.x12 ↦ᵣ typePtr) **
              (.x13 ↦ᵣ innerPtr) **
                bytesRegion txBase txBytes **
                  (typePtr ↦ₘ oldT) ** (innerPtr ↦ₘ oldI) ** (.x0 ↦ᵣ (0 : Word)))
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
      hnt5
  have hli2 := li_spec_gen_within .x6 (1 : Word) (2 : Word) (D + 24) (by decide)
  have hli2E :=
    cpsTripleWithin_extend_code
      (CodeReq.ofProg_mem_at D (D + 24) typeProg 6 (.LI .x6 (2 : Word)) D24
        (by rw [type_length]; decide) rfl type_bound)
      hli2
  have hli2F :=
    cpsTripleWithin_frameR
      ((.x1 ↦ᵣ raIn) **
        (.x10 ↦ᵣ txBase) **
          (.x11 ↦ᵣ BitVec.ofNat 64 txBytes.length) **
            (.x12 ↦ᵣ typePtr) **
              (.x13 ↦ᵣ innerPtr) **
                bytesRegion txBase txBytes **
                  (typePtr ↦ₘ oldT) **
                    (innerPtr ↦ₘ oldI) **
                      (.x5 ↦ᵣ ((4 : BitVec 8).zeroExtend 64)) ** (.x0 ↦ᵣ (0 : Word)))
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
      hli2E
  have hbr7 :=
    cpsBranchWithin_extend_code
      (CodeReq.ofProg_mem_at D (D + 28) typeProg 7 (.BEQ .x5 .x6 (64 : BitVec 13)) D28
        (by rw [type_length]; decide) rfl type_bound)
      (beq_spec_gen_within .x5 .x6 (64 : BitVec 13) ((4 : BitVec 8).zeroExtend 64) (2 : Word)
        (D + 28))
  have hnt7 :=
    cpsBranchWithin_ntakenStripPure2 hbr7
      (fun _ hq => by
        obtain ⟨_, _, _, _, _, hrest⟩ := hq
        exact absurd ((sepConj_pure_right _).1 hrest).2 hne42)
  have hnt7F :=
    cpsTripleWithin_frameR
      ((.x1 ↦ᵣ raIn) **
        (.x10 ↦ᵣ txBase) **
          (.x11 ↦ᵣ BitVec.ofNat 64 txBytes.length) **
            (.x12 ↦ᵣ typePtr) **
              (.x13 ↦ᵣ innerPtr) **
                bytesRegion txBase txBytes **
                  (typePtr ↦ₘ oldT) ** (innerPtr ↦ₘ oldI) ** (.x0 ↦ᵣ (0 : Word)))
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
      hnt7
  have hli3 := li_spec_gen_within .x6 (2 : Word) (3 : Word) (D + 32) (by decide)
  have hli3E :=
    cpsTripleWithin_extend_code
      (CodeReq.ofProg_mem_at D (D + 32) typeProg 8 (.LI .x6 (3 : Word)) D32
        (by rw [type_length]; decide) rfl type_bound)
      hli3
  have hli3F :=
    cpsTripleWithin_frameR
      ((.x1 ↦ᵣ raIn) **
        (.x10 ↦ᵣ txBase) **
          (.x11 ↦ᵣ BitVec.ofNat 64 txBytes.length) **
            (.x12 ↦ᵣ typePtr) **
              (.x13 ↦ᵣ innerPtr) **
                bytesRegion txBase txBytes **
                  (typePtr ↦ₘ oldT) **
                    (innerPtr ↦ₘ oldI) **
                      (.x5 ↦ᵣ ((4 : BitVec 8).zeroExtend 64)) ** (.x0 ↦ᵣ (0 : Word)))
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
      hli3E
  have hbr9 :=
    cpsBranchWithin_extend_code
      (CodeReq.ofProg_mem_at D (D + 36) typeProg 9 (.BEQ .x5 .x6 (80 : BitVec 13)) D36
        (by rw [type_length]; decide) rfl type_bound)
      (beq_spec_gen_within .x5 .x6 (80 : BitVec 13) ((4 : BitVec 8).zeroExtend 64) (3 : Word)
        (D + 36))
  have hnt9 :=
    cpsBranchWithin_ntakenStripPure2 hbr9
      (fun _ hq => by
        obtain ⟨_, _, _, _, _, hrest⟩ := hq
        exact absurd ((sepConj_pure_right _).1 hrest).2 hne43)
  have hnt9F :=
    cpsTripleWithin_frameR
      ((.x1 ↦ᵣ raIn) **
        (.x10 ↦ᵣ txBase) **
          (.x11 ↦ᵣ BitVec.ofNat 64 txBytes.length) **
            (.x12 ↦ᵣ typePtr) **
              (.x13 ↦ᵣ innerPtr) **
                bytesRegion txBase txBytes **
                  (typePtr ↦ₘ oldT) ** (innerPtr ↦ₘ oldI) ** (.x0 ↦ᵣ (0 : Word)))
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
      hnt9
  have hli4 := li_spec_gen_within .x6 (3 : Word) (4 : Word) (D + 40) (by decide)
  have hli4E :=
    cpsTripleWithin_extend_code
      (CodeReq.ofProg_mem_at D (D + 40) typeProg 10 (.LI .x6 (4 : Word)) D40
        (by rw [type_length]; decide) rfl type_bound)
      hli4
  have hli4F :=
    cpsTripleWithin_frameR
      ((.x1 ↦ᵣ raIn) **
        (.x10 ↦ᵣ txBase) **
          (.x11 ↦ᵣ BitVec.ofNat 64 txBytes.length) **
            (.x12 ↦ᵣ typePtr) **
              (.x13 ↦ᵣ innerPtr) **
                bytesRegion txBase txBytes **
                  (typePtr ↦ₘ oldT) **
                    (innerPtr ↦ₘ oldI) **
                      (.x5 ↦ᵣ ((4 : BitVec 8).zeroExtend 64)) ** (.x0 ↦ᵣ (0 : Word)))
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
      hli4E
  have hbr11 :=
    cpsBranchWithin_extend_code
      (CodeReq.ofProg_mem_at D (D + 44) typeProg 11 (.BEQ .x5 .x6 (96 : BitVec 13)) D44
        (by rw [type_length]; decide) rfl type_bound)
      (beq_spec_gen_within .x5 .x6 (96 : BitVec 13) ((4 : BitVec 8).zeroExtend 64) (4 : Word)
        (D + 44))
  have hpc11 : (D + 44) + signExtend13 (96 : BitVec 13) = Type4Li := by
    simp only [Type4Li, D, GuestAddrs.tx_type_dispatch]; decide
  rw [hpc11] at hbr11
  have htk11 :=
    cpsBranchWithin_takenStripPure2 hbr11
      (fun _ hq => by
        obtain ⟨_, _, _, _, _, hrest⟩ := hq
        exact absurd hzx4 ((sepConj_pure_right _).1 hrest).2)
  have htk11F :=
    cpsTripleWithin_frameR
      ((.x1 ↦ᵣ raIn) **
        (.x10 ↦ᵣ txBase) **
          (.x11 ↦ᵣ BitVec.ofNat 64 txBytes.length) **
            (.x12 ↦ᵣ typePtr) **
              (.x13 ↦ᵣ innerPtr) **
                bytesRegion txBase txBytes **
                  (typePtr ↦ₘ oldT) ** (innerPtr ↦ₘ oldI) ** (.x0 ↦ᵣ (0 : Word)))
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
      htk11
  have hret4 :=
    type4OkRet_spec raIn txBase typePtr innerPtr oldT oldI txBase (BitVec.ofNat 64 txBytes.length)
      ((4 : BitVec 8).zeroExtend 64) (4 : Word) txBytes hret
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hnt0F hlbuF
  have c02 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c01 hli192F
  have c03 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c02 hnt3F
  have c04 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c03 hli1F
  have c05 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c04 hnt5F
  have c06 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c05 hli2F
  have c07 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c06 hnt7F
  have c08 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c07 hli3F
  have c09 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c08 hnt9F
  have c10 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c09 hli4F
  have c11 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c10 htk11F
  have c12 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c11 hret4
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => by xperm_hyp hq) c12


-- @@ L947-947 verbatim
#print axioms txTypeDispatch_type1_spec_within

-- @@ L948-948 verbatim
#print axioms txTypeDispatch_type2_spec_within

-- @@ L949-949 verbatim
#print axioms txTypeDispatch_type3_spec_within

-- @@ L950-950 verbatim
#print axioms txTypeDispatch_type4_spec_within


-- @@ L952-952 verbatim
end EvmAsm.Codegen.TxTypeDispatchSpec
