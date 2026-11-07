/- Byte-identical linked-PC verification of `frame_depth_push`. -/

import EvmAsm.Codegen.Programs.CallFrameSwitch
import EvmAsm.Rv64.LaResolve
import EvmAsm.Rv64.SAsm.FramePort
import EvmAsm.Evm64.CallingConvention


-- @@ L8-8 verbatim
namespace EvmAsm.Codegen

-- @@ L9-9 verbatim
open EvmAsm.Rv64 EvmAsm.Rv64.SAsm

-- @@ L10-10 verbatim
namespace FrameDepthPushSAsm


-- @@ L12-16 verbatim
def frameDepthPushBody : List Instr :=
  [ .AUIPC .x5 (laHi GuestAddrs.evm_call_depth GuestAddrs.frame_depth_push),
    .ADDI .x5 .x5 (laLo GuestAddrs.evm_call_depth GuestAddrs.frame_depth_push),
    .LD .x10 .x5 (0 : BitVec 12), .ADDI .x10 .x10 (1 : BitVec 12),
    .SD .x5 .x10 (0 : BitVec 12) ]


-- @@ L18-19 verbatim
theorem frameDepthPush_byte_tie :
    frameDepthPushBody ++ [.JALR .x0 .x1 (0 : BitVec 12)] = frameDepthPush_prog := by rfl


-- @@ L21-22 verbatim
def frameDepthPushCr : CodeReq :=
  CodeReq.ofProg (GuestAddrs.frame_depth_push : Word) frameDepthPush_prog


-- @@ L24-86 expanded
theorem frameDepthPush_spec (depth old5 old10 ret : Word) (halign : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin 6 (GuestAddrs.frame_depth_push : Word) ret frameDepthPushCr
      (((.x5 : Reg) ↦ᵣ old5) **
        ((.x10 : Reg) ↦ᵣ old10) **
          ((.x1 : Reg) ↦ᵣ ret) ** ((GuestAddrs.evm_call_depth : Word) ↦ₘ depth))
      (((.x5 : Reg) ↦ᵣ (GuestAddrs.evm_call_depth : Word)) **
        ((.x10 : Reg) ↦ᵣ (depth + 1)) **
          ((.x1 : Reg) ↦ᵣ ret) ** ((GuestAddrs.evm_call_depth : Word) ↦ₘ (depth + 1))) :=
  by
  have hla :=
    la_materialize_within .x5 old5 (GuestAddrs.frame_depth_push : Word)
      (GuestAddrs.evm_call_depth : Word) (cr := frameDepthPushCr) (by decide) (by decide)
      (by unfold frameDepthPushCr;
        first
        | (with_reducible exact fun a i h => h)
        | ((with_reducible refine CodeReq.singleton_mono ?_); decide)
        | ((with_reducible refine CodeReq.sub_ofProg_of_lookup _ _ ?_ ?_) <;> decide))
      (by unfold frameDepthPushCr;
        first
        | (with_reducible exact fun a i h => h)
        | ((with_reducible refine CodeReq.singleton_mono ?_); decide)
        | ((with_reducible refine CodeReq.sub_ofProg_of_lookup _ _ ?_ ?_) <;> decide))
  rw [show (GuestAddrs.frame_depth_push : Word) + 8 = (GuestAddrs.frame_depth_push + 8 : Word) from
      by decide] at hla
  have hlaF :=
    cpsTripleWithin_frameR
      (((.x10 : Reg) ↦ᵣ old10) **
        ((.x1 : Reg) ↦ᵣ ret) ** ((GuestAddrs.evm_call_depth : Word) ↦ₘ depth))
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
      hla
  have hld0 :=
    ld_spec_gen_within .x10 .x5 (GuestAddrs.evm_call_depth : Word) old10 depth 0
      (GuestAddrs.frame_depth_push + 8 : Word) (by decide)
  rw [show
      (GuestAddrs.evm_call_depth : Word) + signExtend12 (0 : BitVec 12) =
        (GuestAddrs.evm_call_depth : Word)
      from by decide,
    show (GuestAddrs.frame_depth_push + 8 : Word) + 4 = (GuestAddrs.frame_depth_push + 12 : Word)
      from by decide] at hld0
  have hld :=
    liftCode (cr' := frameDepthPushCr) hld0
      (by unfold frameDepthPushCr;
        first
        | (with_reducible exact fun a i h => h)
        | ((with_reducible refine CodeReq.singleton_mono ?_); decide)
        | ((with_reducible refine CodeReq.sub_ofProg_of_lookup _ _ ?_ ?_) <;> decide))
  have hldF :=
    cpsTripleWithin_frameR (((.x1 : Reg) ↦ᵣ ret))
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
      hld
  have hadd0 :=
    addi_spec_gen_same_within .x10 depth 1 (GuestAddrs.frame_depth_push + 12 : Word) (by decide)
  rw [show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide,
    show (GuestAddrs.frame_depth_push + 12 : Word) + 4 = (GuestAddrs.frame_depth_push + 16 : Word)
      from by decide] at hadd0
  have hadd :=
    liftCode (cr' := frameDepthPushCr) hadd0
      (by unfold frameDepthPushCr;
        first
        | (with_reducible exact fun a i h => h)
        | ((with_reducible refine CodeReq.singleton_mono ?_); decide)
        | ((with_reducible refine CodeReq.sub_ofProg_of_lookup _ _ ?_ ?_) <;> decide))
  have haddF :=
    cpsTripleWithin_frameR
      (((.x5 : Reg) ↦ᵣ (GuestAddrs.evm_call_depth : Word)) **
        ((.x1 : Reg) ↦ᵣ ret) ** ((GuestAddrs.evm_call_depth : Word) ↦ₘ depth))
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
      hadd
  have hsd0 :=
    sd_spec_gen_within .x5 .x10 (GuestAddrs.evm_call_depth : Word) (depth + 1) depth 0
      (GuestAddrs.frame_depth_push + 16 : Word)
  rw [show
      (GuestAddrs.evm_call_depth : Word) + signExtend12 (0 : BitVec 12) =
        (GuestAddrs.evm_call_depth : Word)
      from by decide,
    show (GuestAddrs.frame_depth_push + 16 : Word) + 4 = (GuestAddrs.frame_depth_push + 20 : Word)
      from by decide] at hsd0
  have hsd :=
    liftCode (cr' := frameDepthPushCr) hsd0
      (by unfold frameDepthPushCr;
        first
        | (with_reducible exact fun a i h => h)
        | ((with_reducible refine CodeReq.singleton_mono ?_); decide)
        | ((with_reducible refine CodeReq.sub_ofProg_of_lookup _ _ ?_ ?_) <;> decide))
  have hsdF :=
    cpsTripleWithin_frameR (((.x1 : Reg) ↦ᵣ ret))
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
      hsd
  have hret0 := EvmAsm.Evm64.ret_spec_within' (GuestAddrs.frame_depth_push + 20 : Word) ret
  rw [halign] at hret0
  have hret :=
    liftCode (cr' := frameDepthPushCr) hret0
      (by unfold frameDepthPushCr;
        first
        | (with_reducible exact fun a i h => h)
        | ((with_reducible refine CodeReq.singleton_mono ?_); decide)
        | ((with_reducible refine CodeReq.sub_ofProg_of_lookup _ _ ?_ ?_) <;> decide))
  have hretF :=
    cpsTripleWithin_frameR
      (((.x5 : Reg) ↦ᵣ (GuestAddrs.evm_call_depth : Word)) **
        ((.x10 : Reg) ↦ᵣ (depth + 1)) ** ((GuestAddrs.evm_call_depth : Word) ↦ₘ (depth + 1)))
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
      hret
  have h12 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hlaF hldF
  have h123 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h12 haddF
  have h1234 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h123 hsdF
  have h12345 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h1234 hretF
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => by xperm_hyp hq) h12345


-- @@ L88-88 verbatim
end FrameDepthPushSAsm

-- @@ L89-89 verbatim
end EvmAsm.Codegen
