/-
  Extract setup + call + success BNE (instr 14-19) for `tx_intrinsic_state_gas`.

  la to_buf / is_creation → jal tx_extract_to_address → bne a0≠0 fail.
  Success arm under ExtractAssumed named hyp.
-/

import EvmAsm.Codegen.Programs.TxIntrinsicStateGasEpilogue
import EvmAsm.Rv64.LaResolve
import EvmAsm.Rv64.SAsm.AbiFrameCall
import EvmAsm.Rv64.Tactics.RunBlock
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Codegen.AsmReloc


-- @@ L15-15 verbatim
namespace EvmAsm.Codegen.TxIntrinsicStateGasSpec


-- @@ L17-17 verbatim
open EvmAsm.Rv64

-- @@ L18-18 verbatim
open EvmAsm.Rv64.SAsm

-- @@ L19-19 verbatim
open EvmAsm.Rv64.Tactics

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
      | exact pcFree_emp
      | exact pcFree_pure
      | exact bytesRegion_pcFree _ _
      | exact pcFree_regsAt _ _
      | exact pcFree_frameSlotsSaved _ _ _)


-- @@ L36-36 verbatim
abbrev ToBufAddr : Word := BitVec.ofNat 64 GuestAddrs.tis_to_buf

-- @@ L37-37 verbatim
abbrev IsCreationAddr : Word := BitVec.ofNat 64 GuestAddrs.tis_is_creation

-- @@ L38-38 verbatim
abbrev TypeAddr : Word := BitVec.ofNat 64 GuestAddrs.tis_type

-- @@ L39-39 verbatim
abbrev InnerOffAddr : Word := BitVec.ofNat 64 GuestAddrs.tis_inner_off

-- @@ L40-40 verbatim
abbrev ExtractEntry : Word := BitVec.ofNat 64 GuestAddrs.tx_extract_to_address

-- @@ L41-41 verbatim
abbrev TypeEntry : Word := BitVec.ofNat 64 GuestAddrs.tx_type_dispatch


-- @@ L43-43 verbatim
abbrev LinkExtract : Word := T + 76

-- @@ L44-44 verbatim
abbrev AfterExtractBne : Word := T + 80

-- @@ L45-45 verbatim
abbrev Fail1 : Word := T + 156


-- @@ L47-48 verbatim
abbrev extractJalOff : BitVec 21 :=
  jalOff GuestAddrs.tx_extract_to_address (GuestAddrs.tx_intrinsic_state_gas + 72)


-- @@ L50-75 verbatim
/-- `la x12, tis_to_buf` at T+56 → T+64. -/
theorem tisLaToBuf (v : Word) :
    cpsTripleWithin 2 (T + 56) (T + 64) fullCode
      (.x12 ↦ᵣ v) (.x12 ↦ᵣ ToBufAddr) := by
  have hau : ∀ a i, CodeReq.singleton (T + 56)
      (.AUIPC .x12 (Codegen.laHi GuestAddrs.tis_to_buf
        (GuestAddrs.tx_intrinsic_state_gas + 56)))
        a = some i → fullCode a = some i := fun a i hi => tis_mono a i
    (CodeReq.ofProg_mem_at T (T + 56) tisProg 14
      (.AUIPC .x12 (Codegen.laHi GuestAddrs.tis_to_buf
        (GuestAddrs.tx_intrinsic_state_gas + 56)))
      (by bv_omega) (by rw [tis_length]; decide) rfl
      (by rw [tis_length]; decide) a i hi)
  have had : ∀ a i, CodeReq.singleton (T + 60)
      (.ADDI .x12 .x12 (Codegen.laLo GuestAddrs.tis_to_buf
        (GuestAddrs.tx_intrinsic_state_gas + 56)))
        a = some i → fullCode a = some i := fun a i hi => tis_mono a i
    (CodeReq.ofProg_mem_at T (T + 60) tisProg 15
      (.ADDI .x12 .x12 (Codegen.laLo GuestAddrs.tis_to_buf
        (GuestAddrs.tx_intrinsic_state_gas + 56)))
      (by bv_omega) (by rw [tis_length]; decide) rfl
      (by rw [tis_length]; decide) a i hi)
  have h := la_materialize_within .x12 v (T + 56) ToBufAddr
    (by decide) (by decide) hau had
  rw [show (T + 56 : Word) + 8 = T + 64 from by bv_omega] at h
  exact h


-- @@ L77-102 verbatim
/-- `la x13, tis_is_creation` at T+64 → T+72. -/
theorem tisLaIsCreation (v : Word) :
    cpsTripleWithin 2 (T + 64) (T + 72) fullCode
      (.x13 ↦ᵣ v) (.x13 ↦ᵣ IsCreationAddr) := by
  have hau : ∀ a i, CodeReq.singleton (T + 64)
      (.AUIPC .x13 (Codegen.laHi GuestAddrs.tis_is_creation
        (GuestAddrs.tx_intrinsic_state_gas + 64)))
        a = some i → fullCode a = some i := fun a i hi => tis_mono a i
    (CodeReq.ofProg_mem_at T (T + 64) tisProg 16
      (.AUIPC .x13 (Codegen.laHi GuestAddrs.tis_is_creation
        (GuestAddrs.tx_intrinsic_state_gas + 64)))
      (by bv_omega) (by rw [tis_length]; decide) rfl
      (by rw [tis_length]; decide) a i hi)
  have had : ∀ a i, CodeReq.singleton (T + 68)
      (.ADDI .x13 .x13 (Codegen.laLo GuestAddrs.tis_is_creation
        (GuestAddrs.tx_intrinsic_state_gas + 64)))
        a = some i → fullCode a = some i := fun a i hi => tis_mono a i
    (CodeReq.ofProg_mem_at T (T + 68) tisProg 17
      (.ADDI .x13 .x13 (Codegen.laLo GuestAddrs.tis_is_creation
        (GuestAddrs.tx_intrinsic_state_gas + 64)))
      (by bv_omega) (by rw [tis_length]; decide) rfl
      (by rw [tis_length]; decide) a i hi)
  have h := la_materialize_within .x13 v (T + 64) IsCreationAddr
    (by decide) (by decide) hau had
  rw [show (T + 64 : Word) + 8 = T + 72 from by bv_omega] at h
  exact h


-- @@ L104-125 expanded
set_option maxRecDepth 8000 in
/-- Setup: two `la`s (instr 14-17). a0/a1 already txBase/len from prologue. -/
theorem tisExtractSetup (txBase txLenW outPtr : Word) (v12 v13 : Word) :
    cpsTripleWithin 4 (T + 56) (T + 72) fullCode
      ((.x10 ↦ᵣ txBase) ** (.x11 ↦ᵣ txLenW) ** (.x12 ↦ᵣ v12) ** (.x13 ↦ᵣ v13) ** (.x18 ↦ᵣ outPtr))
      ((.x10 ↦ᵣ txBase) **
        (.x11 ↦ᵣ txLenW) ** (.x12 ↦ᵣ ToBufAddr) ** (.x13 ↦ᵣ IsCreationAddr) ** (.x18 ↦ᵣ outPtr)) :=
  by
  have h0 := tisLaToBuf v12
  have h0F :=
    cpsTripleWithin_frameR
      ((.x10 ↦ᵣ txBase) ** (.x11 ↦ᵣ txLenW) ** (.x13 ↦ᵣ v13) ** (.x18 ↦ᵣ outPtr))
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
      h0
  have h1 := tisLaIsCreation v13
  have h1F :=
    cpsTripleWithin_frameR
      ((.x10 ↦ᵣ txBase) ** (.x11 ↦ᵣ txLenW) ** (.x12 ↦ᵣ ToBufAddr) ** (.x18 ↦ᵣ outPtr))
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
      h1
  have h01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h0F h1F
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => by xperm_hyp hq) h01


-- @@ L127-136 verbatim
/-- Callee footprint for extract call (no ra). -/
def extractCalleeP (txBase lenW : Word) (txBytes : List (BitVec 8)) : Assertion :=
  (.x10 ↦ᵣ txBase) ** (.x11 ↦ᵣ lenW) **
  (.x12 ↦ᵣ ToBufAddr) ** (.x13 ↦ᵣ IsCreationAddr) **
  bytesRegion txBase txBytes **
  memOwn ToBufAddr ** memOwn IsCreationAddr **
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
  regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
  regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
  (.x0 ↦ᵣ (0 : Word))


-- @@ L138-146 verbatim
def extractCalleeQ (txBase : Word) (txBytes : List (BitVec 8)) : Assertion :=
  (.x10 ↦ᵣ (0 : Word)) **
  bytesRegion txBase txBytes **
  memOwn ToBufAddr ** memOwn IsCreationAddr **
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
  regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
  regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
  regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
  (.x0 ↦ᵣ (0 : Word))


-- @@ L148-150 expanded
theorem extractCalleeP_pcFree (txBase lenW : Word) (txBytes : List (BitVec 8)) :
    (extractCalleeP txBase lenW txBytes).pcFree := by unfold extractCalleeP;
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
    | exact pcFree_regFileIs _


-- @@ L152-187 verbatim
set_option maxRecDepth 8000 in
/-- Call extract under ExtractAssumed; success a0=0 at LinkExtract. -/
theorem tisExtractCall
    (asm : ExtractAssumed fullCode)
    (hentry : asm.entry = ExtractEntry)
    (txBase lenW : Word) (txBytes : List (BitVec 8))
    (old1 : Word)
    (hlen : lenW = BitVec.ofNat 64 txBytes.length) :
    cpsTripleWithin (1 + nExtractSteps) (T + 72) LinkExtract fullCode
      ((.x1 ↦ᵣ old1) ** extractCalleeP txBase lenW txBytes)
      ((.x1 ↦ᵣ LinkExtract) ** extractCalleeQ txBase txBytes) := by
  have hret : (LinkExtract &&& ~~~(1 : Word)) = LinkExtract := by
    simp only [LinkExtract, T]; decide
  have hcallee0 := asm.success_flat LinkExtract txBase lenW
    ToBufAddr IsCreationAddr txBytes hret hlen
  have hcallee0' : cpsTripleWithin nExtractSteps asm.entry LinkExtract fullCode
      ((.x1 ↦ᵣ LinkExtract) ** extractCalleeP txBase lenW txBytes)
      ((.x1 ↦ᵣ LinkExtract) ** extractCalleeQ txBase txBytes) := by
    unfold extractCalleeP extractCalleeQ
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hcallee0
  have hcallee : cpsTripleWithin nExtractSteps ExtractEntry LinkExtract fullCode
      ((.x1 ↦ᵣ LinkExtract) ** extractCalleeP txBase lenW txBytes)
      ((.x1 ↦ᵣ LinkExtract) ** extractCalleeQ txBase txBytes) := by
    rw [← hentry]; exact hcallee0'
  have hcall := callWithin_spec (T + 72) ExtractEntry old1 extractJalOff nExtractSteps
    (by show (T + 72) + signExtend21 extractJalOff = ExtractEntry; decide)
    (fun a i hi => tis_mono a i
      (CodeReq.ofProg_mem_at T (T + 72) tisProg 18
        (.JAL .x1 extractJalOff) (by bv_omega) (by rw [tis_length]; decide) rfl
        (by rw [tis_length]; decide) a i hi))
    (extractCalleeP_pcFree txBase lenW txBytes)
    hcallee
  rw [show (T + 72 + 4 : Word) = LinkExtract from by
    simp only [LinkExtract]; bv_omega] at hcall
  exact hcall


-- @@ L189-210 verbatim
set_option maxRecDepth 8000 in
/-- BNE a0≠0 fail: ntaken when a0=0 → AfterExtractBne. -/
theorem tisExtractBneOk :
    cpsTripleWithin 1 LinkExtract AfterExtractBne fullCode
      ((.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) := by
  have hbr := bne_spec_gen_within .x10 .x0 (80 : BitVec 13)
    (0 : Word) (0 : Word) LinkExtract
  have hbrC := cpsBranchWithin_extend_code
    (fun a i hi => tis_mono a i
      (CodeReq.ofProg_mem_at T LinkExtract tisProg 19
        (.BNE .x10 .x0 (80 : BitVec 13))
        (by simp only [LinkExtract]; bv_omega)
        (by rw [tis_length]; decide) rfl
        (by rw [tis_length]; decide) a i hi)) hbr
  have hnt := cpsBranchWithin_ntakenStripPure2 hbrC (fun _ hQt => by
    obtain ⟨_, _, _, _, _, hrest⟩ := hQt
    exact absurd rfl ((sepConj_pure_right _).1 hrest).2)
  have hpc : LinkExtract + 4 = AfterExtractBne := by
    simp only [LinkExtract, AfterExtractBne]; bv_omega
  rw [hpc] at hnt
  exact hnt


-- @@ L212-264 expanded
set_option maxRecDepth 8000 in
/-- Extract setup + call + BNE ok under ExtractAssumed. -/
theorem tisExtractSuccess (asm : ExtractAssumed fullCode) (hentry : asm.entry = ExtractEntry)
    (txBase lenW outPtr : Word) (txBytes : List (BitVec 8)) (old1 v12 v13 : Word)
    (hlen : lenW = BitVec.ofNat 64 txBytes.length) :
    cpsTripleWithin (4 + (1 + nExtractSteps) + 1) (T + 56) AfterExtractBne fullCode
      ((.x1 ↦ᵣ old1) **
        (.x10 ↦ᵣ txBase) **
          (.x11 ↦ᵣ lenW) **
            (.x12 ↦ᵣ v12) **
              (.x13 ↦ᵣ v13) **
                (.x18 ↦ᵣ outPtr) **
                  bytesRegion txBase txBytes **
                    memOwn ToBufAddr **
                      memOwn IsCreationAddr **
                        regOwn .x5 **
                          regOwn .x6 **
                            regOwn .x7 **
                              regOwn .x14 **
                                regOwn .x15 **
                                  regOwn .x16 **
                                    regOwn .x28 **
                                      regOwn .x29 **
                                        regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)))
      ((.x1 ↦ᵣ LinkExtract) **
        (.x10 ↦ᵣ (0 : Word)) **
          (.x0 ↦ᵣ (0 : Word)) **
            (.x18 ↦ᵣ outPtr) **
              bytesRegion txBase txBytes **
                memOwn ToBufAddr **
                  memOwn IsCreationAddr **
                    regOwn .x5 **
                      regOwn .x6 **
                        regOwn .x7 **
                          regOwn .x11 **
                            regOwn .x12 **
                              regOwn .x13 **
                                regOwn .x14 **
                                  regOwn .x15 **
                                    regOwn .x16 **
                                      regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31) :=
  by
  have hsetup := tisExtractSetup txBase lenW outPtr v12 v13
  have hsetupF :=
    cpsTripleWithin_frameR
      ((.x1 ↦ᵣ old1) **
        bytesRegion txBase txBytes **
          memOwn ToBufAddr **
            memOwn IsCreationAddr **
              regOwn .x5 **
                regOwn .x6 **
                  regOwn .x7 **
                    regOwn .x14 **
                      regOwn .x15 **
                        regOwn .x16 **
                          regOwn .x28 **
                            regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)))
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
      hsetup
  have hcall := tisExtractCall asm hentry txBase lenW txBytes old1 hlen
  have hcallF := cpsTripleWithin_frameR (.x18 ↦ᵣ outPtr) (by exact pcFree_regIs) hcall
  have h01 :=
    cpsTripleWithin_seq_perm_same_cr
      (fun _ hp => by
        unfold extractCalleeP at *
        xperm_hyp hp)
      hsetupF hcallF
  have hbne := tisExtractBneOk
  have hbneF :=
    cpsTripleWithin_frameR
      ((.x1 ↦ᵣ LinkExtract) **
        (.x18 ↦ᵣ outPtr) **
          bytesRegion txBase txBytes **
            memOwn ToBufAddr **
              memOwn IsCreationAddr **
                regOwn .x5 **
                  regOwn .x6 **
                    regOwn .x7 **
                      regOwn .x11 **
                        regOwn .x12 **
                          regOwn .x13 **
                            regOwn .x14 **
                              regOwn .x15 **
                                regOwn .x16 **
                                  regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)
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
      hbne
  have h12 :=
    cpsTripleWithin_seq_perm_same_cr
      (fun _ hp => by
        unfold extractCalleeQ at *
        xperm_hyp hp)
      h01 hbneF
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => by xperm_hyp hq) h12


-- @@ L266-266 verbatim
end EvmAsm.Codegen.TxIntrinsicStateGasSpec


