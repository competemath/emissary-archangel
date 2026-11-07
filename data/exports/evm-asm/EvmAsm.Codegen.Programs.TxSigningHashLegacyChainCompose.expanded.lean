/-
  K146 chain-buffer setup and loop composition.

  The loop itself is proved in `TxSigningHashLegacyLoopSpec`.  This file only
  supplies the linked K146 `la`/`li` setup and lifts that local loop contract
  to the deployed union, so this boundary can be reviewed independently of
  the later encoding and hashing stages.
-/

import EvmAsm.Codegen.Programs.TxSigningHashLegacyBodyCompose


-- @@ L12-12 verbatim
namespace EvmAsm.Codegen.TxSigningHashLegacyChainCompose


-- @@ L14-14 verbatim
open EvmAsm.Rv64 EvmAsm.Rv64.SAsm

-- @@ L15-15 verbatim
open EvmAsm.Codegen

-- @@ L16-16 verbatim
open EvmAsm.Codegen.TxSigningHashLegacySpec

-- @@ L17-17 verbatim
open EvmAsm.Codegen.TxSigningHashLegacyCompose

-- @@ L18-18 verbatim
open EvmAsm.Codegen.TxSigningHashLegacyLoopSpec


-- @@ L20-20 verbatim
abbrev legacyChainInitPtrPC : Word := legacyH + 160


-- @@ L22-26 verbatim
theorem legacy_la_chain_init_hi :
    Codegen.laHi GuestAddrs.t155_chain_be
        (GuestAddrs.tx_signing_hash_legacy_eip155 + 160) =
      Rv64.laHi legacyChainInitPtrPC legacyLinkedChainPtr := by
  decide


-- @@ L28-32 verbatim
theorem legacy_la_chain_init_lo :
    Codegen.laLo GuestAddrs.t155_chain_be
        (GuestAddrs.tx_signing_hash_legacy_eip155 + 160) =
      Rv64.laLo legacyChainInitPtrPC legacyLinkedChainPtr := by
  decide


-- @@ L34-36 verbatim
theorem legacy_la_chain_init_range :
    laInRange legacyChainInitPtrPC legacyLinkedChainPtr := by
  decide


-- @@ L38-66 verbatim
theorem legacyChainInitPtr_spec (v5 : Word) :
    cpsTripleWithin 2 (legacyH + 160) (legacyH + 168) legacyFullCode
      (.x5 ↦ᵣ v5) (.x5 ↦ᵣ legacyLinkedChainPtr) := by
  have hau : ∀ a i,
      CodeReq.singleton (legacyH + 160)
        (.AUIPC .x5 (Rv64.laHi legacyChainInitPtrPC legacyLinkedChainPtr)) a =
          some i → legacyFullCode a = some i := by
    intro a i hi
    have hmem := legacy_mem_at (legacyH + 160) 40
      (.AUIPC .x5 (Codegen.laHi GuestAddrs.t155_chain_be
        (GuestAddrs.tx_signing_hash_legacy_eip155 + 160))) (by decide)
      (by decide) (by intro h; rfl)
    exact hmem a i (by rwa [← legacy_la_chain_init_hi] at hi)
  have had : ∀ a i,
      CodeReq.singleton ((legacyH + 160) + 4)
        (.ADDI .x5 .x5 (Rv64.laLo legacyChainInitPtrPC legacyLinkedChainPtr)) a =
          some i → legacyFullCode a = some i := by
    intro a i hi
    have hmem := legacy_mem_at (legacyH + 164) 41
      (.ADDI .x5 .x5 (Codegen.laLo GuestAddrs.t155_chain_be
        (GuestAddrs.tx_signing_hash_legacy_eip155 + 160))) (by decide)
      (by decide) (by intro h; rfl)
    have hpc : (legacyH + 160 : Word) + 4 = legacyH + 164 := by decide
    rw [hpc, ← legacy_la_chain_init_lo] at hi
    exact hmem a i hi
  have hla := la_materialize_within .x5 v5 legacyChainInitPtrPC
    legacyLinkedChainPtr (by decide) legacy_la_chain_init_range hau had
  rw [show (legacyH + 160 : Word) + 8 = legacyH + 168 from by decide] at hla
  exact hla


-- @@ L68-215 expanded
theorem legacyChainLoopSetup_spec (v5 v6 v7 v28 chainId : Word) (F : Assertion) (hF : F.pcFree)
    (halign : legacyLinkedChainPtr.toNat % 8 = 0) (hover : legacyLinkedChainPtr.toNat + 8 ≤ 2 ^ 64)
    (hvalid : ∀ k, k < 8 → isValidByteAccess (legacyLinkedChainPtr + BitVec.ofNat 64 k) = true)
    (hbound : 4 * loopProg.length < 2 ^ 64) :
    cpsTripleWithin 68 (legacyH + 160) (legacyH + 204) legacyFullCode
      (((.x5 : Reg) ↦ᵣ v5) **
        ((.x6 : Reg) ↦ᵣ v6) **
          ((.x7 : Reg) ↦ᵣ v7) **
            ((.x18 : Reg) ↦ᵣ chainId) **
              ((.x28 : Reg) ↦ᵣ v28) **
                ((.x0 : Reg) ↦ᵣ (0 : Word)) **
                  bytesRegion legacyLinkedChainPtr (List.replicate 8 0) ** F)
      (((.x5 : Reg) ↦ᵣ (legacyLinkedChainPtr + BitVec.ofNat 64 8)) **
        ((.x6 : Reg) ↦ᵣ (-1 : Word)) **
          ((.x18 : Reg) ↦ᵣ chainId) **
            ((.x0 : Reg) ↦ᵣ (0 : Word)) **
              regOwn .x7 **
                regOwn .x28 ** bytesRegion legacyLinkedChainPtr (chainBytes chainId) ** F) :=
  by
  have hla := legacyChainInitPtr_spec v5
  have hlaF :=
    cpsTripleWithin_frameR
      (((.x6 : Reg) ↦ᵣ v6) **
        ((.x7 : Reg) ↦ᵣ v7) **
          ((.x18 : Reg) ↦ᵣ chainId) **
            ((.x28 : Reg) ↦ᵣ v28) **
              ((.x0 : Reg) ↦ᵣ (0 : Word)) **
                bytesRegion legacyLinkedChainPtr (List.replicate 8 0) ** F)
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
          | exact pcFree_regFileIs _;
        exact hF)
      hla
  have hlaW :
    cpsTripleWithin 2 (legacyH + 160) (legacyH + 168) legacyFullCode
      (((.x5 : Reg) ↦ᵣ v5) **
        ((.x6 : Reg) ↦ᵣ v6) **
          ((.x7 : Reg) ↦ᵣ v7) **
            ((.x18 : Reg) ↦ᵣ chainId) **
              ((.x28 : Reg) ↦ᵣ v28) **
                ((.x0 : Reg) ↦ᵣ (0 : Word)) **
                  bytesRegion legacyLinkedChainPtr (List.replicate 8 0) ** F)
      (((.x5 : Reg) ↦ᵣ legacyLinkedChainPtr) **
        ((.x6 : Reg) ↦ᵣ v6) **
          ((.x7 : Reg) ↦ᵣ v7) **
            ((.x18 : Reg) ↦ᵣ chainId) **
              ((.x28 : Reg) ↦ᵣ v28) **
                ((.x0 : Reg) ↦ᵣ (0 : Word)) **
                  bytesRegion legacyLinkedChainPtr (List.replicate 8 0) ** F) :=
    by exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => by xperm_hyp hq) hlaF
  have hli := li_spec_gen_within .x6 v6 (7 : Word) (legacyH + 168) (by decide)
  have hli' :=
    cpsTripleWithin_extend_code
      (legacy_mem_at (legacyH + 168) 42 (.LI .x6 (7 : Word)) (by decide) (by decide)
        (by intro h; rfl))
      hli
  have hliF :=
    cpsTripleWithin_frameR
      (((.x5 : Reg) ↦ᵣ legacyLinkedChainPtr) **
        ((.x7 : Reg) ↦ᵣ v7) **
          ((.x18 : Reg) ↦ᵣ chainId) **
            ((.x28 : Reg) ↦ᵣ v28) **
              ((.x0 : Reg) ↦ᵣ (0 : Word)) **
                bytesRegion legacyLinkedChainPtr (List.replicate 8 0) ** F)
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
          | exact pcFree_regFileIs _;
        exact hF)
      hli'
  have hliW :
    cpsTripleWithin 1 (legacyH + 168) (legacyH + 172) legacyFullCode
      (((.x5 : Reg) ↦ᵣ legacyLinkedChainPtr) **
        ((.x6 : Reg) ↦ᵣ v6) **
          ((.x7 : Reg) ↦ᵣ v7) **
            ((.x18 : Reg) ↦ᵣ chainId) **
              ((.x28 : Reg) ↦ᵣ v28) **
                ((.x0 : Reg) ↦ᵣ (0 : Word)) **
                  bytesRegion legacyLinkedChainPtr (List.replicate 8 0) ** F)
      (((.x5 : Reg) ↦ᵣ legacyLinkedChainPtr) **
        ((.x6 : Reg) ↦ᵣ (7 : Word)) **
          ((.x7 : Reg) ↦ᵣ v7) **
            ((.x18 : Reg) ↦ᵣ chainId) **
              ((.x28 : Reg) ↦ᵣ v28) **
                ((.x0 : Reg) ↦ᵣ (0 : Word)) **
                  bytesRegion legacyLinkedChainPtr (List.replicate 8 0) ** F) :=
    by exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => by xperm_hyp hq) hliF
  have hsetup := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hlaW hliW
  have hsetupLoop :
    cpsTripleWithin 3 (legacyH + 160) (legacyH + 172) legacyFullCode
      (((.x5 : Reg) ↦ᵣ v5) **
        ((.x6 : Reg) ↦ᵣ v6) **
          ((.x7 : Reg) ↦ᵣ v7) **
            ((.x18 : Reg) ↦ᵣ chainId) **
              ((.x28 : Reg) ↦ᵣ v28) **
                ((.x0 : Reg) ↦ᵣ (0 : Word)) **
                  bytesRegion legacyLinkedChainPtr (List.replicate 8 0) ** F)
      (((.x5 : Reg) ↦ᵣ legacyLinkedChainPtr) **
        ((.x6 : Reg) ↦ᵣ (7 : Word)) **
          ((.x7 : Reg) ↦ᵣ v7) **
            ((.x18 : Reg) ↦ᵣ chainId) **
              ((.x28 : Reg) ↦ᵣ v28) **
                ((.x0 : Reg) ↦ᵣ (0 : Word)) **
                  bytesRegion legacyLinkedChainPtr (List.replicate 8 0) ** F) :=
    hsetup
  have hloop := legacyLoop_callWithin legacyLinkedChainPtr chainId F hF halign hover hvalid hbound
  have hloopW :
    cpsTripleWithin 65 legacyLoopBase (legacyLoopBase + 32) legacyFullCode
      (((.x5 : Reg) ↦ᵣ legacyLinkedChainPtr) **
        ((.x6 : Reg) ↦ᵣ (7 : Word)) **
          ((.x7 : Reg) ↦ᵣ v7) **
            ((.x18 : Reg) ↦ᵣ chainId) **
              ((.x28 : Reg) ↦ᵣ v28) **
                ((.x0 : Reg) ↦ᵣ (0 : Word)) **
                  bytesRegion legacyLinkedChainPtr (List.replicate 8 0) ** F)
      (((.x5 : Reg) ↦ᵣ (legacyLinkedChainPtr + BitVec.ofNat 64 8)) **
        ((.x6 : Reg) ↦ᵣ (-1 : Word)) **
          ((.x18 : Reg) ↦ᵣ chainId) **
            ((.x0 : Reg) ↦ᵣ (0 : Word)) **
              regOwn .x7 **
                regOwn .x28 ** bytesRegion legacyLinkedChainPtr (chainBytes chainId) ** F) :=
    cpsTripleWithin_weaken
      (fun h hp => by
        simp only [loopInv, chainWin_zero, counterVal] at hp ⊢
        let tail : Assertion :=
          ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion legacyLinkedChainPtr (List.replicate 8 0) ** F
        have hmap28 : ∀ h, (((.x28 : Reg) ↦ᵣ v28) ** tail) h → (regOwn .x28 ** tail) h :=
          by
          intro h hq
          exact sepConj_mono (regIs_to_regOwn .x28 v28) (fun _ hx => hx) h hq
        have hmap18 :
          ∀ h,
            (((.x18 : Reg) ↦ᵣ chainId) ** ((.x28 : Reg) ↦ᵣ v28) ** tail) h →
              (((.x18 : Reg) ↦ᵣ chainId) ** regOwn .x28 ** tail) h :=
          by
          intro h hq
          exact sepConj_mono (fun _ hx => hx) hmap28 h hq
        have hmap7 :
          ∀ h,
            (((.x7 : Reg) ↦ᵣ v7) ** ((.x18 : Reg) ↦ᵣ chainId) ** ((.x28 : Reg) ↦ᵣ v28) ** tail) h →
              (regOwn .x7 ** ((.x18 : Reg) ↦ᵣ chainId) ** regOwn .x28 ** tail) h :=
          by
          intro h hq
          exact sepConj_mono (regIs_to_regOwn .x7 v7) hmap18 h hq
        have hmap6 :
          ∀ h,
            (((.x6 : Reg) ↦ᵣ (7 : Word)) **
                  ((.x7 : Reg) ↦ᵣ v7) ** ((.x18 : Reg) ↦ᵣ chainId) ** ((.x28 : Reg) ↦ᵣ v28) ** tail)
                h →
              (((.x6 : Reg) ↦ᵣ (7 : Word)) **
                  (regOwn .x7 ** ((.x18 : Reg) ↦ᵣ chainId) ** regOwn .x28 ** tail))
                h :=
          by
          intro h hq
          exact sepConj_mono (fun _ hx => hx) hmap7 h hq
        have hmap5 :
          ∀ h,
            (((.x5 : Reg) ↦ᵣ legacyLinkedChainPtr) **
                  ((.x6 : Reg) ↦ᵣ (7 : Word)) **
                    ((.x7 : Reg) ↦ᵣ v7) **
                      ((.x18 : Reg) ↦ᵣ chainId) ** ((.x28 : Reg) ↦ᵣ v28) ** tail)
                h →
              (((.x5 : Reg) ↦ᵣ legacyLinkedChainPtr) **
                  ((.x6 : Reg) ↦ᵣ (7 : Word)) **
                    (regOwn .x7 ** ((.x18 : Reg) ↦ᵣ chainId) ** regOwn .x28 ** tail))
                h :=
          by
          intro h hq
          exact sepConj_mono (fun _ hx => hx) hmap6 h hq
        have hmapped := hmap5 h hp
        simp [tail] at hmapped ⊢
        xperm_hyp hmapped)
      (fun _ hq => by simpa [loopInv, chainWin_full, counterVal] using hq) hloop
  have hseq := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hsetupLoop hloopW
  have hexit : legacyLoopBase + 32 = legacyH + 204 := by decide
  rw [hexit] at hseq
  simpa [chainWin_full, chainBytes_length] using hseq


-- @@ L217-217 verbatim
end EvmAsm.Codegen.TxSigningHashLegacyChainCompose
