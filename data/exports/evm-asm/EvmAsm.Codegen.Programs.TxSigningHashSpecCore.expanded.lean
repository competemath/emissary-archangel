/-
  EvmAsm.Codegen.Programs.TxSigningHashSpecCore

  Scaffold + callWithins for K145 `tx_signing_hash` (#12038).

  Proof-only module. Pins `H := GuestAddrs.tx_signing_hash` (a REAL linked
  guest address — every `la`/`jalOff` in `txSigningHash_prog` is baked against
  that base and real callees). Models the top-level shape of
  `HeaderExtractNumberSpec.header_extract_number_spec_within`.

  ## Callee (multi-rate)

  `txSigningHash_prog` always JALs `zkvm_keccak256_segments` with a
  **3-segment** gather (type-prefix byte || RLP list-prefix || payload).
  The callee is the ungated multi-rate triple
  `zkvm_keccak256_segments_spec_within` (`kssCallerPost_multi` /
  `kssBodyFuelMulti`) — no `|msg| ≤ 135` INPUT-DOMAIN gate.

  ## Shape

  `txSigningHash_prog` (93 insn) = ABI frame (-64 / +64, 8 slots) around a
  74-instruction body with three cross-calls:
    `rlp_list_nth_item`, `rlp_encode_list_prefix`, `zkvm_keccak256_segments`.
-/

import EvmAsm.Codegen.Programs.TxSigningHash
import EvmAsm.Codegen.Programs.TxSigningHashResidual
import EvmAsm.Codegen.Programs.RlpListNthItemCallSAsm
import EvmAsm.Codegen.Programs.RlpSpliceHelperSpec
import EvmAsm.Codegen.Proofs.HashBridgeKeccakSegTop
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Rv64.SAsm.AbiFrame
import EvmAsm.Rv64.SAsm.AbiFrameCall
import EvmAsm.Rv64.MemRegion
import EvmAsm.Stateless.SpecRef.Crypto


-- @@ L37-37 verbatim
namespace EvmAsm.Codegen.TxSigningHashSpec


-- @@ L39-39 verbatim
open EvmAsm.Rv64 EvmAsm.Rv64.SAsm

-- @@ L40-40 verbatim
open EvmAsm.Codegen

-- @@ L41-41 verbatim
open EvmAsm.Codegen.TxSigningHashResidual

-- @@ L42-42 verbatim
open EvmAsm.Codegen.Proofs

-- @@ L43-43 verbatim
open EvmAsm.Stateless.SpecRef

-- @@ L44-44 verbatim
open EvmAsm.Rv64.Tactics


-- @@ L46-46 verbatim
/-! ## Linked base and ABI-frame decomposition -/


-- @@ L48-49 verbatim
/-- Real linked guest entry of `tx_signing_hash`. -/
abbrev H : Word := BitVec.ofNat 64 GuestAddrs.tx_signing_hash


-- @@ L51-51 verbatim
abbrev NthB : Word := BitVec.ofNat 64 GuestAddrs.rlp_list_nth_item

-- @@ L52-52 verbatim
abbrev PrefixB : Word := BitVec.ofNat 64 GuestAddrs.rlp_encode_list_prefix

-- @@ L53-53 verbatim
abbrev KssB' : Word := BitVec.ofNat 64 GuestAddrs.zkvm_keccak256_segments

-- @@ L54-54 verbatim
abbrev TshBuf : Word := BitVec.ofNat 64 GuestAddrs.tsh_buf


-- @@ L56-59 verbatim
/-- Frame: `ra` + `s0 s1 s2 s3 s4 s5 s6` — matches the emitted saves. -/
def tshFrame : FrameDesc :=
  [(.x1, 0), (.x8, 8), (.x9, 16), (.x18, 24), (.x19, 32), (.x20, 40),
   (.x21, 48), (.x22, 56)]



-- @@ L62-137 verbatim
def tshBody : List Instr :=  [
    .MV .x8 .x10,
    .MV .x9 .x11,
    .MV .x18 .x12,
    .MV .x19 .x13,
    .MV .x20 .x14,
    .AUIPC .x5 (laHi GuestAddrs.tsh_buf (GuestAddrs.tx_signing_hash + 56)),
    .ADDI .x5 .x5 (laLo GuestAddrs.tsh_buf (GuestAddrs.tx_signing_hash + 56)),
    .SB .x5 .x19 (0 : BitVec 12),
    .BEQ .x9 .x0 (260 : BitVec 13),
    .LBU .x5 .x8 (0 : BitVec 12),
    .LI .x6 (192 : Word),
    .BLTU .x5 .x6 (248 : BitVec 13),
    .LI .x6 (248 : Word),
    .BLTU .x5 .x6 (16 : BitVec 13),
    .ADDI .x21 .x5 (-247 : BitVec 12),
    .ADDI .x21 .x21 (1 : BitVec 12),
    .JAL .x0 (8 : BitVec 21),
    .LI .x21 (1 : Word),
    .LI .x22 (0 : Word),
    .BEQ .x18 .x0 (76 : BitVec 13),
    .ADDI .x5 .x18 (-1 : BitVec 12),
    .MV .x10 .x8,
    .MV .x11 .x9,
    .MV .x12 .x5,
    .AUIPC .x13 (laHi GuestAddrs.tsh_buf (GuestAddrs.tx_signing_hash + 132)),
    .ADDI .x13 .x13 (laLo GuestAddrs.tsh_buf (GuestAddrs.tx_signing_hash + 132)),
    .ADDI .x13 .x13 (64 : BitVec 12),
    .AUIPC .x14 (laHi GuestAddrs.tsh_buf (GuestAddrs.tx_signing_hash + 144)),
    .ADDI .x14 .x14 (laLo GuestAddrs.tsh_buf (GuestAddrs.tx_signing_hash + 144)),
    .ADDI .x14 .x14 (72 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.rlp_list_nth_item (GuestAddrs.tx_signing_hash + 156)),
    .BNE .x10 .x0 (168 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.tsh_buf (GuestAddrs.tx_signing_hash + 164)),
    .ADDI .x5 .x5 (laLo GuestAddrs.tsh_buf (GuestAddrs.tx_signing_hash + 164)),
    .LD .x6 .x5 (64 : BitVec 12),
    .LD .x7 .x5 (72 : BitVec 12),
    .ADD .x6 .x6 .x7,
    .SUB .x22 .x6 .x21,
    .MV .x10 .x22,
    .AUIPC .x11 (laHi GuestAddrs.tsh_buf (GuestAddrs.tx_signing_hash + 192)),
    .ADDI .x11 .x11 (laLo GuestAddrs.tsh_buf (GuestAddrs.tx_signing_hash + 192)),
    .ADDI .x11 .x11 (16 : BitVec 12),
    .AUIPC .x12 (laHi GuestAddrs.tsh_buf (GuestAddrs.tx_signing_hash + 204)),
    .ADDI .x12 .x12 (laLo GuestAddrs.tsh_buf (GuestAddrs.tx_signing_hash + 204)),
    .ADDI .x12 .x12 (80 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.rlp_encode_list_prefix (GuestAddrs.tx_signing_hash + 216)),
    .AUIPC .x5 (laHi GuestAddrs.tsh_buf (GuestAddrs.tx_signing_hash + 220)),
    .ADDI .x5 .x5 (laLo GuestAddrs.tsh_buf (GuestAddrs.tx_signing_hash + 220)),
    .LD .x29 .x5 (80 : BitVec 12),
    .AUIPC .x30 (laHi GuestAddrs.tsh_buf (GuestAddrs.tx_signing_hash + 232)),
    .ADDI .x30 .x30 (laLo GuestAddrs.tsh_buf (GuestAddrs.tx_signing_hash + 232)),
    .ADDI .x30 .x30 (128 : BitVec 12),
    .LI .x5 (0 : Word),
    .BEQ .x19 .x0 (8 : BitVec 13),
    .LI .x5 (1 : Word),
    .AUIPC .x31 (laHi GuestAddrs.tsh_buf (GuestAddrs.tx_signing_hash + 256)),
    .ADDI .x31 .x31 (laLo GuestAddrs.tsh_buf (GuestAddrs.tx_signing_hash + 256)),
    .SD .x30 .x31 (0 : BitVec 12),
    .SD .x30 .x5 (8 : BitVec 12),
    .AUIPC .x31 (laHi GuestAddrs.tsh_buf (GuestAddrs.tx_signing_hash + 272)),
    .ADDI .x31 .x31 (laLo GuestAddrs.tsh_buf (GuestAddrs.tx_signing_hash + 272)),
    .ADDI .x31 .x31 (16 : BitVec 12),
    .SD .x30 .x31 (16 : BitVec 12),
    .SD .x30 .x29 (24 : BitVec 12),
    .ADD .x31 .x8 .x21,
    .SD .x30 .x31 (32 : BitVec 12),
    .SD .x30 .x22 (40 : BitVec 12),
    .MV .x10 .x30,
    .LI .x11 (3 : Word),
    .MV .x12 .x20,
    .JAL .x1 (jalOff GuestAddrs.zkvm_keccak256_segments (GuestAddrs.tx_signing_hash + 316)),
    .LI .x10 (0 : Word),
    .JAL .x0 (8 : BitVec 21),
    .LI .x10 (1 : Word)
  ]




-- @@ L141-141 verbatim
theorem tshBody_length : tshBody.length = 74 := by decide


-- @@ L143-143 verbatim
theorem tshFrame_length : tshFrame.length = 8 := by decide


-- @@ L145-148 verbatim
/-- Byte-identity: the emitted Program IS the ABI frame around `tshBody`. -/
theorem txSigningHash_prog_eq_abiFrame :
    abiFrameProg (-64 : BitVec 12) (64 : BitVec 12) tshFrame tshBody
      = txSigningHash_prog := rfl


-- @@ L150-150 verbatim
theorem tsh_prog_length : txSigningHash_prog.length = 93 := by decide


-- @@ L152-152 verbatim
/-! ## CodeReq closure (wrapper ∪ three callees) -/


-- @@ L154-154 verbatim
def tshCode : CodeReq := CodeReq.ofProg H txSigningHash_prog


-- @@ L156-156 verbatim
def nthCode : CodeReq := EvmAsm.Codegen.RlpListNthItemSAsm.code


-- @@ L158-158 verbatim
def prefixCode : CodeReq := CodeReq.ofProg PrefixB rlpEncodeListPrefix_prog


-- @@ L160-160 verbatim
def kssCode : CodeReq := kssCr


-- @@ L162-164 verbatim
/-- Full linked image used by the whole-routine triple. -/
def fullCode : CodeReq :=
  tshCode.union (nthCode.union (prefixCode.union kssCode))


-- @@ L166-171 verbatim
theorem tsh_nth_disjoint : tshCode.Disjoint nthCode := by
  unfold tshCode nthCode EvmAsm.Codegen.RlpListNthItemSAsm.code
  apply CodeReq.Disjoint.ofProg_ranges
  · rw [tsh_prog_length]; decide
  · rw [EvmAsm.Codegen.RlpListNthItemSAsm.total_length]; decide
  · rw [tsh_prog_length, EvmAsm.Codegen.RlpListNthItemSAsm.total_length]; decide


-- @@ L173-178 verbatim
theorem tsh_prefix_disjoint : tshCode.Disjoint prefixCode := by
  unfold tshCode prefixCode
  apply CodeReq.Disjoint.ofProg_ranges
  · rw [tsh_prog_length]; decide
  · decide
  · rw [tsh_prog_length]; decide


-- @@ L180-185 verbatim
theorem tsh_kss_disjoint : tshCode.Disjoint kssCode := by
  unfold tshCode kssCode kssCr
  apply CodeReq.Disjoint.ofProg_ranges
  · rw [tsh_prog_length]; decide
  · rw [kssProgL_len]; decide
  · rw [tsh_prog_length, kssProgL_len]; decide


-- @@ L187-190 verbatim
theorem tsh_mono : ∀ a i, tshCode a = some i → fullCode a = some i := by
  intro a i hi
  unfold fullCode
  exact CodeReq.union_mono_left a i hi


-- @@ L192-197 verbatim
theorem nth_prefix_disjoint : nthCode.Disjoint prefixCode := by
  unfold nthCode prefixCode EvmAsm.Codegen.RlpListNthItemSAsm.code
  apply CodeReq.Disjoint.ofProg_ranges
  · rw [EvmAsm.Codegen.RlpListNthItemSAsm.total_length]; decide
  · decide
  · rw [EvmAsm.Codegen.RlpListNthItemSAsm.total_length]; decide


-- @@ L199-204 verbatim
theorem nth_kss_disjoint : nthCode.Disjoint kssCode := by
  unfold nthCode kssCode kssCr EvmAsm.Codegen.RlpListNthItemSAsm.code
  apply CodeReq.Disjoint.ofProg_ranges
  · rw [EvmAsm.Codegen.RlpListNthItemSAsm.total_length]; decide
  · rw [kssProgL_len]; decide
  · rw [EvmAsm.Codegen.RlpListNthItemSAsm.total_length, kssProgL_len]; decide


-- @@ L206-211 verbatim
theorem prefix_kss_disjoint : prefixCode.Disjoint kssCode := by
  unfold prefixCode kssCode kssCr
  apply CodeReq.Disjoint.ofProg_ranges
  · decide
  · rw [kssProgL_len]; decide
  · rw [kssProgL_len]; decide


-- @@ L213-231 verbatim
/-- `kssCode ⊆ fullCode` via pairwise misses + `union_skip` (avoids
    `mono_union_right` whnf on nested `ofProg` Disjoints). -/
theorem kss_mono : ∀ a i, kssCode a = some i → fullCode a = some i := by
  intro a i hi
  have htsh : tshCode a = none := by
    cases tsh_kss_disjoint a with
    | inl h => exact h
    | inr h => rw [h] at hi; cases hi
  have hnth : nthCode a = none := by
    cases nth_kss_disjoint a with
    | inl h => exact h
    | inr h => rw [h] at hi; cases hi
  have hpre : prefixCode a = none := by
    cases prefix_kss_disjoint a with
    | inl h => exact h
    | inr h => rw [h] at hi; cases hi
  change (tshCode.union (nthCode.union (prefixCode.union kssCode))) a = some i
  exact CodeReq.union_skip htsh
    (CodeReq.union_skip hnth (CodeReq.union_skip hpre hi))


-- @@ L233-241 verbatim
/-- `nthCode ⊆ fullCode` — skip TSH head, then hit nth. -/
theorem nth_mono : ∀ a i, nthCode a = some i → fullCode a = some i := by
  intro a i hi
  have htsh : tshCode a = none := by
    cases tsh_nth_disjoint a with
    | inl h => exact h
    | inr h => rw [h] at hi; cases hi
  change (tshCode.union (nthCode.union (prefixCode.union kssCode))) a = some i
  exact CodeReq.union_skip htsh (CodeReq.union_hit hi)


-- @@ L243-255 verbatim
/-- Discharge `CodeReq.singleton` for an instruction of the emitted Program. -/
theorem tshMem (prog : List Instr) (hprog : prog = (txSigningHash_prog : List Instr))
    (A : Word) (k : Nat) (ins : Instr)
    (hk : k < prog.length)
    (hA : A = H + BitVec.ofNat 64 (4 * k))
    (hins : prog[k]'hk = ins) :
    ∀ a i, CodeReq.singleton A ins a = some i → fullCode a = some i := by
  subst hprog
  intro a i hs
  unfold fullCode
  apply CodeReq.union_mono_left
  exact CodeReq.ofProg_mem_at H A (txSigningHash_prog : List Instr) k ins hA hk hins
    (by rw [tsh_prog_length]; norm_num) a i hs


-- @@ L257-257 verbatim
/-! ## Cross-call PCs (real GuestAddrs offsets) -/


-- @@ L259-259 verbatim
abbrev tshNthJalPC : Word := H + BitVec.ofNat 64 156

-- @@ L260-260 verbatim
abbrev tshPrefixJalPC : Word := H + BitVec.ofNat 64 216

-- @@ L261-261 verbatim
abbrev tshKssJalPC : Word := H + BitVec.ofNat 64 316


-- @@ L263-264 verbatim
def tshNthJalOff : BitVec 21 :=
  jalOff GuestAddrs.rlp_list_nth_item (GuestAddrs.tx_signing_hash + 156)


-- @@ L266-267 verbatim
def tshPrefixJalOff : BitVec 21 :=
  jalOff GuestAddrs.rlp_encode_list_prefix (GuestAddrs.tx_signing_hash + 216)


-- @@ L269-270 verbatim
def tshKssJalOff : BitVec 21 :=
  jalOff GuestAddrs.zkvm_keccak256_segments (GuestAddrs.tx_signing_hash + 316)


-- @@ L272-273 verbatim
theorem tshNthJal_target : tshNthJalPC + signExtend21 tshNthJalOff = NthB := by
  unfold tshNthJalPC tshNthJalOff H NthB; decide


-- @@ L275-276 verbatim
theorem tshPrefixJal_target : tshPrefixJalPC + signExtend21 tshPrefixJalOff = PrefixB := by
  unfold tshPrefixJalPC tshPrefixJalOff H PrefixB; decide


-- @@ L278-279 verbatim
theorem tshKssJal_target : tshKssJalPC + signExtend21 tshKssJalOff = KssB' := by
  unfold tshKssJalPC tshKssJalOff H KssB'; decide


-- @@ L281-283 verbatim
theorem tshKssJal_ret_even :
    ((tshKssJalPC + 4) &&& ~~~(1 : Word)) = tshKssJalPC + 4 := by
  unfold tshKssJalPC H; decide


-- @@ L285-291 verbatim
theorem tshKssJal_mem :
    ∀ a i, CodeReq.singleton tshKssJalPC (.JAL .x1 tshKssJalOff) a = some i →
      fullCode a = some i :=
  tshMem (txSigningHash_prog : List Instr) rfl tshKssJalPC 79
    (.JAL .x1 tshKssJalOff)
    (by simpa [Program] using (by rw [tsh_prog_length]; decide))
    (by unfold tshKssJalPC H; decide) rfl


-- @@ L293-299 verbatim
theorem tshNthJal_mem :
    ∀ a i, CodeReq.singleton tshNthJalPC (.JAL .x1 tshNthJalOff) a = some i →
      fullCode a = some i :=
  tshMem (txSigningHash_prog : List Instr) rfl tshNthJalPC 39
    (.JAL .x1 tshNthJalOff)
    (by simpa [Program] using (by rw [tsh_prog_length]; decide))
    (by unfold tshNthJalPC H; decide) rfl


-- @@ L301-307 verbatim
theorem tshPrefixJal_mem :
    ∀ a i, CodeReq.singleton tshPrefixJalPC (.JAL .x1 tshPrefixJalOff) a = some i →
      fullCode a = some i :=
  tshMem (txSigningHash_prog : List Instr) rfl tshPrefixJalPC 54
    (.JAL .x1 tshPrefixJalOff)
    (by simpa [Program] using (by rw [tsh_prog_length]; decide))
    (by unfold tshPrefixJalPC H; decide) rfl


-- @@ L309-309 verbatim
theorem KssB'_eq : KssB' = KssB := rfl


-- @@ L311-314 verbatim
/-! ## Multi-rate segments triple, lifted into `fullCode`

    Reuses ungated `zkvm_keccak256_segments_spec_within` at the real linked
    `GuestAddrs.zkvm_keccak256_segments` base. -/


-- @@ L316-343 verbatim
theorem tsh_kss_in_fullCode
    (sp0 ret segsBase outputBase : Word) (segs : List KssSeg)
    (os : List (BitVec 8)) (v5 v6 v7 v8 v9 v18 v19 v20 v21 v22 : Word)
    (A : Assertion) (hA : A.pcFree)
    (halign_ret : (ret &&& ~~~(1 : Word)) = ret)
    (hos : os.length = 200)
    (hcount : segs.length < 2 ^ 64)
    (hsegs : ∀ s ∈ segs, s.2.length < 2 ^ 64 ∧
      (∀ i, i < s.2.length →
        s.1.toNat + i < 2 ^ 64 ∧
        isValidByteAccess (s.1 + BitVec.ofNat 64 i) = true))
    (source : KssSource := kssDefaultSource) :
    let vals := kssEntryVals ret v8 v9 v18 v19 v20 v21 v22
    let newSp := sp0 + signExtend12 ((-64 : BitVec 12))
    cpsTripleWithin (19 + kssBodyFuelMulti segs) KssB' ret fullCode
      ((.x2 ↦ᵣ sp0) ** regsAt kssFrame vals **
        frameSlotsOwn kssFrame newSp **
        kssCallerPre segsBase outputBase segs os
      (List.replicate 32 (0 : BitVec 8)) v5 v6 v7 A source)
      ((.x2 ↦ᵣ sp0) ** regsAt kssFrame vals **
        frameSlotsSaved kssFrame newSp vals **
        kssCallerPost_multi segsBase outputBase segs A source) := by
  intro vals newSp
  have h := zkvm_keccak256_segments_spec_within sp0 ret segsBase outputBase
    segs os (List.replicate 32 (0 : BitVec 8))
    v5 v6 v7 v8 v9 v18 v19 v20 v21 v22 A hA halign_ret hos
    (by simp only [List.length_replicate]) hcount hsegs source
  exact cpsTripleWithin_extend_code kss_mono h


-- @@ L345-351 verbatim
/-- Factor `ra` out of `regsAt kssFrame` for `callWithin_spec`. -/
theorem tsh_kssRegs_factor (ret v8 v9 v18 v19 v20 v21 v22 : Word) :
    regsAt kssFrame (kssEntryVals ret v8 v9 v18 v19 v20 v21 v22) =
      ((.x1 ↦ᵣ ret) **
        ((.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19) **
          (.x20 ↦ᵣ v20) ** (.x21 ↦ᵣ v21) ** (.x22 ↦ᵣ v22))) := by
  simp only [regsAt, kssFrame, kssEntryVals, List.foldr, sepConj_emp_right']


-- @@ L353-356 verbatim
/-- Callee-saved s-regs of the segments frame (no `ra`). -/
def tshKssSregs (v8 v9 v18 v19 v20 v21 v22 : Word) : Assertion :=
  (.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19) **
    (.x20 ↦ᵣ v20) ** (.x21 ↦ᵣ v21) ** (.x22 ↦ᵣ v22)


-- @@ L358-361 verbatim
theorem tshKssSregs_pcFree (v8 v9 v18 v19 v20 v21 v22 : Word) :
    (tshKssSregs v8 v9 v18 v19 v20 v21 v22).pcFree := by
  unfold tshKssSregs
  repeat first | apply pcFree_sepConj | exact pcFree_regIs


-- @@ L363-370 verbatim
/-- Call-site pre without `ra` (owned by `callWithin_spec`). -/
def tshKssCallPre (sp0 newSp segsBase outputBase : Word) (segs : List KssSeg)
    (os : List (BitVec 8)) (v5 v6 v7 v8 v9 v18 v19 v20 v21 v22 : Word)
    (A : Assertion) (source : KssSource := kssDefaultSource) : Assertion :=
  (.x2 ↦ᵣ sp0) ** tshKssSregs v8 v9 v18 v19 v20 v21 v22 **
    frameSlotsOwn kssFrame newSp **
    kssCallerPre segsBase outputBase segs os
      (List.replicate 32 (0 : BitVec 8)) v5 v6 v7 A source


-- @@ L372-378 verbatim
/-- Call-site post without `ra`. -/
def tshKssCallPost (sp0 newSp ret segsBase outputBase : Word) (segs : List KssSeg)
    (v8 v9 v18 v19 v20 v21 v22 : Word) (A : Assertion)
    (source : KssSource := kssDefaultSource) : Assertion :=
  (.x2 ↦ᵣ sp0) ** tshKssSregs v8 v9 v18 v19 v20 v21 v22 **
    frameSlotsSaved kssFrame newSp (kssEntryVals ret v8 v9 v18 v19 v20 v21 v22) **
    kssCallerPost_multi segsBase outputBase segs A source


-- @@ L380-390 verbatim
theorem tshKssCallPre_pcFree (sp0 newSp segsBase outputBase : Word)
    (segs : List KssSeg) (os : List (BitVec 8))
    (v5 v6 v7 v8 v9 v18 v19 v20 v21 v22 : Word) (A : Assertion)
    (hA : A.pcFree) (source : KssSource := kssDefaultSource) :
    (tshKssCallPre sp0 newSp segsBase outputBase segs os
      v5 v6 v7 v8 v9 v18 v19 v20 v21 v22 A source).pcFree := by
  unfold tshKssCallPre
  exact pcFree_sepConj pcFree_regIs
    (pcFree_sepConj (tshKssSregs_pcFree _ _ _ _ _ _ _)
      (pcFree_sepConj (pcFree_frameSlotsOwn _ _)
        (kssCallerPre_pcFree _ _ _ _ _ _ _ _ _ hA source)))


-- @@ L392-436 verbatim
/-- Reshape the lifted segments triple so `ra` is the `callWithin` head. -/
theorem tsh_kss_ra_factored
    (sp0 ret segsBase outputBase : Word) (segs : List KssSeg)
    (os : List (BitVec 8)) (v5 v6 v7 v8 v9 v18 v19 v20 v21 v22 : Word)
    (A : Assertion) (hA : A.pcFree)
    (halign_ret : (ret &&& ~~~(1 : Word)) = ret)
    (hos : os.length = 200)
    (hcount : segs.length < 2 ^ 64)
    (hsegs : ∀ s ∈ segs, s.2.length < 2 ^ 64 ∧
      (∀ i, i < s.2.length →
        s.1.toNat + i < 2 ^ 64 ∧
        isValidByteAccess (s.1 + BitVec.ofNat 64 i) = true))
    (source : KssSource := kssDefaultSource) :
    let newSp := sp0 + signExtend12 ((-64 : BitVec 12))
    let fuel := 19 + kssBodyFuelMulti segs
    cpsTripleWithin fuel KssB' ret fullCode
      (((.x1 ↦ᵣ ret) **
        tshKssCallPre sp0 newSp segsBase outputBase segs os
          v5 v6 v7 v8 v9 v18 v19 v20 v21 v22 A source))
      (((.x1 ↦ᵣ ret) **
        tshKssCallPost sp0 newSp ret segsBase outputBase segs
          v8 v9 v18 v19 v20 v21 v22 A source)) := by
  intro newSp fuel
  have hcore := tsh_kss_in_fullCode sp0 ret segsBase outputBase segs os
    v5 v6 v7 v8 v9 v18 v19 v20 v21 v22 A hA halign_ret hos hcount hsegs source
  -- hcore pre/post still under `let vals` / `let newSp`; reduce them.
  change cpsTripleWithin (19 + kssBodyFuelMulti segs) KssB' ret fullCode
    ((.x2 ↦ᵣ sp0) **
      regsAt kssFrame (kssEntryVals ret v8 v9 v18 v19 v20 v21 v22) **
      frameSlotsOwn kssFrame newSp **
      kssCallerPre segsBase outputBase segs os
      (List.replicate 32 (0 : BitVec 8)) v5 v6 v7 A source)
    ((.x2 ↦ᵣ sp0) **
      regsAt kssFrame (kssEntryVals ret v8 v9 v18 v19 v20 v21 v22) **
      frameSlotsSaved kssFrame newSp (kssEntryVals ret v8 v9 v18 v19 v20 v21 v22) **
      kssCallerPost_multi segsBase outputBase segs A source) at hcore
  refine cpsTripleWithin_weaken (fun h hp => ?_) (fun h hq => ?_) hcore
  · -- P' → P: expand CallPre; split goal regsAt; xperm
    unfold tshKssCallPre tshKssSregs at hp
    rw [tsh_kssRegs_factor]
    xperm_hyp hp
  · -- Q → Q': split hq regsAt; fold into CallPost; xperm
    unfold tshKssCallPost tshKssSregs
    rw [tsh_kssRegs_factor] at hq
    xperm_hyp hq


-- @@ L438-471 verbatim
/-- **`callWithin` at `tx_signing_hash+316` (multi-rate segments).** -/
theorem tsh_kss_callWithin
    (vOld sp0 segsBase outputBase : Word) (segs : List KssSeg)
    (os : List (BitVec 8)) (v5 v6 v7 v8 v9 v18 v19 v20 v21 v22 : Word)
    (A F : Assertion) (hA : A.pcFree) (hF : F.pcFree)
    (hos : os.length = 200)
    (hcount : segs.length < 2 ^ 64)
    (hsegs : ∀ s ∈ segs, s.2.length < 2 ^ 64 ∧
      (∀ i, i < s.2.length →
        s.1.toNat + i < 2 ^ 64 ∧
        isValidByteAccess (s.1 + BitVec.ofNat 64 i) = true))
    (source : KssSource := kssDefaultSource) :
    let ret := tshKssJalPC + 4
    let newSp := sp0 + signExtend12 ((-64 : BitVec 12))
    let fuel := 19 + kssBodyFuelMulti segs
    cpsTripleWithin (1 + fuel) tshKssJalPC ret fullCode
      (((.x1 ↦ᵣ vOld) **
        (tshKssCallPre sp0 newSp segsBase outputBase segs os
          v5 v6 v7 v8 v9 v18 v19 v20 v21 v22 A source ** F)))
      (((.x1 ↦ᵣ ret) **
        (tshKssCallPost sp0 newSp ret segsBase outputBase segs
          v8 v9 v18 v19 v20 v21 v22 A source ** F))) := by
  intro ret newSp fuel
  have hret_even : (ret &&& ~~~(1 : Word)) = ret := tshKssJal_ret_even
  have hcallee := tsh_kss_ra_factored sp0 ret segsBase outputBase segs os
    v5 v6 v7 v8 v9 v18 v19 v20 v21 v22 A hA hret_even hos hcount hsegs source
  have hcalleeF := cpsTripleWithin_frameR F hF hcallee
  have hP := pcFree_sepConj
    (tshKssCallPre_pcFree sp0 newSp segsBase outputBase segs os
      v5 v6 v7 v8 v9 v18 v19 v20 v21 v22 A hA source) hF
  exact callWithin_spec tshKssJalPC KssB' vOld tshKssJalOff fuel
    tshKssJal_target tshKssJal_mem hP
    (cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hcalleeF)


-- @@ L473-473 verbatim
/-! ## `rlp_list_nth_item` callWithin at `tx_signing_hash+156` -/


-- @@ L475-475 verbatim
abbrev tshNthOffPtr : Word := TshBuf + 64

-- @@ L476-476 verbatim
abbrev tshNthLenPtr : Word := TshBuf + 72


-- @@ L478-480 verbatim
theorem tshNthJal_ret_even :
    ((tshNthJalPC + 4) &&& ~~~(1 : Word)) = tshNthJalPC + 4 := by
  unfold tshNthJalPC H; decide


-- @@ L482-512 verbatim
/-- **`rlp_list_nth_item` callWithin at the real K145 jal site.** -/
theorem tsh_nth_callWithin
    (vOld sp0 listBase listLenW indexW oldOffset oldLen : Word)
    (saved : EvmAsm.Codegen.RlpListNthItemSAsm.Saved)
    (bytes : List (BitVec 8)) (listLen index : Nat)
    (F : Assertion) (hF : F.pcFree)
    (hlistLenW : listLenW = BitVec.ofNat 64 listLen)
    (hindexW : indexW = BitVec.ofNat 64 index)
    (hindex : index < 2 ^ 64)
    (hsalign : listBase.toNat % 8 = 0)
    (hslack : listLen + 9 ≤ bytes.length)
    (hover : listBase.toNat + bytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < bytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin
      (1 + ((12 + ((85 + 93 * (index + 2)) + 6)) + 9))
      tshNthJalPC (tshNthJalPC + 4) fullCode
      (((.x1 ↦ᵣ vOld) **
        EvmAsm.Codegen.RlpListNthItemSAsm.callEntryRest sp0 listBase listLenW indexW
          tshNthOffPtr tshNthLenPtr oldOffset oldLen
          { saved with ra := tshNthJalPC + 4 } bytes) ** F)
      (((.x1 ↦ᵣ (tshNthJalPC + 4)) **
        EvmAsm.Codegen.RlpListNthItemSAsm.callReturnResult sp0 listBase indexW
          tshNthOffPtr tshNthLenPtr oldOffset oldLen
          { saved with ra := tshNthJalPC + 4 } bytes listLen index) ** F) := by
  exact EvmAsm.Codegen.RlpListNthItemSAsm.rlpListNthItem_call_spec_within
    (cr := fullCode) (callerPC := tshNthJalPC) (calleeEntry := NthB)
    vOld sp0 listBase listLenW indexW tshNthOffPtr tshNthLenPtr
    oldOffset oldLen tshNthJalOff F hF saved bytes listLen index
    hlistLenW hindexW hindex hsalign (by omega) (by omega) hover hvalid (by omega)
    tshNthJal_ret_even tshNthJal_target rfl tshNthJal_mem nth_mono


-- @@ L514-514 verbatim
/-! ## Short `rlp_encode_list_prefix` lifted into `fullCode` -/


-- @@ L516-528 verbatim
theorem prefix_mono : ∀ a i, prefixCode a = some i → fullCode a = some i := by
  intro a i hi
  have htsh : tshCode a = none := by
    cases tsh_prefix_disjoint a with
    | inl h => exact h
    | inr h => rw [h] at hi; cases hi
  have hnth : nthCode a = none := by
    cases nth_prefix_disjoint a with
    | inl h => exact h
    | inr h => rw [h] at hi; cases hi
  change (tshCode.union (nthCode.union (prefixCode.union kssCode))) a = some i
  exact CodeReq.union_skip htsh
    (CodeReq.union_skip hnth (CodeReq.union_hit hi))


-- @@ L530-553 verbatim
theorem tsh_prefix_short_in_fullCode
    (len outPtr cellPtr raVal v5 v6 v7 : Word)
    (outBytes : List (BitVec 8)) (cellOld : Word)
    (h_len : len.toNat < 56)
    (h_out_align : outPtr.toNat % 8 = 0)
    (h_out_len : 0 < outBytes.length)
    (h_out_valid : ∀ k, k < outBytes.length →
      isValidByteAccess (outPtr + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin 8 PrefixB (raVal &&& ~~~1) fullCode
      (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ len) **
       ((.x11 : Reg) ↦ᵣ outPtr) ** ((.x12 : Reg) ↦ᵣ cellPtr) **
       ((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) ** ((.x7 : Reg) ↦ᵣ v7) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion outPtr outBytes ** (cellPtr ↦ₘ cellOld))
      (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ (0 : Word)) **
       ((.x11 : Reg) ↦ᵣ outPtr) ** ((.x12 : Reg) ↦ᵣ cellPtr) **
       regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion outPtr (outBytes.set 0 (BitVec.ofNat 8 (0xC0 + len.toNat))) **
       (cellPtr ↦ₘ (1 : Word))) :=
  cpsTripleWithin_extend_code prefix_mono
    (EvmAsm.Codegen.RlpSpliceHelperSpec.rlp_encode_list_prefix_short_pinned_spec_within
      PrefixB len outPtr cellPtr
      raVal v5 v6 v7 outBytes cellOld h_len h_out_align h_out_len h_out_valid)


-- @@ L555-557 verbatim
theorem tshPrefixJal_ret_even :
    ((tshPrefixJalPC + 4) &&& ~~~(1 : Word)) = tshPrefixJalPC + 4 := by
  unfold tshPrefixJalPC H; decide


-- @@ L559-620 verbatim
/-- Short list-prefix `callWithin` at `tx_signing_hash+216`.
    Gate `len.toNat < 56` matches the short path of `rlp_encode_list_prefix`
    (residual INPUT-DOMAIN gate after multi-rate keccak re-point). -/
theorem tsh_prefix_short_callWithin
    (vOld len outPtr cellPtr v5 v6 v7 : Word)
    (outBytes : List (BitVec 8)) (cellOld : Word)
    (F : Assertion) (hF : F.pcFree)
    (h_len : len.toNat < 56)
    (h_out_align : outPtr.toNat % 8 = 0)
    (h_out_len : 0 < outBytes.length)
    (h_out_valid : ∀ k, k < outBytes.length →
      isValidByteAccess (outPtr + BitVec.ofNat 64 k) = true) :
    let ret := tshPrefixJalPC + 4
    cpsTripleWithin (1 + 8) tshPrefixJalPC ret fullCode
      (((.x1 ↦ᵣ vOld) **
        (((.x10 : Reg) ↦ᵣ len) ** ((.x11 : Reg) ↦ᵣ outPtr) **
         ((.x12 : Reg) ↦ᵣ cellPtr) ** ((.x5 : Reg) ↦ᵣ v5) **
         ((.x6 : Reg) ↦ᵣ v6) ** ((.x7 : Reg) ↦ᵣ v7) **
         ((.x0 : Reg) ↦ᵣ (0 : Word)) **
         bytesRegion outPtr outBytes ** (cellPtr ↦ₘ cellOld) ** F)))
      (((.x1 ↦ᵣ ret) **
        (((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ outPtr) **
         ((.x12 : Reg) ↦ᵣ cellPtr) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
         ((.x0 : Reg) ↦ᵣ (0 : Word)) **
         bytesRegion outPtr (outBytes.set 0 (BitVec.ofNat 8 (0xC0 + len.toNat))) **
         (cellPtr ↦ₘ (1 : Word)) ** F))) := by
  intro ret
  have hret_eq : (ret &&& ~~~(1 : Word)) = ret := tshPrefixJal_ret_even
  have hcore := tsh_prefix_short_in_fullCode len outPtr cellPtr ret v5 v6 v7
    outBytes cellOld h_len h_out_align h_out_len h_out_valid
  rw [hret_eq] at hcore
  have hcallee : cpsTripleWithin 8 PrefixB ret fullCode
      (((.x1 ↦ᵣ ret) **
        (((.x10 : Reg) ↦ᵣ len) ** ((.x11 : Reg) ↦ᵣ outPtr) **
         ((.x12 : Reg) ↦ᵣ cellPtr) ** ((.x5 : Reg) ↦ᵣ v5) **
         ((.x6 : Reg) ↦ᵣ v6) ** ((.x7 : Reg) ↦ᵣ v7) **
         ((.x0 : Reg) ↦ᵣ (0 : Word)) **
         bytesRegion outPtr outBytes ** (cellPtr ↦ₘ cellOld))))
      (((.x1 ↦ᵣ ret) **
        (((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ outPtr) **
         ((.x12 : Reg) ↦ᵣ cellPtr) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
         ((.x0 : Reg) ↦ᵣ (0 : Word)) **
         bytesRegion outPtr (outBytes.set 0 (BitVec.ofNat 8 (0xC0 + len.toNat))) **
         (cellPtr ↦ₘ (1 : Word))))) :=
    cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hcore
  have hcalleeF := cpsTripleWithin_frameR F hF hcallee
  have hP : ((((.x10 : Reg) ↦ᵣ len) ** ((.x11 : Reg) ↦ᵣ outPtr) **
      ((.x12 : Reg) ↦ᵣ cellPtr) ** ((.x5 : Reg) ↦ᵣ v5) **
      ((.x6 : Reg) ↦ᵣ v6) ** ((.x7 : Reg) ↦ᵣ v7) **
      ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      bytesRegion outPtr outBytes ** (cellPtr ↦ₘ cellOld) ** F)).pcFree := by
    repeat first
      | apply pcFree_sepConj
      | exact pcFree_regIs
      | exact pcFree_memIs
      | exact bytesRegion_pcFree _ _
      | exact hF
  exact callWithin_spec tshPrefixJalPC PrefixB vOld tshPrefixJalOff 8
    tshPrefixJal_target tshPrefixJal_mem hP
    (cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hcalleeF)


-- @@ L622-622 verbatim
end EvmAsm.Codegen.TxSigningHashSpec
