/-
  EvmAsm.Codegen.Programs.HeaderValidateParentHashSpec

  Shared scaffold for `header_validate_parent_hash` (#12346 residual callee
  triple; file-size split for PR #12365).  Pre/post match the pinned premise
  shape in `ValidateHeaderParentHashCorrespondence` (PR #12362) exactly:

    hvphEntryRest / hvphCalleePost
      — x1 link, x2 at caller sp0, 32-byte frameSlotsOwn/Saved,
        a0..a3 = this/parent RLP, scratch ownership, both byte regions.

  Arm residuals + adapters live in sibling modules (same namespace):
    * `HeaderValidateParentHashExtractFail`
    * `HeaderValidateParentHashKeccak` (keccak+compare shared body)
    * `HeaderValidateParentHashMatch`
    * `HeaderValidateParentHashMismatch`

  Program length 43. Status (a0): 0 match, 1 RLP extract fail, 2 hash mismatch.
-/

import EvmAsm.Codegen.Programs.HeadersKeccak
import EvmAsm.Codegen.Proofs.HashBridgeKeccakTop
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Rv64.SAsm.AbiFrame
import EvmAsm.Rv64.SAsm.AbiFrameCall
import EvmAsm.Rv64.SAsm.TwoExitLoop
import EvmAsm.Rv64.SAsm.SelectedRead
import EvmAsm.Rv64.SAsm.MeasureLoop
import EvmAsm.Evm64.CallingConvention
import EvmAsm.Rv64.Tactics.XSimp


-- @@ L32-32 verbatim
namespace EvmAsm.Codegen.HeaderValidateParentHashSpec


-- @@ L34-34 verbatim
open EvmAsm.Rv64 EvmAsm.Rv64.SAsm

-- @@ L35-35 verbatim
open EvmAsm.Codegen.Proofs


-- @@ L37-50 verbatim
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
      | exact pcFree_frameSlotsOwn _ _
      | exact pcFree_frameSlotsSaved _ _ _)


-- @@ L52-52 verbatim
/-! ## Bases, code, and the pinned ABI shape (#12362) -/


-- @@ L54-54 verbatim
abbrev H : Word := (GuestAddrs.header_validate_parent_hash : Word)

-- @@ L55-55 verbatim
abbrev K : Word := (GuestAddrs.zkvm_keccak256 : Word)

-- @@ L56-56 verbatim
abbrev P : Word := (GuestAddrs.headers_parent_hash : Word)

-- @@ L57-57 verbatim
abbrev Claimed : Word := (GuestAddrs.hvph_claimed : Word)

-- @@ L58-58 verbatim
abbrev Computed : Word := (GuestAddrs.hvph_computed : Word)


-- @@ L60-60 verbatim
abbrev hvphProg : Program := headerValidateParentHash_prog

-- @@ L61-61 verbatim
abbrev keccakProg : Program := zkvmKeccak256_prog

-- @@ L62-62 verbatim
abbrev headersProg : Program := headersParentHash_prog


-- @@ L64-64 verbatim
theorem hvph_length : hvphProg.length = 43 := by decide

-- @@ L65-65 verbatim
theorem headers_length : headersProg.length = 34 := by decide


-- @@ L67-67 verbatim
def hvphCode : CodeReq := CodeReq.ofProg H hvphProg

-- @@ L68-68 verbatim
def keccakCode : CodeReq := CodeReq.ofProg K keccakProg

-- @@ L69-69 verbatim
def headersCode : CodeReq := CodeReq.ofProg P headersProg


-- @@ L71-73 verbatim
/-- HVPH plus both callees. -/
def fullCode : CodeReq :=
  hvphCode.union (headersCode.union keccakCode)


-- @@ L75-77 verbatim
/-- 32-byte ABI frame — identical to the #12362 adapter pin. -/
def hvphFrame : FrameDesc :=
  [(.x1, 0), (.x8, 8), (.x9, 16), (.x18, 24)]


-- @@ L79-80 verbatim
def hvphSavedFrame : FrameDesc :=
  [(.x8, 8), (.x9, 16), (.x18, 24)]


-- @@ L82-83 verbatim
def hvphFrameVals (ret : Word) (vals : Reg → Word) : Reg → Word :=
  fun r => if r = .x1 then ret else vals r


-- @@ L85-97 verbatim
/-- Entry assertion — identical to adapter `hvphEntryRest`. -/
def hvphPre
    (sp0 thisPtr thisLen parentPtr parentLen : Word) (vals : Reg → Word)
    (thisBytes parentBytes : List (BitVec 8)) : Assertion :=
  (.x2 ↦ᵣ sp0) **
  frameSlotsOwn hvphFrame (sp0 + signExtend12 (-32 : BitVec 12)) **
  regsAt hvphSavedFrame vals **
  (.x10 ↦ᵣ thisPtr) ** (.x11 ↦ᵣ thisLen) **
  (.x12 ↦ᵣ parentPtr) ** (.x13 ↦ᵣ parentLen) **
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
  regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
  (.x0 ↦ᵣ (0 : Word)) **
  bytesRegion thisPtr thisBytes ** bytesRegion parentPtr parentBytes


-- @@ L99-112 verbatim
/-- Exit assertion — identical to adapter `hvphCalleePost`. -/
def hvphPost
    (sp0 thisPtr parentPtr ret status : Word) (vals : Reg → Word)
    (thisBytes parentBytes : List (BitVec 8)) : Assertion :=
  (.x1 ↦ᵣ ret) ** (.x2 ↦ᵣ sp0) **
  frameSlotsSaved hvphFrame (sp0 + signExtend12 (-32 : BitVec 12))
    (hvphFrameVals ret vals) **
  regsAt hvphSavedFrame vals **
  (.x10 ↦ᵣ status) **
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x11 **
  regOwn .x12 ** regOwn .x13 ** regOwn .x28 **
  regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
  (.x0 ↦ᵣ (0 : Word)) **
  bytesRegion thisPtr thisBytes ** bytesRegion parentPtr parentBytes


-- @@ L114-120 expanded
theorem hvphPre_pcFree (sp0 thisPtr thisLen parentPtr parentLen : Word) (vals : Reg → Word)
    (thisBytes parentBytes : List (BitVec 8)) :
    (hvphPre sp0 thisPtr thisLen parentPtr parentLen vals thisBytes parentBytes).pcFree :=
  by
  unfold hvphPre hvphFrame hvphSavedFrame
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


-- @@ L122-131 verbatim
/-- Keccak jal at H+68 is the one-shot entry (not segments). -/
theorem hvph_keccak_jal_oneshot :
    (∀ a i, CodeReq.singleton (H + 68)
        (.JAL .x1 (jalOff GuestAddrs.zkvm_keccak256
          (GuestAddrs.header_validate_parent_hash + 68))) a = some i →
      hvphCode a = some i) ∧
    (GuestAddrs.zkvm_keccak256 : Nat) ≠ GuestAddrs.zkvm_keccak256_segments := by
  refine ⟨?_, by decide⟩
  exact CodeReq.ofProg_mem_at H (H + 68) hvphProg 17 _
    (by bv_omega) (by rw [hvph_length]; decide) rfl (by rw [hvph_length]; decide)


-- @@ L133-133 verbatim
/-! ## Code membership helpers -/


-- @@ L135-138 verbatim
theorem hvph_mono : ∀ a i, hvphCode a = some i → fullCode a = some i := by
  intro a i hi
  unfold fullCode
  exact CodeReq.union_mono_left a i hi


-- @@ L140-145 verbatim
theorem hvph_headers_disjoint : hvphCode.Disjoint headersCode := by
  unfold hvphCode headersCode
  apply CodeReq.Disjoint.ofProg_ranges
  · rw [hvph_length]; decide
  · rw [headers_length]; decide
  · rw [hvph_length, headers_length]; decide


-- @@ L147-152 verbatim
theorem hvph_keccak_disjoint : hvphCode.Disjoint keccakCode := by
  unfold hvphCode keccakCode
  apply CodeReq.Disjoint.ofProg_ranges
  · rw [hvph_length]; decide
  · decide  -- zkvmKeccak256_prog.length
  · decide


-- @@ L154-159 verbatim
theorem headers_keccak_disjoint : headersCode.Disjoint keccakCode := by
  unfold headersCode keccakCode
  apply CodeReq.Disjoint.ofProg_ranges
  · rw [headers_length]; decide
  · decide
  · rw [headers_length]; decide


-- @@ L161-165 verbatim
theorem headers_mono : ∀ a i, headersCode a = some i → fullCode a = some i := by
  intro a i hi
  unfold fullCode
  exact CodeReq.mono_union_right hvph_headers_disjoint
    (fun a i h => CodeReq.union_mono_left a i h) a i hi


-- @@ L167-172 verbatim
theorem keccak_mono : ∀ a i, keccakCode a = some i → fullCode a = some i := by
  intro a i hi
  unfold fullCode
  exact CodeReq.mono_union_right hvph_keccak_disjoint
    (fun a i h => CodeReq.mono_union_right headers_keccak_disjoint
      (fun _ _ h' => h') a i h) a i hi


-- @@ L174-193 verbatim
/-! ## Callees (objdump-confirmed)

    `header_validate_parent_hash` is **not** self-contained:

    | Offset | Target | Machine status |
    |--------|--------|----------------|
    | **+36** | `headers_parent_hash` | **proven + gated**: Progress row
      `headers_parent_hash` `.proven` at `Progress/Routines.lean:483` with
      witness `headers_parent_hash_spec_within`, private abbrev
      `_headers_parent_hash_routine_witness`, and entry in
      `scripts/axiom-witness-registry-allow.txt` |
    | **+68** | `zkvm_keccak256` (one-shot) | **proven** `zkvm_keccak256_spec_within` |

    Conjunct 11 chain: validate_header adapter → HVPH → headers_parent_hash → keccak.
    The **leaf** (`headers_parent_hash`) is proven and in the axiom gate; what
    remains open is the **adapter** from `validate_header` through HVPH to that
    leaf. HVPH itself has **no** Progress row; the HVPH top triple still names
    an explicit **`headers_parent_hash` premise** (composition residual, not a
    missing leaf). Keccak is discharged by its proven leaf (not a premise).
-/


-- @@ L195-202 verbatim
/-- Objdump pin: +36 jal targets `headers_parent_hash`. -/
theorem hvph_headers_jal_mem :
    ∀ a i, CodeReq.singleton (H + 36)
        (.JAL .x1 (jalOff GuestAddrs.headers_parent_hash
          (GuestAddrs.header_validate_parent_hash + 36))) a = some i →
      hvphCode a = some i :=
  CodeReq.ofProg_mem_at H (H + 36) hvphProg 9 _
    (by bv_omega) (by rw [hvph_length]; decide) rfl (by rw [hvph_length]; decide)


-- @@ L204-212 verbatim
/-! ## Top theorem (shape pin)

    Landed: prologue ;; headers premise ;; extract-fail (`19+nH`); keccak setup+call
    (`5+nK`); compare rounds + match/mismatch exits; from-`H+72` match (`24`) /
    mismatch0 (`14`) with `regOwn` scratch; keccak→compare-match (`29+nK`);
    from-`H+40` match (`30+nK`) / mismatch0 (`20+nK`);
    prologue→match (`40+nH+nK`) / mismatch0 (`30+nH+nK`);
    adapter-shaped: match / mismatch0 / extract-fail (hvphPre/Post + BSS).
-/


-- @@ L214-233 verbatim
/-- **Shape-locked top contract** for `header_validate_parent_hash`.

    Matches #12362 adapter `hvphPre`/`hvphPost` exactly.  The statement takes a
    named `headers_parent_hash` premise (`h_headers`); the keccak call at +68 is
    *not* a premise — proofs must invoke `zkvm_keccak256_spec_within`.

    `claimedBytes` / ambient BSS ownership will be threaded through the body
    composition (adapter shape itself does not name them). -/
def header_validate_parent_hash_spec_within_type
    (n : Nat) (sp0 thisPtr thisLen parentPtr parentLen ret status : Word)
    (vals : Reg → Word)
    (thisBytes parentBytes : List (BitVec 8))
    (h_headers : Prop) : Prop :=
  h_headers →
  cpsTripleWithin n H ret fullCode
    ((.x1 ↦ᵣ ret) **
      hvphPre sp0 thisPtr thisLen parentPtr parentLen vals thisBytes parentBytes)
    (hvphPost sp0 thisPtr parentPtr ret status vals thisBytes parentBytes)

-- Length / pin KATs used by review and by the adapter's oneshot check.

-- @@ L234-234 verbatim
example : hvphProg.length = 43 := hvph_length

-- @@ L235-236 verbatim
example : (GuestAddrs.zkvm_keccak256 : Nat) ≠ GuestAddrs.zkvm_keccak256_segments :=
  hvph_keccak_jal_oneshot.2


-- @@ L238-238 verbatim
/-! ## Prologue (instr 0–4): allocate + storeSeq -/


-- @@ L240-243 verbatim
theorem regsAt_hvphFrame_of_vals (ret : Word) (vals : Reg → Word) :
    regsAt hvphFrame (hvphFrameVals ret vals) =
      ((.x1 ↦ᵣ ret) ** regsAt hvphSavedFrame vals) := by
  simp [hvphFrame, hvphSavedFrame, hvphFrameVals, regsAt, sepConj_emp_right']


-- @@ L245-248 verbatim
theorem regsAt_hvphSavedFrame (vals : Reg → Word) :
    regsAt hvphSavedFrame vals =
      ((.x8 ↦ᵣ vals .x8) ** (.x9 ↦ᵣ vals .x9) ** (.x18 ↦ᵣ vals .x18)) := by
  simp [hvphSavedFrame, regsAt, sepConj_emp_right']


-- @@ L250-281 expanded
set_option maxRecDepth 8000 in
/-- ADDI sp,-32 ;; SD ra/s0/s1/s2 (instr 0–4). Leaves PC at `H+20`. -/
theorem hvphFrameSave (sp0 spC ret : Word) (vals : Reg → Word)
    (hspC : spC = sp0 + signExtend12 (-32 : BitVec 12)) :
    cpsTripleWithin 5 H (H + 20) hvphCode
      ((.x2 ↦ᵣ sp0) ** regsAt hvphFrame (hvphFrameVals ret vals) ** frameSlotsOwn hvphFrame spC)
      ((.x2 ↦ᵣ spC) **
        regsAt hvphFrame (hvphFrameVals ret vals) **
          frameSlotsSaved hvphFrame spC (hvphFrameVals ret vals)) :=
  by
  have ha0 := addi_spec_gen_same_within .x2 sp0 (-32 : BitVec 12) H (by decide)
  rw [← hspC] at ha0
  have ha :=
    cpsTripleWithin_extend_code
      (CodeReq.ofProg_mem_at H H hvphProg 0 (.ADDI .x2 .x2 (-32 : BitVec 12)) rfl
        (by rw [hvph_length]; decide) rfl (by rw [hvph_length]; decide))
      ha0
  have haF :=
    cpsTripleWithin_frameR
      (regsAt hvphFrame (hvphFrameVals ret vals) ** frameSlotsOwn hvphFrame spC)
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
      ha
  have hs0 := storeSeq_spec hvphFrame spC (hvphFrameVals ret vals) (H + 4) (by decide)
  have h_storeMono :
    ∀ a i, CodeReq.ofProg (H + 4) (storeProg hvphFrame) a = some i → hvphCode a = some i :=
    by
    intro a i h_mem
    exact
      CodeReq.ofProg_mono_sub H (H + 4) hvphProg (storeProg hvphFrame) 1 (by bv_omega) rfl
        (by rw [hvph_length]; simp [hvphFrame, storeProg]) (by rw [hvph_length]; decide) a i h_mem
  have hs := cpsTripleWithin_extend_code h_storeMono hs0
  rw [show H + 4 + BitVec.ofNat 64 (4 * hvphFrame.length) = H + 20 from by simp [hvphFrame];
      bv_omega] at hs
  exact cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) haF hs


-- @@ L283-283 verbatim
/-! ## Setup (instr 5–8): park parent in s0/s1; `la a2, hvph_claimed` -/


-- @@ L285-336 expanded
set_option maxRecDepth 8000 in
/-- `mv s0,a2` ;; `mv s1,a3` ;; `la a2, claimed` (instr 5–8). Leaves PC at
    `H+36` — the `jal headers_parent_hash` site. -/
theorem hvphSetup (spC ret thisPtr thisLen parentPtr parentLen : Word) (vals : Reg → Word) :
    cpsTripleWithin 4 (H + 20) (H + 36) hvphCode
      ((.x2 ↦ᵣ spC) **
        (.x1 ↦ᵣ ret) **
          (.x8 ↦ᵣ vals .x8) **
            (.x9 ↦ᵣ vals .x9) **
              (.x18 ↦ᵣ vals .x18) **
                (.x10 ↦ᵣ thisPtr) **
                  (.x11 ↦ᵣ thisLen) **
                    (.x12 ↦ᵣ parentPtr) **
                      (.x13 ↦ᵣ parentLen) ** frameSlotsSaved hvphFrame spC (hvphFrameVals ret vals))
      ((.x2 ↦ᵣ spC) **
        (.x1 ↦ᵣ ret) **
          (.x8 ↦ᵣ parentPtr) **
            (.x9 ↦ᵣ parentLen) **
              (.x18 ↦ᵣ vals .x18) **
                (.x10 ↦ᵣ thisPtr) **
                  (.x11 ↦ᵣ thisLen) **
                    (.x12 ↦ᵣ Claimed) **
                      (.x13 ↦ᵣ parentLen) **
                        frameSlotsSaved hvphFrame spC (hvphFrameVals ret vals)) :=
  by
  have h0 := mv_spec_gen_within .x8 .x12 parentPtr (vals .x8) (H + 20) (by decide)
  have h1 := mv_spec_gen_within .x9 .x13 parentLen (vals .x9) (H + 24) (by decide)
  have e0 :=
    cpsTripleWithin_extend_code
      (CodeReq.ofProg_mem_at H (H + 20) hvphProg 5 (.MV .x8 .x12) (by bv_omega)
        (by rw [hvph_length]; decide) rfl (by rw [hvph_length]; decide))
      h0
  have e1 :=
    cpsTripleWithin_extend_code
      (CodeReq.ofProg_mem_at H (H + 24) hvphProg 6 (.MV .x9 .x13) (by bv_omega)
        (by rw [hvph_length]; decide) rfl (by rw [hvph_length]; decide))
      h1
  have hau :=
    CodeReq.ofProg_mem_at H (H + 28) hvphProg 7
      (.AUIPC .x12
        (EvmAsm.Codegen.laHi GuestAddrs.hvph_claimed (GuestAddrs.header_validate_parent_hash + 28)))
      (by bv_omega) (by rw [hvph_length]; decide) rfl (by rw [hvph_length]; decide)
  have had :=
    CodeReq.ofProg_mem_at H (H + 32) hvphProg 8
      (.ADDI .x12 .x12
        (EvmAsm.Codegen.laLo GuestAddrs.hvph_claimed (GuestAddrs.header_validate_parent_hash + 28)))
      (by bv_omega) (by rw [hvph_length]; decide) rfl (by rw [hvph_length]; decide)
  have hla :=
    EvmAsm.Rv64.la_materialize_within .x12 parentPtr (H + 28) Claimed (by decide)
      (by unfold H Claimed; decide) hau had
  have e0F :=
    cpsTripleWithin_frameR
      ((.x2 ↦ᵣ spC) **
        (.x1 ↦ᵣ ret) **
          (.x9 ↦ᵣ vals .x9) **
            (.x18 ↦ᵣ vals .x18) **
              (.x10 ↦ᵣ thisPtr) **
                (.x11 ↦ᵣ thisLen) **
                  (.x13 ↦ᵣ parentLen) ** frameSlotsSaved hvphFrame spC (hvphFrameVals ret vals))
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
      e0
  have e1F :=
    cpsTripleWithin_frameR
      ((.x2 ↦ᵣ spC) **
        (.x1 ↦ᵣ ret) **
          (.x8 ↦ᵣ parentPtr) **
            (.x18 ↦ᵣ vals .x18) **
              (.x10 ↦ᵣ thisPtr) **
                (.x11 ↦ᵣ thisLen) **
                  (.x12 ↦ᵣ parentPtr) ** frameSlotsSaved hvphFrame spC (hvphFrameVals ret vals))
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
      e1
  have hlaF :=
    cpsTripleWithin_frameR
      ((.x2 ↦ᵣ spC) **
        (.x1 ↦ᵣ ret) **
          (.x8 ↦ᵣ parentPtr) **
            (.x9 ↦ᵣ parentLen) **
              (.x18 ↦ᵣ vals .x18) **
                (.x10 ↦ᵣ thisPtr) **
                  (.x11 ↦ᵣ thisLen) **
                    (.x13 ↦ᵣ parentLen) ** frameSlotsSaved hvphFrame spC (hvphFrameVals ret vals))
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
  have h01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) e0F e1F
  have hall := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h01 hlaF
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => by xperm_hyp hq) hall


-- @@ L338-363 expanded
set_option maxRecDepth 8000 in
/-- Frame save + setup through `H+36` (ready for `jal headers_parent_hash`). -/
theorem hvphPrologue (sp0 spC ret thisPtr thisLen parentPtr parentLen : Word) (vals : Reg → Word)
    (hspC : spC = sp0 + signExtend12 (-32 : BitVec 12)) :
    cpsTripleWithin 9 H (H + 36) hvphCode
      ((.x2 ↦ᵣ sp0) **
        regsAt hvphFrame (hvphFrameVals ret vals) **
          frameSlotsOwn hvphFrame spC **
            (.x10 ↦ᵣ thisPtr) ** (.x11 ↦ᵣ thisLen) ** (.x12 ↦ᵣ parentPtr) ** (.x13 ↦ᵣ parentLen))
      ((.x2 ↦ᵣ spC) **
        (.x1 ↦ᵣ ret) **
          (.x8 ↦ᵣ parentPtr) **
            (.x9 ↦ᵣ parentLen) **
              (.x18 ↦ᵣ vals .x18) **
                (.x10 ↦ᵣ thisPtr) **
                  (.x11 ↦ᵣ thisLen) **
                    (.x12 ↦ᵣ Claimed) **
                      (.x13 ↦ᵣ parentLen) **
                        frameSlotsSaved hvphFrame spC (hvphFrameVals ret vals)) :=
  by
  have hsave := hvphFrameSave sp0 spC ret vals hspC
  have hsaveF :=
    cpsTripleWithin_frameR
      ((.x10 ↦ᵣ thisPtr) ** (.x11 ↦ᵣ thisLen) ** (.x12 ↦ᵣ parentPtr) ** (.x13 ↦ᵣ parentLen))
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
      hsave
  have hsetup := hvphSetup spC ret thisPtr thisLen parentPtr parentLen vals
  have h01 :=
    cpsTripleWithin_seq_perm_same_cr
      (fun _ hp => by
        rw [regsAt_hvphFrame_of_vals, regsAt_hvphSavedFrame] at hp
        xperm_hyp hp)
      hsaveF hsetup
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => by xperm_hyp hq) h01


-- @@ L365-368 verbatim
/-! ## `headers_parent_hash` premise shape (no machine triple yet)

    Call at `H+36` returns to `H+40`.  ABI: `a0/a1` = this RLP, `a2` = Claimed
    out-buffer.  `a0=0` success (32 bytes written); nonzero → extract fail. -/


-- @@ L370-372 verbatim
/-- Out-buffer ownership for the claimed parent-hash scratch (32 bytes). -/
abbrev claimedOwn (claimedBytes : List (BitVec 8)) : Assertion :=
  bytesRegion Claimed claimedBytes


-- @@ L374-392 verbatim
/-- Call-site premise for `headers_parent_hash` under HVPH's frame.

    Pre: a0/a1/a2 set, Claimed buffer owned, this-bytes ambient, frame/saved
    regs/`sp` framed in `F`.  Post: a0 = `statusHdr`; Claimed holds
    `claimedOut` (caller picks; equal to `claimedBytes` on the fail path);
    a1/a2 returned as `regOwn` (havoc — callee clobbers entry values;
    ownership is required for the caller's re-bind at `H+52`). -/
def headersCallPremise
    (nH : Nat) (retHdr statusHdr thisPtr thisLen : Word)
    (thisBytes claimedBytes claimedOut : List (BitVec 8))
    (F : Assertion) : Prop :=
  cpsTripleWithin nH P retHdr headersCode
    ((.x1 ↦ᵣ retHdr) ** (.x10 ↦ᵣ thisPtr) ** (.x11 ↦ᵣ thisLen) **
      (.x12 ↦ᵣ Claimed) ** claimedOwn claimedBytes **
      bytesRegion thisPtr thisBytes ** F)
    ((.x1 ↦ᵣ retHdr) ** (.x10 ↦ᵣ statusHdr) **
      claimedOwn claimedOut **
      bytesRegion thisPtr thisBytes **
      regOwn .x11 ** regOwn .x12 ** F)


-- @@ L394-398 verbatim
/-! ## Epilogue (instr 37–42 at `H+148`)

    `loadSeq` ra/s0/s1/s2; ADDI sp,+32; JALR.  Carries `a0 = status` and ambient
    `G` (byte regions / scratch).  Saved slot values (`vals`) are restored into
    regs; `vals'` are the clobbered pre-restore register values. -/


-- @@ L400-400 verbatim
theorem hvphFrame_hne : ∀ p ∈ hvphFrame, p.1 ≠ .x0 := by decide


-- @@ L402-406 verbatim
theorem regsAt_hvphFrame (vals : Reg → Word) :
    regsAt hvphFrame vals =
      ((.x1 ↦ᵣ vals .x1) ** (.x8 ↦ᵣ vals .x8) ** (.x9 ↦ᵣ vals .x9) **
        (.x18 ↦ᵣ vals .x18)) := by
  simp [hvphFrame, regsAt, sepConj_emp_right']


-- @@ L408-414 verbatim
theorem frameSlotsSaved_hvphFrame (spC : Word) (vals : Reg → Word) :
    frameSlotsSaved hvphFrame spC vals =
      (((spC + signExtend12 (0 : BitVec 12)) ↦ₘ vals .x1) **
        ((spC + signExtend12 (8 : BitVec 12)) ↦ₘ vals .x8) **
        ((spC + signExtend12 (16 : BitVec 12)) ↦ₘ vals .x9) **
        ((spC + signExtend12 (24 : BitVec 12)) ↦ₘ vals .x18)) := by
  simp [hvphFrame, frameSlotsSaved, sepConj_emp_right']


-- @@ L416-487 expanded
set_option maxRecDepth 8000 in
theorem hvphEpi (sp0 spC status : Word) (vals vals' : Reg → Word) (G : Assertion) (hG : G.pcFree)
    (hspC : spC = sp0 + signExtend12 (-32 : BitVec 12))
    (hret : vals .x1 &&& ~~~(1 : Word) = vals .x1) :
    cpsTripleWithin 6 (H + 148) (vals .x1) hvphCode
      ((.x10 ↦ᵣ status) **
        (.x2 ↦ᵣ spC) ** regsAt hvphFrame vals' ** frameSlotsSaved hvphFrame spC vals ** G)
      ((.x10 ↦ᵣ status) **
        (.x1 ↦ᵣ vals .x1) **
          (.x2 ↦ᵣ sp0) **
            (.x8 ↦ᵣ vals .x8) **
              (.x9 ↦ᵣ vals .x9) **
                (.x18 ↦ᵣ vals .x18) ** frameSlotsSaved hvphFrame spC vals ** G) :=
  by
  have hs0 := loadSeq_spec hvphFrame spC vals vals' (H + 148) (by decide) hvphFrame_hne
  have h_loadMono :
    ∀ a i, CodeReq.ofProg (H + 148) (loadProg hvphFrame) a = some i → hvphCode a = some i :=
    by
    intro a i h_mem
    exact
      CodeReq.ofProg_mono_sub H (H + 148) hvphProg (loadProg hvphFrame) 37 (by bv_omega) (by rfl)
        (by rw [hvph_length]; simp [hvphFrame, loadProg]) (by rw [hvph_length]; decide) a i h_mem
  have hs := cpsTripleWithin_extend_code h_loadMono hs0
  rw [show H + 148 + BitVec.ofNat 64 (4 * hvphFrame.length) = H + 164 from by simp [hvphFrame];
      bv_omega] at hs
  have ha0 := addi_spec_gen_same_within .x2 spC (32 : BitVec 12) (H + 164) (by decide)
  have hsp : spC + signExtend12 (32 : BitVec 12) = sp0 :=
    by
    rw [hspC]
    rw [show signExtend12 (-32 : BitVec 12) = (-32 : Word) from by decide,
      show signExtend12 (32 : BitVec 12) = (32 : Word) from by decide]
    bv_omega
  rw [hsp] at ha0
  have ha :=
    cpsTripleWithin_extend_code
      (CodeReq.ofProg_mem_at H (H + 164) hvphProg 41 (.ADDI .x2 .x2 (32 : BitVec 12)) (by bv_omega)
        (by rw [hvph_length]; decide) rfl (by rw [hvph_length]; decide))
      ha0
  have haF :=
    cpsTripleWithin_frameR (regsAt hvphFrame vals ** frameSlotsSaved hvphFrame spC vals)
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
      ha
  have hload_addi := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hs haF
  have hpc : (H + 164 : Word) + 4 = H + 168 := by bv_omega
  rw [hpc] at hload_addi
  have hjalr0 := EvmAsm.Evm64.ret_spec_within' (H + 168) (vals .x1)
  rw [hret] at hjalr0
  have hjalrC :=
    cpsTripleWithin_extend_code
      (CodeReq.ofProg_mem_at H (H + 168) hvphProg 42 (.JALR .x0 .x1 (0 : BitVec 12)) (by bv_omega)
        (by rw [hvph_length]; decide) rfl (by rw [hvph_length]; decide))
      hjalr0
  have hjalrF :=
    cpsTripleWithin_frameR
      ((.x2 ↦ᵣ sp0) **
        (.x8 ↦ᵣ vals .x8) **
          (.x9 ↦ᵣ vals .x9) ** (.x18 ↦ᵣ vals .x18) ** frameSlotsSaved hvphFrame spC vals)
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
      hjalrC
  have hall :=
    cpsTripleWithin_seq_perm_same_cr
      (fun _ hp => by
        rw [regsAt_hvphFrame] at hp
        xperm_hyp hp)
      hload_addi hjalrF
  have hn : hvphFrame.length + 1 + 1 = 6 := by simp [hvphFrame]
  rw [hn] at hall
  have hcore :
    cpsTripleWithin 6 (H + 148) (vals .x1) hvphCode
      ((.x2 ↦ᵣ spC) ** regsAt hvphFrame vals' ** frameSlotsSaved hvphFrame spC vals)
      ((.x1 ↦ᵣ vals .x1) **
        (.x2 ↦ᵣ sp0) **
          (.x8 ↦ᵣ vals .x8) **
            (.x9 ↦ᵣ vals .x9) ** (.x18 ↦ᵣ vals .x18) ** frameSlotsSaved hvphFrame spC vals) :=
    cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => by xperm_hyp hq) hall
  have hframed :=
    cpsTripleWithin_frameR ((.x10 ↦ᵣ status) ** G)
      (by refine pcFree_sepConj ?_ hG;
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
      hcore
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => by xperm_hyp hq) hframed


-- @@ L489-491 verbatim
/-! ## Status-1 exit — `li a0, 1` @ `H+44` → `j` → epilogue

    Taken when `headers_parent_hash` returns nonzero (extract failure). -/


-- @@ L493-526 expanded
set_option maxRecDepth 8000 in
theorem hvphStatus1Exit (sp0 spC o10 : Word) (vals vals' : Reg → Word) (G : Assertion)
    (hG : G.pcFree) (hspC : spC = sp0 + signExtend12 (-32 : BitVec 12))
    (hret : vals .x1 &&& ~~~(1 : Word) = vals .x1) :
    cpsTripleWithin 8 (H + 44) (vals .x1) hvphCode
      ((.x10 ↦ᵣ o10) **
        (.x2 ↦ᵣ spC) ** regsAt hvphFrame vals' ** frameSlotsSaved hvphFrame spC vals ** G)
      ((.x10 ↦ᵣ (1 : Word)) **
        (.x1 ↦ᵣ vals .x1) **
          (.x2 ↦ᵣ sp0) **
            (.x8 ↦ᵣ vals .x8) **
              (.x9 ↦ᵣ vals .x9) **
                (.x18 ↦ᵣ vals .x18) ** frameSlotsSaved hvphFrame spC vals ** G) :=
  by
  have s0 := li_spec_gen_within .x10 o10 (1 : Word) (H + 44) (by decide)
  have s1 := jal_x0_spec_gen_within (100 : BitVec 21) (H + 48)
  rw [show (H + 48) + signExtend21 (100 : BitVec 21) = H + 148 from
      by
      rw [show signExtend21 (100 : BitVec 21) = (100 : Word) from by decide]
      bv_omega] at s1
  have s0C :=
    cpsTripleWithin_extend_code
      (CodeReq.ofProg_mem_at H (H + 44) hvphProg 11 (.LI .x10 (1 : Word)) (by bv_omega)
        (by rw [hvph_length]; decide) rfl (by rw [hvph_length]; decide))
      s0
  have s1C :=
    cpsTripleWithin_extend_code
      (CodeReq.ofProg_mem_at H (H + 48) hvphProg 12 (.JAL .x0 (100 : BitVec 21)) (by bv_omega)
        (by rw [hvph_length]; decide) rfl (by rw [hvph_length]; decide))
      s1
  have hblock :
    cpsTripleWithin 2 (H + 44) (H + 148) hvphCode ((.x10 ↦ᵣ o10)) ((.x10 ↦ᵣ (1 : Word))) := by
    runBlock s0C s1C
  have hblockF :=
    cpsTripleWithin_frameR
      ((.x2 ↦ᵣ spC) ** regsAt hvphFrame vals' ** frameSlotsSaved hvphFrame spC vals ** G)
      (by
        refine pcFree_sepConj ?_ (pcFree_sepConj ?_ (pcFree_sepConj ?_ hG)) <;>
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
      hblock
  have hepi := hvphEpi sp0 spC (1 : Word) vals vals' G hG hspC hret
  have hall := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hblockF hepi
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => by xperm_hyp hq) hall


-- @@ L528-528 verbatim
/-! ## Extract-fail branch (instr 10): `beq a0,x0` fall-through when nonzero -/


-- @@ L530-546 verbatim
set_option maxRecDepth 8000 in
/-- `beq a0, x0` not-taken when `statusHdr ≠ 0` (fall through to `H+44`). -/
theorem hvphBeqExtractFail (statusHdr : Word) (h_nz : statusHdr ≠ (0 : Word)) :
    cpsTripleWithin 1 (H + 40) (H + 44) hvphCode
      ((.x10 ↦ᵣ statusHdr) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x10 ↦ᵣ statusHdr) ** (.x0 ↦ᵣ (0 : Word))) := by
  have hbeq := beq_spec_gen_within .x10 .x0 (12 : BitVec 13) statusHdr (0 : Word) (H + 40)
  rw [show (H + 40 : Word) + 4 = H + 44 from by bv_omega,
    show (H + 40) + signExtend13 (12 : BitVec 13) = H + 52 from by
      rw [show signExtend13 (12 : BitVec 13) = (12 : Word) from by decide]; bv_omega] at hbeq
  exact cpsBranchWithin_ntakenStripPure2
    (cpsBranchWithin_extend_code
      (CodeReq.ofProg_mem_at H (H + 40) hvphProg 10 (.BEQ .x10 .x0 (12 : BitVec 13))
        (by bv_omega) (by rw [hvph_length]; decide) rfl (by rw [hvph_length]; decide)) hbeq)
    (fun _ hQt => by
      obtain ⟨_, _, _, _, _, hBP⟩ := hQt
      exact h_nz ((sepConj_pure_right _).1 hBP).2)


-- @@ L548-564 verbatim
set_option maxRecDepth 8000 in
/-- `beq a0, x0` taken when `a0 = 0` (branch to success setup at `H+52`). -/
theorem hvphBeqExtractOk :
    cpsTripleWithin 1 (H + 40) (H + 52) hvphCode
      ((.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) := by
  have hbeq := beq_spec_gen_within .x10 .x0 (12 : BitVec 13) (0 : Word) (0 : Word) (H + 40)
  rw [show (H + 40 : Word) + 4 = H + 44 from by bv_omega,
    show (H + 40) + signExtend13 (12 : BitVec 13) = H + 52 from by
      rw [show signExtend13 (12 : BitVec 13) = (12 : Word) from by decide]; bv_omega] at hbeq
  exact cpsBranchWithin_takenStripPure2
    (cpsBranchWithin_extend_code
      (CodeReq.ofProg_mem_at H (H + 40) hvphProg 10 (.BEQ .x10 .x0 (12 : BitVec 13))
        (by bv_omega) (by rw [hvph_length]; decide) rfl (by rw [hvph_length]; decide)) hbeq)
    (fun _ hQf => by
      obtain ⟨_, _, _, _, _, hBP⟩ := hQf
      exact ((sepConj_pure_right _).1 hBP).2 rfl)


-- @@ L566-575 verbatim
/-- Ambient framed across the `headers_parent_hash` call (HVPH frame + parent). -/
def headersCallFrame
    (spC ret parentPtr parentLen : Word) (vals : Reg → Word)
    (parentBytes : List (BitVec 8)) : Assertion :=
  (.x2 ↦ᵣ spC) ** (.x8 ↦ᵣ parentPtr) ** (.x9 ↦ᵣ parentLen) **
  (.x18 ↦ᵣ vals .x18) ** (.x13 ↦ᵣ parentLen) **
  frameSlotsSaved hvphFrame spC (hvphFrameVals ret vals) **
  bytesRegion parentPtr parentBytes **
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
  regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word))


-- @@ L577-581 expanded
theorem headersCallFrame_pcFree (spC ret parentPtr parentLen : Word) (vals : Reg → Word)
    (parentBytes : List (BitVec 8)) :
    (headersCallFrame spC ret parentPtr parentLen vals parentBytes).pcFree := by
  unfold headersCallFrame hvphFrame;
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


-- @@ L583-589 verbatim
/-- Current regs at post-headers (link = `H+40`, parent still in s0/s1). -/
def hvphPostHeadersVals (parentPtr parentLen : Word) (vals : Reg → Word) : Reg → Word :=
  fun r =>
    if r = .x1 then (H + 40 : Word)
    else if r = .x8 then parentPtr
    else if r = .x9 then parentLen
    else vals r


-- @@ L591-595 verbatim
theorem hvph_headers_jal_disj :
    (CodeReq.singleton (H + 36)
      (.JAL .x1 (jalOff GuestAddrs.headers_parent_hash
        (GuestAddrs.header_validate_parent_hash + 36)))).Disjoint headersCode :=
  CodeReq.Disjoint.singleton_ofProg (by decide)


-- @@ L597-603 verbatim
/-- Prest for `WP.cpsCallWithin` at the headers jal (everything but link). -/
def headersCallPrest
    (spC ret thisPtr thisLen parentPtr parentLen : Word) (vals : Reg → Word)
    (thisBytes parentBytes claimedBytes : List (BitVec 8)) : Assertion :=
  (.x10 ↦ᵣ thisPtr) ** (.x11 ↦ᵣ thisLen) ** (.x12 ↦ᵣ Claimed) **
  claimedOwn claimedBytes ** bytesRegion thisPtr thisBytes **
  headersCallFrame spC ret parentPtr parentLen vals parentBytes


-- @@ L605-610 expanded
theorem headersCallPrest_pcFree (spC ret thisPtr thisLen parentPtr parentLen : Word)
    (vals : Reg → Word) (thisBytes parentBytes claimedBytes : List (BitVec 8)) :
    (headersCallPrest spC ret thisPtr thisLen parentPtr parentLen vals thisBytes parentBytes
        claimedBytes).pcFree :=
  by unfold headersCallPrest headersCallFrame claimedOwn hvphFrame;
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


-- @@ L612-672 verbatim
set_option maxRecDepth 8000 in
/-- `jal headers_parent_hash` at `H+36` under `headersCallPremise` (returns `H+40`). -/
theorem hvphHeadersCall
    (nH : Nat) (spC ret thisPtr thisLen parentPtr parentLen statusHdr : Word)
    (vals : Reg → Word)
    (thisBytes parentBytes claimedBytes claimedOut : List (BitVec 8))
    (h_headers : headersCallPremise nH (H + 40) statusHdr thisPtr thisLen
      thisBytes claimedBytes claimedOut
      (headersCallFrame spC ret parentPtr parentLen vals parentBytes)) :
    cpsTripleWithin (1 + nH) (H + 36) (H + 40) fullCode
      ((.x1 ↦ᵣ ret) **
        headersCallPrest spC ret thisPtr thisLen parentPtr parentLen vals
          thisBytes parentBytes claimedBytes)
      ((.x1 ↦ᵣ (H + 40)) ** (.x10 ↦ᵣ statusHdr) **
        claimedOwn claimedOut ** bytesRegion thisPtr thisBytes **
        regOwn .x11 ** regOwn .x12 **
        headersCallFrame spC ret parentPtr parentLen vals parentBytes) := by
  have htarget : (H + 36) + signExtend21 (jalOff GuestAddrs.headers_parent_hash
      (GuestAddrs.header_validate_parent_hash + 36)) = P := by
    change BitVec.ofNat 64 GuestAddrs.header_validate_parent_hash + BitVec.ofNat 64 36 + _ =
      BitVec.ofNat 64 GuestAddrs.headers_parent_hash
    exact jalOff_correct_add GuestAddrs.headers_parent_hash
      GuestAddrs.header_validate_parent_hash 36
      (by decide) (by decide) (by decide) (by decide)
  have hret40 : ((H + 36 : Word) + 4) &&& ~~~(1 : Word) = (H + 36) + 4 := by decide
  have hPrest := headersCallPrest_pcFree spC ret thisPtr thisLen parentPtr parentLen vals
    thisBytes parentBytes claimedBytes
  have hcallee : cpsTripleWithin nH P ((H + 36 + 4) &&& ~~~(1 : Word)) headersCode
      ((.x1 ↦ᵣ (H + 36 + 4)) **
        headersCallPrest spC ret thisPtr thisLen parentPtr parentLen vals
          thisBytes parentBytes claimedBytes)
      ((.x1 ↦ᵣ (H + 40)) ** (.x10 ↦ᵣ statusHdr) **
        claimedOwn claimedOut ** bytesRegion thisPtr thisBytes **
        regOwn .x11 ** regOwn .x12 **
        headersCallFrame spC ret parentPtr parentLen vals parentBytes) := by
    rw [hret40, show (H + 36 + 4 : Word) = H + 40 from by bv_omega]
    unfold headersCallPremise at h_headers
    refine cpsTripleWithin_weaken (fun _ hp => by
      unfold headersCallPrest at hp
      xperm_hyp hp) (fun _ hq => hq) h_headers
  have hcall0 := WP.cpsCallWithin
    (nSteps := nH) (callerPC := H + 36) (calleeEntry := P) (vOld := ret)
    (calleeCode := headersCode)
    (Prest := headersCallPrest spC ret thisPtr thisLen parentPtr parentLen vals
      thisBytes parentBytes claimedBytes)
    (Q := (.x1 ↦ᵣ (H + 40)) ** (.x10 ↦ᵣ statusHdr) **
      claimedOwn claimedOut ** bytesRegion thisPtr thisBytes **
      regOwn .x11 ** regOwn .x12 **
      headersCallFrame spC ret parentPtr parentLen vals parentBytes)
    (jalOff GuestAddrs.headers_parent_hash
      (GuestAddrs.header_validate_parent_hash + 36))
    htarget hret40 hPrest hvph_headers_jal_disj hcallee
  have hcallCode : ∀ a i,
      ((CodeReq.singleton (H + 36)
        (.JAL .x1 (jalOff GuestAddrs.headers_parent_hash
          (GuestAddrs.header_validate_parent_hash + 36)))).union headersCode) a = some i →
      fullCode a = some i :=
    CodeReq.union_split_mono
      (fun a i h => hvph_mono a i (hvph_headers_jal_mem a i h))
      headers_mono
  exact cpsTripleWithin_extend_code hcallCode hcall0


-- @@ L674-726 expanded
set_option maxRecDepth 8000 in
/-- Prologue through headers return (`H → H+40`) under `headersCallPremise`. -/
theorem hvphPrologueHeaders (nH : Nat)
    (sp0 spC ret thisPtr thisLen parentPtr parentLen statusHdr : Word) (vals : Reg → Word)
    (thisBytes parentBytes claimedBytes claimedOut : List (BitVec 8))
    (hspC : spC = sp0 + signExtend12 (-32 : BitVec 12))
    (h_headers :
      headersCallPremise nH (H + 40) statusHdr thisPtr thisLen thisBytes claimedBytes claimedOut
        (headersCallFrame spC ret parentPtr parentLen vals parentBytes)) :
    cpsTripleWithin (9 + (1 + nH)) H (H + 40) fullCode
      ((.x2 ↦ᵣ sp0) **
        regsAt hvphFrame (hvphFrameVals ret vals) **
          frameSlotsOwn hvphFrame spC **
            (.x10 ↦ᵣ thisPtr) **
              (.x11 ↦ᵣ thisLen) **
                (.x12 ↦ᵣ parentPtr) **
                  (.x13 ↦ᵣ parentLen) **
                    claimedOwn claimedBytes **
                      bytesRegion thisPtr thisBytes **
                        bytesRegion parentPtr parentBytes **
                          regOwn .x5 **
                            regOwn .x6 **
                              regOwn .x7 **
                                regOwn .x28 **
                                  regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)))
      ((.x1 ↦ᵣ (H + 40)) **
        (.x10 ↦ᵣ statusHdr) **
          claimedOwn claimedOut **
            bytesRegion thisPtr thisBytes **
              regOwn .x11 **
                regOwn .x12 ** headersCallFrame spC ret parentPtr parentLen vals parentBytes) :=
  by
  have hpro0 := hvphPrologue sp0 spC ret thisPtr thisLen parentPtr parentLen vals hspC
  have hpro := cpsTripleWithin_extend_code hvph_mono hpro0
  have hproF :=
    cpsTripleWithin_frameR
      (claimedOwn claimedBytes **
        bytesRegion thisPtr thisBytes **
          bytesRegion parentPtr parentBytes **
            regOwn .x5 **
              regOwn .x6 **
                regOwn .x7 **
                  regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)))
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
      hpro
  have hcall0 :=
    hvphHeadersCall nH spC ret thisPtr thisLen parentPtr parentLen statusHdr vals thisBytes
      parentBytes claimedBytes claimedOut h_headers
  have hcall :
    cpsTripleWithin (1 + nH) (H + 36) (H + 40) fullCode
      ((.x1 ↦ᵣ ret) **
        (.x2 ↦ᵣ spC) **
          (.x8 ↦ᵣ parentPtr) **
            (.x9 ↦ᵣ parentLen) **
              (.x18 ↦ᵣ vals .x18) **
                (.x10 ↦ᵣ thisPtr) **
                  (.x11 ↦ᵣ thisLen) **
                    (.x12 ↦ᵣ Claimed) **
                      (.x13 ↦ᵣ parentLen) **
                        frameSlotsSaved hvphFrame spC (hvphFrameVals ret vals) **
                          claimedOwn claimedBytes **
                            bytesRegion thisPtr thisBytes **
                              bytesRegion parentPtr parentBytes **
                                regOwn .x5 **
                                  regOwn .x6 **
                                    regOwn .x7 **
                                      regOwn .x28 **
                                        regOwn .x29 **
                                          regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)))
      ((.x1 ↦ᵣ (H + 40)) **
        (.x10 ↦ᵣ statusHdr) **
          claimedOwn claimedOut **
            bytesRegion thisPtr thisBytes **
              regOwn .x11 **
                regOwn .x12 ** headersCallFrame spC ret parentPtr parentLen vals parentBytes) :=
    cpsTripleWithin_weaken
      (fun _ hp => by
        unfold headersCallPrest headersCallFrame claimedOwn
        xperm_hyp hp)
      (fun _ hq => hq) hcall0
  have h01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hproF hcall
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => hq) h01


-- @@ L728-737 verbatim
/-- `headersCallFrame` without the `x0` atom (for framing around `beq`). -/
def headersCallFrameCore
    (spC ret parentPtr parentLen : Word) (vals : Reg → Word)
    (parentBytes : List (BitVec 8)) : Assertion :=
  (.x2 ↦ᵣ spC) ** (.x8 ↦ᵣ parentPtr) ** (.x9 ↦ᵣ parentLen) **
  (.x18 ↦ᵣ vals .x18) ** (.x13 ↦ᵣ parentLen) **
  frameSlotsSaved hvphFrame spC (hvphFrameVals ret vals) **
  bytesRegion parentPtr parentBytes **
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
  regOwn .x29 ** regOwn .x30 ** regOwn .x31


-- @@ L739-762 expanded
set_option maxRecDepth 8000 in
/-- Post-headers `beq` fall-through, framed by call-frame core (no double-`x0`). -/
theorem hvphBeqExtractFailFramed (spC ret parentPtr parentLen statusHdr : Word) (vals : Reg → Word)
    (thisPtr : Word) (thisBytes claimedOut parentBytes : List (BitVec 8))
    (h_nz : statusHdr ≠ (0 : Word)) :
    cpsTripleWithin 1 (H + 40) (H + 44) fullCode
      ((.x1 ↦ᵣ (H + 40)) **
        (.x10 ↦ᵣ statusHdr) **
          (.x0 ↦ᵣ (0 : Word)) **
            claimedOwn claimedOut **
              bytesRegion thisPtr thisBytes **
                regOwn .x11 **
                  regOwn .x12 ** headersCallFrameCore spC ret parentPtr parentLen vals parentBytes)
      ((.x1 ↦ᵣ (H + 40)) **
        (.x10 ↦ᵣ statusHdr) **
          (.x0 ↦ᵣ (0 : Word)) **
            claimedOwn claimedOut **
              bytesRegion thisPtr thisBytes **
                regOwn .x11 **
                  regOwn .x12 **
                    headersCallFrameCore spC ret parentPtr parentLen vals parentBytes) :=
  by
  have hbeq0 := hvphBeqExtractFail statusHdr h_nz
  have hbeq := cpsTripleWithin_extend_code hvph_mono hbeq0
  have hbeqF :=
    cpsTripleWithin_frameR
      ((.x1 ↦ᵣ (H + 40)) **
        claimedOwn claimedOut **
          bytesRegion thisPtr thisBytes **
            regOwn .x11 **
              regOwn .x12 ** headersCallFrameCore spC ret parentPtr parentLen vals parentBytes)
      (by unfold headersCallFrameCore claimedOwn;
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
      hbeq
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => by xperm_hyp hq) hbeqF


-- @@ L764-773 verbatim
/-- Ambient for status-1 exit on the extract-fail path. -/
def hvphFailG
    (thisPtr : Word) (thisBytes claimedOut : List (BitVec 8)) (parentLen : Word) :
    Assertion :=
  claimedOwn claimedOut ** bytesRegion thisPtr thisBytes **
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
  regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
  regOwn .x11 ** regOwn .x12 **
  (.x0 ↦ᵣ (0 : Word)) **
  (.x13 ↦ᵣ parentLen)


-- @@ L775-778 expanded
theorem hvphFailG_pcFree (thisPtr : Word) (thisBytes claimedOut : List (BitVec 8))
    (parentLen : Word) : (hvphFailG thisPtr thisBytes claimedOut parentLen).pcFree := by
  unfold hvphFailG claimedOwn;
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


-- @@ L780-802 expanded
set_option maxRecDepth 8000 in
/-- Post-headers `beq` taken (status 0), framed by call-frame core. -/
theorem hvphBeqExtractOkFramed (spC ret parentPtr parentLen : Word) (vals : Reg → Word)
    (thisPtr : Word) (thisBytes claimedOut parentBytes : List (BitVec 8)) (G : Assertion)
    (hG : G.pcFree) :
    cpsTripleWithin 1 (H + 40) (H + 52) fullCode
      ((.x1 ↦ᵣ (H + 40)) **
        (.x10 ↦ᵣ (0 : Word)) **
          (.x0 ↦ᵣ (0 : Word)) **
            claimedOwn claimedOut **
              bytesRegion thisPtr thisBytes **
                headersCallFrameCore spC ret parentPtr parentLen vals parentBytes ** G)
      ((.x1 ↦ᵣ (H + 40)) **
        (.x10 ↦ᵣ (0 : Word)) **
          (.x0 ↦ᵣ (0 : Word)) **
            claimedOwn claimedOut **
              bytesRegion thisPtr thisBytes **
                headersCallFrameCore spC ret parentPtr parentLen vals parentBytes ** G) :=
  by
  have hbeq0 := hvphBeqExtractOk
  have hbeq := cpsTripleWithin_extend_code hvph_mono hbeq0
  have hbeqF :=
    cpsTripleWithin_frameR
      ((.x1 ↦ᵣ (H + 40)) **
        claimedOwn claimedOut **
          bytesRegion thisPtr thisBytes **
            headersCallFrameCore spC ret parentPtr parentLen vals parentBytes ** G)
      (by unfold headersCallFrameCore claimedOwn;
        refine pcFree_sepConj ?_ (pcFree_sepConj ?_ (pcFree_sepConj ?_ (pcFree_sepConj ?_ hG))) <;>
          first
          | exact bytesRegion_pcFree _ _
          |
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
      hbeq
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => by xperm_hyp hq) hbeqF


-- @@ L804-804 verbatim
end EvmAsm.Codegen.HeaderValidateParentHashSpec
