/-
  MptWalkWlEnabledHit — enable=1 **hit** residual discharge at the three walk
  sites (#12036).

  The hit residual `wlCallWithinShapeHitEn` is the ambient of
  `wlhCallWithin_enabled_one_hit` (fuel 1+402, `stackFree sp0 16`). This module
  establishes it under walk `fullCode` at all three `jal
  witness_lookup_by_hash` sites — root pc 35, branch pc 101, ext pc 210 —
  exactly as `MptWalkWlEnabledEmpty` does for the empty-miss residual
  `wlCallWithinShapeEn` (#12183).

  ## Domain (SAY SO) — `widx_count = 1`

  `widx_enabled = 1`, registered section pointer AND length matched to
  `a0`/`a1` (both free), `widx_count = 1`, the sole `widx_records` record's
  hash equal to the target. This is the sole-record hit domain of
  `witness_lookup_by_hash_spec_within_enabled_one_hit`. STILL OPEN and NOT
  claimed here: arbitrary `widx_count` (the real binary search) and the linear
  scan with `zkvm_keccak256`.

  ## What this does NOT retire

  ⚠️ `MptWalkResidualChain.wlCallWithinShapeHit` — the free `h_wl` on
  `root/branch/ext_wl_hit_chain` — is a DIFFERENT residual and stays open. Its
  ambient is the enable=0 walk shape: `wlCallEntry`/`wlHitReturn` carry
  `stackFree sp0 8` and only the six-cell `wlTelemetry`, with no
  `widx_section_ptr`/`widx_section_len`/`widx_count`/`wlh_indexed_*` cells and
  no `widx_records` byte region. No enable=1 hit triple can produce that shape,
  because the routine's indexed arm reads and writes precisely the cells it
  omits and carves a second frame the `stackFree sp0 8` does not cover.
  Converting the hop-glue chain onto `wlCallWithinShapeHitEn` is separate work.
-/
import EvmAsm.Codegen.Programs.MptWalkMachine
import EvmAsm.Codegen.Programs.MptWalkResiduals
import EvmAsm.Codegen.Programs.WitnessLookupByHashEnabledOneHitWrap
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Rv64.Tactics.XPermChunked


-- @@ L39-39 verbatim
namespace EvmAsm.Codegen.MptWalkSpec


-- @@ L41-41 verbatim
open EvmAsm.Codegen

-- @@ L42-42 verbatim
open EvmAsm.Codegen.WitnessLookupByHashSpec

-- @@ L43-43 verbatim
open EvmAsm.Codegen.WitnessLookupByHashIndexedSpec (WidxRecordsBase)

-- @@ L44-44 verbatim
open EvmAsm.Rv64

-- @@ L45-45 verbatim
open EvmAsm.Rv64.SAsm


-- @@ L47-47 verbatim
set_option maxRecDepth 8000


-- @@ L49-53 verbatim
private theorem root_hit_jal_target :
    pc 35 + signExtend21
      (jalOff GuestAddrs.witness_lookup_by_hash (GuestAddrs.mpt_walk + 140)) =
      WlB := by
  unfold pc walkB WlB; decide


-- @@ L55-59 verbatim
private theorem branch_hit_jal_target :
    pc 101 + signExtend21
      (jalOff GuestAddrs.witness_lookup_by_hash (GuestAddrs.mpt_walk + 404)) =
      WlB := by
  unfold pc walkB WlB; decide


-- @@ L61-65 verbatim
private theorem ext_hit_jal_target :
    pc 210 + signExtend21
      (jalOff GuestAddrs.witness_lookup_by_hash (GuestAddrs.mpt_walk + 840)) =
      WlB := by
  unfold pc walkB WlB; decide


-- @@ L67-100 verbatim
/-- Thin apply of `wlCallWithinShapeHitEn_of_callWithin` +
    `enableFull_in_walk_fullCode` at an arbitrary walk JAL site.

    `widx_count = 1` hit domain — SAY SO. -/
theorem wl_enabled_hit_establishes_shape_at
    (callPc : Word) (offset : BitVec 21)
    (vOld sp0 : Word) (vals : Reg → Word) (F : Assertion)
    (v5 v6 secPtr secLen hashPtr outOff outLen offOld lenOld : Word)
    (w7 w15 w16 w17 w28 w29 w30 w31 : Word)
    (nCalls nIdx nHit nMiss nLin nLast nMax nLinMiss : Word)
    (hF : F.pcFree)
    (hvals : vals .x1 = callPc + 4)
    (halign : ((callPc + 4) &&& ~~~(1 : Word)) = callPc + 4)
    (htarget : callPc + signExtend21 offset = WlB)
    (halignH : hashPtr.toNat % 8 = 0)
    (hovH : hashPtr.toNat + 32 < 2 ^ 64)
    (hvalidR : ∀ k, k < 32 →
      isValidByteAccess (WidxRecordsBase + BitVec.ofNat 64 k) = true)
    (hvalidH : ∀ k, k < 32 →
      isValidByteAccess (hashPtr + BitVec.ofNat 64 k) = true)
    (hmem : ∀ a i, CodeReq.singleton callPc (.JAL .x1 offset) a = some i →
      fullCode a = some i) :
    wlCallWithinShapeHitEn fullCode callPc vOld sp0 vals
      v5 v6 secPtr secLen hashPtr outOff outLen offOld lenOld
      w7 w15 w16 w17 w28 w29 w30 w31
      nCalls nIdx nHit nMiss nLin nLast nMax nLinMiss offset F := by
  refine wlCallWithinShapeHitEn_of_callWithin fullCode callPc vOld sp0 offset
    vals F v5 v6 secPtr secLen hashPtr outOff outLen offOld lenOld
    w7 w15 w16 w17 w28 w29 w30 w31
    nCalls nIdx nHit nMiss nLin nLast nMax nLinMiss
    hF hvals (by simpa using halign) htarget halignH hovH hvalidR hvalidH
    hmem ?hcode
  intro a i ha
  exact enableFull_in_walk_fullCode a i ha


-- @@ L102-131 verbatim
/-- Root site (pc 35). `widx_count = 1` hit domain — SAY SO. -/
theorem root_wl_enabled_hit_establishes_shape
    (vOld sp0 : Word) (vals : Reg → Word) (F : Assertion)
    (v5 v6 secPtr secLen hashPtr outOff outLen offOld lenOld : Word)
    (w7 w15 w16 w17 w28 w29 w30 w31 : Word)
    (nCalls nIdx nHit nMiss nLin nLast nMax nLinMiss : Word)
    (hF : F.pcFree)
    (hvals : vals .x1 = pc 35 + 4)
    (halign : ((pc 35 + 4) &&& ~~~(1 : Word)) = pc 35 + 4)
    (halignH : hashPtr.toNat % 8 = 0)
    (hovH : hashPtr.toNat + 32 < 2 ^ 64)
    (hvalidR : ∀ k, k < 32 →
      isValidByteAccess (WidxRecordsBase + BitVec.ofNat 64 k) = true)
    (hvalidH : ∀ k, k < 32 →
      isValidByteAccess (hashPtr + BitVec.ofNat 64 k) = true) :
    wlCallWithinShapeHitEn fullCode (pc 35) vOld sp0 vals
      v5 v6 secPtr secLen hashPtr outOff outLen offOld lenOld
      w7 w15 w16 w17 w28 w29 w30 w31
      nCalls nIdx nHit nMiss nLin nLast nMax nLinMiss
      (jalOff GuestAddrs.witness_lookup_by_hash (GuestAddrs.mpt_walk + 140)) F := by
  refine wl_enabled_hit_establishes_shape_at (pc 35)
    (jalOff GuestAddrs.witness_lookup_by_hash (GuestAddrs.mpt_walk + 140))
    vOld sp0 vals F v5 v6 secPtr secLen hashPtr outOff outLen offOld lenOld
    w7 w15 w16 w17 w28 w29 w30 w31
    nCalls nIdx nHit nMiss nLin nLast nMax nLinMiss hF hvals
    (by simpa using halign) root_hit_jal_target halignH hovH hvalidR hvalidH ?hm
  intro a i ha
  exact walkMem (pc 35) 35
    (.JAL .x1 (jalOff GuestAddrs.witness_lookup_by_hash (GuestAddrs.mpt_walk + 140)))
    (by decide) (by unfold pc walkB; decide) (by decide) a i ha


-- @@ L133-162 verbatim
/-- Branch site (pc 101). `widx_count = 1` hit domain — SAY SO. -/
theorem branch_wl_enabled_hit_establishes_shape
    (vOld sp0 : Word) (vals : Reg → Word) (F : Assertion)
    (v5 v6 secPtr secLen hashPtr outOff outLen offOld lenOld : Word)
    (w7 w15 w16 w17 w28 w29 w30 w31 : Word)
    (nCalls nIdx nHit nMiss nLin nLast nMax nLinMiss : Word)
    (hF : F.pcFree)
    (hvals : vals .x1 = pc 101 + 4)
    (halign : ((pc 101 + 4) &&& ~~~(1 : Word)) = pc 101 + 4)
    (halignH : hashPtr.toNat % 8 = 0)
    (hovH : hashPtr.toNat + 32 < 2 ^ 64)
    (hvalidR : ∀ k, k < 32 →
      isValidByteAccess (WidxRecordsBase + BitVec.ofNat 64 k) = true)
    (hvalidH : ∀ k, k < 32 →
      isValidByteAccess (hashPtr + BitVec.ofNat 64 k) = true) :
    wlCallWithinShapeHitEn fullCode (pc 101) vOld sp0 vals
      v5 v6 secPtr secLen hashPtr outOff outLen offOld lenOld
      w7 w15 w16 w17 w28 w29 w30 w31
      nCalls nIdx nHit nMiss nLin nLast nMax nLinMiss
      (jalOff GuestAddrs.witness_lookup_by_hash (GuestAddrs.mpt_walk + 404)) F := by
  refine wl_enabled_hit_establishes_shape_at (pc 101)
    (jalOff GuestAddrs.witness_lookup_by_hash (GuestAddrs.mpt_walk + 404))
    vOld sp0 vals F v5 v6 secPtr secLen hashPtr outOff outLen offOld lenOld
    w7 w15 w16 w17 w28 w29 w30 w31
    nCalls nIdx nHit nMiss nLin nLast nMax nLinMiss hF hvals
    (by simpa using halign) branch_hit_jal_target halignH hovH hvalidR hvalidH ?hm
  intro a i ha
  exact walkMem (pc 101) 101
    (.JAL .x1 (jalOff GuestAddrs.witness_lookup_by_hash (GuestAddrs.mpt_walk + 404)))
    (by decide) (by unfold pc walkB; decide) (by decide) a i ha


-- @@ L164-193 verbatim
/-- Extension site (pc 210). `widx_count = 1` hit domain — SAY SO. -/
theorem ext_wl_enabled_hit_establishes_shape
    (vOld sp0 : Word) (vals : Reg → Word) (F : Assertion)
    (v5 v6 secPtr secLen hashPtr outOff outLen offOld lenOld : Word)
    (w7 w15 w16 w17 w28 w29 w30 w31 : Word)
    (nCalls nIdx nHit nMiss nLin nLast nMax nLinMiss : Word)
    (hF : F.pcFree)
    (hvals : vals .x1 = pc 210 + 4)
    (halign : ((pc 210 + 4) &&& ~~~(1 : Word)) = pc 210 + 4)
    (halignH : hashPtr.toNat % 8 = 0)
    (hovH : hashPtr.toNat + 32 < 2 ^ 64)
    (hvalidR : ∀ k, k < 32 →
      isValidByteAccess (WidxRecordsBase + BitVec.ofNat 64 k) = true)
    (hvalidH : ∀ k, k < 32 →
      isValidByteAccess (hashPtr + BitVec.ofNat 64 k) = true) :
    wlCallWithinShapeHitEn fullCode (pc 210) vOld sp0 vals
      v5 v6 secPtr secLen hashPtr outOff outLen offOld lenOld
      w7 w15 w16 w17 w28 w29 w30 w31
      nCalls nIdx nHit nMiss nLin nLast nMax nLinMiss
      (jalOff GuestAddrs.witness_lookup_by_hash (GuestAddrs.mpt_walk + 840)) F := by
  refine wl_enabled_hit_establishes_shape_at (pc 210)
    (jalOff GuestAddrs.witness_lookup_by_hash (GuestAddrs.mpt_walk + 840))
    vOld sp0 vals F v5 v6 secPtr secLen hashPtr outOff outLen offOld lenOld
    w7 w15 w16 w17 w28 w29 w30 w31
    nCalls nIdx nHit nMiss nLin nLast nMax nLinMiss hF hvals
    (by simpa using halign) ext_hit_jal_target halignH hovH hvalidR hvalidH ?hm
  intro a i ha
  exact walkMem (pc 210) 210
    (.JAL .x1 (jalOff GuestAddrs.witness_lookup_by_hash (GuestAddrs.mpt_walk + 840)))
    (by decide) (by unfold pc walkB; decide) (by decide) a i ha


-- @@ L195-209 verbatim
/-! ## Non-vacuity of the discharged bundle

    Three parts, per the repo's anti-vacuity rule:

    * **satisfiable** — `root_wl_enabled_hit_shape_sat`, a fully closed
      instance of the residual at the root site, every hypothesis of the site
      lemma discharged at concrete values;
    * **negative control** — `root_wl_enabled_hit_shape_wrong_offset_false`,
      an instantiation at which the bundle is provably FALSE, so the shape is
      not something any argument list satisfies;
    * **a model of the precondition** — `MptWalkWlEnabledHitSat`
      (`hit_site_entryState_exists`): a concrete `MachineState` satisfying the
      residual's pre, so the `cpsTripleWithin` inside it is not vacuously true.
      That is the gap #12690 left open on the parent side.
-/


-- @@ L211-228 verbatim
/-- Every byte of a 32-byte buffer that starts inside RAM and ends before
    `RAM_MEM_END` is byte-accessible. -/
private theorem ram32_bytes_valid (base : Word)
    (hlo : EvmAsm.Rv64.RAM_MEM_START ≤ base.toNat)
    (hhi : base.toNat + 32 ≤ EvmAsm.Rv64.RAM_MEM_END) :
    ∀ k, k < 32 → isValidByteAccess (base + BitVec.ofNat 64 k) = true := by
  intro k hk
  unfold EvmAsm.Rv64.RAM_MEM_START at hlo
  unfold EvmAsm.Rv64.RAM_MEM_END at hhi
  have hk64 : k < 2 ^ 64 := Nat.lt_trans hk (by decide)
  have hsum : (base + BitVec.ofNat 64 k).toNat = base.toNat + k := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk64,
      Nat.mod_eq_of_lt (by omega)]
  simp only [isValidByteAccess, isValidMemAddr, Bool.or_eq_true, Bool.and_eq_true,
    decide_eq_true_eq]
  refine Or.inr ⟨?_, ?_⟩
  · rw [hsum]; unfold EvmAsm.Rv64.RAM_MEM_START; omega
  · rw [hsum]; unfold EvmAsm.Rv64.RAM_MEM_END; omega


-- @@ L230-237 verbatim
private theorem widxRecords_bytes_valid :
    ∀ k, k < 32 →
      isValidByteAccess (WidxRecordsBase + BitVec.ofNat 64 k) = true :=
  ram32_bytes_valid WidxRecordsBase
    (by unfold EvmAsm.Rv64.RAM_MEM_START WidxRecordsBase GuestAddrs.widx_records
        decide)
    (by unfold EvmAsm.Rv64.RAM_MEM_END WidxRecordsBase GuestAddrs.widx_records
        decide)


-- @@ L239-246 verbatim
private theorem mwLookupHash_bytes_valid :
    ∀ k, k < 32 →
      isValidByteAccess (MwLookupHash + BitVec.ofNat 64 k) = true :=
  ram32_bytes_valid MwLookupHash
    (by unfold EvmAsm.Rv64.RAM_MEM_START MwLookupHash GuestAddrs.mw_lookup_hash
        decide)
    (by unfold EvmAsm.Rv64.RAM_MEM_END MwLookupHash GuestAddrs.mw_lookup_hash
        decide)


-- @@ L248-272 verbatim
/-- ⭐ **Satisfiable**: a closed instance of the hit residual at the root site.
    Hash buffer is the walk's own `mw_lookup_hash` cell, return address is the
    site's `pc 35 + 4`, ambient `F` is `emp`; every hypothesis of
    `root_wl_enabled_hit_establishes_shape` is discharged here, so the bundle
    is inhabited on the domain the three discharges range over. -/
theorem root_wl_enabled_hit_shape_sat
    (vOld sp0 : Word)
    (v5 v6 secPtr secLen outOff outLen offOld lenOld : Word)
    (w7 w15 w16 w17 w28 w29 w30 w31 : Word)
    (nCalls nIdx nHit nMiss nLin nLast nMax nLinMiss : Word) :
    wlCallWithinShapeHitEn fullCode (pc 35) vOld sp0
      (fun _ => pc 35 + 4)
      v5 v6 secPtr secLen MwLookupHash outOff outLen offOld lenOld
      w7 w15 w16 w17 w28 w29 w30 w31
      nCalls nIdx nHit nMiss nLin nLast nMax nLinMiss
      (jalOff GuestAddrs.witness_lookup_by_hash (GuestAddrs.mpt_walk + 140))
      empAssertion :=
  root_wl_enabled_hit_establishes_shape vOld sp0 (fun _ => pc 35 + 4)
    empAssertion v5 v6 secPtr secLen MwLookupHash outOff outLen offOld lenOld
    w7 w15 w16 w17 w28 w29 w30 w31
    nCalls nIdx nHit nMiss nLin nLast nMax nLinMiss
    pcFree_emp rfl (by unfold pc walkB; decide)
    (by unfold MwLookupHash GuestAddrs.mw_lookup_hash; decide)
    (by unfold MwLookupHash GuestAddrs.mw_lookup_hash; decide)
    widxRecords_bytes_valid mwLookupHash_bytes_valid


-- @@ L274-294 verbatim
/-- ⛔ **Negative control**: the same shape at the root site with the BRANCH
    site's jump offset is provably false — its target conjunct then reads
    `pc 35 + off(pc 101) = wlhB`, which is false. So
    `wlCallWithinShapeHitEn` is not a proposition every argument list
    satisfies: the three discharges above are claims about their own sites. -/
theorem root_wl_enabled_hit_shape_wrong_offset_false
    (vOld sp0 : Word) (vals : Reg → Word) (F : Assertion)
    (v5 v6 secPtr secLen hashPtr outOff outLen offOld lenOld : Word)
    (w7 w15 w16 w17 w28 w29 w30 w31 : Word)
    (nCalls nIdx nHit nMiss nLin nLast nMax nLinMiss : Word) :
    ¬ wlCallWithinShapeHitEn fullCode (pc 35) vOld sp0 vals
        v5 v6 secPtr secLen hashPtr outOff outLen offOld lenOld
        w7 w15 w16 w17 w28 w29 w30 w31
        nCalls nIdx nHit nMiss nLin nLast nMax nLinMiss
        (jalOff GuestAddrs.witness_lookup_by_hash (GuestAddrs.mpt_walk + 404))
        F := by
  intro h
  obtain ⟨-, -, -, htgt, -⟩ := h
  revert htgt
  unfold pc walkB wlhB
  decide


-- @@ L296-296 verbatim
end EvmAsm.Codegen.MptWalkSpec
