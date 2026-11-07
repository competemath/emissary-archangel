/-
  EvmAsm.Rv64.SAsm.GlobalDataDemo

  End-to-end demo of the global-data footprint model (bead evm-asm-85699),
  mirroring the AbiFrame demos: a synthetic leaf routine that

  ```
    la  t0, CONST      -- auipc x5, %pcrel_hi ; addi x5, x5, %pcrel_lo
    ld  t1, 0(t0)      -- read the read-only constant
    la  t2, CELL       -- auipc x7, %pcrel_hi ; addi x7, x7, %pcrel_lo
    sd  t1, 0(t2)      -- write it into the RW scratch cell
    ret
  ```

  with code at `0x80001000`, the constant global at `0x80040000`, and the
  RW cell at `0x80040008`.  The `%pcrel_hi`/`%pcrel_lo` immediates are
  COMPUTED by `laHi`/`laLo` and `#guard`-tied to the hand-written literal
  program (hi 63, lo 0 and hi 63, lo −4) — the emitter formula reproduces the exact
  bytes.  `gdDemo_spec` proves the genuine post: `t1` observed the
  constant, the constant global is unchanged, and the RW cell now holds
  it.  Addresses are materialized by `la_materialize_within` — proven, not
  assumed.
-/

import EvmAsm.Rv64.SAsm.GlobalData
import EvmAsm.Rv64.SAsm.FramePort
import EvmAsm.Evm64.CallingConvention


-- @@ L29-29 verbatim
namespace EvmAsm.Rv64.SAsm


-- @@ L31-31 verbatim
open EvmAsm.Rv64


-- @@ L33-33 verbatim
namespace GlobalDataDemo


-- @@ L35-36 verbatim
/-- Code base, constant global, RW scratch cell (synthetic layout). -/
def demoBase : Word := 0x80001000

-- @@ L37-37 verbatim
def demoConstAddr : Word := 0x80040000

-- @@ L38-38 verbatim
def demoCellAddr : Word := 0x80040008


-- @@ L40-48 verbatim
/-- The demo routine, immediates computed by the `la` resolution model. -/
def gdDemo_prog : Program :=
  [ .AUIPC .x5 (laHi demoBase demoConstAddr),
    .ADDI .x5 .x5 (laLo demoBase demoConstAddr),
    .LD .x6 .x5 (0 : BitVec 12),
    .AUIPC .x7 (laHi (demoBase + 12) demoCellAddr),
    .ADDI .x7 .x7 (laLo (demoBase + 12) demoCellAddr),
    .SD .x7 .x6 (0 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]


-- @@ L50-59 verbatim
/-- Byte identity (kernel-checked): the computed `%pcrel_hi`/`%pcrel_lo`
    immediates ARE the hand-written literals an assembler would emit. -/
theorem gdDemo_prog_eq : gdDemo_prog =
    [ .AUIPC .x5 (63 : BitVec 20), .ADDI .x5 .x5 (0 : BitVec 12),
      .LD .x6 .x5 (0 : BitVec 12),
      .AUIPC .x7 (63 : BitVec 20), .ADDI .x7 .x7 (-4 : BitVec 12),
      .SD .x7 .x6 (0 : BitVec 12),
      .JALR .x0 .x1 (0 : BitVec 12) ] := rfl

-- Both `la` displacements are representable.

-- @@ L60-60 verbatim
#guard decide (laInRange demoBase demoConstAddr)

-- @@ L61-61 verbatim
#guard decide (laInRange (demoBase + 12) demoCellAddr)


-- @@ L63-123 expanded
/-- **The demo spec** (genuine post): after the routine, `t1` holds the
    constant `K`, the read-only global still holds `K`, and the RW scratch
    cell has been UPDATED from `old` to `K`.  Both global addresses were
    materialized by the proven `la` model. -/
theorem gdDemo_spec (K old ret v5 v6 v7 : Word) (halign : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin 7 demoBase ret (CodeReq.ofProg demoBase gdDemo_prog)
      ((.x5 ↦ᵣ v5) **
        (.x6 ↦ᵣ v6) **
          (.x7 ↦ᵣ v7) **
            ((.x1 : Reg) ↦ᵣ ret) ** globalCellIs demoConstAddr K ** globalCellIs demoCellAddr old)
      ((.x5 ↦ᵣ demoConstAddr) **
        (.x6 ↦ᵣ K) **
          (.x7 ↦ᵣ demoCellAddr) **
            ((.x1 : Reg) ↦ᵣ ret) ** globalCellIs demoConstAddr K ** globalCellIs demoCellAddr K) :=
  by
  unfold globalCellIs
  have hla1 :=
    la_materialize_within .x5 v5 demoBase demoConstAddr (cr := CodeReq.ofProg demoBase gdDemo_prog)
      (by decide) (by decide)
      (by
        first
        | (with_reducible exact fun a i h => h)
        | ((with_reducible refine CodeReq.singleton_mono ?_); decide)
        | ((with_reducible refine CodeReq.sub_ofProg_of_lookup _ _ ?_ ?_) <;> decide))
      (by
        first
        | (with_reducible exact fun a i h => h)
        | ((with_reducible refine CodeReq.singleton_mono ?_); decide)
        | ((with_reducible refine CodeReq.sub_ofProg_of_lookup _ _ ?_ ?_) <;> decide))
        -- ld t1, 0(t0)
        
  have hld :=
    liftCode (cr' := CodeReq.ofProg demoBase gdDemo_prog)
      (ld_spec_within .x6 .x5 demoConstAddr v6 K (0 : BitVec 12) (demoBase + 8) (by decide))
      (by
        first
        | (with_reducible exact fun a i h => h)
        | ((with_reducible refine CodeReq.singleton_mono ?_); decide)
        | ((with_reducible refine CodeReq.sub_ofProg_of_lookup _ _ ?_ ?_) <;> decide))
  rw [show demoConstAddr + signExtend12 (0 : BitVec 12) = demoConstAddr from by decide,
    show (demoBase + 8 : Word) + 4 = demoBase + 12 from by decide] at hld
  have hla2 :=
    la_materialize_within .x7 v7 (demoBase + 12) demoCellAddr (cr :=
      CodeReq.ofProg demoBase gdDemo_prog) (by decide) (by decide)
      (by
        first
        | (with_reducible exact fun a i h => h)
        | ((with_reducible refine CodeReq.singleton_mono ?_); decide)
        | ((with_reducible refine CodeReq.sub_ofProg_of_lookup _ _ ?_ ?_) <;> decide))
      (by
        first
        | (with_reducible exact fun a i h => h)
        | ((with_reducible refine CodeReq.singleton_mono ?_); decide)
        | ((with_reducible refine CodeReq.sub_ofProg_of_lookup _ _ ?_ ?_) <;> decide))
  rw [show (demoBase + 12 : Word) + 8 = demoBase + 20 from by decide] at hla2
  have hsd :=
    liftCode (cr' := CodeReq.ofProg demoBase gdDemo_prog)
      (sd_spec_within .x7 .x6 demoCellAddr K old (0 : BitVec 12) (demoBase + 20))
      (by
        first
        | (with_reducible exact fun a i h => h)
        | ((with_reducible refine CodeReq.singleton_mono ?_); decide)
        | ((with_reducible refine CodeReq.sub_ofProg_of_lookup _ _ ?_ ?_) <;> decide))
  rw [show demoCellAddr + signExtend12 (0 : BitVec 12) = demoCellAddr from by decide,
    show (demoBase + 20 : Word) + 4 = demoBase + 24 from by decide] at hsd
  have hret :=
    liftCode (cr' := CodeReq.ofProg demoBase gdDemo_prog)
      (EvmAsm.Evm64.ret_spec_within' (demoBase + 24) ret)
      (by
        first
        | (with_reducible exact fun a i h => h)
        | ((with_reducible refine CodeReq.singleton_mono ?_); decide)
        | ((with_reducible refine CodeReq.sub_ofProg_of_lookup _ _ ?_ ?_) <;> decide))
  rw [halign] at hret
  have hla1F :=
    cpsTripleWithin_frameR
      ((.x6 ↦ᵣ v6) **
        (.x7 ↦ᵣ v7) ** ((.x1 : Reg) ↦ᵣ ret) ** (demoConstAddr ↦ₘ K) ** (demoCellAddr ↦ₘ old))
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
      hla1
  have hldF :=
    cpsTripleWithin_frameR ((.x7 ↦ᵣ v7) ** ((.x1 : Reg) ↦ᵣ ret) ** (demoCellAddr ↦ₘ old))
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
  have hla2F :=
    cpsTripleWithin_frameR
      ((.x5 ↦ᵣ demoConstAddr) **
        (.x6 ↦ᵣ K) ** ((.x1 : Reg) ↦ᵣ ret) ** (demoConstAddr ↦ₘ K) ** (demoCellAddr ↦ₘ old))
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
      hla2
  have hsdF :=
    cpsTripleWithin_frameR ((.x5 ↦ᵣ demoConstAddr) ** ((.x1 : Reg) ↦ᵣ ret) ** (demoConstAddr ↦ₘ K))
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
  have hretF :=
    cpsTripleWithin_frameR
      ((.x5 ↦ᵣ demoConstAddr) **
        (.x6 ↦ᵣ K) ** (.x7 ↦ᵣ demoCellAddr) ** (demoConstAddr ↦ₘ K) ** (demoCellAddr ↦ₘ K))
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
  have c1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hla1F hldF
  have c2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c1 hla2F
  have c3 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c2 hsdF
  have c4 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c3 hretF
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => by xperm_hyp hq) c4


-- @@ L126-126 verbatim
end GlobalDataDemo


-- @@ L128-128 verbatim
end EvmAsm.Rv64.SAsm
