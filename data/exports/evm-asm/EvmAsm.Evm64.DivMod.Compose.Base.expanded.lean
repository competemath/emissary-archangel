/-
  EvmAsm.Evm64.DivMod.Compose.Base

  Shared infrastructure for DivMod composition: divCode/modCode definitions,
  program length lemmas, and the skipBlock tactic macro.
-/

module

public import EvmAsm.Rv64.AddrNorm
public import EvmAsm.Rv64.Tactics.XPerm
public import EvmAsm.Evm64.DivMod.Compose.Offsets
meta import EvmAsm.Rv64.AddrNorm
meta import EvmAsm.Rv64.Tactics.XPerm
meta import EvmAsm.Evm64.DivMod.Compose.Offsets


-- @@ L17-17 verbatim
@[expose] public section


-- @@ L19-19 verbatim
open EvmAsm.Rv64.Tactics


-- @@ L21-21 verbatim
namespace EvmAsm.Evm64


-- @@ L23-28 verbatim
open EvmAsm.Rv64

-- ============================================================================
-- Program length lemmas (via decide)
-- Non-private so they are accessible from sub-files via skipBlock macro.
-- ============================================================================


-- @@ L30-30 verbatim
theorem divK_phaseA_len : (divK_phaseA 1020).length = 8 := by decide

-- @@ L31-31 verbatim
theorem divK_phaseB_len : divK_phaseB.length = 21 := by decide

-- @@ L32-32 verbatim
theorem divK_clz_len : divK_clz.length = 24 := by decide

-- @@ L33-33 verbatim
theorem divK_phaseC2_len : (divK_phaseC2 172).length = 4 := by decide

-- @@ L34-34 verbatim
theorem divK_normB_len : divK_normB.length = 21 := by decide

-- @@ L35-35 verbatim
theorem divK_normA_len : (divK_normA 40).length = 21 := by decide

-- @@ L36-36 verbatim
theorem divK_copyAU_len : divK_copyAU.length = 9 := by decide

-- @@ L37-37 verbatim
theorem divK_loopSetup_len : (divK_loopSetup 464).length = 4 := by decide

-- @@ L38-38 verbatim
theorem divK_loopBody_len : (divK_loopBody 560 7736).length = 115 := by decide

-- @@ L39-39 verbatim
theorem divK_denorm_len : divK_denorm.length = 25 := by decide

-- @@ L40-40 verbatim
theorem divK_divEpilogue_len : (divK_div_epilogue 24).length = 10 := by decide

-- @@ L41-41 verbatim
theorem divK_zeroPath_len : divK_zeroPath.length = 5 := by decide

-- @@ L42-42 verbatim
theorem divK_nop_len : (ADDI .x0 .x0 0 : Program).length = 1 := by decide

-- @@ L43-43 verbatim
theorem divK_div128_len : divK_div128.length = 51 := by decide

-- @@ L44-44 verbatim
theorem divK_div128_v2_len : divK_div128_v2.length = 61 := by decide

-- @@ L45-45 verbatim
theorem divK_div128_v4_len : divK_div128_v4.length = 75 := by decide

-- @@ L46-46 verbatim
theorem divK_div128_v5_len : divK_div128_v5.length = 85 := by decide

-- @@ L47-47 verbatim
theorem divK_modEpilogue_len : (divK_mod_epilogue 24).length = 10 := by decide


-- @@ L49-63 verbatim
/-- Skip one ofProg block in a right-nested union via range disjointness.
    Closes the disjointness goal using block length lemmas + bv_omega. -/
macro "skipBlock" : tactic =>
  `(tactic| apply CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range (fun k1 k2 hk1 hk2 => by
        simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
          divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len,
          divK_loopBody_len, divK_denorm_len, divK_divEpilogue_len,
          divK_zeroPath_len, divK_nop_len, divK_div128_len, divK_div128_v2_len,
          divK_div128_v4_len, divK_div128_v5_len, divK_modEpilogue_len] at hk1 hk2
        bv_omega)))

-- ============================================================================
-- Full program CodeReq definitions
-- ============================================================================


-- @@ L65-85 verbatim
/-- The full evm_div code split into 14 per-phase CodeReq.ofProg blocks.
    This is the canonical CodeReq for all composed specs.
    Block offsets are named constants defined in `Compose.Offsets` — see
    that file for the canonical layout and drift checks. -/
abbrev divCode (base : Word) : CodeReq :=
  CodeReq.unionAll [
    CodeReq.ofProg  base                  (divK_phaseA 1020),     -- block 0
    CodeReq.ofProg (base + phaseBOff)     divK_phaseB,            -- block 1
    CodeReq.ofProg (base + clzOff)        divK_clz,               -- block 2
    CodeReq.ofProg (base + phaseC2Off)    (divK_phaseC2 172),     -- block 3
    CodeReq.ofProg (base + normBOff)      divK_normB,             -- block 4
    CodeReq.ofProg (base + normAOff)      (divK_normA 40),        -- block 5
    CodeReq.ofProg (base + copyAUOff)     divK_copyAU,            -- block 6
    CodeReq.ofProg (base + loopSetupOff)  (divK_loopSetup 464),   -- block 7
    CodeReq.ofProg (base + loopBodyOff)   (divK_loopBody 560 7736),-- block 8
    CodeReq.ofProg (base + denormOff)     divK_denorm,            -- block 9
    CodeReq.ofProg (base + epilogueOff)   (divK_div_epilogue 24), -- block 10
    CodeReq.ofProg (base + zeroPathOff)   divK_zeroPath,          -- block 11
    CodeReq.ofProg (base + nopOff)        (ADDI .x0 .x0 0),       -- block 12
    CodeReq.ofProg (base + div128Off)     divK_div128             -- block 13
  ]


-- @@ L87-109 verbatim
/-- The full evm_mod code split into 14 per-phase CodeReq.ofProg blocks.
    Identical to divCode except block 10 uses divK_mod_epilogue. -/
abbrev modCode (base : Word) : CodeReq :=
  CodeReq.unionAll [
    CodeReq.ofProg  base                  (divK_phaseA 1020),
    CodeReq.ofProg (base + phaseBOff)     divK_phaseB,
    CodeReq.ofProg (base + clzOff)        divK_clz,
    CodeReq.ofProg (base + phaseC2Off)    (divK_phaseC2 172),
    CodeReq.ofProg (base + normBOff)      divK_normB,
    CodeReq.ofProg (base + normAOff)      (divK_normA 40),
    CodeReq.ofProg (base + copyAUOff)     divK_copyAU,
    CodeReq.ofProg (base + loopSetupOff)  (divK_loopSetup 464),
    CodeReq.ofProg (base + loopBodyOff)   (divK_loopBody 560 7736),
    CodeReq.ofProg (base + denormOff)     divK_denorm,
    CodeReq.ofProg (base + epilogueOff)   (divK_mod_epilogue 24), -- block 10 differs from divCode
    CodeReq.ofProg (base + zeroPathOff)   divK_zeroPath,
    CodeReq.ofProg (base + nopOff)        (ADDI .x0 .x0 0),
    CodeReq.ofProg (base + div128Off)     divK_div128
  ]

-- ============================================================================
-- Shared code: blocks common to divCode and modCode (all except epilogue)
-- ============================================================================


-- @@ L111-130 verbatim
/-- Shared code blocks between divCode and modCode (everything except block 10, the epilogue).
    Used as the code requirement for loop body and div128 specs, which are identical
    for DIV and MOD. -/
abbrev sharedDivModCode (base : Word) : CodeReq :=
  CodeReq.unionAll [
    CodeReq.ofProg  base                  (divK_phaseA 1020),     -- block 0
    CodeReq.ofProg (base + phaseBOff)     divK_phaseB,            -- block 1
    CodeReq.ofProg (base + clzOff)        divK_clz,               -- block 2
    CodeReq.ofProg (base + phaseC2Off)    (divK_phaseC2 172),     -- block 3
    CodeReq.ofProg (base + normBOff)      divK_normB,             -- block 4
    CodeReq.ofProg (base + normAOff)      (divK_normA 40),        -- block 5
    CodeReq.ofProg (base + copyAUOff)     divK_copyAU,            -- block 6
    CodeReq.ofProg (base + loopSetupOff)  (divK_loopSetup 464),   -- block 7
    CodeReq.ofProg (base + loopBodyOff)   (divK_loopBody 560 7736),-- block 8
    CodeReq.ofProg (base + denormOff)     divK_denorm,            -- block 9
    -- NO epilogue block (this is where divCode and modCode differ)
    CodeReq.ofProg (base + zeroPathOff)   divK_zeroPath,          -- block 10 (was 11)
    CodeReq.ofProg (base + nopOff)        (ADDI .x0 .x0 0),       -- block 11 (was 12)
    CodeReq.ofProg (base + div128Off)     divK_div128             -- block 12 (was 13)
  ]


-- @@ L132-157 verbatim
/-- v4 mirror of `sharedDivModCode` — uses `divK_div128_v4` (full
    Knuth Algorithm D with 2-correction in BOTH Phase 1b and Phase 2b)
    at block 12.

    Used as the code requirement for v4-migrated specs. NOTE: block 8
    (`divK_loopBody 560 7736`) retains the v1/v2 offset constants for
    now; once LoopBody migrates to v4 the JAL target offset will need
    re-tuning since v4's div128 is 14 instructions longer than v2.

    Issue #1337 algorithm fix migration / PR-B1 of v4 migration plan. -/
abbrev sharedDivModCode_v4 (base : Word) : CodeReq :=
  CodeReq.unionAll [
    CodeReq.ofProg  base                  (divK_phaseA 1020),     -- block 0
    CodeReq.ofProg (base + phaseBOff)     divK_phaseB,            -- block 1
    CodeReq.ofProg (base + clzOff)        divK_clz,               -- block 2
    CodeReq.ofProg (base + phaseC2Off)    (divK_phaseC2 172),     -- block 3
    CodeReq.ofProg (base + normBOff)      divK_normB,             -- block 4
    CodeReq.ofProg (base + normAOff)      (divK_normA 40),        -- block 5
    CodeReq.ofProg (base + copyAUOff)     divK_copyAU,            -- block 6
    CodeReq.ofProg (base + loopSetupOff)  (divK_loopSetup 464),   -- block 7
    CodeReq.ofProg (base + loopBodyOff)   (divK_loopBody 560 7736),-- block 8
    CodeReq.ofProg (base + denormOff)     divK_denorm,            -- block 9
    CodeReq.ofProg (base + zeroPathOff)   divK_zeroPath,          -- block 10
    CodeReq.ofProg (base + nopOff)        (ADDI .x0 .x0 0),       -- block 11
    CodeReq.ofProg (base + div128Off)     divK_div128_v4          -- block 12 (v4)
  ]


-- @@ L159-180 verbatim
/-- Shared DIV/MOD code bundle with the NOP return slot omitted.
    This is the shared-code analogue of `divCode_noNop` / `modCode_noNop`:
    it keeps all blocks common to DIV and MOD except the epilogue and the
    old NOP at `nopOff`. -/
abbrev sharedDivModCodeNoNop (base : Word) : CodeReq :=
  CodeReq.unionAll [
    CodeReq.ofProg  base                  (divK_phaseA 1020),
    CodeReq.ofProg (base + phaseBOff)     divK_phaseB,
    CodeReq.ofProg (base + clzOff)        divK_clz,
    CodeReq.ofProg (base + phaseC2Off)    (divK_phaseC2 172),
    CodeReq.ofProg (base + normBOff)      divK_normB,
    CodeReq.ofProg (base + normAOff)      (divK_normA 40),
    CodeReq.ofProg (base + copyAUOff)     divK_copyAU,
    CodeReq.ofProg (base + loopSetupOff)  (divK_loopSetup 464),
    CodeReq.ofProg (base + loopBodyOff)   (divK_loopBody 560 7736),
    CodeReq.ofProg (base + denormOff)     divK_denorm,
    CodeReq.ofProg (base + zeroPathOff)   divK_zeroPath,
    CodeReq.ofProg (base + div128Off)     divK_div128
  ]

-- Per-block subsumption: each shared block ⊆ divCode.
-- Blocks 0-9 are at the same union positions; blocks 10-12 (shared) = blocks 11-13 (divCode).

-- @@ L181-182 verbatim
private theorem shared_b0_div {b : Word} : ∀ a i, (CodeReq.ofProg b (divK_phaseA 1020)) a = some i → (divCode b) a = some i := by
  unfold divCode; simp only [CodeReq.unionAll_cons]; exact CodeReq.union_mono_left

-- @@ L183-184 expanded
private theorem shared_b1_div {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + phaseBOff) divK_phaseB) a = some i → (divCode b) a = some i := by
  unfold divCode; simp only [CodeReq.unionAll_cons];
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  exact CodeReq.union_mono_left


-- @@ L185-186 expanded
private theorem shared_b2_div {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + clzOff) divK_clz) a = some i → (divCode b) a = some i := by
  unfold divCode; simp only [CodeReq.unionAll_cons];
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  exact CodeReq.union_mono_left


-- @@ L187-188 expanded
private theorem shared_b3_div {b : Word} :
    ∀ a i,
      (CodeReq.ofProg (b + phaseC2Off) (divK_phaseC2 172)) a = some i → (divCode b) a = some i :=
  by unfold divCode; simp only [CodeReq.unionAll_cons];
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  exact CodeReq.union_mono_left


-- @@ L189-190 expanded
private theorem shared_b4_div {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + normBOff) divK_normB) a = some i → (divCode b) a = some i := by
  unfold divCode; simp only [CodeReq.unionAll_cons];
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  exact CodeReq.union_mono_left


-- @@ L191-192 expanded
private theorem shared_b5_div {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + normAOff) (divK_normA 40)) a = some i → (divCode b) a = some i := by
  unfold divCode; simp only [CodeReq.unionAll_cons];
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  exact CodeReq.union_mono_left


-- @@ L193-194 expanded
private theorem shared_b6_div {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + copyAUOff) divK_copyAU) a = some i → (divCode b) a = some i := by
  unfold divCode; simp only [CodeReq.unionAll_cons];
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  exact CodeReq.union_mono_left


-- @@ L195-196 expanded
private theorem shared_b7_div {b : Word} :
    ∀ a i,
      (CodeReq.ofProg (b + loopSetupOff) (divK_loopSetup 464)) a = some i →
        (divCode b) a = some i :=
  by unfold divCode; simp only [CodeReq.unionAll_cons];
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  exact CodeReq.union_mono_left


-- @@ L197-198 expanded
private theorem shared_b8_div {b : Word} :
    ∀ a i,
      (CodeReq.ofProg (b + loopBodyOff) (divK_loopBody 560 7736)) a = some i →
        (divCode b) a = some i :=
  by unfold divCode; simp only [CodeReq.unionAll_cons];
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  exact CodeReq.union_mono_left


-- @@ L199-200 expanded
private theorem shared_b9_div {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + denormOff) divK_denorm) a = some i → (divCode b) a = some i := by
  unfold divCode; simp only [CodeReq.unionAll_cons];
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  exact CodeReq.union_mono_left


-- @@ L201-202 expanded
private theorem shared_b10_div {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + zeroPathOff) divK_zeroPath) a = some i → (divCode b) a = some i :=
  by unfold divCode; simp only [CodeReq.unionAll_cons];
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  exact CodeReq.union_mono_left


-- @@ L203-204 expanded
private theorem shared_b11_div {b : Word} :
    ∀ a i,
      (CodeReq.ofProg (b + nopOff) (ADDI .x0 .x0 0 : Program)) a = some i →
        (divCode b) a = some i :=
  by unfold divCode; simp only [CodeReq.unionAll_cons];
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  exact CodeReq.union_mono_left


-- @@ L205-206 expanded
private theorem shared_b12_div {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + div128Off) divK_div128) a = some i → (divCode b) a = some i := by
  unfold divCode; simp only [CodeReq.unionAll_cons];
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  exact CodeReq.union_mono_left


-- @@ L208-228 verbatim
/-- sharedDivModCode ⊆ divCode: every shared block is also in divCode. -/
theorem sharedDivModCode_sub_divCode {base : Word} :
    ∀ a i, (sharedDivModCode base) a = some i → (divCode base) a = some i := by
  unfold sharedDivModCode; simp only [CodeReq.unionAll_cons]
  exact CodeReq.union_split_mono shared_b0_div
    (CodeReq.union_split_mono shared_b1_div
    (CodeReq.union_split_mono shared_b2_div
    (CodeReq.union_split_mono shared_b3_div
    (CodeReq.union_split_mono shared_b4_div
    (CodeReq.union_split_mono shared_b5_div
    (CodeReq.union_split_mono shared_b6_div
    (CodeReq.union_split_mono shared_b7_div
    (CodeReq.union_split_mono shared_b8_div
    (CodeReq.union_split_mono shared_b9_div
    (CodeReq.union_split_mono shared_b10_div
    (CodeReq.union_split_mono shared_b11_div
    (CodeReq.union_split_mono shared_b12_div
    (fun _ _ h => by simp [CodeReq.unionAll_nil, CodeReq.empty] at h)))))))))))))

-- Per-block subsumption for modCode. Same pattern as shared_b*_div — the
-- shared blocks occupy the same union positions in modCode as in divCode.

-- @@ L229-230 verbatim
private theorem shared_b0_mod {b : Word} : ∀ a i, (CodeReq.ofProg b (divK_phaseA 1020)) a = some i → (modCode b) a = some i := by
  unfold modCode; simp only [CodeReq.unionAll_cons]; exact CodeReq.union_mono_left

-- @@ L231-232 expanded
private theorem shared_b1_mod {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + phaseBOff) divK_phaseB) a = some i → (modCode b) a = some i := by
  unfold modCode; simp only [CodeReq.unionAll_cons];
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  exact CodeReq.union_mono_left


-- @@ L233-234 expanded
private theorem shared_b2_mod {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + clzOff) divK_clz) a = some i → (modCode b) a = some i := by
  unfold modCode; simp only [CodeReq.unionAll_cons];
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  exact CodeReq.union_mono_left


-- @@ L235-236 expanded
private theorem shared_b3_mod {b : Word} :
    ∀ a i,
      (CodeReq.ofProg (b + phaseC2Off) (divK_phaseC2 172)) a = some i → (modCode b) a = some i :=
  by unfold modCode; simp only [CodeReq.unionAll_cons];
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  exact CodeReq.union_mono_left


-- @@ L237-238 expanded
private theorem shared_b4_mod {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + normBOff) divK_normB) a = some i → (modCode b) a = some i := by
  unfold modCode; simp only [CodeReq.unionAll_cons];
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  exact CodeReq.union_mono_left


-- @@ L239-240 expanded
private theorem shared_b5_mod {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + normAOff) (divK_normA 40)) a = some i → (modCode b) a = some i := by
  unfold modCode; simp only [CodeReq.unionAll_cons];
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  exact CodeReq.union_mono_left


-- @@ L241-242 expanded
private theorem shared_b6_mod {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + copyAUOff) divK_copyAU) a = some i → (modCode b) a = some i := by
  unfold modCode; simp only [CodeReq.unionAll_cons];
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  exact CodeReq.union_mono_left


-- @@ L243-244 expanded
private theorem shared_b7_mod {b : Word} :
    ∀ a i,
      (CodeReq.ofProg (b + loopSetupOff) (divK_loopSetup 464)) a = some i →
        (modCode b) a = some i :=
  by unfold modCode; simp only [CodeReq.unionAll_cons];
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  exact CodeReq.union_mono_left


-- @@ L245-246 expanded
private theorem shared_b8_mod {b : Word} :
    ∀ a i,
      (CodeReq.ofProg (b + loopBodyOff) (divK_loopBody 560 7736)) a = some i →
        (modCode b) a = some i :=
  by unfold modCode; simp only [CodeReq.unionAll_cons];
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  exact CodeReq.union_mono_left


-- @@ L247-248 expanded
private theorem shared_b9_mod {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + denormOff) divK_denorm) a = some i → (modCode b) a = some i := by
  unfold modCode; simp only [CodeReq.unionAll_cons];
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  exact CodeReq.union_mono_left


-- @@ L249-250 expanded
private theorem shared_b10_mod {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + zeroPathOff) divK_zeroPath) a = some i → (modCode b) a = some i :=
  by unfold modCode; simp only [CodeReq.unionAll_cons];
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  exact CodeReq.union_mono_left


-- @@ L251-252 expanded
private theorem shared_b11_mod {b : Word} :
    ∀ a i,
      (CodeReq.ofProg (b + nopOff) (ADDI .x0 .x0 0 : Program)) a = some i →
        (modCode b) a = some i :=
  by unfold modCode; simp only [CodeReq.unionAll_cons];
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  exact CodeReq.union_mono_left


-- @@ L253-254 expanded
private theorem shared_b12_mod {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + div128Off) divK_div128) a = some i → (modCode b) a = some i := by
  unfold modCode; simp only [CodeReq.unionAll_cons];
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  exact CodeReq.union_mono_left


-- @@ L256-274 verbatim
/-- sharedDivModCode ⊆ modCode: every shared block is also in modCode.
    Mirror of `sharedDivModCode_sub_divCode`. -/
theorem sharedDivModCode_sub_modCode {base : Word} :
    ∀ a i, (sharedDivModCode base) a = some i → (modCode base) a = some i := by
  unfold sharedDivModCode; simp only [CodeReq.unionAll_cons]
  exact CodeReq.union_split_mono shared_b0_mod
    (CodeReq.union_split_mono shared_b1_mod
    (CodeReq.union_split_mono shared_b2_mod
    (CodeReq.union_split_mono shared_b3_mod
    (CodeReq.union_split_mono shared_b4_mod
    (CodeReq.union_split_mono shared_b5_mod
    (CodeReq.union_split_mono shared_b6_mod
    (CodeReq.union_split_mono shared_b7_mod
    (CodeReq.union_split_mono shared_b8_mod
    (CodeReq.union_split_mono shared_b9_mod
    (CodeReq.union_split_mono shared_b10_mod
    (CodeReq.union_split_mono shared_b11_mod
    (CodeReq.union_split_mono shared_b12_mod
    (fun _ _ h => by simp [CodeReq.unionAll_nil, CodeReq.empty] at h)))))))))))))


-- @@ L276-310 expanded
/-- v4 mirror of `shared_b12_div128_v2_sub`: block 12 (`divK_div128_v4`)
    is included in `sharedDivModCode_v4 base`. Used by `div128_v4_spec_shared`
    to lift `div128_v4_spec` from singleton-`ofProg` cr to shared cr. -/
theorem shared_b12_div128_v4_sub {b : Word} :
    ∀ a i,
      (CodeReq.ofProg (b + div128Off) divK_div128_v4) a = some i →
        (sharedDivModCode_v4 b) a = some i :=
  by
  unfold sharedDivModCode_v4; simp only [CodeReq.unionAll_cons]
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega))
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega))
  exact CodeReq.union_mono_left


-- @@ L312-329 verbatim
/-- 13-block CodeReq for `evm_div`'s phases minus the NOP at `nopOff`. -/
abbrev divCode_noNop (base : Word) : CodeReq :=
  CodeReq.unionAll [
    CodeReq.ofProg  base                  (divK_phaseA 1020),     -- block 0
    CodeReq.ofProg (base + phaseBOff)     divK_phaseB,            -- block 1
    CodeReq.ofProg (base + clzOff)        divK_clz,               -- block 2
    CodeReq.ofProg (base + phaseC2Off)    (divK_phaseC2 172),     -- block 3
    CodeReq.ofProg (base + normBOff)      divK_normB,             -- block 4
    CodeReq.ofProg (base + normAOff)      (divK_normA 40),        -- block 5
    CodeReq.ofProg (base + copyAUOff)     divK_copyAU,            -- block 6
    CodeReq.ofProg (base + loopSetupOff)  (divK_loopSetup 464),   -- block 7
    CodeReq.ofProg (base + loopBodyOff)   (divK_loopBody 560 7736),-- block 8
    CodeReq.ofProg (base + denormOff)     divK_denorm,            -- block 9
    CodeReq.ofProg (base + epilogueOff)   (divK_div_epilogue 24), -- block 10
    CodeReq.ofProg (base + zeroPathOff)   divK_zeroPath,          -- block 11
    -- NO NOP block (block 12 omitted)
    CodeReq.ofProg (base + div128Off)     divK_div128             -- block 12 (was 13)
  ]


-- @@ L331-352 verbatim
/-- 13-block CodeReq for `evm_mod`'s phases minus the NOP at `nopOff`.
    Identical to `divCode_noNop` except block 10 uses `divK_mod_epilogue`. -/
abbrev modCode_noNop (base : Word) : CodeReq :=
  CodeReq.unionAll [
    CodeReq.ofProg  base                  (divK_phaseA 1020),
    CodeReq.ofProg (base + phaseBOff)     divK_phaseB,
    CodeReq.ofProg (base + clzOff)        divK_clz,
    CodeReq.ofProg (base + phaseC2Off)    (divK_phaseC2 172),
    CodeReq.ofProg (base + normBOff)      divK_normB,
    CodeReq.ofProg (base + normAOff)      (divK_normA 40),
    CodeReq.ofProg (base + copyAUOff)     divK_copyAU,
    CodeReq.ofProg (base + loopSetupOff)  (divK_loopSetup 464),
    CodeReq.ofProg (base + loopBodyOff)   (divK_loopBody 560 7736),
    CodeReq.ofProg (base + denormOff)     divK_denorm,
    CodeReq.ofProg (base + epilogueOff)   (divK_mod_epilogue 24), -- block 10 differs
    CodeReq.ofProg (base + zeroPathOff)   divK_zeroPath,
    CodeReq.ofProg (base + div128Off)     divK_div128
  ]

-- Per-block subsumption: each noNop block ⊆ divCode. Blocks 0-11 sit at the
-- same union positions in both; the trailing div128 block is at position 12
-- in noNop but position 13 in divCode (one extra skipBlock to bypass NOP).

-- @@ L353-355 verbatim
private theorem noNop_b0_div {b : Word} :
    ∀ a i, (CodeReq.ofProg b (divK_phaseA 1020)) a = some i → (divCode b) a = some i := by
  unfold divCode; simp only [CodeReq.unionAll_cons]; exact CodeReq.union_mono_left

-- @@ L356-358 expanded
private theorem noNop_b1_div {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + phaseBOff) divK_phaseB) a = some i → (divCode b) a = some i := by
  unfold divCode; simp only [CodeReq.unionAll_cons];
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  exact CodeReq.union_mono_left


-- @@ L359-361 expanded
private theorem noNop_b2_div {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + clzOff) divK_clz) a = some i → (divCode b) a = some i := by
  unfold divCode; simp only [CodeReq.unionAll_cons];
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  exact CodeReq.union_mono_left


-- @@ L362-364 expanded
private theorem noNop_b3_div {b : Word} :
    ∀ a i,
      (CodeReq.ofProg (b + phaseC2Off) (divK_phaseC2 172)) a = some i → (divCode b) a = some i :=
  by unfold divCode; simp only [CodeReq.unionAll_cons];
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  exact CodeReq.union_mono_left


-- @@ L365-367 expanded
private theorem noNop_b4_div {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + normBOff) divK_normB) a = some i → (divCode b) a = some i := by
  unfold divCode; simp only [CodeReq.unionAll_cons];
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  exact CodeReq.union_mono_left


-- @@ L368-370 expanded
private theorem noNop_b5_div {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + normAOff) (divK_normA 40)) a = some i → (divCode b) a = some i := by
  unfold divCode; simp only [CodeReq.unionAll_cons];
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  exact CodeReq.union_mono_left


-- @@ L371-373 expanded
private theorem noNop_b6_div {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + copyAUOff) divK_copyAU) a = some i → (divCode b) a = some i := by
  unfold divCode; simp only [CodeReq.unionAll_cons];
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  exact CodeReq.union_mono_left


-- @@ L374-376 expanded
private theorem noNop_b7_div {b : Word} :
    ∀ a i,
      (CodeReq.ofProg (b + loopSetupOff) (divK_loopSetup 464)) a = some i →
        (divCode b) a = some i :=
  by unfold divCode; simp only [CodeReq.unionAll_cons];
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  exact CodeReq.union_mono_left


-- @@ L377-379 expanded
private theorem noNop_b8_div {b : Word} :
    ∀ a i,
      (CodeReq.ofProg (b + loopBodyOff) (divK_loopBody 560 7736)) a = some i →
        (divCode b) a = some i :=
  by unfold divCode; simp only [CodeReq.unionAll_cons];
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  exact CodeReq.union_mono_left


-- @@ L380-382 expanded
private theorem noNop_b9_div {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + denormOff) divK_denorm) a = some i → (divCode b) a = some i := by
  unfold divCode; simp only [CodeReq.unionAll_cons];
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  exact CodeReq.union_mono_left


-- @@ L383-385 expanded
private theorem noNop_b10_div {b : Word} :
    ∀ a i,
      (CodeReq.ofProg (b + epilogueOff) (divK_div_epilogue 24)) a = some i →
        (divCode b) a = some i :=
  by unfold divCode; simp only [CodeReq.unionAll_cons];
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  exact CodeReq.union_mono_left


-- @@ L386-388 expanded
private theorem noNop_b11_div {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + zeroPathOff) divK_zeroPath) a = some i → (divCode b) a = some i :=
  by unfold divCode; simp only [CodeReq.unionAll_cons];
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  exact CodeReq.union_mono_left


-- @@ L389-391 expanded
private theorem noNop_b12_div {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + div128Off) divK_div128) a = some i → (divCode b) a = some i := by
  unfold divCode; simp only [CodeReq.unionAll_cons];
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  exact CodeReq.union_mono_left


-- @@ L393-410 verbatim
/-- divCode_noNop ⊆ divCode: every noNop block also occurs in divCode. -/
theorem divCode_noNop_sub_divCode {base : Word} :
    ∀ a i, (divCode_noNop base) a = some i → (divCode base) a = some i := by
  unfold divCode_noNop; simp only [CodeReq.unionAll_cons]
  exact CodeReq.union_split_mono noNop_b0_div
    (CodeReq.union_split_mono noNop_b1_div
    (CodeReq.union_split_mono noNop_b2_div
    (CodeReq.union_split_mono noNop_b3_div
    (CodeReq.union_split_mono noNop_b4_div
    (CodeReq.union_split_mono noNop_b5_div
    (CodeReq.union_split_mono noNop_b6_div
    (CodeReq.union_split_mono noNop_b7_div
    (CodeReq.union_split_mono noNop_b8_div
    (CodeReq.union_split_mono noNop_b9_div
    (CodeReq.union_split_mono noNop_b10_div
    (CodeReq.union_split_mono noNop_b11_div
    (CodeReq.union_split_mono noNop_b12_div
    (fun _ _ h => by simp [CodeReq.unionAll_nil, CodeReq.empty] at h)))))))))))))


-- @@ L412-426 expanded
/-- The shared loop body block is present in `divCode_noNop`.

    This public block-level inclusion is useful when rebuilding loop
    compositions over the no-NOP code surface: unlike `sharedDivModCode`, the
    no-NOP bundle omits the old return-slot NOP and can be used by callable
    wrappers that preserve the caller's return address. -/
theorem divK_loopBody_ofProg_sub_divCode_noNop {base : Word} :
    ∀ a i,
      (CodeReq.ofProg (base + loopBodyOff) (divK_loopBody 560 7736)) a = some i →
        (divCode_noNop base) a = some i :=
  by
  unfold divCode_noNop; simp only [CodeReq.unionAll_cons]
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega))
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega))
  exact CodeReq.union_mono_left


-- @@ L427-429 verbatim
private theorem sharedNoNop_b0_div {b : Word} :
    ∀ a i, (CodeReq.ofProg b (divK_phaseA 1020)) a = some i → (divCode_noNop b) a = some i := by
  unfold divCode_noNop; simp only [CodeReq.unionAll_cons]; exact CodeReq.union_mono_left

-- @@ L430-432 expanded
private theorem sharedNoNop_b1_div {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + phaseBOff) divK_phaseB) a = some i → (divCode_noNop b) a = some i :=
  by unfold divCode_noNop; simp only [CodeReq.unionAll_cons];
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  exact CodeReq.union_mono_left


-- @@ L433-435 expanded
private theorem sharedNoNop_b2_div {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + clzOff) divK_clz) a = some i → (divCode_noNop b) a = some i := by
  unfold divCode_noNop; simp only [CodeReq.unionAll_cons];
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  exact CodeReq.union_mono_left


-- @@ L436-438 expanded
private theorem sharedNoNop_b3_div {b : Word} :
    ∀ a i,
      (CodeReq.ofProg (b + phaseC2Off) (divK_phaseC2 172)) a = some i →
        (divCode_noNop b) a = some i :=
  by unfold divCode_noNop; simp only [CodeReq.unionAll_cons];
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  exact CodeReq.union_mono_left


-- @@ L439-441 expanded
private theorem sharedNoNop_b4_div {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + normBOff) divK_normB) a = some i → (divCode_noNop b) a = some i :=
  by unfold divCode_noNop; simp only [CodeReq.unionAll_cons];
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  exact CodeReq.union_mono_left


-- @@ L442-444 expanded
private theorem sharedNoNop_b5_div {b : Word} :
    ∀ a i,
      (CodeReq.ofProg (b + normAOff) (divK_normA 40)) a = some i → (divCode_noNop b) a = some i :=
  by unfold divCode_noNop; simp only [CodeReq.unionAll_cons];
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  exact CodeReq.union_mono_left


-- @@ L445-447 expanded
private theorem sharedNoNop_b6_div {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + copyAUOff) divK_copyAU) a = some i → (divCode_noNop b) a = some i :=
  by unfold divCode_noNop; simp only [CodeReq.unionAll_cons];
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  exact CodeReq.union_mono_left


-- @@ L448-450 expanded
private theorem sharedNoNop_b7_div {b : Word} :
    ∀ a i,
      (CodeReq.ofProg (b + loopSetupOff) (divK_loopSetup 464)) a = some i →
        (divCode_noNop b) a = some i :=
  by unfold divCode_noNop; simp only [CodeReq.unionAll_cons];
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  exact CodeReq.union_mono_left


-- @@ L451-453 expanded
private theorem sharedNoNop_b8_div {b : Word} :
    ∀ a i,
      (CodeReq.ofProg (b + loopBodyOff) (divK_loopBody 560 7736)) a = some i →
        (divCode_noNop b) a = some i :=
  by unfold divCode_noNop; simp only [CodeReq.unionAll_cons];
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  exact CodeReq.union_mono_left


-- @@ L454-456 expanded
private theorem sharedNoNop_b9_div {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + denormOff) divK_denorm) a = some i → (divCode_noNop b) a = some i :=
  by unfold divCode_noNop; simp only [CodeReq.unionAll_cons];
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  exact CodeReq.union_mono_left


-- @@ L457-459 expanded
private theorem sharedNoNop_b10_div {b : Word} :
    ∀ a i,
      (CodeReq.ofProg (b + zeroPathOff) divK_zeroPath) a = some i → (divCode_noNop b) a = some i :=
  by unfold divCode_noNop; simp only [CodeReq.unionAll_cons];
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  exact CodeReq.union_mono_left


-- @@ L460-462 expanded
private theorem sharedNoNop_b11_div {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + div128Off) divK_div128) a = some i → (divCode_noNop b) a = some i :=
  by unfold divCode_noNop; simp only [CodeReq.unionAll_cons];
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  exact CodeReq.union_mono_left


-- @@ L464-484 verbatim
/-- `sharedDivModCodeNoNop ⊆ divCode_noNop`: every shared no-NOP block is
    also present in the DIV no-NOP code bundle. -/
theorem sharedDivModCodeNoNop_sub_divCode_noNop {base : Word} :
    ∀ a i, (sharedDivModCodeNoNop base) a = some i →
      (divCode_noNop base) a = some i := by
  unfold sharedDivModCodeNoNop; simp only [CodeReq.unionAll_cons]
  exact CodeReq.union_split_mono sharedNoNop_b0_div
    (CodeReq.union_split_mono sharedNoNop_b1_div
    (CodeReq.union_split_mono sharedNoNop_b2_div
    (CodeReq.union_split_mono sharedNoNop_b3_div
    (CodeReq.union_split_mono sharedNoNop_b4_div
    (CodeReq.union_split_mono sharedNoNop_b5_div
    (CodeReq.union_split_mono sharedNoNop_b6_div
    (CodeReq.union_split_mono sharedNoNop_b7_div
    (CodeReq.union_split_mono sharedNoNop_b8_div
    (CodeReq.union_split_mono sharedNoNop_b9_div
    (CodeReq.union_split_mono sharedNoNop_b10_div
    (CodeReq.union_split_mono sharedNoNop_b11_div
    (fun _ _ h => by simp [CodeReq.unionAll_nil, CodeReq.empty] at h))))))))))))

-- MOD side mirror.

-- @@ L485-487 verbatim
private theorem noNop_b0_mod {b : Word} :
    ∀ a i, (CodeReq.ofProg b (divK_phaseA 1020)) a = some i → (modCode b) a = some i := by
  unfold modCode; simp only [CodeReq.unionAll_cons]; exact CodeReq.union_mono_left

-- @@ L488-490 expanded
private theorem noNop_b1_mod {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + phaseBOff) divK_phaseB) a = some i → (modCode b) a = some i := by
  unfold modCode; simp only [CodeReq.unionAll_cons];
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  exact CodeReq.union_mono_left


-- @@ L491-493 expanded
private theorem noNop_b2_mod {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + clzOff) divK_clz) a = some i → (modCode b) a = some i := by
  unfold modCode; simp only [CodeReq.unionAll_cons];
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  exact CodeReq.union_mono_left


-- @@ L494-496 expanded
private theorem noNop_b3_mod {b : Word} :
    ∀ a i,
      (CodeReq.ofProg (b + phaseC2Off) (divK_phaseC2 172)) a = some i → (modCode b) a = some i :=
  by unfold modCode; simp only [CodeReq.unionAll_cons];
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  exact CodeReq.union_mono_left


-- @@ L497-499 expanded
private theorem noNop_b4_mod {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + normBOff) divK_normB) a = some i → (modCode b) a = some i := by
  unfold modCode; simp only [CodeReq.unionAll_cons];
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  exact CodeReq.union_mono_left


-- @@ L500-502 expanded
private theorem noNop_b5_mod {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + normAOff) (divK_normA 40)) a = some i → (modCode b) a = some i := by
  unfold modCode; simp only [CodeReq.unionAll_cons];
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  exact CodeReq.union_mono_left


-- @@ L503-505 expanded
private theorem noNop_b6_mod {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + copyAUOff) divK_copyAU) a = some i → (modCode b) a = some i := by
  unfold modCode; simp only [CodeReq.unionAll_cons];
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  exact CodeReq.union_mono_left


-- @@ L506-508 expanded
private theorem noNop_b7_mod {b : Word} :
    ∀ a i,
      (CodeReq.ofProg (b + loopSetupOff) (divK_loopSetup 464)) a = some i →
        (modCode b) a = some i :=
  by unfold modCode; simp only [CodeReq.unionAll_cons];
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  exact CodeReq.union_mono_left


-- @@ L509-511 expanded
private theorem noNop_b8_mod {b : Word} :
    ∀ a i,
      (CodeReq.ofProg (b + loopBodyOff) (divK_loopBody 560 7736)) a = some i →
        (modCode b) a = some i :=
  by unfold modCode; simp only [CodeReq.unionAll_cons];
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  exact CodeReq.union_mono_left


-- @@ L512-514 expanded
private theorem noNop_b9_mod {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + denormOff) divK_denorm) a = some i → (modCode b) a = some i := by
  unfold modCode; simp only [CodeReq.unionAll_cons];
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  exact CodeReq.union_mono_left


-- @@ L515-517 expanded
private theorem noNop_b10_mod {b : Word} :
    ∀ a i,
      (CodeReq.ofProg (b + epilogueOff) (divK_mod_epilogue 24)) a = some i →
        (modCode b) a = some i :=
  by unfold modCode; simp only [CodeReq.unionAll_cons];
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  exact CodeReq.union_mono_left


-- @@ L518-520 expanded
private theorem noNop_b11_mod {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + zeroPathOff) divK_zeroPath) a = some i → (modCode b) a = some i :=
  by unfold modCode; simp only [CodeReq.unionAll_cons];
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  exact CodeReq.union_mono_left


-- @@ L521-523 expanded
private theorem noNop_b12_mod {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + div128Off) divK_div128) a = some i → (modCode b) a = some i := by
  unfold modCode; simp only [CodeReq.unionAll_cons];
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  exact CodeReq.union_mono_left


-- @@ L525-544 verbatim
/-- modCode_noNop ⊆ modCode: every noNop block also occurs in modCode. -/
theorem modCode_noNop_sub_modCode {base : Word} :
    ∀ a i, (modCode_noNop base) a = some i → (modCode base) a = some i := by
  unfold modCode_noNop; simp only [CodeReq.unionAll_cons]
  exact CodeReq.union_split_mono noNop_b0_mod
    (CodeReq.union_split_mono noNop_b1_mod
    (CodeReq.union_split_mono noNop_b2_mod
    (CodeReq.union_split_mono noNop_b3_mod
    (CodeReq.union_split_mono noNop_b4_mod
    (CodeReq.union_split_mono noNop_b5_mod
    (CodeReq.union_split_mono noNop_b6_mod
    (CodeReq.union_split_mono noNop_b7_mod
    (CodeReq.union_split_mono noNop_b8_mod
    (CodeReq.union_split_mono noNop_b9_mod
    (CodeReq.union_split_mono noNop_b10_mod
    (CodeReq.union_split_mono noNop_b11_mod
    (CodeReq.union_split_mono noNop_b12_mod
    (fun _ _ h => by simp [CodeReq.unionAll_nil, CodeReq.empty] at h)))))))))))))

-- Shared no-NOP blocks as subsets of `modCode_noNop`.

-- @@ L545-547 verbatim
private theorem sharedNoNop_b0_mod {b : Word} :
    ∀ a i, (CodeReq.ofProg b (divK_phaseA 1020)) a = some i → (modCode_noNop b) a = some i := by
  unfold modCode_noNop; simp only [CodeReq.unionAll_cons]; exact CodeReq.union_mono_left

-- @@ L548-550 expanded
private theorem sharedNoNop_b1_mod {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + phaseBOff) divK_phaseB) a = some i → (modCode_noNop b) a = some i :=
  by unfold modCode_noNop; simp only [CodeReq.unionAll_cons];
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  exact CodeReq.union_mono_left


-- @@ L551-553 expanded
private theorem sharedNoNop_b2_mod {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + clzOff) divK_clz) a = some i → (modCode_noNop b) a = some i := by
  unfold modCode_noNop; simp only [CodeReq.unionAll_cons];
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  exact CodeReq.union_mono_left


-- @@ L554-556 expanded
private theorem sharedNoNop_b3_mod {b : Word} :
    ∀ a i,
      (CodeReq.ofProg (b + phaseC2Off) (divK_phaseC2 172)) a = some i →
        (modCode_noNop b) a = some i :=
  by unfold modCode_noNop; simp only [CodeReq.unionAll_cons];
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  exact CodeReq.union_mono_left


-- @@ L557-559 expanded
private theorem sharedNoNop_b4_mod {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + normBOff) divK_normB) a = some i → (modCode_noNop b) a = some i :=
  by unfold modCode_noNop; simp only [CodeReq.unionAll_cons];
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  exact CodeReq.union_mono_left


-- @@ L560-562 expanded
private theorem sharedNoNop_b5_mod {b : Word} :
    ∀ a i,
      (CodeReq.ofProg (b + normAOff) (divK_normA 40)) a = some i → (modCode_noNop b) a = some i :=
  by unfold modCode_noNop; simp only [CodeReq.unionAll_cons];
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  exact CodeReq.union_mono_left


-- @@ L563-565 expanded
private theorem sharedNoNop_b6_mod {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + copyAUOff) divK_copyAU) a = some i → (modCode_noNop b) a = some i :=
  by unfold modCode_noNop; simp only [CodeReq.unionAll_cons];
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  exact CodeReq.union_mono_left


-- @@ L566-568 expanded
private theorem sharedNoNop_b7_mod {b : Word} :
    ∀ a i,
      (CodeReq.ofProg (b + loopSetupOff) (divK_loopSetup 464)) a = some i →
        (modCode_noNop b) a = some i :=
  by unfold modCode_noNop; simp only [CodeReq.unionAll_cons];
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  exact CodeReq.union_mono_left


-- @@ L569-571 expanded
private theorem sharedNoNop_b8_mod {b : Word} :
    ∀ a i,
      (CodeReq.ofProg (b + loopBodyOff) (divK_loopBody 560 7736)) a = some i →
        (modCode_noNop b) a = some i :=
  by unfold modCode_noNop; simp only [CodeReq.unionAll_cons];
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  exact CodeReq.union_mono_left


-- @@ L572-574 expanded
private theorem sharedNoNop_b9_mod {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + denormOff) divK_denorm) a = some i → (modCode_noNop b) a = some i :=
  by unfold modCode_noNop; simp only [CodeReq.unionAll_cons];
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  exact CodeReq.union_mono_left


-- @@ L575-577 expanded
private theorem sharedNoNop_b10_mod {b : Word} :
    ∀ a i,
      (CodeReq.ofProg (b + zeroPathOff) divK_zeroPath) a = some i → (modCode_noNop b) a = some i :=
  by unfold modCode_noNop; simp only [CodeReq.unionAll_cons];
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  exact CodeReq.union_mono_left


-- @@ L578-580 expanded
private theorem sharedNoNop_b11_mod {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + div128Off) divK_div128) a = some i → (modCode_noNop b) a = some i :=
  by unfold modCode_noNop; simp only [CodeReq.unionAll_cons];
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  exact CodeReq.union_mono_left


-- @@ L582-611 verbatim
/-- `sharedDivModCodeNoNop ⊆ modCode_noNop`: every shared no-NOP block is
    also present in the MOD no-NOP code bundle. -/
theorem sharedDivModCodeNoNop_sub_modCode_noNop {base : Word} :
    ∀ a i, (sharedDivModCodeNoNop base) a = some i →
      (modCode_noNop base) a = some i := by
  unfold sharedDivModCodeNoNop; simp only [CodeReq.unionAll_cons]
  exact CodeReq.union_split_mono sharedNoNop_b0_mod
    (CodeReq.union_split_mono sharedNoNop_b1_mod
    (CodeReq.union_split_mono sharedNoNop_b2_mod
    (CodeReq.union_split_mono sharedNoNop_b3_mod
    (CodeReq.union_split_mono sharedNoNop_b4_mod
    (CodeReq.union_split_mono sharedNoNop_b5_mod
    (CodeReq.union_split_mono sharedNoNop_b6_mod
    (CodeReq.union_split_mono sharedNoNop_b7_mod
    (CodeReq.union_split_mono sharedNoNop_b8_mod
    (CodeReq.union_split_mono sharedNoNop_b9_mod
    (CodeReq.union_split_mono sharedNoNop_b10_mod
    (CodeReq.union_split_mono sharedNoNop_b11_mod
    (fun _ _ h => by simp [CodeReq.unionAll_nil, CodeReq.empty] at h))))))))))))

-- ============================================================================
-- Postcondition bundle for loopSetup (shift ≠ 0) path
-- Encapsulates 11 let bindings (shift normalization of b[] and a[]) plus
-- the full 30-atom assertion chain into a single opaque Assertion.
-- Used by all 8 _to_loopSetup_spec theorems (n=1..4, DIV and MOD).
-- ============================================================================

-- ============================================================================
-- Scratch region bundle: 15 memory cells used by the 256-bit DIV/MOD program
-- ============================================================================


-- @@ L613-639 verbatim
/-- The 15 scratch memory cells that the DIV/MOD program reads and writes
    during execution. All live at negative offsets from the stack pointer
    (`sp + signExtend12 …` with 12-bit values ≥ 2048 wrapping to negative).

    Layout:
    - `q0..q3` at `sp + signExtend12 4088/4080/4072/4064` — accumulated quotient digits
    - `u0..u4` at `sp + signExtend12 4056/4048/4040/4032/4024` — normalized dividend
    - `u5..u7` at `sp + signExtend12 4016/4008/4000` — overflow/scratch
    - `shiftMem` at `sp + signExtend12 3992`, `nMem` at `sp + signExtend12 3984`
    - `jMem` at `sp + signExtend12 3976`

    This is the precondition shape — specific starting values for every cell.
    The full-path specs universally-quantify over these values since the program
    overwrites them; the predicate packages them so stack specs aren't littered
    with fifteen `↦ₘ` lines at every call site. -/
@[irreducible]
def divScratchValues (sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    shiftMem nMem jMem : Word) : Assertion :=
  ((sp + signExtend12 4088) ↦ₘ q0) ** ((sp + signExtend12 4080) ↦ₘ q1) **
  ((sp + signExtend12 4072) ↦ₘ q2) ** ((sp + signExtend12 4064) ↦ₘ q3) **
  ((sp + signExtend12 4056) ↦ₘ u0) ** ((sp + signExtend12 4048) ↦ₘ u1) **
  ((sp + signExtend12 4040) ↦ₘ u2) ** ((sp + signExtend12 4032) ↦ₘ u3) **
  ((sp + signExtend12 4024) ↦ₘ u4) ** ((sp + signExtend12 4016) ↦ₘ u5) **
  ((sp + signExtend12 4008) ↦ₘ u6) ** ((sp + signExtend12 4000) ↦ₘ u7) **
  ((sp + signExtend12 3992) ↦ₘ shiftMem) **
  ((sp + signExtend12 3984) ↦ₘ nMem) **
  ((sp + signExtend12 3976) ↦ₘ jMem)


-- @@ L641-657 verbatim
/-- Unfold `divScratchValues` into its 15 underlying memory atoms. The bundle
    is `@[irreducible]`, so `unfold` won't see through it — this named rewrite
    is the supported way in at call sites (parallel to `divScratchOwn_unfold`). -/
theorem divScratchValues_unfold {sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    shiftMem nMem jMem : Word} :
    divScratchValues sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem =
    (((sp + signExtend12 4088) ↦ₘ q0) ** ((sp + signExtend12 4080) ↦ₘ q1) **
     ((sp + signExtend12 4072) ↦ₘ q2) ** ((sp + signExtend12 4064) ↦ₘ q3) **
     ((sp + signExtend12 4056) ↦ₘ u0) ** ((sp + signExtend12 4048) ↦ₘ u1) **
     ((sp + signExtend12 4040) ↦ₘ u2) ** ((sp + signExtend12 4032) ↦ₘ u3) **
     ((sp + signExtend12 4024) ↦ₘ u4) ** ((sp + signExtend12 4016) ↦ₘ u5) **
     ((sp + signExtend12 4008) ↦ₘ u6) ** ((sp + signExtend12 4000) ↦ₘ u7) **
     ((sp + signExtend12 3992) ↦ₘ shiftMem) **
     ((sp + signExtend12 3984) ↦ₘ nMem) **
     ((sp + signExtend12 3976) ↦ₘ jMem)) := by
  delta divScratchValues; rfl


-- @@ L659-674 verbatim
/-- Extension of `divScratchValues` with the 4 additional call-path scratch
    cells at `sp + signExtend12 3968/3960/3952/3944` — the `div128`-subroutine
    return address, the normalized top-divisor limb `d = b3'`, its low 32
    bits `dLo`, and the `u_top`-next-limb normalized halfword. Total: 19 cells.

    Used by the call-trial paths (`evm_div_n4_full_call_{skip,addback}_spec`)
    which need these 4 extra scratch slots for the `div128Quot` computation.
    The max-trial paths use only the 15 cells of `divScratchValues`. -/
@[irreducible]
def divScratchValuesCall (sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    shiftMem nMem jMem retMem dMem dloMem scratch_un0 : Word) : Assertion :=
  divScratchValues sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7 shiftMem nMem jMem **
  ((sp + signExtend12 3968) ↦ₘ retMem) **
  ((sp + signExtend12 3960) ↦ₘ dMem) **
  ((sp + signExtend12 3952) ↦ₘ dloMem) **
  ((sp + signExtend12 3944) ↦ₘ scratch_un0) ** regOwn .x1


-- @@ L676-686 verbatim
/-- Named unfold for `divScratchValuesCall`. -/
theorem divScratchValuesCall_unfold {sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    shiftMem nMem jMem retMem dMem dloMem scratch_un0 : Word} :
    divScratchValuesCall sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0 =
    (divScratchValues sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7 shiftMem nMem jMem **
     ((sp + signExtend12 3968) ↦ₘ retMem) **
     ((sp + signExtend12 3960) ↦ₘ dMem) **
     ((sp + signExtend12 3952) ↦ₘ dloMem) **
     ((sp + signExtend12 3944) ↦ₘ scratch_un0) ** regOwn .x1) := by
  delta divScratchValuesCall; rfl


-- @@ L688-702 verbatim
/-- Value-agnostic counterpart to `divScratchValues`: the same 15 cells but
    with ownership only (no commitment to specific values). Suitable for the
    postcondition of a stack-level DIV/MOD spec that doesn't want to expose
    the algorithm's internal scratch state to callers. -/
@[irreducible]
def divScratchOwn (sp : Word) : Assertion :=
  memOwn (sp + signExtend12 4088) ** memOwn (sp + signExtend12 4080) **
  memOwn (sp + signExtend12 4072) ** memOwn (sp + signExtend12 4064) **
  memOwn (sp + signExtend12 4056) ** memOwn (sp + signExtend12 4048) **
  memOwn (sp + signExtend12 4040) ** memOwn (sp + signExtend12 4032) **
  memOwn (sp + signExtend12 4024) ** memOwn (sp + signExtend12 4016) **
  memOwn (sp + signExtend12 4008) ** memOwn (sp + signExtend12 4000) **
  memOwn (sp + signExtend12 3992) **
  memOwn (sp + signExtend12 3984) **
  memOwn (sp + signExtend12 3976)


-- @@ L704-718 verbatim
/-- Named unfold for `divScratchOwn`. Restores access to the underlying
    definition once the `@[irreducible]` attribute has made `delta` the only
    way in at call sites. Parallel to `divScratchValues_unfold`. -/
theorem divScratchOwn_unfold {sp : Word} :
    divScratchOwn sp =
    (memOwn (sp + signExtend12 4088) ** memOwn (sp + signExtend12 4080) **
     memOwn (sp + signExtend12 4072) ** memOwn (sp + signExtend12 4064) **
     memOwn (sp + signExtend12 4056) ** memOwn (sp + signExtend12 4048) **
     memOwn (sp + signExtend12 4040) ** memOwn (sp + signExtend12 4032) **
     memOwn (sp + signExtend12 4024) ** memOwn (sp + signExtend12 4016) **
     memOwn (sp + signExtend12 4008) ** memOwn (sp + signExtend12 4000) **
     memOwn (sp + signExtend12 3992) **
     memOwn (sp + signExtend12 3984) **
     memOwn (sp + signExtend12 3976)) := by
  delta divScratchOwn; rfl


-- @@ L720-724 verbatim
theorem pcFree_divScratchValues {sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    shiftMem nMem jMem : Word} :
    (divScratchValues sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem).pcFree := by
  unfold divScratchValues; pcFree


-- @@ L726-729 verbatim
instance (sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7 shiftMem nMem jMem : Word) :
    Assertion.PCFree (divScratchValues sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem) :=
  ⟨pcFree_divScratchValues⟩


-- @@ L731-734 verbatim
/-- `divScratchOwn` is pc-free: all its 15 atoms are `memOwn`. Proof goes
    through the `_unfold` rewrite since the bundle is `@[irreducible]`. -/
theorem pcFree_divScratchOwn {sp : Word} : (divScratchOwn sp).pcFree := by
  rw [divScratchOwn_unfold]; pcFree


-- @@ L736-748 verbatim
/-- Value-agnostic counterpart to `divScratchValuesCall`: the same 19 cells
    but with ownership only. Extends `divScratchOwn` with the 4 call-path
    cells (at sp + 3968/3960/3952/3944).

    Used for call-trial stack-spec postconditions that don't expose the
    `div128` subroutine's internal state to callers. -/
@[irreducible]
def divScratchOwnCall (sp : Word) : Assertion :=
  divScratchOwn sp **
  memOwn (sp + signExtend12 3968) **
  memOwn (sp + signExtend12 3960) **
  memOwn (sp + signExtend12 3952) **
  memOwn (sp + signExtend12 3944) ** regOwn .x1


-- @@ L750-759 verbatim
/-- Named unfold for `divScratchOwnCall`. Parallel to `divScratchOwn_unfold`
    and `divScratchValuesCall_unfold`. -/
theorem divScratchOwnCall_unfold {sp : Word} :
    divScratchOwnCall sp =
    (divScratchOwn sp **
     memOwn (sp + signExtend12 3968) **
     memOwn (sp + signExtend12 3960) **
     memOwn (sp + signExtend12 3952) **
     memOwn (sp + signExtend12 3944) ** regOwn .x1) := by
  delta divScratchOwnCall; rfl


-- @@ L761-773 verbatim
/-- Callable-ready concrete call scratch bundle, with `x1` kept out of the
    scratch ownership so wrappers can expose the exact return address as its
    own atom. This is intentionally separate from `divScratchValuesCall`, whose
    historical shape includes `regOwn .x1` for public dispatcher posts. -/
@[irreducible]
def divScratchValuesCallNoX1 (sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    shiftMem nMem jMem retMem dMem dloMem scratch_un0 : Word) : Assertion :=
  divScratchValues sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    shiftMem nMem jMem **
  ((sp + signExtend12 3968) ↦ₘ retMem) **
  ((sp + signExtend12 3960) ↦ₘ dMem) **
  ((sp + signExtend12 3952) ↦ₘ dloMem) **
  ((sp + signExtend12 3944) ↦ₘ scratch_un0)


-- @@ L775-786 verbatim
/-- Named unfold for `divScratchValuesCallNoX1`. -/
theorem divScratchValuesCallNoX1_unfold {sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    shiftMem nMem jMem retMem dMem dloMem scratch_un0 : Word} :
    divScratchValuesCallNoX1 sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0 =
      (divScratchValues sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem **
       ((sp + signExtend12 3968) ↦ₘ retMem) **
       ((sp + signExtend12 3960) ↦ₘ dMem) **
       ((sp + signExtend12 3952) ↦ₘ dloMem) **
       ((sp + signExtend12 3944) ↦ₘ scratch_un0)) := by
  delta divScratchValuesCallNoX1; rfl


-- @@ L788-796 verbatim
/-- Callable-ready ownership counterpart to `divScratchValuesCallNoX1`;
    intentionally omits `regOwn .x1`. -/
@[irreducible]
def divScratchOwnCallNoX1 (sp : Word) : Assertion :=
  divScratchOwn sp **
  memOwn (sp + signExtend12 3968) **
  memOwn (sp + signExtend12 3960) **
  memOwn (sp + signExtend12 3952) **
  memOwn (sp + signExtend12 3944)


-- @@ L798-806 verbatim
/-- Named unfold for `divScratchOwnCallNoX1`. -/
theorem divScratchOwnCallNoX1_unfold {sp : Word} :
    divScratchOwnCallNoX1 sp =
    (divScratchOwn sp **
     memOwn (sp + signExtend12 3968) **
     memOwn (sp + signExtend12 3960) **
     memOwn (sp + signExtend12 3952) **
     memOwn (sp + signExtend12 3944)) := by
  delta divScratchOwnCallNoX1; rfl


-- @@ L808-810 verbatim
instance pcFreeInst_divScratchOwn (sp : Word) :
    Assertion.PCFree (divScratchOwn sp) :=
  ⟨pcFree_divScratchOwn⟩


-- @@ L812-819 verbatim
instance pcFreeInst_divScratchValuesCallNoX1
    (sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7 shiftMem nMem jMem
      retMem dMem dloMem scratch_un0 : Word) :
    Assertion.PCFree (divScratchValuesCallNoX1 sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratch_un0) := by
  constructor
  rw [divScratchValuesCallNoX1_unfold]
  pcFree


-- @@ L821-825 verbatim
instance pcFreeInst_divScratchOwnCallNoX1 (sp : Word) :
    Assertion.PCFree (divScratchOwnCallNoX1 sp) := by
  constructor
  rw [divScratchOwnCallNoX1_unfold, divScratchOwn_unfold]
  pcFree


-- @@ L827-836 verbatim
/-- Weakening: any concrete scratch state implies ownership of the same 15
    cells. This lets a stack spec hide the scratch values on exit. -/
theorem divScratchValues_implies_divScratchOwn
    (sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7 shiftMem nMem jMem : Word) :
    ∀ h, divScratchValues sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem h → divScratchOwn sp h := by
  unfold divScratchValues divScratchOwn
  -- Weaken each of the 15 memIs cells to memOwn, left to right.
  iterate 14 apply sepConj_mono memIs_implies_memOwn
  exact memIs_implies_memOwn


-- @@ L838-855 verbatim
/-- Call-path weakening: the 19-cell `divScratchValuesCall` implies the
    value-agnostic `divScratchOwnCall`. Used by the forthcoming
    `div_n4_call_skip_stack_weaken` and friends to hide the call-trial
    scratch state (including the 4 `div128`-subroutine cells at
    `sp + 3968/3960/3952/3944`) on stack-spec exit. -/
theorem divScratchValuesCall_implies_divScratchOwnCall
    (sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7 shiftMem nMem jMem
     retMem dMem dloMem scratch_un0 : Word) :
    ∀ h, divScratchValuesCall sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0 h →
      divScratchOwnCall sp h := by
  unfold divScratchValuesCall divScratchOwnCall
  -- Head: divScratchValues → divScratchOwn via the 15-cell weakener.
  apply sepConj_mono (divScratchValues_implies_divScratchOwn
    sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7 shiftMem nMem jMem)
  -- Tail: 4 memIs → memOwn, preserving the framed return register.
  iterate 4 apply sepConj_mono memIs_implies_memOwn
  exact fun _ hp => hp


-- @@ L857-869 verbatim
/-- Callable-ready call-path weakening, keeping `x1` outside the scratch
    bundle so it can be tracked exactly by wrappers. -/
theorem divScratchValuesCallNoX1_implies_divScratchOwnCallNoX1
    (sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7 shiftMem nMem jMem
     retMem dMem dloMem scratch_un0 : Word) :
    ∀ h, divScratchValuesCallNoX1 sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0 h →
      divScratchOwnCallNoX1 sp h := by
  unfold divScratchValuesCallNoX1 divScratchOwnCallNoX1
  apply sepConj_mono (divScratchValues_implies_divScratchOwn
    sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7 shiftMem nMem jMem)
  iterate 3 apply sepConj_mono memIs_implies_memOwn
  exact memIs_implies_memOwn


-- @@ L871-902 verbatim
/-- Postcondition for the shift≠0 path from entry to loop setup.
    Encapsulates the shift/antiShift computation, normalized b'[0..3],
    and normalized u[0..4] as internal let bindings.
    Marked @[irreducible] so xperm treats this as 1 opaque atom. -/
@[irreducible]
def loopSetupPost (sp nVal shift a0 a1 a2 a3 b0 b1 b2 b3 : Word) : Assertion :=
  let antiShift := signExtend12 (0 : BitVec 12) - shift
  let b3' := (b3 <<< (shift.toNat % 64)) ||| (b2 >>> (antiShift.toNat % 64))
  let b2' := (b2 <<< (shift.toNat % 64)) ||| (b1 >>> (antiShift.toNat % 64))
  let b1' := (b1 <<< (shift.toNat % 64)) ||| (b0 >>> (antiShift.toNat % 64))
  let b0' := b0 <<< (shift.toNat % 64)
  let u4 := a3 >>> (antiShift.toNat % 64)
  let u3 := (a3 <<< (shift.toNat % 64)) ||| (a2 >>> (antiShift.toNat % 64))
  let u2 := (a2 <<< (shift.toNat % 64)) ||| (a1 >>> (antiShift.toNat % 64))
  let u1 := (a1 <<< (shift.toNat % 64)) ||| (a0 >>> (antiShift.toNat % 64))
  let u0 := a0 <<< (shift.toNat % 64)
  (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ nVal) ** (.x10 ↦ᵣ (a0 >>> (antiShift.toNat % 64))) **
  (.x0 ↦ᵣ (0 : Word)) **
  (.x6 ↦ᵣ shift) ** (.x7 ↦ᵣ u0) ** (.x2 ↦ᵣ antiShift) **
  (.x9 ↦ᵣ signExtend12 (4 : BitVec 12) - nVal) **
  ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
  ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
  ((sp + 32) ↦ₘ b0') ** ((sp + 40) ↦ₘ b1') **
  ((sp + 48) ↦ₘ b2') ** ((sp + 56) ↦ₘ b3') **
  ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
  ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
  ((sp + signExtend12 4056) ↦ₘ u0) ** ((sp + signExtend12 4048) ↦ₘ u1) **
  ((sp + signExtend12 4040) ↦ₘ u2) ** ((sp + signExtend12 4032) ↦ₘ u3) **
  ((sp + signExtend12 4024) ↦ₘ u4) **
  ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
  ((sp + signExtend12 4000) ↦ₘ (0 : Word)) ** ((sp + signExtend12 3984) ↦ₘ nVal) **
  ((sp + signExtend12 3992) ↦ₘ shift)


-- @@ L904-933 verbatim
/-- Unfold the opaque loopSetupPost back to its expanded form. -/
theorem loopSetupPost_unfold {sp nVal shift a0 a1 a2 a3 b0 b1 b2 b3 : Word} :
    loopSetupPost sp nVal shift a0 a1 a2 a3 b0 b1 b2 b3 =
    let antiShift := signExtend12 (0 : BitVec 12) - shift
    let b3' := (b3 <<< (shift.toNat % 64)) ||| (b2 >>> (antiShift.toNat % 64))
    let b2' := (b2 <<< (shift.toNat % 64)) ||| (b1 >>> (antiShift.toNat % 64))
    let b1' := (b1 <<< (shift.toNat % 64)) ||| (b0 >>> (antiShift.toNat % 64))
    let b0' := b0 <<< (shift.toNat % 64)
    let u4 := a3 >>> (antiShift.toNat % 64)
    let u3 := (a3 <<< (shift.toNat % 64)) ||| (a2 >>> (antiShift.toNat % 64))
    let u2 := (a2 <<< (shift.toNat % 64)) ||| (a1 >>> (antiShift.toNat % 64))
    let u1 := (a1 <<< (shift.toNat % 64)) ||| (a0 >>> (antiShift.toNat % 64))
    let u0 := a0 <<< (shift.toNat % 64)
    (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ nVal) ** (.x10 ↦ᵣ (a0 >>> (antiShift.toNat % 64))) **
    (.x0 ↦ᵣ (0 : Word)) **
    (.x6 ↦ᵣ shift) ** (.x7 ↦ᵣ u0) ** (.x2 ↦ᵣ antiShift) **
    (.x9 ↦ᵣ signExtend12 (4 : BitVec 12) - nVal) **
    ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
    ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
    ((sp + 32) ↦ₘ b0') ** ((sp + 40) ↦ₘ b1') **
    ((sp + 48) ↦ₘ b2') ** ((sp + 56) ↦ₘ b3') **
    ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
    ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
    ((sp + signExtend12 4056) ↦ₘ u0) ** ((sp + signExtend12 4048) ↦ₘ u1) **
    ((sp + signExtend12 4040) ↦ₘ u2) ** ((sp + signExtend12 4032) ↦ₘ u3) **
    ((sp + signExtend12 4024) ↦ₘ u4) **
    ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
    ((sp + signExtend12 4000) ↦ₘ (0 : Word)) ** ((sp + signExtend12 3984) ↦ₘ nVal) **
    ((sp + signExtend12 3992) ↦ₘ shift) := by
  delta loopSetupPost; rfl


-- @@ L935-938 verbatim
/-- `loopSetupPost` is pc-free: all its atoms are `regIs` / `memIs`. -/
theorem pcFree_loopSetupPost {sp nVal shift a0 a1 a2 a3 b0 b1 b2 b3 : Word} :
    (loopSetupPost sp nVal shift a0 a1 a2 a3 b0 b1 b2 b3).pcFree := by
  rw [loopSetupPost_unfold]; pcFree


-- @@ L940-947 verbatim
instance pcFreeInst_loopSetupPost
    (sp nVal shift a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    Assertion.PCFree (loopSetupPost sp nVal shift a0 a1 a2 a3 b0 b1 b2 b3) :=
  ⟨pcFree_loopSetupPost⟩

-- ============================================================================
-- Postcondition bundles for denorm + epilogue paths
-- ============================================================================


-- @@ L949-965 verbatim
/-- Postcondition for DIV denorm + epilogue (shift ≠ 0).
    Encapsulates antiShift and denormalized u'[0..3]. -/
@[irreducible]
def denormDivPost (sp shift u0 u1 u2 u3 q0 q1 q2 q3 : Word) : Assertion :=
  let antiShift := signExtend12 (0 : BitVec 12) - shift
  let u0' := (u0 >>> (shift.toNat % 64)) ||| (u1 <<< (antiShift.toNat % 64))
  let u1' := (u1 >>> (shift.toNat % 64)) ||| (u2 <<< (antiShift.toNat % 64))
  let u2' := (u2 >>> (shift.toNat % 64)) ||| (u3 <<< (antiShift.toNat % 64))
  let u3' := u3 >>> (shift.toNat % 64)
  (.x12 ↦ᵣ (sp + 32)) ** (.x5 ↦ᵣ q0) ** (.x6 ↦ᵣ q1) ** (.x7 ↦ᵣ q2) **
  (.x2 ↦ᵣ antiShift) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ q3) **
  ((sp + signExtend12 4056) ↦ₘ u0') ** ((sp + signExtend12 4048) ↦ₘ u1') **
  ((sp + signExtend12 4040) ↦ₘ u2') ** ((sp + signExtend12 4032) ↦ₘ u3') **
  ((sp + signExtend12 4088) ↦ₘ q0) ** ((sp + signExtend12 4080) ↦ₘ q1) **
  ((sp + signExtend12 4072) ↦ₘ q2) ** ((sp + signExtend12 4064) ↦ₘ q3) **
  ((sp + 32) ↦ₘ q0) ** ((sp + 40) ↦ₘ q1) **
  ((sp + 48) ↦ₘ q2) ** ((sp + 56) ↦ₘ q3)


-- @@ L967-982 verbatim
theorem denormDivPost_unfold {sp shift u0 u1 u2 u3 q0 q1 q2 q3 : Word} :
    denormDivPost sp shift u0 u1 u2 u3 q0 q1 q2 q3 =
    let antiShift := signExtend12 (0 : BitVec 12) - shift
    let u0' := (u0 >>> (shift.toNat % 64)) ||| (u1 <<< (antiShift.toNat % 64))
    let u1' := (u1 >>> (shift.toNat % 64)) ||| (u2 <<< (antiShift.toNat % 64))
    let u2' := (u2 >>> (shift.toNat % 64)) ||| (u3 <<< (antiShift.toNat % 64))
    let u3' := u3 >>> (shift.toNat % 64)
    (.x12 ↦ᵣ (sp + 32)) ** (.x5 ↦ᵣ q0) ** (.x6 ↦ᵣ q1) ** (.x7 ↦ᵣ q2) **
    (.x2 ↦ᵣ antiShift) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ q3) **
    ((sp + signExtend12 4056) ↦ₘ u0') ** ((sp + signExtend12 4048) ↦ₘ u1') **
    ((sp + signExtend12 4040) ↦ₘ u2') ** ((sp + signExtend12 4032) ↦ₘ u3') **
    ((sp + signExtend12 4088) ↦ₘ q0) ** ((sp + signExtend12 4080) ↦ₘ q1) **
    ((sp + signExtend12 4072) ↦ₘ q2) ** ((sp + signExtend12 4064) ↦ₘ q3) **
    ((sp + 32) ↦ₘ q0) ** ((sp + 40) ↦ₘ q1) **
    ((sp + 48) ↦ₘ q2) ** ((sp + 56) ↦ₘ q3) := by
  delta denormDivPost; rfl


-- @@ L984-987 verbatim
/-- `denormDivPost` is pc-free: all its atoms are `regIs` / `memIs`. -/
theorem pcFree_denormDivPost {sp shift u0 u1 u2 u3 q0 q1 q2 q3 : Word} :
    (denormDivPost sp shift u0 u1 u2 u3 q0 q1 q2 q3).pcFree := by
  rw [denormDivPost_unfold]; pcFree


-- @@ L989-991 verbatim
instance pcFreeInst_denormDivPost (sp shift u0 u1 u2 u3 q0 q1 q2 q3 : Word) :
    Assertion.PCFree (denormDivPost sp shift u0 u1 u2 u3 q0 q1 q2 q3) :=
  ⟨pcFree_denormDivPost⟩


-- @@ L993-1007 verbatim
/-- Postcondition for MOD denorm + epilogue (shift ≠ 0).
    Encapsulates antiShift and denormalized u'[0..3]. -/
@[irreducible]
def denormModPost (sp shift u0 u1 u2 u3 : Word) : Assertion :=
  let antiShift := signExtend12 (0 : BitVec 12) - shift
  let u0' := (u0 >>> (shift.toNat % 64)) ||| (u1 <<< (antiShift.toNat % 64))
  let u1' := (u1 >>> (shift.toNat % 64)) ||| (u2 <<< (antiShift.toNat % 64))
  let u2' := (u2 >>> (shift.toNat % 64)) ||| (u3 <<< (antiShift.toNat % 64))
  let u3' := u3 >>> (shift.toNat % 64)
  (.x12 ↦ᵣ (sp + 32)) ** (.x5 ↦ᵣ u0') ** (.x6 ↦ᵣ u1') ** (.x7 ↦ᵣ u2') **
  (.x2 ↦ᵣ antiShift) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ u3') **
  ((sp + signExtend12 4056) ↦ₘ u0') ** ((sp + signExtend12 4048) ↦ₘ u1') **
  ((sp + signExtend12 4040) ↦ₘ u2') ** ((sp + signExtend12 4032) ↦ₘ u3') **
  ((sp + 32) ↦ₘ u0') ** ((sp + 40) ↦ₘ u1') **
  ((sp + 48) ↦ₘ u2') ** ((sp + 56) ↦ₘ u3')


-- @@ L1009-1022 verbatim
theorem denormModPost_unfold {sp shift u0 u1 u2 u3 : Word} :
    denormModPost sp shift u0 u1 u2 u3 =
    let antiShift := signExtend12 (0 : BitVec 12) - shift
    let u0' := (u0 >>> (shift.toNat % 64)) ||| (u1 <<< (antiShift.toNat % 64))
    let u1' := (u1 >>> (shift.toNat % 64)) ||| (u2 <<< (antiShift.toNat % 64))
    let u2' := (u2 >>> (shift.toNat % 64)) ||| (u3 <<< (antiShift.toNat % 64))
    let u3' := u3 >>> (shift.toNat % 64)
    (.x12 ↦ᵣ (sp + 32)) ** (.x5 ↦ᵣ u0') ** (.x6 ↦ᵣ u1') ** (.x7 ↦ᵣ u2') **
    (.x2 ↦ᵣ antiShift) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ u3') **
    ((sp + signExtend12 4056) ↦ₘ u0') ** ((sp + signExtend12 4048) ↦ₘ u1') **
    ((sp + signExtend12 4040) ↦ₘ u2') ** ((sp + signExtend12 4032) ↦ₘ u3') **
    ((sp + 32) ↦ₘ u0') ** ((sp + 40) ↦ₘ u1') **
    ((sp + 48) ↦ₘ u2') ** ((sp + 56) ↦ₘ u3') := by
  delta denormModPost; rfl


-- @@ L1024-1027 verbatim
/-- `denormModPost` is pc-free: all its atoms are `regIs` / `memIs`. -/
theorem pcFree_denormModPost {sp shift u0 u1 u2 u3 : Word} :
    (denormModPost sp shift u0 u1 u2 u3).pcFree := by
  rw [denormModPost_unfold]; pcFree


-- @@ L1029-1035 verbatim
instance pcFreeInst_denormModPost (sp shift u0 u1 u2 u3 : Word) :
    Assertion.PCFree (denormModPost sp shift u0 u1 u2 u3) :=
  ⟨pcFree_denormModPost⟩

-- ============================================================================
-- Postcondition bundle for normB (PhaseAB + CLZ + PhaseC2 + NormB)
-- ============================================================================


-- @@ L1037-1055 verbatim
/-- Postcondition after PhaseAB + CLZ + PhaseC2(ntaken) + NormB.
    Encapsulates shift, antiShift, and normalized b'[0..3]. -/
@[irreducible]
def normBPost (sp nVal shift b0 b1 b2 b3 : Word) : Assertion :=
  let antiShift := signExtend12 (0 : BitVec 12) - shift
  let b3' := (b3 <<< (shift.toNat % 64)) ||| (b2 >>> (antiShift.toNat % 64))
  let b2' := (b2 <<< (shift.toNat % 64)) ||| (b1 >>> (antiShift.toNat % 64))
  let b1' := (b1 <<< (shift.toNat % 64)) ||| (b0 >>> (antiShift.toNat % 64))
  let b0' := b0 <<< (shift.toNat % 64)
  (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ b0') ** (.x10 ↦ᵣ b3) ** (.x0 ↦ᵣ (0 : Word)) **
  (.x6 ↦ᵣ shift) ** (.x7 ↦ᵣ (b0 >>> (antiShift.toNat % 64))) **
  (.x2 ↦ᵣ antiShift) **
  ((sp + 32) ↦ₘ b0') ** ((sp + 40) ↦ₘ b1') **
  ((sp + 48) ↦ₘ b2') ** ((sp + 56) ↦ₘ b3') **
  ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
  ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
  ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
  ((sp + signExtend12 4000) ↦ₘ (0 : Word)) ** ((sp + signExtend12 3984) ↦ₘ nVal) **
  ((sp + signExtend12 3992) ↦ₘ shift)


-- @@ L1057-1074 verbatim
theorem normBPost_unfold {sp nVal shift b0 b1 b2 b3 : Word} :
    normBPost sp nVal shift b0 b1 b2 b3 =
    let antiShift := signExtend12 (0 : BitVec 12) - shift
    let b3' := (b3 <<< (shift.toNat % 64)) ||| (b2 >>> (antiShift.toNat % 64))
    let b2' := (b2 <<< (shift.toNat % 64)) ||| (b1 >>> (antiShift.toNat % 64))
    let b1' := (b1 <<< (shift.toNat % 64)) ||| (b0 >>> (antiShift.toNat % 64))
    let b0' := b0 <<< (shift.toNat % 64)
    (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ b0') ** (.x10 ↦ᵣ b3) ** (.x0 ↦ᵣ (0 : Word)) **
    (.x6 ↦ᵣ shift) ** (.x7 ↦ᵣ (b0 >>> (antiShift.toNat % 64))) **
    (.x2 ↦ᵣ antiShift) **
    ((sp + 32) ↦ₘ b0') ** ((sp + 40) ↦ₘ b1') **
    ((sp + 48) ↦ₘ b2') ** ((sp + 56) ↦ₘ b3') **
    ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
    ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
    ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
    ((sp + signExtend12 4000) ↦ₘ (0 : Word)) ** ((sp + signExtend12 3984) ↦ₘ nVal) **
    ((sp + signExtend12 3992) ↦ₘ shift) := by
  delta normBPost; rfl


-- @@ L1076-1079 verbatim
/-- `normBPost` is pc-free: all its atoms are `regIs` / `memIs`. -/
theorem pcFree_normBPost {sp nVal shift b0 b1 b2 b3 : Word} :
    (normBPost sp nVal shift b0 b1 b2 b3).pcFree := by
  rw [normBPost_unfold]; pcFree


-- @@ L1081-1083 verbatim
instance pcFreeInst_normBPost (sp nVal shift b0 b1 b2 b3 : Word) :
    Assertion.PCFree (normBPost sp nVal shift b0 b1 b2 b3) :=
  ⟨pcFree_normBPost⟩


-- @@ L1085-1102 verbatim
/-- Postcondition for the NormA block: the normalized `u[]`
    sequence written to scratch slots, with `x5`/`x7`/`x10` holding the
    top-of-the-shift intermediate values. Wrapped `@[irreducible]` so that
    downstream proofs do not re-reduce the 15-atom sepConj. -/
@[irreducible]
def normAFullPost (sp a0 a1 a2 a3 shift antiShift : Word) : Assertion :=
  let u4 := a3 >>> (antiShift.toNat % 64)
  let u3 := (a3 <<< (shift.toNat % 64)) ||| (a2 >>> (antiShift.toNat % 64))
  let u2 := (a2 <<< (shift.toNat % 64)) ||| (a1 >>> (antiShift.toNat % 64))
  let u1 := (a1 <<< (shift.toNat % 64)) ||| (a0 >>> (antiShift.toNat % 64))
  let u0 := a0 <<< (shift.toNat % 64)
  (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ u1) ** (.x7 ↦ᵣ u0) ** (.x10 ↦ᵣ (a0 >>> (antiShift.toNat % 64))) **
  (.x6 ↦ᵣ shift) ** (.x2 ↦ᵣ antiShift) **
  ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
  ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
  ((sp + signExtend12 4024) ↦ₘ u4) ** ((sp + signExtend12 4032) ↦ₘ u3) **
  ((sp + signExtend12 4040) ↦ₘ u2) ** ((sp + signExtend12 4048) ↦ₘ u1) **
  ((sp + signExtend12 4056) ↦ₘ u0)


-- @@ L1104-1124 verbatim
theorem normAFullPost_unfold {sp a0 a1 a2 a3 shift antiShift : Word} :
    normAFullPost sp a0 a1 a2 a3 shift antiShift =
      (let u4 := a3 >>> (antiShift.toNat % 64)
       let u3 := (a3 <<< (shift.toNat % 64)) ||| (a2 >>> (antiShift.toNat % 64))
       let u2 := (a2 <<< (shift.toNat % 64)) ||| (a1 >>> (antiShift.toNat % 64))
       let u1 := (a1 <<< (shift.toNat % 64)) ||| (a0 >>> (antiShift.toNat % 64))
       let u0 := a0 <<< (shift.toNat % 64)
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ u1) ** (.x7 ↦ᵣ u0) ** (.x10 ↦ᵣ (a0 >>> (antiShift.toNat % 64))) **
       (.x6 ↦ᵣ shift) ** (.x2 ↦ᵣ antiShift) **
       ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
       ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
       ((sp + signExtend12 4024) ↦ₘ u4) ** ((sp + signExtend12 4032) ↦ₘ u3) **
       ((sp + signExtend12 4040) ↦ₘ u2) ** ((sp + signExtend12 4048) ↦ₘ u1) **
       ((sp + signExtend12 4056) ↦ₘ u0)) := by
  delta normAFullPost; rfl

-- ============================================================================
-- Postcondition bundle for normB full spec (without extra normBPost atoms).
-- Used by divK_normB_full_spec_within, divK_normB_full_spec_within_noNop, and
-- mod_normB_full_spec_within to avoid statement let-chains in callers.
-- ============================================================================


-- @@ L1126-1137 verbatim
/-- Postcondition after the NormB block (21 instructions): shift, antiShift,
    and the four normalized limbs b'[0..3] written to memory. -/
@[irreducible]
def normBFullPost (sp b0 b1 b2 b3 shift antiShift : Word) : Assertion :=
  let b3' := (b3 <<< (shift.toNat % 64)) ||| (b2 >>> (antiShift.toNat % 64))
  let b2' := (b2 <<< (shift.toNat % 64)) ||| (b1 >>> (antiShift.toNat % 64))
  let b1' := (b1 <<< (shift.toNat % 64)) ||| (b0 >>> (antiShift.toNat % 64))
  let b0' := b0 <<< (shift.toNat % 64)
  (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ b0') ** (.x7 ↦ᵣ (b0 >>> (antiShift.toNat % 64))) **
  (.x6 ↦ᵣ shift) ** (.x2 ↦ᵣ antiShift) **
  ((sp + 32) ↦ₘ b0') ** ((sp + 40) ↦ₘ b1') **
  ((sp + 48) ↦ₘ b2') ** ((sp + 56) ↦ₘ b3')


-- @@ L1139-1169 verbatim
theorem normBFullPost_unfold {sp b0 b1 b2 b3 shift antiShift : Word} :
    normBFullPost sp b0 b1 b2 b3 shift antiShift =
      (let b3' := (b3 <<< (shift.toNat % 64)) ||| (b2 >>> (antiShift.toNat % 64))
       let b2' := (b2 <<< (shift.toNat % 64)) ||| (b1 >>> (antiShift.toNat % 64))
       let b1' := (b1 <<< (shift.toNat % 64)) ||| (b0 >>> (antiShift.toNat % 64))
       let b0' := b0 <<< (shift.toNat % 64)
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ b0') ** (.x7 ↦ᵣ (b0 >>> (antiShift.toNat % 64))) **
       (.x6 ↦ᵣ shift) ** (.x2 ↦ᵣ antiShift) **
       ((sp + 32) ↦ₘ b0') ** ((sp + 40) ↦ₘ b1') **
       ((sp + 48) ↦ₘ b2') ** ((sp + 56) ↦ₘ b3')) := by
  delta normBFullPost; rfl

-- ============================================================================
-- `se12_32`/`se12_40`/`se12_48`/`se12_56` were deleted by issue #493 / #494:
-- they now live canonically in `Rv64/AddrNorm.lean` as part of the
-- `rv64_addr` grindset. Consumers should `open EvmAsm.Rv64.AddrNorm
-- (se12_32 se12_40 se12_48 se12_56)` directly instead of relying on these
-- duplicates.
-- ============================================================================

-- ============================================================================
-- Shared `phB_off_*` address rewrites.
-- `base + phaseBOff` is the entry PC of `divK_phaseB` (and the structurally
-- identical block in `modCode`). `phB_off_k` rewrites `(base + phaseBOff) + k`
-- to `base + (phaseBOff + k)` with the constant folded on the RHS, so that
-- `simp only [phB_off_k]` closes the address-matching goal that appears when
-- a `divK_phaseB_*` sub-spec is embedded in `divCode base` / `modCode base`.
-- Consumers: PhaseAB.lean (DIV side), ModPhaseB.lean, ModPhaseBn3.lean,
-- ModPhaseBn21.lean (MOD side). Previously duplicated as `private phB_off_*`
-- in PhaseAB.lean and `mod_phB_off_28` in ModPhaseB.lean.
-- ============================================================================


-- @@ L1171-1177 verbatim
theorem phB_off_28 {base : Word} : (base + phaseBOff : Word) + 28 = base + phaseBInit2Off := by
  change (base + 32 : Word) + 28 = base + 60
  bv_omega

-- n=4 special: x1 = signExtend12 4 - 4 = 0, used by the shift-0 fast path
-- and the main `FullPathN4` path. Shared here so the two consumer files
-- (`FullPathN4.lean`, `FullPathN4Shift0.lean`) don't re-declare it privately.

-- @@ L1178-1185 verbatim
theorem x1_val_n4 : signExtend12 (4 : BitVec 12) - (4 : Word) = (0 : Word) := by decide

-- Shared `signExtend13`/`signExtend21` evaluations for these seven concrete
-- offsets (8, 16, 24, 172, 464, 1020 and 21_40) used to live here as
-- `theorem signExtend13_N`. They have been migrated to the repo-wide
-- `rv64_addr` grindset (GRIND.md Phase 3): see `EvmAsm/Rv64/AddrNorm.lean`
-- for `se13_N` / `se21_N`. Consumer files `open EvmAsm.Rv64.AddrNorm (…)`
-- and rewrite via `simp only [se13_N]` / `rw [se13_N]` directly.


-- @@ L1187-1190 verbatim
/-- When b ≠ 0, 0 < b in unsigned ordering (BitVec.ult). -/
theorem ult_zero_of_ne {b : Word} (h : b ≠ 0) : BitVec.ult 0 b := by
  unfold BitVec.ult; simp
  exact Nat.pos_of_ne_zero (fun h0 => h (BitVec.eq_of_toNat_eq h0))


-- @@ L1192-1192 verbatim
end EvmAsm.Evm64
