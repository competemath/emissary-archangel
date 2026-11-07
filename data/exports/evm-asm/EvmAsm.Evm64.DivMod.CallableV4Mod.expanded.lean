module

public import EvmAsm.Evm64.DivMod.Callable
public import EvmAsm.Evm64.DivMod.Spec.N3V4StackPre
public import EvmAsm.Evm64.DivMod.Spec.N3V4StackPreAnyX9


-- @@ L7-7 verbatim
public section


-- @@ L9-9 verbatim
namespace EvmAsm.Evm64


-- @@ L11-11 verbatim
open EvmAsm.Rv64


-- @@ L13-61 verbatim
open EvmAsm.Rv64.CodeReq in
theorem evm_mod_callable_code_v4_eq_ofProg (base : Word) :
    evm_mod_callable_code_v4 base = CodeReq.ofProg base evm_mod_callable_v4 := by
  unfold evm_mod_callable_code_v4 evm_mod_callable_v4 cc_ret_code
  simp only [unionAll_cons, unionAll_nil, union_empty_right]
  unfold seq
  unfold Program
  symm
  rw [ofProg_append]
  rw [show base + BitVec.ofNat 64 (4 * (divK_phaseA 1020).length) =
        base + phaseBOff by rw [divK_phaseA_len]; rfl]
  rw [ofProg_append]
  rw [show (base + phaseBOff) + BitVec.ofNat 64 (4 * divK_phaseB.length) =
        base + clzOff by rw [divK_phaseB_len]; bv_omega]
  rw [ofProg_append]
  rw [show (base + clzOff) + BitVec.ofNat 64 (4 * divK_clz.length) =
        base + phaseC2Off by rw [divK_clz_len]; bv_omega]
  rw [ofProg_append]
  rw [show (base + phaseC2Off) + BitVec.ofNat 64 (4 * (divK_phaseC2 172).length) =
        base + normBOff by rw [divK_phaseC2_len]; bv_omega]
  rw [ofProg_append]
  rw [show (base + normBOff) + BitVec.ofNat 64 (4 * divK_normB.length) =
        base + normAOff by rw [divK_normB_len]; bv_omega]
  rw [ofProg_append]
  rw [show (base + normAOff) + BitVec.ofNat 64 (4 * (divK_normA 40).length) =
        base + copyAUOff by rw [divK_normA_len]; bv_omega]
  rw [ofProg_append]
  rw [show (base + copyAUOff) + BitVec.ofNat 64 (4 * divK_copyAU.length) =
        base + loopSetupOff by rw [divK_copyAU_len]; bv_omega]
  rw [ofProg_append]
  rw [show (base + loopSetupOff) + BitVec.ofNat 64 (4 * (divK_loopSetup 464).length) =
        base + loopBodyOff by rw [divK_loopSetup_len]; bv_omega]
  rw [ofProg_append]
  rw [show (base + loopBodyOff) + BitVec.ofNat 64 (4 * (divK_loopBody 560 7736).length) =
        base + denormOff by rw [divK_loopBody_len]; bv_omega]
  rw [ofProg_append]
  rw [show (base + denormOff) + BitVec.ofNat 64 (4 * divK_denorm.length) =
        base + epilogueOff by rw [divK_denorm_len]; bv_omega]
  rw [ofProg_append]
  rw [show (base + epilogueOff) + BitVec.ofNat 64 (4 * (divK_mod_epilogue 24).length) =
        base + zeroPathOff by rw [divK_modEpilogue_len]; bv_omega]
  rw [ofProg_append]
  rw [show (base + zeroPathOff) + BitVec.ofNat 64 (4 * divK_zeroPath.length) =
        base + nopOff by rw [divK_zeroPath_len]; bv_omega]
  rw [ofProg_append]
  rw [show (base + nopOff) + BitVec.ofNat 64 (4 * cc_ret.length) =
        base + div128Off by
    show (base + nopOff) + BitVec.ofNat 64 (4 * 1) = base + div128Off
    bv_omega]


-- @@ L63-67 verbatim
private theorem callable_b0_mod_v4 {b : Word} :
    ∀ a i, (CodeReq.ofProg b (divK_phaseA 1020)) a = some i →
      (evm_mod_callable_code_v4 b) a = some i := by
  unfold evm_mod_callable_code_v4; simp only [CodeReq.unionAll_cons]
  exact CodeReq.union_mono_left

-- @@ L68-72 expanded
private theorem callable_b1_mod_v4 {b : Word} :
    ∀ a i,
      (CodeReq.ofProg (b + phaseBOff) divK_phaseB) a = some i →
        (evm_mod_callable_code_v4 b) a = some i :=
  by
  unfold evm_mod_callable_code_v4; simp only [CodeReq.unionAll_cons]
  apply
    CodeReq.mono_union_right
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


-- @@ L73-77 expanded
private theorem callable_b2_mod_v4 {b : Word} :
    ∀ a i,
      (CodeReq.ofProg (b + clzOff) divK_clz) a = some i → (evm_mod_callable_code_v4 b) a = some i :=
  by
  unfold evm_mod_callable_code_v4; simp only [CodeReq.unionAll_cons]
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
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


-- @@ L78-82 expanded
private theorem callable_b3_mod_v4 {b : Word} :
    ∀ a i,
      (CodeReq.ofProg (b + phaseC2Off) (divK_phaseC2 172)) a = some i →
        (evm_mod_callable_code_v4 b) a = some i :=
  by
  unfold evm_mod_callable_code_v4; simp only [CodeReq.unionAll_cons]
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
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


-- @@ L83-87 expanded
private theorem callable_b4_mod_v4 {b : Word} :
    ∀ a i,
      (CodeReq.ofProg (b + normBOff) divK_normB) a = some i →
        (evm_mod_callable_code_v4 b) a = some i :=
  by
  unfold evm_mod_callable_code_v4; simp only [CodeReq.unionAll_cons]
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
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


-- @@ L88-92 expanded
private theorem callable_b5_mod_v4 {b : Word} :
    ∀ a i,
      (CodeReq.ofProg (b + normAOff) (divK_normA 40)) a = some i →
        (evm_mod_callable_code_v4 b) a = some i :=
  by
  unfold evm_mod_callable_code_v4; simp only [CodeReq.unionAll_cons]
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
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


-- @@ L93-97 expanded
private theorem callable_b6_mod_v4 {b : Word} :
    ∀ a i,
      (CodeReq.ofProg (b + copyAUOff) divK_copyAU) a = some i →
        (evm_mod_callable_code_v4 b) a = some i :=
  by
  unfold evm_mod_callable_code_v4; simp only [CodeReq.unionAll_cons]
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
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


-- @@ L98-103 expanded
private theorem callable_b7_mod_v4 {b : Word} :
    ∀ a i,
      (CodeReq.ofProg (b + loopSetupOff) (divK_loopSetup 464)) a = some i →
        (evm_mod_callable_code_v4 b) a = some i :=
  by
  unfold evm_mod_callable_code_v4; simp only [CodeReq.unionAll_cons]
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
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


-- @@ L104-109 expanded
private theorem callable_b8_mod_v4 {b : Word} :
    ∀ a i,
      (CodeReq.ofProg (b + loopBodyOff) (divK_loopBody 560 7736)) a = some i →
        (evm_mod_callable_code_v4 b) a = some i :=
  by
  unfold evm_mod_callable_code_v4; simp only [CodeReq.unionAll_cons]
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
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


-- @@ L110-115 expanded
private theorem callable_b9_mod_v4 {b : Word} :
    ∀ a i,
      (CodeReq.ofProg (b + denormOff) divK_denorm) a = some i →
        (evm_mod_callable_code_v4 b) a = some i :=
  by
  unfold evm_mod_callable_code_v4; simp only [CodeReq.unionAll_cons]
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
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
  exact CodeReq.union_mono_left


-- @@ L116-121 expanded
private theorem callable_b10_mod_v4 {b : Word} :
    ∀ a i,
      (CodeReq.ofProg (b + epilogueOff) (divK_mod_epilogue 24)) a = some i →
        (evm_mod_callable_code_v4 b) a = some i :=
  by
  unfold evm_mod_callable_code_v4; simp only [CodeReq.unionAll_cons]
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
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
  exact CodeReq.union_mono_left


-- @@ L122-127 expanded
private theorem callable_b11_mod_v4 {b : Word} :
    ∀ a i,
      (CodeReq.ofProg (b + zeroPathOff) divK_zeroPath) a = some i →
        (evm_mod_callable_code_v4 b) a = some i :=
  by
  unfold evm_mod_callable_code_v4; simp only [CodeReq.unionAll_cons]
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
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
  exact CodeReq.union_mono_left


-- @@ L128-134 expanded
private theorem callable_b12_mod_v4 {b : Word} :
    ∀ a i, (cc_ret_code (b + nopOff)) a = some i → (evm_mod_callable_code_v4 b) a = some i :=
  by
  unfold evm_mod_callable_code_v4; simp only [CodeReq.unionAll_cons]
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_modEpilogue_len, cc_ret_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_modEpilogue_len, cc_ret_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_modEpilogue_len, cc_ret_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_modEpilogue_len, cc_ret_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_modEpilogue_len, cc_ret_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_modEpilogue_len, cc_ret_len] at hk1 hk2
          bv_omega))
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_modEpilogue_len, cc_ret_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_modEpilogue_len, cc_ret_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_modEpilogue_len, cc_ret_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_modEpilogue_len, cc_ret_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_modEpilogue_len, cc_ret_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_modEpilogue_len, cc_ret_len] at hk1 hk2
          bv_omega))
  exact CodeReq.union_mono_left


-- @@ L135-140 expanded
private theorem callable_b13_mod_v4 {b : Word} :
    ∀ a i,
      (CodeReq.ofProg (b + div128Off) divK_div128_v4) a = some i →
        (evm_mod_callable_code_v4 b) a = some i :=
  by
  unfold evm_mod_callable_code_v4; simp only [CodeReq.unionAll_cons, cc_ret_code]
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
            divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len,
            divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len, divK_nop_len, divK_div128_len,
            divK_div128_v2_len, divK_div128_v4_len, divK_div128_v5_len,
            divK_modEpilogue_len] at hk1 hk2
          bv_omega));
  apply
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
            divK_div128_v2_len, divK_div128_v4_len, divK_modEpilogue_len, cc_ret_len] at hk1 hk2
          bv_omega));
  exact CodeReq.union_mono_left


-- @@ L142-148 verbatim
theorem evm_mod_callable_code_v4_ret_sub {base : Word} :
    ∀ a i, (CodeReq.singleton (base + nopOff) (.JALR .x0 .x1 0)) a = some i →
      (evm_mod_callable_code_v4 base) a = some i := by
  intro a i h
  apply callable_b12_mod_v4
  unfold cc_ret_code cc_ret
  exact h


-- @@ L150-166 verbatim
theorem sharedDivModCodeNoNop_v4_sub_mod_callable_code_v4 {base : Word} :
    ∀ a i, (sharedDivModCodeNoNop_v4 base) a = some i →
           (evm_mod_callable_code_v4 base) a = some i := by
  unfold sharedDivModCodeNoNop_v4; simp only [CodeReq.unionAll_cons]
  exact CodeReq.union_split_mono callable_b0_mod_v4
    (CodeReq.union_split_mono callable_b1_mod_v4
    (CodeReq.union_split_mono callable_b2_mod_v4
    (CodeReq.union_split_mono callable_b3_mod_v4
    (CodeReq.union_split_mono callable_b4_mod_v4
    (CodeReq.union_split_mono callable_b5_mod_v4
    (CodeReq.union_split_mono callable_b6_mod_v4
    (CodeReq.union_split_mono callable_b7_mod_v4
    (CodeReq.union_split_mono callable_b8_mod_v4
    (CodeReq.union_split_mono callable_b9_mod_v4
    (CodeReq.union_split_mono callable_b11_mod_v4
    (CodeReq.union_split_mono callable_b13_mod_v4
    (fun _ _ h => by simp [CodeReq.unionAll_nil, CodeReq.empty] at h))))))))))))


-- @@ L168-187 verbatim
/-- `modCode_noNop_v4 ⊆ evm_mod_callable_code_v4`: the callable MOD code is
    the no-NOP MOD body plus the return slot. -/
theorem modCode_noNop_v4_sub_mod_callable_code_v4 {base : Word} :
    ∀ a i, (modCode_noNop_v4 base) a = some i →
           (evm_mod_callable_code_v4 base) a = some i := by
  unfold modCode_noNop_v4; simp only [CodeReq.unionAll_cons]
  exact CodeReq.union_split_mono callable_b0_mod_v4
    (CodeReq.union_split_mono callable_b1_mod_v4
    (CodeReq.union_split_mono callable_b2_mod_v4
    (CodeReq.union_split_mono callable_b3_mod_v4
    (CodeReq.union_split_mono callable_b4_mod_v4
    (CodeReq.union_split_mono callable_b5_mod_v4
    (CodeReq.union_split_mono callable_b6_mod_v4
    (CodeReq.union_split_mono callable_b7_mod_v4
    (CodeReq.union_split_mono callable_b8_mod_v4
    (CodeReq.union_split_mono callable_b9_mod_v4
    (CodeReq.union_split_mono callable_b10_mod_v4
    (CodeReq.union_split_mono callable_b11_mod_v4
    (CodeReq.union_split_mono callable_b13_mod_v4
    (fun _ _ h => by simp [CodeReq.unionAll_nil, CodeReq.empty] at h)))))))))))))


-- @@ L189-218 verbatim
theorem evm_mod_callable_v4_spec_from_noNop_preserving_x1 (sp base raVal : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 : Word)
    (branch : ModStackSpecCase base a b)
    (hStack :
      cpsTripleWithin unifiedDivBound base (base + nopOff) (sharedDivModCodeNoNop_v4 base)
        (divModStackDispatchPreNoX1 sp a b
          branch.x1 raVal branch.x2 v5 v6 v7 v10 v11
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0)
        (modStackDispatchPostCallable sp a b ** (.x1 ↦ᵣ raVal))) :
    cpsTripleWithin (unifiedDivBound + 1) base (raVal &&& ~~~1)
      (evm_mod_callable_code_v4 base)
      (divModStackDispatchPreNoX1 sp a b
        branch.x1 raVal branch.x2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0)
      (modStackDispatchPostCallable sp a b ** (.x1 ↦ᵣ raVal)) := by
  have hpcFreePost : (modStackDispatchPostCallable sp a b).pcFree :=
    modStackDispatchPostCallable_pcFree sp a b
  have hStackCall :=
    cpsTripleWithin_extend_code
      (hmono := sharedDivModCodeNoNop_v4_sub_mod_callable_code_v4) hStack
  have hRet :=
    cpsTripleWithin_extend_code (hmono := evm_mod_callable_code_v4_ret_sub (base := base))
      (ret_spec_within' (base + nopOff) raVal)
  have hRetFramed :=
    cpsTripleWithin_frameL (modStackDispatchPostCallable sp a b) hpcFreePost hRet
  exact cpsTripleWithin_seq_same_cr hStackCall hRetFramed


-- @@ L220-245 verbatim
theorem evm_mod_callable_v4_spec_from_noNop_preserving_x1_framed
    {F : Assertion} [Assertion.PCFree F] (sp base raVal : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 : Word)
    (branch : ModStackSpecCase base a b)
    (hStack :
      cpsTripleWithin unifiedDivBound base (base + nopOff) (sharedDivModCodeNoNop_v4 base)
        (divModStackDispatchPreNoX1 sp a b
          branch.x1 raVal branch.x2 v5 v6 v7 v10 v11
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0)
        (modStackDispatchPostCallable sp a b ** (.x1 ↦ᵣ raVal))) :
    cpsTripleWithin (unifiedDivBound + 1) base (raVal &&& ~~~1)
      (evm_mod_callable_code_v4 base)
      (divModStackDispatchPreNoX1 sp a b
        branch.x1 raVal branch.x2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 ** F)
      ((modStackDispatchPostCallable sp a b ** (.x1 ↦ᵣ raVal)) ** F) := by
  exact
    cpsTripleWithin_frameR F (by pcFree)
      (evm_mod_callable_v4_spec_from_noNop_preserving_x1
        sp base raVal a b v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        nMem shiftMem jMem retMem dMem dloMem scratchUn0 branch hStack)


-- @@ L247-279 verbatim
/-- v4 MOD callable wrapper with exact `x1` and no `x9` frame.

This is the return/`cc_ret` adapter only: callers supply a v4 no-NOP stack
proof already shaped for `divModStackDispatchPreCallable`. -/
theorem evm_mod_callable_v4_spec_from_noNop_preserving_x1_noX9
    (sp base raVal : Word)
    (a b : EvmWord) (v2 v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 : Word)
    (hStack :
      cpsTripleWithin unifiedDivBound base (base + nopOff) (sharedDivModCodeNoNop_v4 base)
        (divModStackDispatchPreCallable sp a b
          raVal v2 v5 v6 v7 v10 v11
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0)
        (modStackDispatchPostCallable sp a b ** (.x1 ↦ᵣ raVal))) :
    cpsTripleWithin (unifiedDivBound + 1) base (raVal &&& ~~~1)
      (evm_mod_callable_code_v4 base)
      (divModStackDispatchPreCallable sp a b
        raVal v2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0)
      (modStackDispatchPostCallable sp a b ** (.x1 ↦ᵣ raVal)) := by
  have hStackCall :=
    cpsTripleWithin_extend_code
      (hmono := sharedDivModCodeNoNop_v4_sub_mod_callable_code_v4) hStack
  have hRet :=
    cpsTripleWithin_extend_code (hmono := evm_mod_callable_code_v4_ret_sub (base := base))
      (ret_spec_within' (base + nopOff) raVal)
  have hRetFramed :=
    cpsTripleWithin_frameL (modStackDispatchPostCallable sp a b)
      (modStackDispatchPostCallable_pcFree sp a b) hRet
  exact cpsTripleWithin_seq_same_cr hStackCall hRetFramed


-- @@ L281-312 verbatim
/-- Like `evm_mod_callable_v4_spec_from_noNop_preserving_x1_noX9` but the
    body proof is over `modCode_noNop_v4` (includes the MOD epilogue).
    Used when the caller has only `modCode_noNop_v4` available (e.g., SMOD). -/
theorem evm_mod_callable_v4_spec_from_modCode_noNop_noX9
    (sp base raVal : Word)
    (a b : EvmWord) (v2 v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 : Word)
    (hStack :
      cpsTripleWithin unifiedDivBound base (base + nopOff) (modCode_noNop_v4 base)
        (divModStackDispatchPreCallable sp a b
          raVal v2 v5 v6 v7 v10 v11
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0)
        (modStackDispatchPostCallable sp a b ** (.x1 ↦ᵣ raVal))) :
    cpsTripleWithin (unifiedDivBound + 1) base (raVal &&& ~~~1)
      (evm_mod_callable_code_v4 base)
      (divModStackDispatchPreCallable sp a b
        raVal v2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0)
      (modStackDispatchPostCallable sp a b ** (.x1 ↦ᵣ raVal)) := by
  have hStackCall :=
    cpsTripleWithin_extend_code
      (hmono := modCode_noNop_v4_sub_mod_callable_code_v4) hStack
  have hRet :=
    cpsTripleWithin_extend_code (hmono := evm_mod_callable_code_v4_ret_sub (base := base))
      (ret_spec_within' (base + nopOff) raVal)
  have hRetFramed :=
    cpsTripleWithin_frameL (modStackDispatchPostCallable sp a b)
      (modStackDispatchPostCallable_pcFree sp a b) hRet
  exact cpsTripleWithin_seq_same_cr hStackCall hRetFramed


-- @@ L314-335 verbatim
/-- v4 zero-divisor MOD callable wrapper with exact `x1` and no `x9` frame. -/
theorem evm_mod_callable_bzero_v4_preserving_x1_noX9_spec (sp base raVal : Word)
    (a b : EvmWord) (v2 v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 : Word)
    (hbz : b = 0) :
    cpsTripleWithin (unifiedDivBound + 1) base (raVal &&& ~~~1)
      (evm_mod_callable_code_v4 base)
      (divModStackDispatchPreCallable sp a b
        raVal v2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0)
      (modStackDispatchPostCallable sp a b ** (.x1 ↦ᵣ raVal)) := by
  exact
    evm_mod_callable_v4_spec_from_noNop_preserving_x1_noX9
      sp base raVal a b v2 v5 v6 v7 v10 v11
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      nMem shiftMem jMem retMem dMem dloMem scratchUn0
      (evm_mod_bzero_stack_spec_within_dispatch_noNop_v4_callable_x1_uni
        sp base a b raVal v2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        nMem shiftMem jMem retMem dMem dloMem scratchUn0 hbz)


-- @@ L337-385 verbatim
/-- v4 callable MOD wrapper for `modCode_noNop_v4` body proofs that transform
    an explicit PC-free frame and return a possibly different exact `x9`
    value. -/
theorem evm_mod_callable_v4_spec_from_modCode_noNop_preserving_x1_x9out_body_frame_transform
    {FPre FPost : Assertion} [Assertion.PCFree FPost]
    (sp base x9In x9Out raVal : Word) (a b : EvmWord)
    (v2 v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 : Word)
    (hStack :
      cpsTripleWithin unifiedDivBound base (base + nopOff) (modCode_noNop_v4 base)
        (divModStackDispatchPreNoX1 sp a b
          x9In raVal v2 v5 v6 v7 v10 v11
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0 ** FPre)
        (((modStackDispatchPostCallable sp a b ** (.x1 ↦ᵣ raVal)) **
          (.x9 ↦ᵣ x9Out)) ** FPost)) :
    cpsTripleWithin (unifiedDivBound + 1) base (raVal &&& ~~~1)
      (evm_mod_callable_code_v4 base)
      (divModStackDispatchPreNoX1 sp a b
        x9In raVal v2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 ** FPre)
      (((modStackDispatchPostCallable sp a b ** (.x1 ↦ᵣ raVal)) **
        (.x9 ↦ᵣ x9Out)) ** FPost) := by
  have hStackCall :=
    cpsTripleWithin_extend_code
      (hmono := modCode_noNop_v4_sub_mod_callable_code_v4) hStack
  have hStackForRet :
      cpsTripleWithin unifiedDivBound base (base + nopOff) (evm_mod_callable_code_v4 base)
        (divModStackDispatchPreNoX1 sp a b
          x9In raVal v2 v5 v6 v7 v10 v11
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0 ** FPre)
        (((modStackDispatchPostCallable sp a b ** (.x9 ↦ᵣ x9Out)) ** FPost) **
          (.x1 ↦ᵣ raVal)) :=
    cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hp => by xperm_hyp hp) hStackCall
  have hRet :=
    cpsTripleWithin_extend_code (hmono := evm_mod_callable_code_v4_ret_sub (base := base))
      (ret_spec_within' (base + nopOff) raVal)
  have hRetFramed :=
    cpsTripleWithin_frameL ((modStackDispatchPostCallable sp a b ** (.x9 ↦ᵣ x9Out)) ** FPost)
      (by
        rw [modStackDispatchPostCallable_unfold, divScratchOwnCallNoX1_unfold,
          divScratchOwn_unfold]
        pcFree)
      hRet
  exact cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hp => by xperm_hyp hp)
    (cpsTripleWithin_seq_same_cr hStackForRet hRetFramed)


-- @@ L387-414 verbatim
/-- Named-post variant of the v4 callable MOD wrapper for `modCode_noNop_v4`
    body proofs that transform an explicit PC-free frame and return a possibly
    different exact `x9` value. -/
theorem evm_mod_callable_v4_spec_from_modCode_noNop_exact_frame_x9out_body_frame_transform
    {FPre FPost : Assertion} [Assertion.PCFree FPost]
    (sp base x9In x9Out raVal : Word) (a b : EvmWord)
    (v2 v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 : Word)
    (hStack :
      cpsTripleWithin unifiedDivBound base (base + nopOff) (modCode_noNop_v4 base)
        (divModStackDispatchPreNoX1 sp a b
          x9In raVal v2 v5 v6 v7 v10 v11
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0 ** FPre)
        (modStackDispatchPostCallableExactFrame sp a b raVal x9Out ** FPost)) :
    cpsTripleWithin (unifiedDivBound + 1) base (raVal &&& ~~~1)
      (evm_mod_callable_code_v4 base)
      (divModStackDispatchPreNoX1 sp a b
        x9In raVal v2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 ** FPre)
      (modStackDispatchPostCallableExactFrame sp a b raVal x9Out ** FPost) := by
  rw [modStackDispatchPostCallableExactFrame_unfold] at hStack ⊢
  exact evm_mod_callable_v4_spec_from_modCode_noNop_preserving_x1_x9out_body_frame_transform
    sp base x9In x9Out raVal a b v2 v5 v6 v7 v10 v11
    q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratchUn0 hStack


-- @@ L416-553 verbatim
/-- Legacy callable-program N3 v4 MOD surface from the no-NOP stack bridge,
    with the v4 trial-call scratch cell framed through the callable return.
    This compatibility wrapper still exposes the raw `fullDivN3Carry2NzV4`
    package; new v4 MOD work should use selected/reachable carry surfaces. -/
theorem evm_mod_callable_v4_n3_stack_pre_to_callable_post_scratch_word
    (sp base : Word) (a b : EvmWord)
    (v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (raVal : Word)
    (hbnz : b ≠ 0)
    (hb3z : b.getLimbN 3 = 0) (hb2nz : b.getLimbN 2 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 2)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu_1 : bltu_1 =
      BitVec.ult (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.2.2
        (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.2.1)
    (hbltu_0 : bltu_0 =
      match bltu_1, hbltu_1 with
      | false, _ =>
        BitVec.ult
          (iterN3Max
            (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).1
            (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.1
            (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.2.1
            (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.2.2
            (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.1
            (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.1
            (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.2.1
            (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.2.2
            (0 : Word)).2.2.2.1
          (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
            (b.getLimbN 2) (b.getLimbN 3)).2.2.1
      | true, _ =>
        BitVec.ult
          (iterWithDoubleAddback
            (divKTrialCallV4QHat
              (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
                (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.2.2
              (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
                (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.2.1
              (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
                (b.getLimbN 2) (b.getLimbN 3)).2.2.1)
            (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).1
            (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.1
            (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.2.1
            (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.2.2
            (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.1
            (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.1
            (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.2.1
            (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.2.2
            (0 : Word)).2.2.2.1
          (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
            (b.getLimbN 2) (b.getLimbN 3)).2.2.1)
    (hcarry2 : fullDivN3Carry2NzV4
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3))
    (hmodWord : fullModN3RemainderWordV4 bltu_1 bltu_0
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) =
        EvmWord.mod a b) :
    cpsTripleWithin (unifiedDivBound + 1) base (raVal &&& ~~~1)
      (evm_mod_callable_code_v4 base)
      (divModStackDispatchPreNoX1 sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word)) raVal
        ((clzResult (b.getLimbN 2)).2 >>> (63 : Nat))
        v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (modStackDispatchPostCallableExactFrame sp a b raVal
        (signExtend12 4095 : Word) **
       ((sp + signExtend12 3936) ↦ₘ
        fullDivN3ScratchMemV4 bltu_1 bltu_0
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
          scratchMem)) := by
  have hBody :=
    cpsTripleWithin_weaken
      (fun _ hp => hp)
      (fun h hq =>
        fullModN3UnifiedPostNoX1V4_frame_to_modStackDispatchPostCallableExactFrame_scratch_word
          bltu_1 bltu_0 sp base a b
          retMem dMem dloMem scratchUn0 scratchMem raVal hmodWord h hq)
      (evm_mod_n3_stack_pre_to_unified_post_v4_noNop
        sp base a b v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem raVal
        hbnz hb3z hb2nz hshift_nz halign hbltu_1 hbltu_0 hcarry2)
  have hBodyUnified :
      cpsTripleWithin unifiedDivBound base (base + nopOff) (modCode_noNop_v4 base)
        (divModStackDispatchPreNoX1 sp a b
          (signExtend12 (4 : BitVec 12) - (4 : Word)) raVal
          ((clzResult (b.getLimbN 2)).2 >>> (63 : Nat))
          v5 v6 v7 v10 v11Old
          q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
         ((sp + signExtend12 3936) ↦ₘ scratchMem))
        (modStackDispatchPostCallableExactFrame sp a b raVal
          (signExtend12 4095 : Word) **
         ((sp + signExtend12 3936) ↦ₘ
          fullDivN3ScratchMemV4 bltu_1 bltu_0
            (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
            (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
            scratchMem)) :=
    cpsTripleWithin_mono_nSteps (by unfold unifiedDivBound; decide) hBody
  exact
    evm_mod_callable_v4_spec_from_modCode_noNop_exact_frame_x9out_body_frame_transform
      (FPre := ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (FPost := ((sp + signExtend12 3936) ↦ₘ
        fullDivN3ScratchMemV4 bltu_1 bltu_0
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
          scratchMem))
      sp base (signExtend12 (4 : BitVec 12) - (4 : Word))
      (signExtend12 4095 : Word) raVal a b
      ((clzResult (b.getLimbN 2)).2 >>> (63 : Nat))
      v5 v6 v7 v10 v11Old
      q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
      nMem shiftMem jMem retMem dMem dloMem scratchUn0 hBodyUnified


-- @@ L555-695 verbatim
/-- Legacy generalization of
    `evm_mod_callable_v4_n3_stack_pre_to_callable_post_scratch_word` allowing
    any initial `x9` value in the precondition. The n=3 loop setup overwrites
    `x9 ← 4 - 3 = 1` before the loop body, so the initial value is irrelevant
    to correctness. This compatibility wrapper still exposes the raw
    `fullDivN3Carry2NzV4` package; new v4 MOD work should use
    selected/reachable carry surfaces. -/
theorem evm_mod_callable_v4_n3_stack_pre_to_callable_post_scratch_word_anyX9
    (x9Init : Word) (sp base : Word) (a b : EvmWord)
    (v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (raVal : Word)
    (hbnz : b ≠ 0)
    (hb3z : b.getLimbN 3 = 0) (hb2nz : b.getLimbN 2 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 2)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu_1 : bltu_1 =
      BitVec.ult (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.2.2
        (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.2.1)
    (hbltu_0 : bltu_0 =
      match bltu_1, hbltu_1 with
      | false, _ =>
        BitVec.ult
          (iterN3Max
            (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).1
            (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.1
            (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.2.1
            (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.2.2
            (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.1
            (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.1
            (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.2.1
            (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.2.2
            (0 : Word)).2.2.2.1
          (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
            (b.getLimbN 2) (b.getLimbN 3)).2.2.1
      | true, _ =>
        BitVec.ult
          (iterWithDoubleAddback
            (divKTrialCallV4QHat
              (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
                (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.2.2
              (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
                (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.2.1
              (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
                (b.getLimbN 2) (b.getLimbN 3)).2.2.1)
            (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).1
            (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.1
            (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.2.1
            (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.2.2
            (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.1
            (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.1
            (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.2.1
            (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.2.2
            (0 : Word)).2.2.2.1
          (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
            (b.getLimbN 2) (b.getLimbN 3)).2.2.1)
    (hcarry2 : fullDivN3Carry2NzV4
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3))
    (hmodWord : fullModN3RemainderWordV4 bltu_1 bltu_0
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) =
        EvmWord.mod a b) :
    cpsTripleWithin (unifiedDivBound + 1) base (raVal &&& ~~~1)
      (evm_mod_callable_code_v4 base)
      (divModStackDispatchPreNoX1 sp a b
        x9Init raVal
        ((clzResult (b.getLimbN 2)).2 >>> (63 : Nat))
        v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (modStackDispatchPostCallableExactFrame sp a b raVal
        (signExtend12 4095 : Word) **
       ((sp + signExtend12 3936) ↦ₘ
        fullDivN3ScratchMemV4 bltu_1 bltu_0
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
          scratchMem)) := by
  have hBody :=
    cpsTripleWithin_weaken
      (fun _ hp => hp)
      (fun h hq =>
        fullModN3UnifiedPostNoX1V4_frame_to_modStackDispatchPostCallableExactFrame_scratch_word
          bltu_1 bltu_0 sp base a b
          retMem dMem dloMem scratchUn0 scratchMem raVal hmodWord h hq)
      (evm_mod_n3_stack_pre_to_unified_post_v4_noNop_anyX9
        sp base x9Init a b v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem raVal
        hbnz hb3z hb2nz hshift_nz halign hbltu_1 hbltu_0 hcarry2)
  have hBodyUnified :
      cpsTripleWithin unifiedDivBound base (base + nopOff) (modCode_noNop_v4 base)
        (divModStackDispatchPreNoX1 sp a b
          x9Init raVal
          ((clzResult (b.getLimbN 2)).2 >>> (63 : Nat))
          v5 v6 v7 v10 v11Old
          q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
         ((sp + signExtend12 3936) ↦ₘ scratchMem))
        (modStackDispatchPostCallableExactFrame sp a b raVal
          (signExtend12 4095 : Word) **
         ((sp + signExtend12 3936) ↦ₘ
          fullDivN3ScratchMemV4 bltu_1 bltu_0
            (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
            (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
            scratchMem)) :=
    cpsTripleWithin_mono_nSteps (by unfold unifiedDivBound; decide) hBody
  exact
    evm_mod_callable_v4_spec_from_modCode_noNop_exact_frame_x9out_body_frame_transform
      (FPre := ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (FPost := ((sp + signExtend12 3936) ↦ₘ
        fullDivN3ScratchMemV4 bltu_1 bltu_0
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
          scratchMem))
      sp base x9Init
      (signExtend12 4095 : Word) raVal a b
      ((clzResult (b.getLimbN 2)).2 >>> (63 : Nat))
      v5 v6 v7 v10 v11Old
      q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
      nMem shiftMem jMem retMem dMem dloMem scratchUn0 hBodyUnified


-- @@ L697-734 verbatim
/-- Callable-program N3 v4 MOD surface from the bundled MOD path predicate. -/
theorem evm_mod_callable_v4_n3_stack_pre_to_callable_post_scratch_of_mod_path_conditions
    (sp base : Word) (a b : EvmWord)
    (v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (raVal : Word)
    (hbnz : b ≠ 0)
    (hb3z : b.getLimbN 3 = 0) (hb2nz : b.getLimbN 2 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 2)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hpath : fullModN3PathConditionsWordV4 bltu_1 bltu_0 a b) :
    cpsTripleWithin (unifiedDivBound + 1) base (raVal &&& ~~~1)
      (evm_mod_callable_code_v4 base)
      (divModStackDispatchPreNoX1 sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word)) raVal
        ((clzResult (b.getLimbN 2)).2 >>> (63 : Nat))
        v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (modStackDispatchPostCallableExactFrame sp a b raVal
        (signExtend12 4095 : Word) **
       ((sp + signExtend12 3936) ↦ₘ
        fullDivN3ScratchMemV4 bltu_1 bltu_0
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
          scratchMem)) := by
  obtain ⟨hdivPath, hmodWord⟩ := hpath
  obtain ⟨hbltu_1, hbltu_0, hcarry2, _, _⟩ := hdivPath
  exact evm_mod_callable_v4_n3_stack_pre_to_callable_post_scratch_word
    sp base a b v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem raVal
    hbnz hb3z hb2nz hshift_nz halign hbltu_1
    (by cases bltu_1 <;> simpa [isTrialN3V4_j0] using hbltu_0)
    hcarry2 hmodWord


-- @@ L736-776 verbatim
/-- Callable-program N3 v4 MOD surface from the bundled `val256` MOD path
predicate. This is equivalent to
`evm_mod_callable_v4_n3_stack_pre_to_callable_post_scratch_of_mod_path_conditions`,
but exposes the remaining MOD proof obligation in the arithmetic form expected
from the normalized-remainder closure. -/
theorem evm_mod_callable_v4_n3_stack_pre_to_callable_post_scratch_of_val256_path_conditions
    (sp base : Word) (a b : EvmWord)
    (v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (raVal : Word)
    (hbnz : b ≠ 0)
    (hb3z : b.getLimbN 3 = 0) (hb2nz : b.getLimbN 2 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 2)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hpath : fullModN3PathConditionsVal256V4 bltu_1 bltu_0 a b) :
    cpsTripleWithin (unifiedDivBound + 1) base (raVal &&& ~~~1)
      (evm_mod_callable_code_v4 base)
      (divModStackDispatchPreNoX1 sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word)) raVal
        ((clzResult (b.getLimbN 2)).2 >>> (63 : Nat))
        v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (modStackDispatchPostCallableExactFrame sp a b raVal
        (signExtend12 4095 : Word) **
       ((sp + signExtend12 3936) ↦ₘ
        fullDivN3ScratchMemV4 bltu_1 bltu_0
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
          scratchMem)) := by
  have hbnz' : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 ||| b.getLimbN 3 ≠ 0 :=
    (EvmWord.ne_zero_iff_getLimbN_or).mp hbnz
  exact evm_mod_callable_v4_n3_stack_pre_to_callable_post_scratch_of_mod_path_conditions
    sp base a b v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem raVal
    hbnz hb3z hb2nz hshift_nz halign
    (fullModN3PathConditionsWordV4_of_val256 bltu_1 bltu_0 a b hbnz' hpath)


-- @@ L778-817 verbatim
/-- Callable-program N3 v4 MOD surface from the normalized scaled-remainder
path predicate. This is the closest caller-facing wrapper to the remaining
loop arithmetic obligation. -/
theorem evm_mod_callable_v4_n3_stack_pre_to_callable_post_scratch_of_scaled_path_conditions
    (sp base : Word) (a b : EvmWord)
    (v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (raVal : Word)
    (hbnz : b ≠ 0)
    (hb3z : b.getLimbN 3 = 0) (hb2nz : b.getLimbN 2 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 2)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hpath : fullModN3PathConditionsScaledV4 bltu_1 bltu_0 a b) :
    cpsTripleWithin (unifiedDivBound + 1) base (raVal &&& ~~~1)
      (evm_mod_callable_code_v4 base)
      (divModStackDispatchPreNoX1 sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word)) raVal
        ((clzResult (b.getLimbN 2)).2 >>> (63 : Nat))
        v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (modStackDispatchPostCallableExactFrame sp a b raVal
        (signExtend12 4095 : Word) **
       ((sp + signExtend12 3936) ↦ₘ
        fullDivN3ScratchMemV4 bltu_1 bltu_0
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
          scratchMem)) := by
  have hshift_nz' : fullDivN3Shift (b.getLimbN 2) ≠ 0 := by
    rw [fullDivN3Shift]
    exact hshift_nz
  exact evm_mod_callable_v4_n3_stack_pre_to_callable_post_scratch_of_val256_path_conditions
    sp base a b v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem raVal
    hbnz hb3z hb2nz hshift_nz halign
    (fullModN3PathConditionsVal256V4_of_scaled bltu_1 bltu_0 a b hshift_nz' hpath)


-- @@ L819-856 verbatim
/-- Callable-program N3 v4 MOD surface from the normalized Euclidean path
predicate. This is the public wrapper for the next loop-arithmetic closure:
prove the normalized mulsub equation and remainder bound, then the existing
scaled/val256/word bridge completes the stack-level MOD post. -/
theorem evm_mod_callable_v4_n3_stack_pre_to_callable_post_scratch_of_normalized_path_conditions
    (sp base : Word) (a b : EvmWord)
    (v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (raVal : Word)
    (hbnz : b ≠ 0)
    (hb3z : b.getLimbN 3 = 0) (hb2nz : b.getLimbN 2 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 2)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hpath : fullModN3PathConditionsNormalizedV4 bltu_1 bltu_0 a b) :
    cpsTripleWithin (unifiedDivBound + 1) base (raVal &&& ~~~1)
      (evm_mod_callable_code_v4 base)
      (divModStackDispatchPreNoX1 sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word)) raVal
        ((clzResult (b.getLimbN 2)).2 >>> (63 : Nat))
        v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (modStackDispatchPostCallableExactFrame sp a b raVal
        (signExtend12 4095 : Word) **
       ((sp + signExtend12 3936) ↦ₘ
        fullDivN3ScratchMemV4 bltu_1 bltu_0
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
          scratchMem)) := by
  exact evm_mod_callable_v4_n3_stack_pre_to_callable_post_scratch_of_scaled_path_conditions
    sp base a b v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem raVal
    hbnz hb3z hb2nz hshift_nz halign
    (fullModN3PathConditionsScaledV4_of_normalized bltu_1 bltu_0 a b hpath)


-- @@ L858-897 verbatim
/-- Callable-program N3 v4 MOD surface from the remaining normalized mulsub
equation. The normalized remainder bound follows from the existing N3 DIV path
overestimate, so this wrapper leaves only the loop conservation equation as
the explicit MOD arithmetic obligation. -/
theorem evm_mod_callable_v4_n3_stack_pre_to_callable_post_scratch_of_normalized_mulsub
    (sp base : Word) (a b : EvmWord)
    (v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (raVal : Word)
    (hbnz : b ≠ 0)
    (hb3z : b.getLimbN 3 = 0) (hb2nz : b.getLimbN 2 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 2)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hdivPath : fullDivN3PathConditionsWordV4 bltu_1 bltu_0 a b)
    (hmulsub : fullDivN3NormalizedMulSubEqV4 bltu_1 bltu_0 a b) :
    cpsTripleWithin (unifiedDivBound + 1) base (raVal &&& ~~~1)
      (evm_mod_callable_code_v4 base)
      (divModStackDispatchPreNoX1 sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word)) raVal
        ((clzResult (b.getLimbN 2)).2 >>> (63 : Nat))
        v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (modStackDispatchPostCallableExactFrame sp a b raVal
        (signExtend12 4095 : Word) **
       ((sp + signExtend12 3936) ↦ₘ
        fullDivN3ScratchMemV4 bltu_1 bltu_0
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
          scratchMem)) := by
  exact evm_mod_callable_v4_n3_stack_pre_to_callable_post_scratch_of_normalized_path_conditions
    sp base a b v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem raVal
    hbnz hb3z hb2nz hshift_nz halign
    (fullModN3PathConditionsNormalizedV4_of_mulsub
      bltu_1 bltu_0 a b hbnz hdivPath hmulsub)


-- @@ L899-938 verbatim
/-- Callable-program N3 v4 MOD surface from raw normalized conservation plus
the final overflow-carry-zero fact. The conservation equation is the direct
shape produced by chaining the two `iterWithDoubleAddback` conservation lemmas. -/
theorem evm_mod_callable_v4_n3_stack_pre_to_callable_post_scratch_of_normalized_conservation
    (sp base : Word) (a b : EvmWord)
    (v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (raVal : Word)
    (hbnz : b ≠ 0)
    (hb3z : b.getLimbN 3 = 0) (hb2nz : b.getLimbN 2 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 2)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hdivPath : fullDivN3PathConditionsWordV4 bltu_1 bltu_0 a b)
    (hcons : fullDivN3NormalizedConservationV4 bltu_1 bltu_0 a b)
    (hcarry_zero : fullDivN3FinalCarryZeroV4 bltu_1 bltu_0 a b) :
    cpsTripleWithin (unifiedDivBound + 1) base (raVal &&& ~~~1)
      (evm_mod_callable_code_v4 base)
      (divModStackDispatchPreNoX1 sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word)) raVal
        ((clzResult (b.getLimbN 2)).2 >>> (63 : Nat))
        v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (modStackDispatchPostCallableExactFrame sp a b raVal
        (signExtend12 4095 : Word) **
       ((sp + signExtend12 3936) ↦ₘ
        fullDivN3ScratchMemV4 bltu_1 bltu_0
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
          scratchMem)) := by
  exact evm_mod_callable_v4_n3_stack_pre_to_callable_post_scratch_of_normalized_mulsub
    sp base a b v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem raVal
    hbnz hb3z hb2nz hshift_nz halign hdivPath
    (fullDivN3NormalizedMulSubEqV4_of_conservation
      bltu_1 bltu_0 a b hcons hcarry_zero)


-- @@ L940-979 verbatim
/-- Callable-program N3 v4 MOD surface from raw normalized conservation. The
final overflow-carry-zero fact follows from the N3 quotient overestimate and
the `b3 = 0` branch invariant, so this wrapper leaves only raw conservation
as the MOD arithmetic obligation. -/
theorem evm_mod_callable_v4_n3_stack_pre_to_callable_post_scratch_of_conservation_path
    (sp base : Word) (a b : EvmWord)
    (v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (raVal : Word)
    (hbnz : b ≠ 0)
    (hb3z : b.getLimbN 3 = 0) (hb2nz : b.getLimbN 2 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 2)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hdivPath : fullDivN3PathConditionsWordV4 bltu_1 bltu_0 a b)
    (hcons : fullDivN3NormalizedConservationV4 bltu_1 bltu_0 a b) :
    cpsTripleWithin (unifiedDivBound + 1) base (raVal &&& ~~~1)
      (evm_mod_callable_code_v4 base)
      (divModStackDispatchPreNoX1 sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word)) raVal
        ((clzResult (b.getLimbN 2)).2 >>> (63 : Nat))
        v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (modStackDispatchPostCallableExactFrame sp a b raVal
        (signExtend12 4095 : Word) **
       ((sp + signExtend12 3936) ↦ₘ
        fullDivN3ScratchMemV4 bltu_1 bltu_0
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
          scratchMem)) := by
  exact evm_mod_callable_v4_n3_stack_pre_to_callable_post_scratch_of_normalized_path_conditions
    sp base a b v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem raVal
    hbnz hb3z hb2nz hshift_nz halign
    (fullModN3PathConditionsNormalizedV4_of_conservation
      bltu_1 bltu_0 a b hbnz hb3z hdivPath hcons)


-- @@ L981-1026 verbatim
theorem evm_mod_callable_v4_spec_from_noNop (sp base raVal : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 : Word)
    (branch : ModStackSpecCase base a b)
    (hStack :
      cpsTripleWithin unifiedDivBound base (base + nopOff) (sharedDivModCodeNoNop_v4 base)
        (divModStackDispatchPreNoX1 sp a b
          branch.x1 raVal branch.x2 v5 v6 v7 v10 v11
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0)
        ((modStackDispatchPostCallable sp a b ** regOwn .x9) **
          (.x1 ↦ᵣ raVal))) :
    cpsTripleWithin (unifiedDivBound + 1) base (raVal &&& ~~~1)
      (evm_mod_callable_code_v4 base)
      (divModStackDispatchPreNoX1 sp a b
        branch.x1 raVal branch.x2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0)
      ((modStackDispatchPostCallable sp a b ** regOwn .x9) **
        (.x1 ↦ᵣ raVal)) := by
  have hStackCall :=
    cpsTripleWithin_extend_code
      (hmono := sharedDivModCodeNoNop_v4_sub_mod_callable_code_v4) hStack
  have hStackForRet :
      cpsTripleWithin unifiedDivBound base (base + nopOff)
        (evm_mod_callable_code_v4 base)
        (divModStackDispatchPreNoX1 sp a b
          branch.x1 raVal branch.x2 v5 v6 v7 v10 v11
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0)
        ((modStackDispatchPostCallable sp a b ** regOwn .x9) **
          (.x1 ↦ᵣ raVal)) :=
    cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hp => by xperm_hyp hp) hStackCall
  have hRet :=
    cpsTripleWithin_extend_code (hmono := evm_mod_callable_code_v4_ret_sub (base := base))
      (ret_spec_within' (base + nopOff) raVal)
  have hRetFramed :=
    cpsTripleWithin_frameL (modStackDispatchPostCallable sp a b ** regOwn .x9)
      (by
        rw [modStackDispatchPostCallable_unfold, divScratchOwnCallNoX1_unfold,
          divScratchOwn_unfold]
        pcFree)
      hRet
  exact cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hp => by xperm_hyp hp)
    (cpsTripleWithin_seq_same_cr hStackForRet hRetFramed)


-- @@ L1028-1055 verbatim
theorem evm_mod_callable_v4_spec_from_noNop_framed
    {F : Assertion} [Assertion.PCFree F] (sp base raVal : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 : Word)
    (branch : ModStackSpecCase base a b)
    (hStack :
      cpsTripleWithin unifiedDivBound base (base + nopOff) (sharedDivModCodeNoNop_v4 base)
        (divModStackDispatchPreNoX1 sp a b
          branch.x1 raVal branch.x2 v5 v6 v7 v10 v11
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0)
        ((modStackDispatchPostCallable sp a b ** regOwn .x9) **
          (.x1 ↦ᵣ raVal))) :
    cpsTripleWithin (unifiedDivBound + 1) base (raVal &&& ~~~1)
      (evm_mod_callable_code_v4 base)
      ((divModStackDispatchPreNoX1 sp a b
        branch.x1 raVal branch.x2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0) ** F)
      (((modStackDispatchPostCallable sp a b ** regOwn .x9) **
        (.x1 ↦ᵣ raVal)) ** F) := by
  exact
    cpsTripleWithin_frameR F (by pcFree)
      (evm_mod_callable_v4_spec_from_noNop
        sp base raVal a b v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        nMem shiftMem jMem retMem dMem dloMem scratchUn0 branch hStack)


-- @@ L1057-1057 verbatim
end EvmAsm.Evm64
