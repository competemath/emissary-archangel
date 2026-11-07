/-
  EvmAsm.Evm64.DivMod.Compose.EpilogueV6

  v6 DIV epilogue brick (10 instrs, base+v6EpilogueOff → base+v6ExitOff) over
  `divCodeV6`. Loads the quotient limbs q[0..3] from scratch, bumps sp by 32,
  stores them to the output area, and `JAL x0 1412` to the embedded v5 NOP exit.
  Mirror of the v1/v4 epilogue composition (Compose/Epilogue.lean): only the
  code bundle, base offset, JAL offset (1412 vs 24), and exit target
  (v6ExitOff vs nopOff) differ.

  Brick of the v6 n=1 fast-path body. Bead `evm-asm-7wbf8.3`.
-/

module

public import EvmAsm.Evm64.DivMod.Compose.Epilogue
public import EvmAsm.Evm64.DivMod.Compose.CLZV6


-- @@ L19-19 verbatim
public section


-- @@ L21-21 verbatim
namespace EvmAsm.Evm64


-- @@ L23-27 verbatim
open EvmAsm.Rv64

-- ============================================================================
-- Code subsumption: DIV epilogue (block index 9 of divCodeV6) into divCodeV6.
-- ============================================================================


-- @@ L29-42 expanded
/-- DIV epilogue block is subsumed by divCodeV6 (9 preceding blocks:
    dispatchN1, clz, fastSetup, normA, copyAU, digit3, digit2, digit1, digit0). -/
private theorem divK_div_epilogue_code_sub_divCodeV6 {base : Word} :
    ∀ a i,
      (CodeReq.ofProg (base + v6EpilogueOff) (divK_div_epilogue 1412)) a = some i →
        (divCodeV6 base) a = some i :=
  by
  unfold divCodeV6; simp only [CodeReq.unionAll_cons]
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_dispatchN1_length, divK_clz_len, divK_fastSetup_length, divK_normA_len,
            divK_copyAU_len, divK_fastDigit_length, divK_div_epilogue_len', divK_div128_v5_len,
            dispatchN1Off, v6ClzOff, v6SetupOff, v6NormAOff, v6CopyAUOff, v6Digit3Off, v6Digit2Off,
            v6Digit1Off, v6Digit0Off, v6EpilogueOff, v6Div128Off] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_dispatchN1_length, divK_clz_len, divK_fastSetup_length, divK_normA_len,
            divK_copyAU_len, divK_fastDigit_length, divK_div_epilogue_len', divK_div128_v5_len,
            dispatchN1Off, v6ClzOff, v6SetupOff, v6NormAOff, v6CopyAUOff, v6Digit3Off, v6Digit2Off,
            v6Digit1Off, v6Digit0Off, v6EpilogueOff, v6Div128Off] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_dispatchN1_length, divK_clz_len, divK_fastSetup_length, divK_normA_len,
            divK_copyAU_len, divK_fastDigit_length, divK_div_epilogue_len', divK_div128_v5_len,
            dispatchN1Off, v6ClzOff, v6SetupOff, v6NormAOff, v6CopyAUOff, v6Digit3Off, v6Digit2Off,
            v6Digit1Off, v6Digit0Off, v6EpilogueOff, v6Div128Off] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_dispatchN1_length, divK_clz_len, divK_fastSetup_length, divK_normA_len,
            divK_copyAU_len, divK_fastDigit_length, divK_div_epilogue_len', divK_div128_v5_len,
            dispatchN1Off, v6ClzOff, v6SetupOff, v6NormAOff, v6CopyAUOff, v6Digit3Off, v6Digit2Off,
            v6Digit1Off, v6Digit0Off, v6EpilogueOff, v6Div128Off] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_dispatchN1_length, divK_clz_len, divK_fastSetup_length, divK_normA_len,
            divK_copyAU_len, divK_fastDigit_length, divK_div_epilogue_len', divK_div128_v5_len,
            dispatchN1Off, v6ClzOff, v6SetupOff, v6NormAOff, v6CopyAUOff, v6Digit3Off, v6Digit2Off,
            v6Digit1Off, v6Digit0Off, v6EpilogueOff, v6Div128Off] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_dispatchN1_length, divK_clz_len, divK_fastSetup_length, divK_normA_len,
            divK_copyAU_len, divK_fastDigit_length, divK_div_epilogue_len', divK_div128_v5_len,
            dispatchN1Off, v6ClzOff, v6SetupOff, v6NormAOff, v6CopyAUOff, v6Digit3Off, v6Digit2Off,
            v6Digit1Off, v6Digit0Off, v6EpilogueOff, v6Div128Off] at hk1 hk2
          bv_omega))
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_dispatchN1_length, divK_clz_len, divK_fastSetup_length, divK_normA_len,
            divK_copyAU_len, divK_fastDigit_length, divK_div_epilogue_len', divK_div128_v5_len,
            dispatchN1Off, v6ClzOff, v6SetupOff, v6NormAOff, v6CopyAUOff, v6Digit3Off, v6Digit2Off,
            v6Digit1Off, v6Digit0Off, v6EpilogueOff, v6Div128Off] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_dispatchN1_length, divK_clz_len, divK_fastSetup_length, divK_normA_len,
            divK_copyAU_len, divK_fastDigit_length, divK_div_epilogue_len', divK_div128_v5_len,
            dispatchN1Off, v6ClzOff, v6SetupOff, v6NormAOff, v6CopyAUOff, v6Digit3Off, v6Digit2Off,
            v6Digit1Off, v6Digit0Off, v6EpilogueOff, v6Div128Off] at hk1 hk2
          bv_omega));
  apply
    CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range
        (fun k1 k2 hk1 hk2 =>
          by
          simp only [divK_dispatchN1_length, divK_clz_len, divK_fastSetup_length, divK_normA_len,
            divK_copyAU_len, divK_fastDigit_length, divK_div_epilogue_len', divK_div128_v5_len,
            dispatchN1Off, v6ClzOff, v6SetupOff, v6NormAOff, v6CopyAUOff, v6Digit3Off, v6Digit2Off,
            v6Digit1Off, v6Digit0Off, v6EpilogueOff, v6Div128Off] at hk1 hk2
          bv_omega))
  exact CodeReq.union_mono_left


-- @@ L44-84 verbatim
theorem divK_div_epilogue_spec_within_v6 (sp : Word) (base : Word)
    (q0 q1 q2 q3 v5 v6 v7 v10 m0 m8 m16 m24 : Word) :
    cpsTripleWithin 10 (base + v6EpilogueOff) (base + v6ExitOff) (divCodeV6 base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x10 ↦ᵣ v10) **
       ((sp + signExtend12 4088) ↦ₘ q0) ** ((sp + signExtend12 4080) ↦ₘ q1) **
       ((sp + signExtend12 4072) ↦ₘ q2) ** ((sp + signExtend12 4064) ↦ₘ q3) **
       ((sp + 32) ↦ₘ m0) ** ((sp + 40) ↦ₘ m8) **
       ((sp + 48) ↦ₘ m16) ** ((sp + 56) ↦ₘ m24))
      ((.x12 ↦ᵣ (sp + 32)) ** (.x5 ↦ᵣ q0) ** (.x6 ↦ᵣ q1) ** (.x7 ↦ᵣ q2) ** (.x10 ↦ᵣ q3) **
       ((sp + signExtend12 4088) ↦ₘ q0) ** ((sp + signExtend12 4080) ↦ₘ q1) **
       ((sp + signExtend12 4072) ↦ₘ q2) ** ((sp + signExtend12 4064) ↦ₘ q3) **
       ((sp + 32) ↦ₘ q0) ** ((sp + 40) ↦ₘ q1) **
       ((sp + 48) ↦ₘ q2) ** ((sp + 56) ↦ₘ q3)) := by
  have hload := divK_epilogue_load_spec_within 4088 4080 4072 4064 sp q0 q1 q2 q3 v5 v6 v7 v10
    (base + v6EpilogueOff)
  have hloade := cpsTripleWithin_extend_code (hmono := fun a i h =>
    divK_div_epilogue_code_sub_divCodeV6 a i
      (CodeReq.ofProg_mono_sub (base + v6EpilogueOff) (base + v6EpilogueOff) (divK_div_epilogue 1412)
        (divK_epilogue_load_prog 4088 4080 4072 4064) 0
        (by bv_addr) (by decide) (by decide) (by decide) a i h)) hload
  have hstore := divK_epilogue_store_spec_within sp (base + v6EpilogueOff + 16) q0 q1 q2 q3 m0 m8 m16 m24 1412
  rw [show (base + v6EpilogueOff + 16 : Word) + 20 + signExtend21 1412 = base + v6ExitOff from by rv64_addr]
    at hstore
  have hstoree := cpsTripleWithin_extend_code (hmono := fun a i h =>
    divK_div_epilogue_code_sub_divCodeV6 a i
      (CodeReq.ofProg_mono_sub (base + v6EpilogueOff) (base + v6EpilogueOff + 16) (divK_div_epilogue 1412)
        (divK_epilogue_store_prog 1412) 4
        (by bv_addr) (by decide) (by decide) (by decide) a i h)) hstore
  have hloadef := cpsTripleWithin_frameR
    (((sp + 32) ↦ₘ m0) ** ((sp + 40) ↦ₘ m8) ** ((sp + 48) ↦ₘ m16) ** ((sp + 56) ↦ₘ m24))
    (by pcFree) hloade
  have hstoref := cpsTripleWithin_frameR
    (((sp + signExtend12 4088) ↦ₘ q0) ** ((sp + signExtend12 4080) ↦ₘ q1) **
     ((sp + signExtend12 4072) ↦ₘ q2) ** ((sp + signExtend12 4064) ↦ₘ q3))
    (by pcFree) hstoree
  have h12 := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) hloadef hstoref
  exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    h12


-- @@ L86-86 verbatim
end EvmAsm.Evm64
