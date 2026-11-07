/-
  Loop + exit for `eip8037_prior_state_used_exact` (a4gbr residual leaf).
-/

import EvmAsm.Codegen.Programs.Eip8037PriorStateUsedExactSpec
import EvmAsm.Codegen.Programs.ChainValidateExtraDataLengthSpec
import EvmAsm.Rv64.LaResolve
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.SAsm.DualReadByteScan


-- @@ L11-11 verbatim
namespace EvmAsm.Codegen.Eip8037PriorStateUsedExactLoop


-- @@ L13-13 verbatim
open EvmAsm.Rv64

-- @@ L14-14 verbatim
open EvmAsm.Codegen

-- @@ L15-15 verbatim
open EvmAsm.Codegen.Eip8037PriorStateUsedExactSpec

-- @@ L16-16 verbatim
open EvmAsm.Codegen.Eip8037PriorStateUsedExactModel

-- @@ L17-19 verbatim
open EvmAsm.Codegen.ChainValidateExtraDataLengthSpec
  (wordArray wordArrayFrom wordArray_split pcFree_wordArray pcFree_wordArrayFrom
   shiftLeft3_ofNat)


-- @@ L21-21 verbatim
abbrev P : Word := Eip8037PriorStateUsedExactSpec.P

-- @@ L22-22 verbatim
abbrev pseProg : Program := Eip8037PriorStateUsedExactSpec.pseProg

-- @@ L23-23 verbatim
abbrev pseCode : CodeReq := Eip8037PriorStateUsedExactSpec.pseCode

-- @@ L24-24 verbatim
abbrev LoopGuard : Word := Eip8037PriorStateUsedExactSpec.LoopGuard

-- @@ L25-25 verbatim
abbrev StoreSum : Word := Eip8037PriorStateUsedExactSpec.StoreSum

-- @@ L26-26 verbatim
abbrev OkLi : Word := Eip8037PriorStateUsedExactSpec.OkLi

-- @@ L27-27 verbatim
abbrev OkRet : Word := Eip8037PriorStateUsedExactSpec.OkRet

-- @@ L28-28 verbatim
abbrev FailLi : Word := Eip8037PriorStateUsedExactSpec.FailLi

-- @@ L29-29 verbatim
abbrev TxStateGasAddr : Word := Eip8037PriorStateUsedExactSpec.TxStateGasAddr

-- @@ L30-30 verbatim
abbrev TxStatusAddr : Word := Eip8037PriorStateUsedExactSpec.TxStatusAddr

-- @@ L31-31 verbatim
abbrev TxExecStateGasAddr : Word := Eip8037PriorStateUsedExactSpec.TxExecStateGasAddr

-- @@ L32-32 verbatim
abbrev ExactOkAddr : Word := Eip8037PriorStateUsedExactSpec.ExactOkAddr

-- @@ L33-33 verbatim
abbrev RuntimeCountAddr : Word := Eip8037PriorStateUsedExactSpec.RuntimeCountAddr


-- @@ L35-35 verbatim
theorem pse_length : pseProg.length = 43 := Eip8037PriorStateUsedExactSpec.pse_length


-- @@ L37-37 verbatim
private theorem se12_zero : signExtend12 (0 : BitVec 12) = (0 : Word) := by decide

-- @@ L38-38 verbatim
private theorem se13_92 : signExtend13 (92 : BitVec 13) = (92 : Word) := by decide


-- @@ L40-42 verbatim
private theorem LoopGuard_plus_92 :
    LoopGuard + signExtend13 (92 : BitVec 13) = StoreSum := by
  simp only [LoopGuard, StoreSum, se13_92]; decide


-- @@ L44-45 verbatim
private theorem StoreSum_plus_4 : StoreSum + 4 = OkLi := by
  simp only [StoreSum, OkLi]; decide


-- @@ L47-48 verbatim
private theorem OkLi_plus_4 : OkLi + 4 = OkRet := by
  simp only [OkLi, OkRet]; decide


-- @@ L50-56 verbatim
/-- Ambient globals framed through the loop (read-only). -/
def loopGlobals (exactOkW runtimeW : Word)
    (stateGas status execGas : List Nat) : Assertion :=
  (ExactOkAddr ↦ₘ exactOkW) ** (RuntimeCountAddr ↦ₘ runtimeW) **
    wordArray TxStateGasAddr stateGas **
    wordArray TxStatusAddr status **
    wordArray TxExecStateGasAddr execGas


-- @@ L58-65 verbatim
theorem pcFree_loopGlobals (exactOkW runtimeW : Word)
    (stateGas status execGas : List Nat) :
    (loopGlobals exactOkW runtimeW stateGas status execGas).pcFree := by
  unfold loopGlobals
  repeat' first
    | apply pcFree_sepConj
    | exact pcFree_memIs
    | exact pcFree_wordArray _ _


-- @@ L67-77 verbatim
/-- Loop invariant at LoopGuard: i ≤ n, sum = priorPrefixExact ... i as Word. -/
def LoopInv
    (raIn priorW outPtr sumW iW : Word)
    (exactOkW runtimeW : Word)
    (stateGas status execGas : List Nat)
    (v28 v29 v30 v31 : Word) : Assertion :=
  (.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ priorW) ** (.x11 ↦ᵣ outPtr) **
    (outPtr ↦ₘ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
    (.x5 ↦ᵣ priorW) ** (.x6 ↦ᵣ iW) ** (.x7 ↦ᵣ sumW) **
    (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
    loopGlobals exactOkW runtimeW stateGas status execGas


-- @@ L79-242 verbatim
set_option maxRecDepth 8000 in
/-- Guard taken (i=n): BEQ → StoreSum, SD sum, OkRet. -/
theorem pseLoopExitOk
    (raIn priorW outPtr sumW : Word)
    (exactOkW runtimeW : Word)
    (stateGas status execGas : List Nat)
    (v28 v29 v30 v31 : Word)
    (hret : raIn &&& ~~~(1 : Word) = raIn) :
    cpsTripleWithin 4 LoopGuard raIn pseCode
      (LoopInv raIn priorW outPtr sumW priorW exactOkW runtimeW
        stateGas status execGas v28 v29 v30 v31)
      (postOk raIn outPtr sumW
        ((.x5 ↦ᵣ priorW) ** (.x6 ↦ᵣ priorW) ** (.x7 ↦ᵣ sumW) **
          (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
          loopGlobals exactOkW runtimeW stateGas status execGas)) := by
  have hGpf : (loopGlobals exactOkW runtimeW stateGas status execGas).pcFree :=
    pcFree_loopGlobals exactOkW runtimeW stateGas status execGas
  -- [15] BEQ i,n taken
  have hbr := beq_spec_gen_within .x6 .x5 (92 : BitVec 13) priorW priorW LoopGuard
  have hbrC := cpsBranchWithin_extend_code
    (CodeReq.ofProg_mem_at P LoopGuard pseProg 15
      (.BEQ .x6 .x5 (92 : BitVec 13))
      (by simp only [LoopGuard]; decide)
      (by rw [pse_length]; decide) rfl (by rw [pse_length]; decide)) hbr
  have htk0 := cpsBranchWithin_takenStripPure2 hbrC (fun _ hq => by
    obtain ⟨_, _, _, _, _, hrest⟩ := hq
    exact absurd rfl ((sepConj_pure_right _).1 hrest).2)
  have htk : cpsTripleWithin 1 LoopGuard StoreSum pseCode
      ((.x6 ↦ᵣ priorW) ** (.x5 ↦ᵣ priorW))
      ((.x6 ↦ᵣ priorW) ** (.x5 ↦ᵣ priorW)) := by
    rwa [LoopGuard_plus_92] at htk0
  have e15F := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ priorW) ** (.x11 ↦ᵣ outPtr) **
      (outPtr ↦ₘ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
      (.x7 ↦ᵣ sumW) **
      (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
      loopGlobals exactOkW runtimeW stateGas status execGas)
    (by
      repeat' first
        | exact hGpf
        | apply pcFree_sepConj
        | exact pcFree_regIs
        | exact pcFree_memIs) htk
  -- [38] SD sum *out
  have haddr : outPtr + signExtend12 (0 : BitVec 12) = outPtr := by
    rw [se12_zero]; exact BitVec.add_zero outPtr
  have e38 :
      cpsTripleWithin 1 StoreSum OkLi pseCode
        ((.x11 ↦ᵣ outPtr) ** (.x7 ↦ᵣ sumW) ** (outPtr ↦ₘ (0 : Word)))
        ((.x11 ↦ᵣ outPtr) ** (.x7 ↦ᵣ sumW) ** (outPtr ↦ₘ sumW)) := by
    have h0 := sd_spec_gen_within .x11 .x7 outPtr sumW (0 : Word)
      (0 : BitVec 12) StoreSum
    rw [haddr] at h0
    have h0' : cpsTripleWithin 1 StoreSum (StoreSum + 4) pseCode
        ((.x11 ↦ᵣ outPtr) ** (.x7 ↦ᵣ sumW) ** (outPtr ↦ₘ (0 : Word)))
        ((.x11 ↦ᵣ outPtr) ** (.x7 ↦ᵣ sumW) ** (outPtr ↦ₘ sumW)) :=
      cpsTripleWithin_extend_code
        (CodeReq.ofProg_mem_at P StoreSum pseProg 38
          (.SD .x11 .x7 (0 : BitVec 12))
          (by simp only [StoreSum]; decide)
          (by rw [pse_length]; decide) rfl (by rw [pse_length]; decide)) h0
    rwa [StoreSum_plus_4] at h0'
  have e38F := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ priorW) ** (.x0 ↦ᵣ (0 : Word)) **
      (.x5 ↦ᵣ priorW) ** (.x6 ↦ᵣ priorW) **
      (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
      loopGlobals exactOkW runtimeW stateGas status execGas)
    (by
      repeat' first
        | exact hGpf
        | apply pcFree_sepConj
        | exact pcFree_regIs) e38
  -- Ok ret: a0 was priorW
  have eOk :
      cpsTripleWithin 2 OkLi raIn pseCode
        ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ priorW) ** (.x11 ↦ᵣ outPtr) **
          (outPtr ↦ₘ sumW) ** (.x0 ↦ᵣ (0 : Word)) **
          (.x5 ↦ᵣ priorW) ** (.x6 ↦ᵣ priorW) ** (.x7 ↦ᵣ sumW) **
          (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
          loopGlobals exactOkW runtimeW stateGas status execGas)
        (postOk raIn outPtr sumW
          ((.x5 ↦ᵣ priorW) ** (.x6 ↦ᵣ priorW) ** (.x7 ↦ᵣ sumW) **
            (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
            loopGlobals exactOkW runtimeW stateGas status execGas)) := by
    have e39 :
        cpsTripleWithin 1 OkLi OkRet pseCode
          (.x10 ↦ᵣ priorW) (.x10 ↦ᵣ (0 : Word)) := by
      have h0 := li_spec_gen_within .x10 priorW (0 : Word) OkLi (by decide)
      have h0' : cpsTripleWithin 1 OkLi (OkLi + 4) pseCode
          (.x10 ↦ᵣ priorW) (.x10 ↦ᵣ (0 : Word)) :=
        cpsTripleWithin_extend_code
          (CodeReq.ofProg_mem_at P OkLi pseProg 39 (.LI .x10 (0 : Word))
            (by simp only [OkLi]; decide)
            (by rw [pse_length]; decide) rfl (by rw [pse_length]; decide)) h0
      rwa [OkLi_plus_4] at h0'
    have e39F := cpsTripleWithin_frameR
      ((.x1 ↦ᵣ raIn) ** (.x11 ↦ᵣ outPtr) ** (outPtr ↦ₘ sumW) **
        (.x0 ↦ᵣ (0 : Word)) **
        (.x5 ↦ᵣ priorW) ** (.x6 ↦ᵣ priorW) ** (.x7 ↦ᵣ sumW) **
        (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
        loopGlobals exactOkW runtimeW stateGas status execGas)
      (by
        repeat' first
          | exact hGpf
          | apply pcFree_sepConj
          | exact pcFree_regIs
          | exact pcFree_memIs) e39
    have hexit :
        ((raIn + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word)) = raIn := by
      have hadd : raIn + signExtend12 (0 : BitVec 12) = raIn := by
        rw [se12_zero]; exact BitVec.add_zero raIn
      rw [hadd, hret]
    have e40 :
        cpsTripleWithin 1 OkRet raIn pseCode
          (.x1 ↦ᵣ raIn) (.x1 ↦ᵣ raIn) := by
      have h0 := jalr_x0_spec_gen_within .x1 raIn (0 : BitVec 12) OkRet
      rw [hexit] at h0
      exact cpsTripleWithin_extend_code
        (CodeReq.ofProg_mem_at P OkRet pseProg 40
          (.JALR .x0 .x1 (0 : BitVec 12))
          (by simp only [OkRet]; decide)
          (by rw [pse_length]; decide) rfl (by rw [pse_length]; decide)) h0
    have e40F0 := cpsTripleWithin_frameR
      ((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ outPtr) ** (outPtr ↦ₘ sumW) **
        (.x0 ↦ᵣ (0 : Word)) **
        (.x5 ↦ᵣ priorW) ** (.x6 ↦ᵣ priorW) ** (.x7 ↦ᵣ sumW) **
        (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
        loopGlobals exactOkW runtimeW stateGas status execGas)
      (by
        repeat' first
          | exact hGpf
          | apply pcFree_sepConj
          | exact pcFree_regIs
          | exact pcFree_memIs) e40
    have e40F : cpsTripleWithin 1 OkRet raIn pseCode
        ((.x10 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raIn) ** (.x11 ↦ᵣ outPtr) **
          (outPtr ↦ₘ sumW) ** (.x0 ↦ᵣ (0 : Word)) **
          (.x5 ↦ᵣ priorW) ** (.x6 ↦ᵣ priorW) ** (.x7 ↦ᵣ sumW) **
          (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
          loopGlobals exactOkW runtimeW stateGas status execGas)
        ((.x10 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raIn) ** (.x11 ↦ᵣ outPtr) **
          (outPtr ↦ₘ sumW) ** (.x0 ↦ᵣ (0 : Word)) **
          (.x5 ↦ᵣ priorW) ** (.x6 ↦ᵣ priorW) ** (.x7 ↦ᵣ sumW) **
          (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
          loopGlobals exactOkW runtimeW stateGas status execGas) :=
      cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
        (fun _ hq => by xperm_hyp hq) e40F0
    have c := cpsTripleWithin_seq_perm_same_cr
      (fun _ hp => by xperm_hyp hp) e39F e40F
    exact cpsTripleWithin_weaken
      (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by
        dsimp only [postOk] at hq ⊢
        xperm_hyp hq) c
  have c01 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) e15F e38F
  have c02 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) c01 eOk
  change cpsTripleWithin (1 + 1 + 2) LoopGuard raIn pseCode _ _ at c02
  exact cpsTripleWithin_weaken
    (fun _ hp => by
      dsimp only [LoopInv] at hp ⊢
      xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) c02


-- @@ L244-244 verbatim
#print axioms pseLoopExitOk


-- @@ L246-246 verbatim
/-! ## Loop addresses / la helpers / one-iter (status = 0) -/


-- @@ L248-248 verbatim
abbrev LoopBody : Word := P + 64

-- @@ L249-249 verbatim
abbrev AfterSlli : Word := P + 68

-- @@ L250-250 verbatim
abbrev AfterLaState : Word := P + 76

-- @@ L251-251 verbatim
abbrev AfterLdState : Word := P + 84

-- @@ L252-252 verbatim
abbrev AfterAddState : Word := P + 88

-- @@ L253-253 verbatim
abbrev AfterMvSum : Word := P + 96

-- @@ L254-254 verbatim
abbrev AfterLaStatus : Word := P + 104

-- @@ L255-255 verbatim
abbrev AfterLdStatus : Word := P + 112

-- @@ L256-256 verbatim
abbrev AfterStatusBne : Word := P + 116  -- fall-through of status BEQ (status ≠ 0)

-- @@ L257-257 verbatim
abbrev AfterLaExec : Word := P + 124

-- @@ L258-258 verbatim
abbrev AfterStatusSkip : Word := P + 144  -- join of status=0 skip and status≠0 exec path

-- @@ L259-259 verbatim
abbrev AfterIncr : Word := P + 148


-- @@ L261-262 verbatim
private theorem LoopGuard_plus_4 : LoopGuard + 4 = LoopBody := by
  simp only [LoopGuard, LoopBody]; decide


-- @@ L264-268 verbatim
private theorem ofNat_addi1 (i : Nat) :
    BitVec.ofNat 64 i + signExtend12 (1 : BitVec 12) = BitVec.ofNat 64 (i + 1) := by
  have h1 : signExtend12 (1 : BitVec 12) = (1 : Word) := by decide
  rw [h1, BitVec.ofNat_add]
  rfl


-- @@ L270-289 verbatim
/-- `la bvgr_tx_state_gas` at instr 17–18 (PC P+68). -/
theorem pseLaStateGas (v : Word) :
    cpsTripleWithin 2 AfterSlli AfterLaState pseCode
      (.x29 ↦ᵣ v) (.x29 ↦ᵣ TxStateGasAddr) := by
  have hau := CodeReq.ofProg_mem_at P AfterSlli pseProg 17
    (.AUIPC .x29 (Codegen.laHi GuestAddrs.bvgr_tx_state_gas
      (GuestAddrs.eip8037_prior_state_used_exact + 68)))
    (by simp only [AfterSlli]; decide)
    (by rw [pse_length]; decide) rfl (by rw [pse_length]; decide)
  have had := CodeReq.ofProg_mem_at P (AfterSlli + 4) pseProg 18
    (.ADDI .x29 .x29 (Codegen.laLo GuestAddrs.bvgr_tx_state_gas
      (GuestAddrs.eip8037_prior_state_used_exact + 68)))
    (by simp only [AfterSlli]; decide)
    (by rw [pse_length]; decide) rfl (by rw [pse_length]; decide)
  have h := la_materialize_within .x29 v AfterSlli TxStateGasAddr
    (by decide)
    (by simp only [AfterSlli, TxStateGasAddr]; decide)
    hau had
  rwa [show AfterSlli + 8 = AfterLaState from by
    simp only [AfterSlli, AfterLaState]; decide] at h


-- @@ L291-310 verbatim
/-- `la bv_tx_status_arr` at instr 24–25 (PC P+96). -/
theorem pseLaStatus (v : Word) :
    cpsTripleWithin 2 AfterMvSum AfterLaStatus pseCode
      (.x29 ↦ᵣ v) (.x29 ↦ᵣ TxStatusAddr) := by
  have hau := CodeReq.ofProg_mem_at P AfterMvSum pseProg 24
    (.AUIPC .x29 (Codegen.laHi GuestAddrs.bv_tx_status_arr
      (GuestAddrs.eip8037_prior_state_used_exact + 96)))
    (by simp only [AfterMvSum]; decide)
    (by rw [pse_length]; decide) rfl (by rw [pse_length]; decide)
  have had := CodeReq.ofProg_mem_at P (AfterMvSum + 4) pseProg 25
    (.ADDI .x29 .x29 (Codegen.laLo GuestAddrs.bv_tx_status_arr
      (GuestAddrs.eip8037_prior_state_used_exact + 96)))
    (by simp only [AfterMvSum]; decide)
    (by rw [pse_length]; decide) rfl (by rw [pse_length]; decide)
  have h := la_materialize_within .x29 v AfterMvSum TxStatusAddr
    (by decide)
    (by simp only [AfterMvSum, TxStatusAddr]; decide)
    hau had
  rwa [show AfterMvSum + 8 = AfterLaStatus from by
    simp only [AfterMvSum, AfterLaStatus]; decide] at h


-- @@ L312-331 verbatim
/-- `la bvgr_tx_exec_state_gas` at instr 29–30 (PC P+116). -/
theorem pseLaExec (v : Word) :
    cpsTripleWithin 2 AfterStatusBne AfterLaExec pseCode
      (.x29 ↦ᵣ v) (.x29 ↦ᵣ TxExecStateGasAddr) := by
  have hau := CodeReq.ofProg_mem_at P AfterStatusBne pseProg 29
    (.AUIPC .x29 (Codegen.laHi GuestAddrs.bvgr_tx_exec_state_gas
      (GuestAddrs.eip8037_prior_state_used_exact + 116)))
    (by simp only [AfterStatusBne]; decide)
    (by rw [pse_length]; decide) rfl (by rw [pse_length]; decide)
  have had := CodeReq.ofProg_mem_at P (AfterStatusBne + 4) pseProg 30
    (.ADDI .x29 .x29 (Codegen.laLo GuestAddrs.bvgr_tx_exec_state_gas
      (GuestAddrs.eip8037_prior_state_used_exact + 116)))
    (by simp only [AfterStatusBne]; decide)
    (by rw [pse_length]; decide) rfl (by rw [pse_length]; decide)
  have h := la_materialize_within .x29 v AfterStatusBne TxExecStateGasAddr
    (by decide)
    (by simp only [AfterStatusBne, TxExecStateGasAddr]; decide)
    hau had
  rwa [show AfterStatusBne + 8 = AfterLaExec from by
    simp only [AfterStatusBne, AfterLaExec]; decide] at h


-- @@ L333-375 verbatim
set_option maxRecDepth 8000 in
/-- Guard fall-through when i ≠ n. -/
theorem pseLoopGuardNtaken
    (raIn priorW outPtr sumW iW : Word)
    (exactOkW runtimeW : Word)
    (stateGas status execGas : List Nat)
    (v28 v29 v30 v31 : Word)
    (hne : iW ≠ priorW) :
    cpsTripleWithin 1 LoopGuard LoopBody pseCode
      (LoopInv raIn priorW outPtr sumW iW exactOkW runtimeW
        stateGas status execGas v28 v29 v30 v31)
      (LoopInv raIn priorW outPtr sumW iW exactOkW runtimeW
        stateGas status execGas v28 v29 v30 v31) := by
  have hGpf : (loopGlobals exactOkW runtimeW stateGas status execGas).pcFree :=
    pcFree_loopGlobals exactOkW runtimeW stateGas status execGas
  have hbr := beq_spec_gen_within .x6 .x5 (92 : BitVec 13) iW priorW LoopGuard
  have hbrC := cpsBranchWithin_extend_code
    (CodeReq.ofProg_mem_at P LoopGuard pseProg 15
      (.BEQ .x6 .x5 (92 : BitVec 13))
      (by simp only [LoopGuard]; decide)
      (by rw [pse_length]; decide) rfl (by rw [pse_length]; decide)) hbr
  have hnt0 := cpsBranchWithin_ntakenStripPure2 hbrC (fun _ hq => by
    obtain ⟨_, _, _, _, _, hrest⟩ := hq
    exact absurd ((sepConj_pure_right _).1 hrest).2 hne)
  have hnt : cpsTripleWithin 1 LoopGuard LoopBody pseCode
      ((.x6 ↦ᵣ iW) ** (.x5 ↦ᵣ priorW))
      ((.x6 ↦ᵣ iW) ** (.x5 ↦ᵣ priorW)) := by
    rwa [LoopGuard_plus_4] at hnt0
  have hF := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ priorW) ** (.x11 ↦ᵣ outPtr) **
      (outPtr ↦ₘ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
      (.x7 ↦ᵣ sumW) **
      (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
      loopGlobals exactOkW runtimeW stateGas status execGas)
    (by
      repeat' first
        | exact hGpf
        | apply pcFree_sepConj
        | exact pcFree_regIs
        | exact pcFree_memIs) hnt
  exact cpsTripleWithin_weaken
    (fun _ hp => by dsimp only [LoopInv] at hp ⊢; xperm_hyp hp)
    (fun _ hq => by dsimp only [LoopInv] at hq ⊢; xperm_hyp hq) hF


-- @@ L377-377 verbatim
#print axioms pseLoopGuardNtaken


-- @@ L379-379 verbatim
#print axioms pseLaStateGas

-- @@ L380-380 verbatim
#print axioms pseLaStatus

-- @@ L381-381 verbatim
#print axioms pseLaExec


-- @@ L383-383 verbatim
end EvmAsm.Codegen.Eip8037PriorStateUsedExactLoop

