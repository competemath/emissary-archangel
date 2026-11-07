/-
  EvmAsm.Codegen.Programs.U256GasPricingSAsm

  Stage-2 machine composition for the EIP-1559 priority-fee helper.
  The second `u256_min` operand is the output buffer itself at the linked
  callsite, so this file deliberately consumes the B-in-place min contract
  rather than the disjoint three-region contract.
-/

import EvmAsm.Codegen.Programs.U256GasPricing
import EvmAsm.Codegen.Programs.U256MinSAsm
import EvmAsm.Codegen.Programs.U256SubBeSAsm
import EvmAsm.Rv64.SAsm.AbiFrameCall
import EvmAsm.Rv64.SAsm.AbiFrameOwn
import EvmAsm.Rv64.SAsm.TwoExitLoop
import EvmAsm.Rv64.Tactics.XPermChunked
import EvmAsm.Rv64.Tactics.XPermPure


-- @@ L19-19 verbatim
namespace EvmAsm.Codegen


-- @@ L21-21 verbatim
open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Crypto

-- @@ L22-22 verbatim
open EvmAsm.Rv64.Tactics

-- @@ L23-23 verbatim
open EvmAsm.Codegen.U256MinSAsm

-- @@ L24-24 verbatim
open EvmAsm.Codegen.U256SubBeSAsm


-- @@ L26-26 verbatim
namespace U256GasPricingSAsm


-- @@ L28-28 verbatim
abbrev P : Word := (GuestAddrs.priority_fee_per_gas_eip1559 : Word)

-- @@ L29-29 verbatim
abbrev pCode : CodeReq := CodeReq.ofProg P priorityFeePerGasEip1559_prog

-- @@ L30-30 verbatim
abbrev subCode : CodeReq := u256SubBeInPlaceCr

-- @@ L31-32 verbatim
abbrev minCode : CodeReq := CodeReq.ofProg
  (GuestAddrs.u256_min : Word) u256Min_prog

-- @@ L33-33 verbatim
abbrev fullCode : CodeReq := pCode.union (subCode.union minCode)


-- @@ L35-37 verbatim
def prioritySubScratch : List Reg :=
  [.x5, .x6, .x7, .x28, .x29, .x30, .x31,
   .x13, .x14, .x15, .x16, .x17]


-- @@ L39-41 verbatim
def prioritySubRetScratch : List Reg :=
  [.x5, .x6, .x7, .x28, .x29, .x30, .x31,
   .x11, .x12, .x13, .x14, .x15, .x16, .x17]


-- @@ L43-45 verbatim
@[irreducible] def prioritySubFn (fPtr bPtr outPtr : Word)
    (fBytes bBytes outBytes : List (BitVec 8)) : Fn :=
  u256SubBeFn fPtr bPtr outPtr fBytes bBytes outBytes


-- @@ L47-52 verbatim
@[irreducible] def prioritySubPre (ret fPtr bPtr outPtr : Word)
    (fBytes bBytes outBytes : List (BitVec 8)) : Assertion :=
  ((.x1 : Reg) ↦ᵣ ret) **
    ((.x10 ↦ᵣ fPtr) ** (.x11 ↦ᵣ bPtr) ** (.x12 ↦ᵣ outPtr) **
      regOwns prioritySubScratch ** bytesRegion outPtr outBytes **
      bytesRegion fPtr fBytes ** bytesRegion bPtr bBytes)


-- @@ L54-60 verbatim
@[irreducible] def prioritySubPost (fPtr bPtr outPtr : Word)
    (fBytes bBytes outBytes : List (BitVec 8)) : Assertion :=
  ((.x1 : Reg) ↦ᵣ (P + 56)) **
    ((.x10 ↦ᵣ u256SubBeBorrow fBytes bBytes outBytes) **
      regOwns prioritySubRetScratch **
      bytesRegion outPtr (u256SubBeBytes fBytes bBytes outBytes) **
      bytesRegion fPtr fBytes ** bytesRegion bPtr bBytes)


-- @@ L62-63 verbatim
theorem priority_prog_length : priorityFeePerGasEip1559_prog.length = 29 := by
  decide


-- @@ L65-67 verbatim
private theorem priority_sub_disjoint : pCode.Disjoint subCode := by
  unfold pCode subCode
  apply CodeReq.Disjoint.ofProg_ranges <;> decide


-- @@ L69-71 verbatim
private theorem priority_min_disjoint : pCode.Disjoint minCode := by
  unfold pCode minCode
  apply CodeReq.Disjoint.ofProg_ranges <;> decide


-- @@ L73-75 verbatim
private theorem sub_min_disjoint : subCode.Disjoint minCode := by
  unfold subCode minCode
  apply CodeReq.Disjoint.ofProg_ranges <;> decide


-- @@ L77-80 verbatim
private theorem p_full_mono : ∀ a i, pCode a = some i → fullCode a = some i := by
  intro a i h
  exact CodeReq.union_mono_left (cr1 := pCode)
    (cr2 := subCode.union minCode) a i h


-- @@ L82-88 verbatim
private theorem sub_full_mono : ∀ a i, subCode a = some i → fullCode a = some i := by
  intro a i h
  have htail : ∀ a i, subCode a = some i → (subCode.union minCode) a = some i :=
    fun a i h => CodeReq.union_mono_left (cr1 := subCode) (cr2 := minCode) a i h
  exact CodeReq.mono_union_right
    (oldCr := subCode) (head := pCode) (tail := subCode.union minCode)
    priority_sub_disjoint htail a i h


-- @@ L90-99 verbatim
private theorem min_full_mono : ∀ a i, minCode a = some i → fullCode a = some i := by
  intro a i h
  have htail : ∀ a i, minCode a = some i → (subCode.union minCode) a = some i :=
    fun a i h => CodeReq.mono_union_right
      (oldCr := minCode) (head := subCode) (tail := minCode)
      sub_min_disjoint (fun _ _ h => h) a i h
  have hdisj : pCode.Disjoint minCode := priority_min_disjoint
  exact CodeReq.mono_union_right
    (oldCr := minCode) (head := pCode) (tail := subCode.union minCode)
    hdisj htail a i h


-- @@ L101-113 verbatim
private theorem subBorrowState_len (a b orig : List (BitVec 8)) (k : Nat) :
    (U256SubBeSAsm.subBorrowState a b orig k).1.length = orig.length := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hst : U256SubBeSAsm.subBorrowState a b orig (k + 1) =
        ((U256SubBeSAsm.subBorrowState a b orig k).1.set (31 - k)
            (U256SubBeSAsm.subBorrowByte (a.getD (31 - k) 0) (b.getD (31 - k) 0)
              (U256SubBeSAsm.subBorrowState a b orig k).2).1,
          (U256SubBeSAsm.subBorrowByte (a.getD (31 - k) 0) (b.getD (31 - k) 0)
            (U256SubBeSAsm.subBorrowState a b orig k).2).2) := rfl
    rw [hst]
    simpa using ih


-- @@ L115-119 verbatim
theorem sub_bytes_length (a b orig : List (BitVec 8))
    (hlen : orig.length = 32) :
    (U256SubBeSAsm.u256SubBeBytes a b orig).length = 32 := by
  rw [U256SubBeSAsm.u256SubBeBytes, subBorrowState_len]
  exact hlen


-- @@ L121-136 verbatim
theorem priority_mem (k : Nat) (ins : Instr) (A : Word)
    (hA : A = P + BitVec.ofNat 64 (4 * k))
    (hk : k < priorityFeePerGasEip1559_prog.length)
    (hins : (show List Instr from priorityFeePerGasEip1559_prog)[k]'hk = ins) :
    ∀ a i, CodeReq.singleton A ins a = some i → fullCode a = some i := by
  intro a i hi
  apply p_full_mono a i
  have hslice :
      ((show List Instr from priorityFeePerGasEip1559_prog).drop k).take 1 = [ins] := by
    rw [List.drop_eq_getElem_cons hk, hins]
    rfl
  have hrange : k + 1 ≤ (show List Instr from priorityFeePerGasEip1559_prog).length := by
    exact Nat.succ_le_of_lt hk
  exact CodeReq.ofProg_mono_sub P A
    (show List Instr from priorityFeePerGasEip1559_prog) [ins] k
    hA hslice hrange (by decide) a i hi


-- @@ L138-147 verbatim
private theorem prioritySub_exposed_split (vf : Reg → Word) :
    regAtomsOf vf exposedRegs =
      (((.x10 : Reg) ↦ᵣ vf .x10) ** ((.x11 : Reg) ↦ᵣ vf .x11) **
        ((.x12 : Reg) ↦ᵣ vf .x12) ** regAtomsOf vf prioritySubScratch) := by
  show regAtomsOf vf
      [.x5, .x6, .x7, .x28, .x29, .x30, .x31,
       .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17] = _
  simp only [prioritySubScratch, regAtomsOf_cons,
    regAtomsOf_nil]
  xperm


-- @@ L149-157 verbatim
private theorem prioritySub_borrow_split (vf : Reg → Word) :
    regAtomsOf vf exposedRegs =
      (((.x10 : Reg) ↦ᵣ vf .x10) ** regAtomsOf vf prioritySubRetScratch) := by
  show regAtomsOf vf
      [.x5, .x6, .x7, .x28, .x29, .x30, .x31,
       .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17] = _
  simp only [prioritySubRetScratch, regAtomsOf_cons,
    regAtomsOf_nil]
  xperm


-- @@ L159-162 verbatim
private theorem prioritySub_args_notin_scratch :
    ∀ r ∈ prioritySubScratch,
      r ≠ (.x10 : Reg) ∧ r ≠ (.x11 : Reg) ∧ r ≠ (.x12 : Reg) := by
  decide


-- @@ L164-272 verbatim
private theorem prioritySubFlat_spec
    (ret fPtr bPtr outPtr : Word)
    (fBytes bBytes outBytes : List (BitVec 8))
    (hrw : RwRegion.wf ⟨outPtr, 32⟩)
    (hroF : Region.wf ⟨fPtr, fBytes⟩)
    (hroB : Region.wf ⟨bPtr, bBytes⟩)
    (hlenF : fBytes.length = 32) (hlenB : bBytes.length = 32)
    (hlenOut : outBytes.length = 32)
    (hovF : fPtr.toNat + 32 < 2 ^ 64)
    (hovB : bPtr.toNat + 32 < 2 ^ 64)
    (hovOut : outPtr.toNat + 32 < 2 ^ 64)
    (hdisjF : fPtr.toNat + 32 ≤ outPtr.toNat ∨
      outPtr.toNat + 32 ≤ fPtr.toNat)
    (hdisjB : bPtr.toNat + 32 ≤ outPtr.toNat ∨
      outPtr.toNat + 32 ≤ bPtr.toNat)
    (hsz : 4 * ((prioritySubFn fPtr bPtr outPtr fBytes bBytes outBytes).body.size + 1)
      ≤ 2 ^ 64)
    (halign : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin
      ((prioritySubFn fPtr bPtr outPtr fBytes bBytes outBytes).body.steps + 1)
      (GuestAddrs.u256_sub_be : Word) ret subCode
      (((.x1 : Reg) ↦ᵣ ret) ** ((.x10 : Reg) ↦ᵣ fPtr) **
        ((.x11 : Reg) ↦ᵣ bPtr) ** ((.x12 : Reg) ↦ᵣ outPtr) **
        regOwns prioritySubScratch ** bytesRegion outPtr outBytes **
        bytesRegion fPtr fBytes ** bytesRegion bPtr bBytes)
      (((.x1 : Reg) ↦ᵣ ret) **
        ((.x10 : Reg) ↦ᵣ u256SubBeBorrow fBytes bBytes outBytes) **
        regOwns prioritySubRetScratch **
        bytesRegion outPtr (u256SubBeBytes fBytes bBytes outBytes) **
        bytesRegion fPtr fBytes ** bytesRegion bPtr bBytes) := by
  rw [prioritySubFn]
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => hq)
    (cpsTripleWithin_peel_regOwns prioritySubScratch (by decide)
      (P := ((.x1 : Reg) ↦ᵣ ret) ** ((.x10 : Reg) ↦ᵣ fPtr) **
        ((.x11 : Reg) ↦ᵣ bPtr) ** ((.x12 : Reg) ↦ᵣ outPtr) **
        bytesRegion outPtr outBytes ** bytesRegion fPtr fBytes **
        bytesRegion bPtr bBytes)
      (fun vf => ?_))
  let rf0 : RegFile := fun r =>
    if r = .x10 then fPtr else if r = .x11 then bPtr
    else if r = .x12 then outPtr else vf r
  have hpre : u256SubBePre fPtr bPtr outPtr fBytes bBytes outBytes
      rf0 outBytes (bytesRegion fPtr fBytes ** bytesRegion bPtr bBytes) := by
    refine ⟨?_, ?_, ?_, rfl, hlenF, hlenB, hlenOut, hovF, hovB, hovOut,
      hdisjF, hdisjB, rfl⟩
    · simp [rf0, RegFile.get]
    · simp [rf0, RegFile.get]
    · simp [rf0, RegFile.get]
  have hsz' : 4 * ((u256SubBeFn fPtr bPtr outPtr fBytes bBytes outBytes).body.size + 1)
      ≤ 2 ^ 64 := by
    simpa only [prioritySubFn] using hsz
  have had := Fn.retSpecFlatAmbient
    (u256SubBeFn fPtr bPtr outPtr fBytes bBytes outBytes)
    (GuestAddrs.u256_sub_be : Word)
    (u256SubBe_spec fPtr bPtr outPtr fBytes bBytes outBytes hrw hroF hroB
      (GuestAddrs.u256_sub_be : Word))
    hsz' ret halign rf0 outBytes
    (bytesRegion fPtr fBytes ** bytesRegion bPtr bBytes) (by pcf)
    (by exact hlenOut) hpre
    (Q := (((.x10 : Reg) ↦ᵣ u256SubBeBorrow fBytes bBytes outBytes) **
      regOwns prioritySubRetScratch **
      bytesRegion outPtr (u256SubBeBytes fBytes bBytes outBytes)) **
      (bytesRegion fPtr fBytes ** bytesRegion bPtr bBytes))
    (fun _ _ _ hpost => by exact hpost.2.2.2.2)
    (fun rf' ws' _hlen hpost hp hh => by
      rcases hpost with ⟨hx10, hx11, hx12, hws, hA⟩
      subst ws'
      have hx10raw : rf' .x10 = u256SubBeBorrow fBytes bBytes outBytes := by
        simpa [RegFile.get] using hx10
      rw [regFileIs_eq_regAtoms,
        regAtoms_eq_regAtomsOf rf' exposedRegs (by decide),
        prioritySub_borrow_split, hx10raw] at hh
      have hh2 :
          (((((.x10 : Reg) ↦ᵣ u256SubBeBorrow fBytes bBytes outBytes) **
            regOwns prioritySubRetScratch) **
            bytesRegion outPtr (u256SubBeBytes fBytes bBytes outBytes)) **
            bytesRegion fPtr fBytes ** bytesRegion bPtr bBytes) hp := by
        exact sepConj_mono_left
          (sepConj_mono_left
            (sepConj_mono_right
              (regAtomsOf_to_regOwns (fun r => rf' r) prioritySubRetScratch)))
          hp hh
      xperm_hyp hh2)
  rw [show (u256SubBeFn fPtr bPtr outPtr fBytes bBytes outBytes).programRet
      (GuestAddrs.u256_sub_be : Word) = u256SubBe_prog from rfl] at had
  have hadC := liftCode (cr' := subCode) had
    (by unfold subCode u256SubBeInPlaceCr; code_mem)
  rw [show (u256SubBeFn fPtr bPtr outPtr fBytes bBytes outBytes).region =
      Region.empty from rfl,
    show (u256SubBeFn fPtr bPtr outPtr fBytes bBytes outBytes).rw.base =
      outPtr from rfl,
    show Region.empty.base = (0 : Word) from rfl,
    show Region.empty.bytes = ([] : List (BitVec 8)) from rfl,
    bytesRegion_nil, sepConj_emp_right'] at hadC
  rw [regFileIs_eq_regAtoms, regAtoms_eq_regAtomsOf _ _ (by decide),
    prioritySub_exposed_split,
    show rf0 .x10 = fPtr from by simp [rf0],
    show rf0 .x11 = bPtr from by simp [rf0],
    show rf0 .x12 = outPtr from by simp [rf0],
    regAtomsOf_congr rf0 vf prioritySubScratch
      (fun r hr => by
        unfold rf0
        rw [if_neg (prioritySub_args_notin_scratch r hr).1,
          if_neg (prioritySub_args_notin_scratch r hr).2.1,
          if_neg (prioritySub_args_notin_scratch r hr).2.2])]
    at hadC
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by rw [sepConj_emp_right'] at hq; xperm_hyp hq) hadC


-- @@ L274-277 verbatim
/-! The seven moves before the first call put the caller arguments in the
    saved-register locals and then expose the exact callee argument shape.
    This is kept separate from the call proofs so the register ownership
    ledger is visible at the first composition boundary. -/

-- @@ L278-369 verbatim
theorem priority_setup_spec
    (ret pPtr fPtr bPtr outPtr v8 v9 v18 v19 : Word)
    (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 7 (P + 24) (P + 52) fullCode
      (((.x1 : Reg) ↦ᵣ ret) ** (.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) **
        (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19) ** (.x10 ↦ᵣ pPtr) **
        (.x11 ↦ᵣ fPtr) ** (.x12 ↦ᵣ bPtr) ** (.x13 ↦ᵣ outPtr) ** F)
      (((.x1 : Reg) ↦ᵣ ret) ** (.x8 ↦ᵣ pPtr) ** (.x9 ↦ᵣ fPtr) **
        (.x18 ↦ᵣ bPtr) ** (.x19 ↦ᵣ outPtr) ** (.x10 ↦ᵣ fPtr) **
        (.x11 ↦ᵣ bPtr) ** (.x12 ↦ᵣ outPtr) ** regOwn .x13 ** F) := by
  have hmv8 := mv_spec_gen_within .x8 .x10 pPtr v8 (P + 24)
    (by decide)
  have hmv8c := cpsTripleWithin_extend_code
    (priority_mem 6 _ (P + 24) (by decide) (by decide) (by rfl)) hmv8
  have hmv8f := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ ret) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) **
      (.x19 ↦ᵣ v19) ** (.x11 ↦ᵣ fPtr) **
      (.x12 ↦ᵣ bPtr) ** (.x13 ↦ᵣ outPtr) ** F) (by pcf; exact hF) hmv8c
  have hmv9 := mv_spec_gen_within .x9 .x11 fPtr v9 (P + 28)
    (by decide)
  have hmv9c := cpsTripleWithin_extend_code
    (priority_mem 7 _ (P + 28) (by decide) (by decide) (by rfl)) hmv9
  have hmv9f := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ ret) ** (.x8 ↦ᵣ pPtr) ** (.x18 ↦ᵣ v18) **
      (.x19 ↦ᵣ v19) ** (.x10 ↦ᵣ pPtr) **
      (.x12 ↦ᵣ bPtr) ** (.x13 ↦ᵣ outPtr) ** F) (by pcf; exact hF) hmv9c
  have hmv18 := mv_spec_gen_within .x18 .x12 bPtr v18 (P + 32)
    (by decide)
  have hmv18c := cpsTripleWithin_extend_code
    (priority_mem 8 _ (P + 32) (by decide) (by decide) (by rfl)) hmv18
  have hmv18f := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ ret) ** (.x8 ↦ᵣ pPtr) ** (.x9 ↦ᵣ fPtr) **
      (.x19 ↦ᵣ v19) ** (.x10 ↦ᵣ pPtr) ** (.x11 ↦ᵣ fPtr) **
      (.x13 ↦ᵣ outPtr) ** F) (by pcf; exact hF) hmv18c
  have hmv19 := mv_spec_gen_within .x19 .x13 outPtr v19 (P + 36)
    (by decide)
  have hmv19c := cpsTripleWithin_extend_code
    (priority_mem 9 _ (P + 36) (by decide) (by decide) (by rfl)) hmv19
  have hmv19f := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ ret) ** (.x8 ↦ᵣ pPtr) ** (.x9 ↦ᵣ fPtr) **
      (.x18 ↦ᵣ bPtr) ** (.x10 ↦ᵣ pPtr) ** (.x11 ↦ᵣ fPtr) **
      (.x12 ↦ᵣ bPtr) ** F) (by pcf; exact hF) hmv19c
  have hmv10 := mv_spec_gen_within .x10 .x9 fPtr pPtr (P + 40)
    (by decide)
  have hmv10c := cpsTripleWithin_extend_code
    (priority_mem 10 _ (P + 40) (by decide) (by decide) (by rfl)) hmv10
  have hmv10f := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ ret) ** (.x8 ↦ᵣ pPtr) **
      (.x18 ↦ᵣ bPtr) ** (.x19 ↦ᵣ outPtr) ** (.x11 ↦ᵣ fPtr) **
      (.x12 ↦ᵣ bPtr) ** (.x13 ↦ᵣ outPtr) ** F) (by pcf; exact hF) hmv10c
  have hmv11 := mv_spec_gen_within .x11 .x18 bPtr fPtr (P + 44)
    (by decide)
  have hmv11c := cpsTripleWithin_extend_code
    (priority_mem 11 _ (P + 44) (by decide) (by decide) (by rfl)) hmv11
  have hmv11f := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ ret) ** (.x8 ↦ᵣ pPtr) ** (.x9 ↦ᵣ fPtr) **
      (.x19 ↦ᵣ outPtr) ** (.x10 ↦ᵣ fPtr) **
      (.x12 ↦ᵣ bPtr) ** (.x13 ↦ᵣ outPtr) ** F) (by pcf; exact hF) hmv11c
  have hmv12 := mv_spec_gen_within .x12 .x19 outPtr bPtr (P + 48)
    (by decide)
  have hmv12c := cpsTripleWithin_extend_code
    (priority_mem 12 _ (P + 48) (by decide) (by decide) (by rfl)) hmv12
  have hmv12f := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ ret) ** (.x8 ↦ᵣ pPtr) ** (.x9 ↦ᵣ fPtr) **
      (.x18 ↦ᵣ bPtr) ** (.x10 ↦ᵣ fPtr) **
      (.x11 ↦ᵣ bPtr) ** (.x13 ↦ᵣ outPtr) ** F) (by pcf; exact hF) hmv12c
  have h01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
    hmv8f hmv9f
  have h012 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
    h01 hmv18f
  have h0123 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
    h012 hmv19f
  have h01234 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
    h0123 hmv10f
  have h012345 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
    h01234 hmv11f
  have h0123456 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
    h012345 hmv12f
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun h_state hq => by
      let A : Assertion :=
        ((.x1 : Reg) ↦ᵣ ret) ** (.x8 ↦ᵣ pPtr) ** (.x9 ↦ᵣ fPtr) **
          (.x18 ↦ᵣ bPtr) ** (.x19 ↦ᵣ outPtr) ** (.x10 ↦ᵣ fPtr) **
          (.x11 ↦ᵣ bPtr) ** (.x12 ↦ᵣ outPtr)
      have hq' : ((A ** (.x13 ↦ᵣ outPtr)) ** F) h_state := by
        dsimp [A]
        xperm_hyp hq
      have hq'' : ((A ** regOwn .x13) ** F) h_state := by
        exact sepConj_mono_left
          (sepConj_mono_right (regIs_to_regOwn .x13 outPtr)) h_state hq'
      dsimp [A] at hq''
      xperm_hyp hq'') h0123456


-- @@ L371-380 verbatim
private theorem priority_sub_target :
    (P + 52) + signExtend21
        (jalOff GuestAddrs.u256_sub_be
          (GuestAddrs.priority_fee_per_gas_eip1559 + 52)) =
      (GuestAddrs.u256_sub_be : Word) := by
  change BitVec.ofNat 64 GuestAddrs.priority_fee_per_gas_eip1559 +
      BitVec.ofNat 64 52 + _ = BitVec.ofNat 64 GuestAddrs.u256_sub_be
  exact jalOff_correct_add GuestAddrs.u256_sub_be
    GuestAddrs.priority_fee_per_gas_eip1559 52
    (by decide) (by decide) (by decide) (by decide)


-- @@ L382-388 verbatim
private theorem priority_sub_mem :
    ∀ a i, CodeReq.singleton (P + 52)
      (.JAL .x1 (jalOff GuestAddrs.u256_sub_be
        (GuestAddrs.priority_fee_per_gas_eip1559 + 52))) a = some i →
      fullCode a = some i := by
  intro a i hi
  exact priority_mem 13 _ (P + 52) (by decide) (by decide) (by rfl) a i hi


-- @@ L390-392 verbatim
/-! The first call is the point where the alias-aware subtraction contract is
    actually consumed.  The frame carries the priority/base pointers and
    regions that the callee does not touch; it is not a decorative premise. -/

-- @@ L393-443 verbatim
private theorem priority_sub_call_core_spec
    (nSteps nSize : Nat) (ret fPtr bPtr outPtr : Word)
    (fBytes bBytes outBytes : List (BitVec 8))
    (hrw : RwRegion.wf ⟨outPtr, 32⟩)
    (hroF : Region.wf ⟨fPtr, fBytes⟩)
    (hroB : Region.wf ⟨bPtr, bBytes⟩)
    (hlenF : fBytes.length = 32)
    (hlenB : bBytes.length = 32)
    (hlenOut : outBytes.length = 32)
    (hovF : fPtr.toNat + 32 < 2 ^ 64)
    (hovB : bPtr.toNat + 32 < 2 ^ 64)
    (hovOut : outPtr.toNat + 32 < 2 ^ 64)
    (hdisjF : fPtr.toNat + 32 ≤ outPtr.toNat ∨
      outPtr.toNat + 32 ≤ fPtr.toNat)
    (hdisjB : bPtr.toNat + 32 ≤ outPtr.toNat ∨
      outPtr.toNat + 32 ≤ bPtr.toNat)
    (hsize : (prioritySubFn fPtr bPtr outPtr fBytes bBytes outBytes).body.size = nSize)
    (hsteps : (prioritySubFn fPtr bPtr outPtr fBytes bBytes outBytes).body.steps = nSteps)
    (hsz : 4 * (nSize + 1) ≤ 2 ^ 64)
    (hret : ((P + 52) + 4 &&& ~~~(1 : Word)) = P + 52 + 4) :
    cpsTripleWithin
      (1 + nSteps + 1)
      (P + 52) (P + 56) fullCode
      (prioritySubPre ret fPtr bPtr outPtr fBytes bBytes outBytes)
      (prioritySubPost fPtr bPtr outPtr fBytes bBytes outBytes) := by
  have hsz' : 4 * ((prioritySubFn fPtr bPtr outPtr fBytes bBytes outBytes).body.size + 1)
      ≤ 2 ^ 64 := by
    rw [hsize]
    exact hsz
  have hsub := prioritySubFlat_spec
    (P + 56) fPtr bPtr outPtr fBytes bBytes outBytes
    hrw hroF hroB hlenF hlenB hlenOut hovF hovB hovOut hdisjF hdisjB hsz' hret
  have hsubc := cpsTripleWithin_extend_code sub_full_mono hsub
  have hcall := callWithin_spec
    (cr := fullCode)
    (P := ((.x10 ↦ᵣ fPtr) ** (.x11 ↦ᵣ bPtr) ** (.x12 ↦ᵣ outPtr) **
      regOwns prioritySubScratch ** bytesRegion outPtr outBytes **
      bytesRegion fPtr fBytes ** bytesRegion bPtr bBytes))
    (Q := ((.x10 ↦ᵣ u256SubBeBorrow fBytes bBytes outBytes) **
      regOwns prioritySubRetScratch **
      bytesRegion outPtr (u256SubBeBytes fBytes bBytes outBytes) **
      bytesRegion fPtr fBytes ** bytesRegion bPtr bBytes))
    (P + 52) (GuestAddrs.u256_sub_be : Word) ret
    (jalOff GuestAddrs.u256_sub_be
      (GuestAddrs.priority_fee_per_gas_eip1559 + 52))
    ((prioritySubFn fPtr bPtr outPtr fBytes bBytes outBytes).body.steps + 1)
    priority_sub_target priority_sub_mem
    (by pcf)
    (by simpa only [show (P + 52) + 4 = P + 56 by bv_omega] using hsubc)
  rw [show P + 52 + 4 = P + 56 by bv_omega, hsteps] at hcall
  simpa only [prioritySubFn, prioritySubPre, prioritySubPost, Nat.add_assoc] using hcall


-- @@ L445-482 verbatim
theorem priority_sub_call_spec
    (ret pPtr fPtr bPtr outPtr : Word)
    (fBytes bBytes outBytes : List (BitVec 8)) (F : Assertion)
    (hF : F.pcFree)
    (hrw : RwRegion.wf ⟨outPtr, 32⟩)
    (hroF : Region.wf ⟨fPtr, fBytes⟩)
    (hroB : Region.wf ⟨bPtr, bBytes⟩)
    (hlenF : fBytes.length = 32)
    (hlenB : bBytes.length = 32)
    (hlenOut : outBytes.length = 32)
    (hovF : fPtr.toNat + 32 < 2 ^ 64)
    (hovB : bPtr.toNat + 32 < 2 ^ 64)
    (hovOut : outPtr.toNat + 32 < 2 ^ 64)
    (hdisjF : fPtr.toNat + 32 ≤ outPtr.toNat ∨
      outPtr.toNat + 32 ≤ fPtr.toNat)
    (hdisjB : bPtr.toNat + 32 ≤ outPtr.toNat ∨
      outPtr.toNat + 32 ≤ bPtr.toNat)
    (hsz : 4 * ((prioritySubFn fPtr bPtr outPtr fBytes bBytes outBytes).body.size + 1)
      ≤ 2 ^ 64)
    (hret : ((P + 52) + 4 &&& ~~~(1 : Word)) = P + 52 + 4) :
    cpsTripleWithin
      (1 + (prioritySubFn fPtr bPtr outPtr fBytes bBytes outBytes).body.steps + 1)
      (P + 52) (P + 56) fullCode
      ((prioritySubPre ret fPtr bPtr outPtr fBytes bBytes outBytes) **
        ((.x8 ↦ᵣ pPtr) ** (.x9 ↦ᵣ fPtr) ** (.x18 ↦ᵣ bPtr) **
          (.x19 ↦ᵣ outPtr) ** F))
      ((prioritySubPost fPtr bPtr outPtr fBytes bBytes outBytes) **
        ((.x8 ↦ᵣ pPtr) ** (.x9 ↦ᵣ fPtr) ** (.x18 ↦ᵣ bPtr) **
          (.x19 ↦ᵣ outPtr) ** F)) := by
  exact cpsTripleWithin_frameR
    ((.x8 ↦ᵣ pPtr) ** (.x9 ↦ᵣ fPtr) ** (.x18 ↦ᵣ bPtr) **
      (.x19 ↦ᵣ outPtr) ** F)
    (by pcf; exact hF)
    (priority_sub_call_core_spec
      ((prioritySubFn fPtr bPtr outPtr fBytes bBytes outBytes).body.steps)
      ((prioritySubFn fPtr bPtr outPtr fBytes bBytes outBytes).body.size)
      ret fPtr bPtr outPtr fBytes bBytes outBytes hrw hroF hroB hlenF hlenB
      hlenOut hovF hovB hovOut hdisjF hdisjB rfl rfl hsz hret)


-- @@ L484-522 verbatim
/-- The full premise set of the linked subtraction adapter is inhabited at a
    concrete, disjoint four-buffer layout.  In particular, the generalized
    body indices in `priority_sub_call_core_spec` are instantiated at the
    actual `Fn` projections rather than left as an unconsumed abstraction. -/
theorem priority_sub_call_spec_concrete :
    cpsTripleWithin
      (1 + (prioritySubFn (0x1000 : Word) (0x4000 : Word) (0x2000 : Word)
        (List.replicate 32 (0 : BitVec 8))
        (List.replicate 32 (0 : BitVec 8))
        (List.replicate 32 (0 : BitVec 8))).body.steps + 1)
      (P + 52) (P + 56) fullCode
      ((prioritySubPre (P + 56) (0x1000 : Word) (0x4000 : Word) (0x2000 : Word)
          (List.replicate 32 (0 : BitVec 8))
          (List.replicate 32 (0 : BitVec 8))
          (List.replicate 32 (0 : BitVec 8))) **
        ((.x8 ↦ᵣ (0x3000 : Word)) ** (.x9 ↦ᵣ (0x1000 : Word)) **
          (.x18 ↦ᵣ (0x4000 : Word)) ** (.x19 ↦ᵣ (0x2000 : Word)) **
          empAssertion))
      ((prioritySubPost (0x1000 : Word) (0x4000 : Word) (0x2000 : Word)
          (List.replicate 32 (0 : BitVec 8))
          (List.replicate 32 (0 : BitVec 8))
          (List.replicate 32 (0 : BitVec 8))) **
        ((.x8 ↦ᵣ (0x3000 : Word)) ** (.x9 ↦ᵣ (0x1000 : Word)) **
          (.x18 ↦ᵣ (0x4000 : Word)) ** (.x19 ↦ᵣ (0x2000 : Word)) **
          empAssertion)) := by
  have hsz :
      4 * ((prioritySubFn (0x1000 : Word) (0x4000 : Word) (0x2000 : Word)
        (List.replicate 32 (0 : BitVec 8))
        (List.replicate 32 (0 : BitVec 8))
        (List.replicate 32 (0 : BitVec 8))).body.size + 1) ≤ 2 ^ 64 := by
    simp only [prioritySubFn]
    decide
  exact priority_sub_call_spec
    (P + 56) (0x3000 : Word) (0x1000 : Word) (0x4000 : Word) (0x2000 : Word)
    (List.replicate 32 (0 : BitVec 8))
    (List.replicate 32 (0 : BitVec 8))
    (List.replicate 32 (0 : BitVec 8)) empAssertion pcFree_emp
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) hsz (by decide)


-- @@ L524-533 verbatim
private theorem priority_min_target :
    (P + 72) + signExtend21
        (jalOff GuestAddrs.u256_min
          (GuestAddrs.priority_fee_per_gas_eip1559 + 72)) =
      (GuestAddrs.u256_min : Word) := by
  change BitVec.ofNat 64 GuestAddrs.priority_fee_per_gas_eip1559 +
      BitVec.ofNat 64 72 + _ = BitVec.ofNat 64 GuestAddrs.u256_min
  exact jalOff_correct_add GuestAddrs.u256_min
    GuestAddrs.priority_fee_per_gas_eip1559 72
    (by decide) (by decide) (by decide) (by decide)


-- @@ L535-541 verbatim
private theorem priority_min_mem :
    ∀ a i, CodeReq.singleton (P + 72)
      (.JAL .x1 (jalOff GuestAddrs.u256_min
        (GuestAddrs.priority_fee_per_gas_eip1559 + 72))) a = some i →
      fullCode a = some i := by
  intro a i hi
  exact priority_mem 18 _ (P + 72) (by decide) (by decide) (by rfl) a i hi


-- @@ L543-546 verbatim
/-! The second call consumes the B-in-place minimum contract.  Its return link
    is the next instruction after the call, and the surrounding caller frame is
    carried separately so the callee's six scratch registers do not get
    accidentally duplicated in the call precondition. -/

-- @@ L547-622 verbatim
private theorem priority_min_call_spec
    (pPtr outPtr : Word) (pBytes outBytes : List (BitVec 8))
    (F : Assertion) (hF : F.pcFree)
    (hlenP : pBytes.length = 32) (hlenOut : outBytes.length = 32)
    (halignP : pPtr.toNat % 8 = 0) (halignOut : outPtr.toNat % 8 = 0)
    (hovP : pPtr.toNat + 32 < 2 ^ 64)
    (hovOut : outPtr.toNat + 32 < 2 ^ 64)
    (hvalidP : ∀ k, k < 32 →
      isValidByteAccess (pPtr + BitVec.ofNat 64 k) = true)
    (hvalidOut : ∀ k, k < 32 →
      isValidByteAccess (outPtr + BitVec.ofNat 64 k) = true)
    (hret : ((P + 72) + 4 &&& ~~~(1 : Word)) = P + 72 + 4) :
    cpsTripleWithin 309 (P + 72) (P + 76) fullCode
      ((((.x1 : Reg) ↦ᵣ (P + 56)) **
        ((.x10 ↦ᵣ pPtr) ** (.x11 ↦ᵣ outPtr) ** (.x12 ↦ᵣ outPtr) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
          regOwn .x29 ** regOwn .x31 ** bytesRegion pPtr pBytes **
          bytesRegion outPtr outBytes)) ** F)
      ((((.x1 : Reg) ↦ᵣ (P + 76)) **
        ((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ outPtr) **
          (.x12 ↦ᵣ outPtr) **
          (.x5 ↦ᵣ (if beBytesToNat pBytes ≤ beBytesToNat outBytes
            then pPtr else outPtr)) **
          regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          (.x31 ↦ᵣ (32 : Word)) ** bytesRegion pPtr pBytes **
          bytesRegion outPtr
            (if beBytesToNat pBytes ≤ beBytesToNat outBytes
              then pBytes else outBytes))) ** F) := by
  have hmin := u256MinBInPlace_spec
    pPtr outPtr (P + 76) pBytes outBytes
    hlenP hlenOut halignP halignOut hovP hovOut hvalidP hvalidOut hret
  have hminc := cpsTripleWithin_extend_code min_full_mono hmin
  have hminc' : cpsTripleWithin 308 (GuestAddrs.u256_min : Word) (P + 76)
      fullCode
      (((.x1 : Reg) ↦ᵣ (P + 76)) **
        ((.x10 ↦ᵣ pPtr) ** (.x11 ↦ᵣ outPtr) ** (.x12 ↦ᵣ outPtr) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
          regOwn .x29 ** regOwn .x31 ** bytesRegion pPtr pBytes **
          bytesRegion outPtr outBytes))
      (((.x1 : Reg) ↦ᵣ (P + 76)) **
        ((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ outPtr) **
          (.x12 ↦ᵣ outPtr) **
          (.x5 ↦ᵣ (if beBytesToNat pBytes ≤ beBytesToNat outBytes
            then pPtr else outPtr)) **
          regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          (.x31 ↦ᵣ (32 : Word)) ** bytesRegion pPtr pBytes **
          bytesRegion outPtr
            (if beBytesToNat pBytes ≤ beBytesToNat outBytes
              then pBytes else outBytes))) := by
    exact cpsTripleWithin_weaken
      (fun _ hp => by xperm_hyp hp) (fun _ hq => by xperm_hyp hq) hminc
  have hcall := callWithin_spec
    (cr := fullCode)
    (P := ((.x10 ↦ᵣ pPtr) ** (.x11 ↦ᵣ outPtr) ** (.x12 ↦ᵣ outPtr) **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
      regOwn .x29 ** regOwn .x31 ** bytesRegion pPtr pBytes **
      bytesRegion outPtr outBytes))
    (Q := ((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ outPtr) **
      (.x12 ↦ᵣ outPtr) **
      (.x5 ↦ᵣ (if beBytesToNat pBytes ≤ beBytesToNat outBytes
        then pPtr else outPtr)) **
      regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
      (.x31 ↦ᵣ (32 : Word)) ** bytesRegion pPtr pBytes **
      bytesRegion outPtr
        (if beBytesToNat pBytes ≤ beBytesToNat outBytes
          then pBytes else outBytes)))
    (P + 72) (GuestAddrs.u256_min : Word) (P + 56)
    (jalOff GuestAddrs.u256_min
      (GuestAddrs.priority_fee_per_gas_eip1559 + 72))
    308 priority_min_target priority_min_mem
    (by pcf)
    (by simpa only [show P + 72 + 4 = P + 76 by bv_omega] using hminc')
  have hcallF := cpsTripleWithin_frameR F hF hcall
  rw [show (1 : Nat) + 308 = 309 from by decide,
    show P + 72 + 4 = P + 76 from by bv_omega] at hcallF
  simpa only [sepConj_assoc] using hcallF


-- @@ L624-626 verbatim
/-! The branch and failure arm are kept separate from the arithmetic call.  The
    status bit is a postcondition of subtraction, so neither branch theorem
    assumes which arm was taken at its entry. -/

-- @@ L627-647 verbatim
private theorem priority_status_branch_spec
    (status : Word) (F : Assertion) (hF : F.pcFree) :
    cpsBranchWithin 1 (P + 56) fullCode
      (((.x10 : Reg) ↦ᵣ status) ** (.x0 ↦ᵣ (0 : Word)) ** F)
      (P + 84)
      (((.x10 : Reg) ↦ᵣ status) ** (.x0 ↦ᵣ (0 : Word)) **
        ⌜status ≠ 0⌝ ** F)
      (P + 60)
      (((.x10 : Reg) ↦ᵣ status) ** (.x0 ↦ᵣ (0 : Word)) **
        ⌜status = 0⌝ ** F) := by
  let off : BitVec 13 := 28
  have hbne := bne_spec_gen_within .x10 .x0 off status (0 : Word) (P + 56)
  rw [show (P + 56) + signExtend13 off = P + 84 by decide,
    show (P + 56) + 4 = P + 60 by bv_omega] at hbne
  have hbnee := cpsBranchWithin_extend_code
    (priority_mem 14 _ (P + 56) (by decide) (by decide) (by rfl)) hbne
  have hbr := cpsBranchWithin_frameR F hF hbnee
  exact cpsBranchWithin_weaken
    (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq)
    (fun _ hq => by xperm_hyp hq) hbr


-- @@ L649-661 verbatim
private theorem priority_failure_spec (status : Word) (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 1 (P + 84) (P + 88) fullCode
      (((.x10 : Reg) ↦ᵣ status) ** F)
      (((.x10 : Reg) ↦ᵣ (1 : Word)) ** F) := by
  have hli := li_spec_gen_within .x10 status (1 : Word) (P + 84)
    (by decide)
  rw [show P + 84 + 4 = P + 88 by bv_omega] at hli
  have hlic := cpsTripleWithin_extend_code
    (priority_mem 21 _ (P + 84) (by decide) (by decide) (by rfl)) hli
  have hliF := cpsTripleWithin_frameR F hF hlic
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hliF


-- @@ L663-664 verbatim
def priorityMinScratch : List Reg :=
  [.x5, .x6, .x7, .x28, .x29, .x31]


-- @@ L666-667 verbatim
def prioritySubResidualScratch : List Reg :=
  [.x30, .x14, .x15, .x16, .x17]


-- @@ L669-671 verbatim
def prioritySetupScratch : List Reg :=
  [.x5, .x6, .x7, .x28, .x29, .x30, .x31,
   .x14, .x15, .x16, .x17]


-- @@ L673-680 verbatim
private theorem prioritySubRetScratch_split :
    (regOwns prioritySubRetScratch) =
      (regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
        regOwns priorityMinScratch ** regOwns prioritySubResidualScratch) := by
  simp only [prioritySubRetScratch, priorityMinScratch,
    prioritySubResidualScratch, regOwns_cons, regOwns_nil,
    sepConj_emp_right']
  xperm


-- @@ L682-687 verbatim
private theorem prioritySubScratch_split :
    (regOwns prioritySubScratch) =
      (regOwn .x13 ** regOwns prioritySetupScratch) := by
  simp only [prioritySubScratch, prioritySetupScratch,
    regOwns_cons, regOwns_nil, sepConj_emp_right']
  xperm


-- @@ L689-790 verbatim
private theorem priority_success_moves_spec
    (pPtr fPtr bPtr outPtr : Word) (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 3 (P + 60) (P + 72) fullCode
      (((.x1 : Reg) ↦ᵣ (P + 56)) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x8 ↦ᵣ pPtr) ** (.x9 ↦ᵣ fPtr) ** (.x18 ↦ᵣ bPtr) **
        (.x19 ↦ᵣ outPtr) ** (.x10 ↦ᵣ (0 : Word)) **
        regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** F)
      (((.x1 : Reg) ↦ᵣ (P + 56)) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x8 ↦ᵣ pPtr) ** (.x9 ↦ᵣ fPtr) ** (.x18 ↦ᵣ bPtr) **
        (.x19 ↦ᵣ outPtr) ** (.x10 ↦ᵣ pPtr) **
        (.x11 ↦ᵣ outPtr) ** (.x12 ↦ᵣ outPtr) ** regOwn .x13 ** F) := by
  have hmv10 := mv_spec_gen_within .x10 .x8 pPtr (0 : Word) (P + 60)
    (by decide)
  have hmv10c := cpsTripleWithin_extend_code
    (priority_mem 15 _ (P + 60) (by decide) (by decide) (by rfl)) hmv10
  have hmv10f := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ (P + 56)) ** (.x0 ↦ᵣ (0 : Word)) **
      (.x9 ↦ᵣ fPtr) ** (.x18 ↦ᵣ bPtr) ** (.x19 ↦ᵣ outPtr) **
      regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** F)
    (by pcf; exact hF) hmv10c
  have hmv11raw : ∀ old11, cpsTripleWithin 1 (P + 64) (P + 68) fullCode
      (((.x11 : Reg) ↦ᵣ old11) **
        (((.x1 : Reg) ↦ᵣ (P + 56)) ** (.x0 ↦ᵣ (0 : Word)) **
          (.x8 ↦ᵣ pPtr) ** (.x9 ↦ᵣ fPtr) ** (.x18 ↦ᵣ bPtr) **
          (.x19 ↦ᵣ outPtr) ** (.x10 ↦ᵣ pPtr) ** regOwn .x12 **
          regOwn .x13 ** F))
      (((.x11 : Reg) ↦ᵣ outPtr) **
        (((.x1 : Reg) ↦ᵣ (P + 56)) ** (.x0 ↦ᵣ (0 : Word)) **
          (.x8 ↦ᵣ pPtr) ** (.x9 ↦ᵣ fPtr) ** (.x18 ↦ᵣ bPtr) **
          (.x19 ↦ᵣ outPtr) ** (.x10 ↦ᵣ pPtr) ** regOwn .x12 **
          regOwn .x13 ** F)) := by
    intro old11
    have hmv11 := mv_spec_gen_within .x11 .x19 outPtr old11 (P + 64)
      (by decide)
    have hmv11c := cpsTripleWithin_extend_code
      (priority_mem 16 _ (P + 64) (by decide) (by decide) (by rfl)) hmv11
    have hmv11f := cpsTripleWithin_frameR
      (((.x1 : Reg) ↦ᵣ (P + 56)) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x8 ↦ᵣ pPtr) ** (.x9 ↦ᵣ fPtr) ** (.x18 ↦ᵣ bPtr) **
        (.x10 ↦ᵣ pPtr) ** regOwn .x12 ** regOwn .x13 ** F)
      (by pcf; exact hF) hmv11c
    exact cpsTripleWithin_weaken
      (fun _ hp => by xperm_hyp hp) (fun _ hq => by xperm_hyp hq) hmv11f
  have hmv11own : cpsTripleWithin 1 (P + 64) (P + 68) fullCode
      (((((.x1 : Reg) ↦ᵣ (P + 56)) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x8 ↦ᵣ pPtr) ** (.x9 ↦ᵣ fPtr) ** (.x18 ↦ᵣ bPtr) **
        (.x19 ↦ᵣ outPtr) ** (.x10 ↦ᵣ pPtr) ** regOwn .x12 **
        regOwn .x13 ** F)) ** regOwn .x11)
      (((.x11 : Reg) ↦ᵣ outPtr) **
        ((.x1 ↦ᵣ (P + 56)) ** (.x0 ↦ᵣ (0 : Word)) **
          (.x8 ↦ᵣ pPtr) ** (.x9 ↦ᵣ fPtr) ** (.x18 ↦ᵣ bPtr) **
          (.x19 ↦ᵣ outPtr) ** (.x10 ↦ᵣ pPtr) ** regOwn .x12 **
          regOwn .x13 ** F)) := by
    apply cpsTripleWithin_of_forall_regIs_to_regOwn
    intro old11
    exact cpsTripleWithin_weaken
      (fun _ hp => by xperm_hyp hp) (fun _ hq => by xperm_hyp hq)
      (hmv11raw old11)
  have hmv12raw : ∀ old12, cpsTripleWithin 1 (P + 68) (P + 72) fullCode
      (((.x12 : Reg) ↦ᵣ old12) **
        (((.x1 : Reg) ↦ᵣ (P + 56)) ** (.x0 ↦ᵣ (0 : Word)) **
          (.x8 ↦ᵣ pPtr) ** (.x9 ↦ᵣ fPtr) ** (.x18 ↦ᵣ bPtr) **
          (.x19 ↦ᵣ outPtr) ** (.x10 ↦ᵣ pPtr) ** (.x11 ↦ᵣ outPtr) **
          regOwn .x13 ** F))
      (((.x12 : Reg) ↦ᵣ outPtr) **
        (((.x1 : Reg) ↦ᵣ (P + 56)) ** (.x0 ↦ᵣ (0 : Word)) **
          (.x8 ↦ᵣ pPtr) ** (.x9 ↦ᵣ fPtr) ** (.x18 ↦ᵣ bPtr) **
          (.x19 ↦ᵣ outPtr) ** (.x10 ↦ᵣ pPtr) ** (.x11 ↦ᵣ outPtr) **
          regOwn .x13 ** F)) := by
    intro old12
    have hmv12 := mv_spec_gen_within .x12 .x19 outPtr old12 (P + 68)
      (by decide)
    have hmv12c := cpsTripleWithin_extend_code
      (priority_mem 17 _ (P + 68) (by decide) (by decide) (by rfl)) hmv12
    have hmv12f := cpsTripleWithin_frameR
      (((.x1 : Reg) ↦ᵣ (P + 56)) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x8 ↦ᵣ pPtr) ** (.x9 ↦ᵣ fPtr) ** (.x18 ↦ᵣ bPtr) **
        (.x10 ↦ᵣ pPtr) ** (.x11 ↦ᵣ outPtr) ** regOwn .x13 ** F)
      (by pcf; exact hF) hmv12c
    exact cpsTripleWithin_weaken
      (fun _ hp => by xperm_hyp hp) (fun _ hq => by xperm_hyp hq) hmv12f
  have hmv12own : cpsTripleWithin 1 (P + 68) (P + 72) fullCode
      (((((.x1 : Reg) ↦ᵣ (P + 56)) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x8 ↦ᵣ pPtr) ** (.x9 ↦ᵣ fPtr) ** (.x18 ↦ᵣ bPtr) **
        (.x19 ↦ᵣ outPtr) ** (.x10 ↦ᵣ pPtr) ** (.x11 ↦ᵣ outPtr) **
        regOwn .x13 ** F)) ** regOwn .x12)
      (((.x12 : Reg) ↦ᵣ outPtr) **
        ((.x1 ↦ᵣ (P + 56)) ** (.x0 ↦ᵣ (0 : Word)) **
          (.x8 ↦ᵣ pPtr) ** (.x9 ↦ᵣ fPtr) ** (.x18 ↦ᵣ bPtr) **
          (.x19 ↦ᵣ outPtr) ** (.x10 ↦ᵣ pPtr) ** (.x11 ↦ᵣ outPtr) **
          regOwn .x13 ** F)) := by
    apply cpsTripleWithin_of_forall_regIs_to_regOwn
    intro old12
    exact cpsTripleWithin_weaken
      (fun _ hp => by xperm_hyp hp) (fun _ hq => by xperm_hyp hq)
      (hmv12raw old12)
  have h01 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hmv10f hmv11own
  have h012 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) h01 hmv12own
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_hyp hp) (fun _ hq => by xperm_hyp hq) h012


-- @@ L792-813 verbatim
private theorem priority_success_tail_spec (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 2 (P + 76) (P + 88) fullCode
      (((.x10 : Reg) ↦ᵣ (0 : Word)) ** F)
      (((.x10 : Reg) ↦ᵣ (0 : Word)) ** F) := by
  have hli := li_spec_gen_within .x10 (0 : Word) (0 : Word) (P + 76)
    (by decide)
  rw [show P + 76 + 4 = P + 80 by bv_omega] at hli
  have hlic := cpsTripleWithin_extend_code
    (priority_mem 19 _ (P + 76) (by decide) (by decide) (by rfl)) hli
  have hlicF := cpsTripleWithin_frameR F hF hlic
  have hjal := jal_x0_spec_gen_within (8 : BitVec 21) (P + 80)
  rw [show P + 80 + signExtend21 (8 : BitVec 21) = P + 88 by decide] at hjal
  have hjale := cpsTripleWithin_extend_code
    (priority_mem 20 _ (P + 80) (by decide) (by decide) (by rfl)) hjal
  have hjalF := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ (0 : Word)) ** F)
    (pcFree_sepConj pcFree_regIs hF) hjale
  rw [sepConj_emp_left'] at hjalF
  have hseq := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hlicF hjalF
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_hyp hp) (fun _ hq => by xperm_hyp hq) hseq


-- @@ L815-900 verbatim
private theorem priority_success_path_spec
    (pPtr fPtr bPtr outPtr : Word) (pBytes subBytes : List (BitVec 8))
    (F : Assertion) (hF : F.pcFree)
    (hlenP : pBytes.length = 32) (hlenOut : subBytes.length = 32)
    (halignP : pPtr.toNat % 8 = 0) (halignOut : outPtr.toNat % 8 = 0)
    (hovP : pPtr.toNat + 32 < 2 ^ 64)
    (hovOut : outPtr.toNat + 32 < 2 ^ 64)
    (hvalidP : ∀ k, k < 32 →
      isValidByteAccess (pPtr + BitVec.ofNat 64 k) = true)
    (hvalidOut : ∀ k, k < 32 →
      isValidByteAccess (outPtr + BitVec.ofNat 64 k) = true)
    (hret : ((P + 72) + 4 &&& ~~~(1 : Word)) = P + 72 + 4) :
    cpsTripleWithin (3 + 309 + 2) (P + 60) (P + 88) fullCode
      (((.x1 : Reg) ↦ᵣ (P + 56)) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x8 ↦ᵣ pPtr) ** (.x9 ↦ᵣ fPtr) ** (.x18 ↦ᵣ bPtr) **
        (.x19 ↦ᵣ outPtr) ** (.x10 ↦ᵣ (0 : Word)) **
        regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
        regOwns priorityMinScratch ** bytesRegion pPtr pBytes **
        bytesRegion outPtr subBytes ** F)
      (((.x10 : Reg) ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ outPtr) **
        (.x12 ↦ᵣ outPtr) **
        (.x1 ↦ᵣ (P + 76)) **
        (.x5 ↦ᵣ (if beBytesToNat pBytes ≤ beBytesToNat subBytes
          then pPtr else outPtr)) **
        regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        (.x31 ↦ᵣ (32 : Word)) ** bytesRegion pPtr pBytes **
        bytesRegion outPtr
          (if beBytesToNat pBytes ≤ beBytesToNat subBytes
            then pBytes else subBytes) **
        (.x0 ↦ᵣ (0 : Word)) ** (.x8 ↦ᵣ pPtr) ** (.x9 ↦ᵣ fPtr) **
        (.x18 ↦ᵣ bPtr) ** (.x19 ↦ᵣ outPtr) ** regOwn .x13 ** F) := by
  let Fmin : Assertion :=
    ((.x0 : Reg) ↦ᵣ (0 : Word)) ** (.x8 ↦ᵣ pPtr) ** (.x9 ↦ᵣ fPtr) **
      (.x18 ↦ᵣ bPtr) ** (.x19 ↦ᵣ outPtr) ** regOwn .x13 ** F
  have hFmin : Fmin.pcFree := by
    dsimp [Fmin]
    pcf
    exact hF
  let Fmoves : Assertion :=
    regOwns priorityMinScratch ** bytesRegion pPtr pBytes **
      bytesRegion outPtr subBytes ** F
  have hFmoves : Fmoves.pcFree := by
    dsimp [Fmoves]
    pcf
    exact hF
  have hmoves := priority_success_moves_spec
    pPtr fPtr bPtr outPtr Fmoves hFmoves
  have hmin := priority_min_call_spec
    pPtr outPtr pBytes subBytes Fmin hFmin hlenP hlenOut
    halignP halignOut hovP hovOut hvalidP hvalidOut hret
  have hmoveMin := cpsTripleWithin_seq_perm_same_cr
    (fun _ hq => by
      dsimp [Fmoves, Fmin] at hq ⊢
      simp only [priorityMinScratch, regOwns_cons, regOwns_nil,
        sepConj_comm', sepConj_left_comm', sepConj_emp_left'] at hq ⊢
      xperm_hyp hq)
    hmoves hmin
  let Ftail : Assertion :=
    ((.x1 : Reg) ↦ᵣ (P + 76)) ** ((.x11 : Reg) ↦ᵣ outPtr) **
      (.x12 ↦ᵣ outPtr) **
      (.x5 ↦ᵣ (if beBytesToNat pBytes ≤ beBytesToNat subBytes
        then pPtr else outPtr)) **
      regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
      (.x31 ↦ᵣ (32 : Word)) ** bytesRegion pPtr pBytes **
      bytesRegion outPtr
        (if beBytesToNat pBytes ≤ beBytesToNat subBytes
          then pBytes else subBytes) ** Fmin
  have hFtail : Ftail.pcFree := by
    dsimp [Ftail]
    pcf
    exact hF
  have htail := priority_success_tail_spec Ftail hFtail
  have hfinal := cpsTripleWithin_seq_perm_same_cr
    (fun _ hq => by
      dsimp [Ftail, Fmin] at hq ⊢
      xperm_hyp hq)
    hmoveMin htail
  exact cpsTripleWithin_weaken
    (fun _ hp => by
      dsimp [P, Fmoves] at hp ⊢
      xperm_hyp hp)
    (fun _ hq => by
      dsimp [P, Ftail, Fmin] at hq ⊢
      simp only [sepConj_comm', sepConj_left_comm']
      xperm_hyp hq)
    hfinal


-- @@ L902-918 verbatim
def prioritySuccessPost
    (pPtr fPtr bPtr outPtr : Word)
    (pBytes fBytes bBytes subBytes : List (BitVec 8))
    (F : Assertion) : Assertion :=
  ((.x10 : Reg) ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ outPtr) **
    (.x12 ↦ᵣ outPtr) ** (.x1 ↦ᵣ (P + 76)) **
    (.x5 ↦ᵣ (if beBytesToNat pBytes ≤ beBytesToNat subBytes
      then pPtr else outPtr)) **
    regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
    (.x31 ↦ᵣ (32 : Word)) ** bytesRegion pPtr pBytes **
    bytesRegion outPtr
      (if beBytesToNat pBytes ≤ beBytesToNat subBytes
        then pBytes else subBytes) ** (.x0 ↦ᵣ (0 : Word)) **
    (.x8 ↦ᵣ pPtr) ** (.x9 ↦ᵣ fPtr) ** (.x18 ↦ᵣ bPtr) **
    (.x19 ↦ᵣ outPtr) ** regOwn .x13 **
    regOwns prioritySubResidualScratch ** bytesRegion fPtr fBytes **
    bytesRegion bPtr bBytes ** F


-- @@ L920-929 verbatim
def priorityFailurePost
    (status : Word) (pPtr fPtr bPtr outPtr : Word)
    (pBytes fBytes bBytes subBytes : List (BitVec 8))
    (F : Assertion) : Assertion :=
  ((.x10 : Reg) ↦ᵣ (1 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
    ⌜status ≠ 0⌝ ** (.x1 ↦ᵣ (P + 56)) **
    regOwns prioritySubRetScratch ** bytesRegion outPtr subBytes **
    bytesRegion fPtr fBytes ** bytesRegion bPtr bBytes **
    (.x8 ↦ᵣ pPtr) ** (.x9 ↦ᵣ fPtr) ** (.x18 ↦ᵣ bPtr) **
    (.x19 ↦ᵣ outPtr) ** bytesRegion pPtr pBytes ** F


-- @@ L931-937 verbatim
private def priorityBodyPost
    (status : Word) (pPtr fPtr bPtr outPtr : Word)
    (pBytes fBytes bBytes subBytes : List (BitVec 8))
    (F : Assertion) : Assertion :=
  fun h =>
    prioritySuccessPost pPtr fPtr bPtr outPtr pBytes fBytes bBytes subBytes F h ∨
      priorityFailurePost status pPtr fPtr bPtr outPtr pBytes fBytes bBytes subBytes F h


-- @@ L939-947 verbatim
private def priorityBranchPre
    (status : Word) (pPtr fPtr bPtr outPtr : Word)
    (pBytes fBytes bBytes subBytes : List (BitVec 8))
    (F : Assertion) : Assertion :=
  ((.x10 : Reg) ↦ᵣ status) ** (.x0 ↦ᵣ (0 : Word)) **
    (.x1 ↦ᵣ (P + 56)) ** regOwns prioritySubRetScratch **
    bytesRegion outPtr subBytes ** bytesRegion fPtr fBytes **
    bytesRegion bPtr bBytes ** (.x8 ↦ᵣ pPtr) ** (.x9 ↦ᵣ fPtr) **
    (.x18 ↦ᵣ bPtr) ** (.x19 ↦ᵣ outPtr) ** bytesRegion pPtr pBytes ** F


-- @@ L949-1039 verbatim
private theorem priority_status_paths_spec
    (status pPtr fPtr bPtr outPtr : Word)
    (pBytes fBytes bBytes subBytes : List (BitVec 8))
    (F : Assertion) (hF : F.pcFree)
    (hlenP : pBytes.length = 32) (hlenOut : subBytes.length = 32)
    (halignP : pPtr.toNat % 8 = 0) (halignOut : outPtr.toNat % 8 = 0)
    (hovP : pPtr.toNat + 32 < 2 ^ 64)
    (hovOut : outPtr.toNat + 32 < 2 ^ 64)
    (hvalidP : ∀ k, k < 32 →
      isValidByteAccess (pPtr + BitVec.ofNat 64 k) = true)
    (hvalidOut : ∀ k, k < 32 →
      isValidByteAccess (outPtr + BitVec.ofNat 64 k) = true)
    (hret : ((P + 72) + 4 &&& ~~~(1 : Word)) = P + 72 + 4) :
    cpsTripleWithin (1 + (3 + 309 + 2)) (P + 56) (P + 88) fullCode
      (priorityBranchPre status pPtr fPtr bPtr outPtr
        pBytes fBytes bBytes subBytes F)
      (priorityBodyPost status pPtr fPtr bPtr outPtr
        pBytes fBytes bBytes subBytes F) := by
  let Fbranch : Assertion :=
    ((.x1 : Reg) ↦ᵣ (P + 56)) ** regOwns prioritySubRetScratch **
      bytesRegion outPtr subBytes ** bytesRegion fPtr fBytes **
      bytesRegion bPtr bBytes ** (.x8 ↦ᵣ pPtr) ** (.x9 ↦ᵣ fPtr) **
      (.x18 ↦ᵣ bPtr) ** (.x19 ↦ᵣ outPtr) ** bytesRegion pPtr pBytes ** F
  have hFbranch : Fbranch.pcFree := by
    dsimp [Fbranch]
    pcf
    exact hF
  have hbranch := priority_status_branch_spec status Fbranch hFbranch
  let Fsuccess : Assertion :=
    regOwns prioritySubResidualScratch ** bytesRegion fPtr fBytes **
      bytesRegion bPtr bBytes ** F
  have hFsuccess : Fsuccess.pcFree := by
    dsimp [Fsuccess]
    pcf
    exact hF
  have hsuccess0 := priority_success_path_spec
    pPtr fPtr bPtr outPtr pBytes subBytes Fsuccess hFsuccess
    hlenP hlenOut halignP halignOut hovP hovOut hvalidP hvalidOut hret
  let Ffail : Assertion :=
    ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ⌜status ≠ 0⌝ ** Fbranch
  have hFfail : Ffail.pcFree := by
    dsimp [Ffail, Fbranch]
    pcf
    exact hF
  have hfailure0 := priority_failure_spec status Ffail hFfail
  let SuccessPost : Assertion :=
    prioritySuccessPost pPtr fPtr bPtr outPtr pBytes fBytes bBytes subBytes F
  let FailurePost : Assertion :=
    priorityFailurePost status pPtr fPtr bPtr outPtr pBytes fBytes bBytes subBytes F
  let BodyPost : Assertion := fun h => SuccessPost h ∨ FailurePost h
  have hsuccess : cpsTripleWithin (3 + 309 + 2) (P + 60) (P + 88) fullCode
      (((.x10 : Reg) ↦ᵣ status) ** (.x0 ↦ᵣ (0 : Word)) **
        ⌜status = 0⌝ ** Fbranch) BodyPost := by
    refine cpsTripleWithin_weaken (fun _ hp => by
      extract_pure_deep hp
      obtain ⟨hstatus, hstate⟩ := hp
      rw [hstatus] at hstate
      dsimp [Fbranch, Fsuccess] at hstate ⊢
      rw [prioritySubRetScratch_split] at hstate
      xperm_chunked hstate) (fun _ hq => by
        left
        dsimp [SuccessPost, Fsuccess, prioritySuccessPost] at hq ⊢
        xperm_chunked hq) hsuccess0
  have hfailure : cpsTripleWithin (3 + 309 + 2) (P + 84) (P + 88) fullCode
      (((.x10 : Reg) ↦ᵣ status) ** (.x0 ↦ᵣ (0 : Word)) **
        ⌜status ≠ 0⌝ ** Fbranch) BodyPost := by
    refine cpsTripleWithin_mono_nSteps (nSteps := 1)
      (nSteps' := 3 + 309 + 2) (by decide) ?_
    exact cpsTripleWithin_weaken (fun _ hp => by
        dsimp [Ffail, Fbranch] at hp ⊢
        xperm_chunked hp)
      (fun _ hq => by
        right
        dsimp [FailurePost, Ffail, priorityFailurePost] at hq ⊢
        simp only [Fbranch] at hq ⊢
        unfold P at hq
        have haddr :
            ((GuestAddrs.priority_fee_per_gas_eip1559 : Word) + 56) =
              BitVec.ofNat 64 GuestAddrs.priority_fee_per_gas_eip1559 +
                BitVec.ofNat 64 56 := by decide
        rw [haddr] at hq
        xperm_hyp hq) hfailure0
  have hmerge := cpsBranchWithin_merge_same_cr hbranch hfailure hsuccess
  exact cpsTripleWithin_weaken
    (fun _ hp => by
      dsimp [priorityBranchPre, Fbranch] at hp ⊢
      exact hp)
    (fun _ hq => by
      dsimp [priorityBodyPost, SuccessPost, FailurePost, BodyPost]
      exact hq)
    hmerge


-- @@ L1041-1044 verbatim
/-! The linked priority-fee body: argument setup, the ordinary three-buffer
    subtraction call, and the status-dependent continuation.  The caller's
    incumbent `ra` is `ret`; the subtraction adapter changes it to `P + 56`
    at the actual JAL and the continuation consumes that link. -/

-- @@ L1045-1122 verbatim
theorem priority_fee_per_gas_eip1559_body_spec
    (ret pPtr fPtr bPtr outPtr v8 v9 v18 v19 : Word)
    (pBytes fBytes bBytes outBytes : List (BitVec 8))
    (F : Assertion) (hF : F.pcFree)
    (hrw : RwRegion.wf ⟨outPtr, 32⟩)
    (hroF : Region.wf ⟨fPtr, fBytes⟩)
    (hroB : Region.wf ⟨bPtr, bBytes⟩)
    (hlenP : pBytes.length = 32)
    (hlenF : fBytes.length = 32)
    (hlenB : bBytes.length = 32)
    (hlenOut : outBytes.length = 32)
    (halignP : pPtr.toNat % 8 = 0)
    (halignOut : outPtr.toNat % 8 = 0)
    (hovP : pPtr.toNat + 32 < 2 ^ 64)
    (hovF : fPtr.toNat + 32 < 2 ^ 64)
    (hovB : bPtr.toNat + 32 < 2 ^ 64)
    (hovOut : outPtr.toNat + 32 < 2 ^ 64)
    (hdisjF : fPtr.toNat + 32 ≤ outPtr.toNat ∨
      outPtr.toNat + 32 ≤ fPtr.toNat)
    (hdisjB : bPtr.toNat + 32 ≤ outPtr.toNat ∨
      outPtr.toNat + 32 ≤ bPtr.toNat)
    (hvalidP : ∀ k, k < 32 →
      isValidByteAccess (pPtr + BitVec.ofNat 64 k) = true)
    (hvalidOut : ∀ k, k < 32 →
      isValidByteAccess (outPtr + BitVec.ofNat 64 k) = true)
    (hsz : 4 * ((prioritySubFn fPtr bPtr outPtr fBytes bBytes outBytes).body.size + 1)
      ≤ 2 ^ 64)
    (hret : ((P + 52) + 4 &&& ~~~(1 : Word)) = P + 52 + 4) :
    cpsTripleWithin
      (7 + (1 + (prioritySubFn fPtr bPtr outPtr fBytes bBytes outBytes).body.steps + 1) +
        (1 + (3 + 309 + 2)))
      (P + 24) (P + 88) fullCode
      (((.x1 : Reg) ↦ᵣ ret) ** (.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) **
        (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19) ** (.x10 ↦ᵣ pPtr) **
        (.x11 ↦ᵣ fPtr) ** (.x12 ↦ᵣ bPtr) ** (.x13 ↦ᵣ outPtr) **
        regOwns prioritySetupScratch ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion pPtr pBytes ** bytesRegion fPtr fBytes **
        bytesRegion bPtr bBytes ** bytesRegion outPtr outBytes ** F)
      (priorityBodyPost (u256SubBeBorrow fBytes bBytes outBytes)
        pPtr fPtr bPtr outPtr pBytes fBytes bBytes
        (u256SubBeBytes fBytes bBytes outBytes) F) := by
  let Fsetup : Assertion :=
    regOwns prioritySetupScratch ** bytesRegion pPtr pBytes **
      bytesRegion fPtr fBytes ** bytesRegion bPtr bBytes **
      bytesRegion outPtr outBytes ** (.x0 ↦ᵣ (0 : Word)) ** F
  have hFsetup : Fsetup.pcFree := by
    dsimp [Fsetup]
    pcf
    exact hF
  have hsetup := priority_setup_spec ret pPtr fPtr bPtr outPtr
    v8 v9 v18 v19 Fsetup hFsetup
  have hsub := priority_sub_call_spec ret pPtr fPtr bPtr outPtr
    fBytes bBytes outBytes
    (((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion pPtr pBytes ** F)
    (by pcf; exact hF)
    hrw hroF hroB hlenF hlenB hlenOut hovF hovB hovOut hdisjF hdisjB hsz hret
  have hlenSub : (u256SubBeBytes fBytes bBytes outBytes).length = 32 :=
    sub_bytes_length fBytes bBytes outBytes hlenOut
  have hstatus := priority_status_paths_spec
    (u256SubBeBorrow fBytes bBytes outBytes) pPtr fPtr bPtr outPtr
    pBytes fBytes bBytes (u256SubBeBytes fBytes bBytes outBytes) F hF
    hlenP hlenSub halignP halignOut hovP hovOut hvalidP hvalidOut (by decide)
  have h12 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by
      simp only [Fsetup, prioritySubPre] at hp ⊢
      rw [prioritySubScratch_split]
      xperm_chunked hp)
    hsetup hsub
  have h123 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by
      simp only [prioritySubPost, priorityBranchPre] at hp ⊢
      xperm_chunked hp)
    h12 hstatus
  exact cpsTripleWithin_weaken
    (fun _ hp => by
      simp only [Fsetup] at hp ⊢
      xperm_chunked hp)
    (fun _ hq => hq) h123


-- @@ L1124-1124 verbatim
#print axioms priority_sub_call_spec_concrete

-- @@ L1125-1125 verbatim
#print axioms priority_fee_per_gas_eip1559_body_spec



-- @@ L1128-1128 verbatim
end U256GasPricingSAsm


-- @@ L1130-1130 verbatim
end EvmAsm.Codegen
