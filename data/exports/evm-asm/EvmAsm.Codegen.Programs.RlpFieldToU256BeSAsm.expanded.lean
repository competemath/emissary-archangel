/-
  Strict K35 `rlp_field_to_u256_be` caller proof.

  The emitted routine composes strict K20 with a bounded right-aligned byte
  copy.  This module fixes the genuine caller-visible semantics and proves the
  real K20 call shape; the loop and whole-wrapper composition are split into
  companion modules to stay below the Codegen file-size gate.
-/

import EvmAsm.Codegen.Programs.RlpFieldToU64WholeSAsm
import EvmAsm.Codegen.Programs.RlpFieldToU256BeOfflineAddrs
import EvmAsm.Rv64.SAsm.AbiFrameOwn
import EvmAsm.Rv64.Tactics.DropPure
import EvmAsm.Rv64.Tactics.XPermPure


-- @@ L16-16 verbatim
namespace EvmAsm.Codegen.RlpFieldToU256BeSAsm


-- @@ L18-18 verbatim
open EvmAsm.Rv64 EvmAsm.Rv64.RLP EvmAsm.Rv64.SAsm


-- @@ L20-20 verbatim
abbrev ListSaved := EvmAsm.Codegen.RlpListNthItemSAsm.Saved

-- @@ L21-21 verbatim
abbrev ListSuccess := EvmAsm.Codegen.RlpListNthItemSAsm.Success

-- @@ L22-22 verbatim
abbrev ListFailure := EvmAsm.Codegen.RlpListNthItemSAsm.Failure


-- @@ L24-26 verbatim
def selectedBytes (bytes : List (BitVec 8)) (offset len : Word) :
    List (BitVec 8) :=
  (bytes.drop offset.toNat).take len.toNat


-- @@ L28-30 verbatim
def rightAligned32 (bytes : List (BitVec 8)) (offset len : Word) :
    List (BitVec 8) :=
  List.replicate (32 - len.toNat) 0 ++ selectedBytes bytes offset len


-- @@ L32-45 verbatim
/-- Genuine unified K35 semantics.  The output is zero on every failure and
    is the selected payload right-aligned in 32 bytes on success. -/
inductive Result (bytes : List (BitVec 8)) (base : Word)
    (listLen index : Nat) : Word → List (BitVec 8) → Prop
  | listFailure (hfail : ListFailure bytes base listLen index) :
      Result bytes base listLen index 1 (List.replicate 32 0)
  | tooLong (offset len : Word)
      (hok : ListSuccess bytes base listLen index offset len)
      (hlen : 32 < len.toNat) :
      Result bytes base listLen index 2 (List.replicate 32 0)
  | success (offset len : Word)
      (hok : ListSuccess bytes base listLen index offset len)
      (hfit : len.toNat ≤ 32) :
      Result bytes base listLen index 0 (rightAligned32 bytes offset len)


-- @@ L47-51 verbatim
theorem Result.status_cases {bytes : List (BitVec 8)} {base : Word}
    {listLen index : Nat} {status : Word} {out : List (BitVec 8)}
    (h : Result bytes base listLen index status out) :
    status = 0 ∨ status = 1 ∨ status = 2 := by
  cases h <;> simp


-- @@ L53-53 verbatim
/-! ## Emitted code and linked closure -/


-- @@ L55-55 verbatim
theorem program_length : rlpFieldToU256Be_prog.length = 44 := by decide


-- @@ L57-57 verbatim
#guard rlpFieldToU256Be_prog.length = 44


-- @@ L59-59 verbatim
abbrev B : Word := (RlpFieldToU256BeOfflineAddrs.rlp_field_to_u256_be : Word)

-- @@ L60-60 verbatim
abbrev K20B : Word := (GuestAddrs.rlp_list_nth_item : Word)

-- @@ L61-61 verbatim
abbrev offsetCell : Word := (GuestAddrs.rfu_offset : Word)

-- @@ L62-62 verbatim
abbrev lengthCell : Word := (GuestAddrs.rfu_length : Word)


-- @@ L64-64 verbatim
def wrapperCode : CodeReq := CodeReq.ofProg B rlpFieldToU256Be_prog

-- @@ L65-65 verbatim
def code : CodeReq := EvmAsm.Codegen.RlpFieldToU64SAsm.code.union wrapperCode


-- @@ L67-75 verbatim
theorem listWrapper_disjoint :
    EvmAsm.Codegen.RlpFieldToU64SAsm.wrapperCode.Disjoint wrapperCode := by
  unfold EvmAsm.Codegen.RlpFieldToU64SAsm.wrapperCode wrapperCode
    EvmAsm.Codegen.RlpFieldToU64SAsm.B B
  apply CodeReq.Disjoint.ofProg_ranges
  · rw [EvmAsm.Codegen.RlpFieldToU64SAsm.program_length]; decide
  · rw [program_length]; decide
  · rw [EvmAsm.Codegen.RlpFieldToU64SAsm.program_length, program_length]
    decide


-- @@ L77-85 verbatim
theorem nthWrapper_disjoint :
    EvmAsm.Codegen.RlpListNthItemSAsm.code.Disjoint wrapperCode := by
  unfold EvmAsm.Codegen.RlpListNthItemSAsm.code wrapperCode
    EvmAsm.Codegen.RlpListNthItemSAsm.B B
  apply CodeReq.Disjoint.ofProg_ranges
  · rw [EvmAsm.Codegen.RlpListNthItemSAsm.total_length]; decide
  · rw [program_length]; decide
  · rw [EvmAsm.Codegen.RlpListNthItemSAsm.total_length, program_length]
    decide


-- @@ L87-94 verbatim
theorem contentWrapper_disjoint :
    EvmAsm.Codegen.RlpFieldToU64SAsm.contentCode.Disjoint wrapperCode := by
  unfold EvmAsm.Codegen.RlpFieldToU64SAsm.contentCode wrapperCode
    EvmAsm.Codegen.RlpFieldToU64SAsm.C64B rlp_content_to_u64_code B
  apply CodeReq.Disjoint.ofProg_ranges
  · rw [rlp_content_to_u64_prog_length]; decide
  · rw [program_length]; decide
  · rw [rlp_content_to_u64_prog_length, program_length]; decide


-- @@ L96-100 verbatim
theorem oldCode_wrapper_disjoint :
    EvmAsm.Codegen.RlpFieldToU64SAsm.code.Disjoint wrapperCode := by
  unfold EvmAsm.Codegen.RlpFieldToU64SAsm.code
  exact CodeReq.Disjoint.union_left listWrapper_disjoint
    (CodeReq.Disjoint.union_left nthWrapper_disjoint contentWrapper_disjoint)


-- @@ L102-105 verbatim
theorem wrapperCode_mono : ∀ a i, wrapperCode a = some i → code a = some i := by
  intro a i hi
  unfold code
  exact CodeReq.mono_union_right oldCode_wrapper_disjoint (fun _ _ h => h) a i hi


-- @@ L107-107 verbatim
/-! ## Reuse K34's generic strict-list result packaging -/


-- @@ L109-109 verbatim
abbrev listSavedRegs := EvmAsm.Codegen.RlpFieldToU64SAsm.listSavedRegs

-- @@ L110-110 verbatim
abbrev listCallResult := EvmAsm.Codegen.RlpFieldToU64SAsm.listCallResult

-- @@ L111-111 verbatim
abbrev listSelected := EvmAsm.Codegen.RlpFieldToU64SAsm.listSelected

-- @@ L112-112 verbatim
abbrev listFailed := EvmAsm.Codegen.RlpFieldToU64SAsm.listFailed


-- @@ L114-175 expanded
/-- The real K35 `jal` at instruction 14, using the reusable K20 flat adapter. -/
theorem callListNth (sp0 listBase listLenW indexW offsetPtr lenPtr oldOffset oldLen vOld : Word)
    (s0 s1 s2 s3 s4 s5 : Word) (bytes : List (BitVec 8)) (listLen index : Nat)
    (hlistLenW : listLenW = BitVec.ofNat 64 listLen) (hindexW : indexW = BitVec.ofNat 64 index)
    (hindex : index < 2 ^ 64) (hsalign : listBase.toNat % 8 = 0)
    (hslack : listLen + 9 ≤ bytes.length) (hover : listBase.toNat + bytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < bytes.length → isValidByteAccess (listBase + BitVec.ofNat 64 k) = true) :
    let saved : ListSaved :=
      { ra := B + 60, s0 := s0, s1 := s1, s2 := s2, s3 := s3, s4 := s4, s5 := s5 }
    cpsTripleWithin (1 + ((12 + ((85 + 93 * (index + 2)) + 6)) + 9)) (B + 56) (B + 60) code
      ((.x1 ↦ᵣ vOld) **
        ((.x2 ↦ᵣ sp0) **
          listSavedRegs saved **
            stackFree sp0 8 **
              EvmAsm.Codegen.RlpListNthItemSAsm.entryRest listBase listLenW indexW offsetPtr lenPtr
                oldOffset oldLen bytes))
      ((.x1 ↦ᵣ (B + 60)) **
        listCallResult sp0 listBase offsetPtr lenPtr oldOffset oldLen saved bytes listLen index) :=
  by
  dsimp
  let saved : ListSaved :=
    { ra := B + 60, s0 := s0, s1 := s1, s2 := s2, s3 := s3, s4 := s4, s5 := s5 }
  have hret : saved.ra &&& ~~~(1 : Word) = saved.ra :=
    by
    dsimp [saved, B]
    decide
  have hcallee0 :=
    EvmAsm.Codegen.RlpFieldToU64SAsm.listCalleeCallContract sp0 listBase listLenW indexW offsetPtr
      lenPtr oldOffset oldLen saved bytes listLen index hlistLenW hindexW hindex hsalign (by omega)
      (by omega) hover hvalid (by omega) hret
  have hcallee :=
    cpsTripleWithin_extend_code (cr' := code)
      (fun a i hi => by
        unfold code
        exact CodeReq.union_mono_left a i hi)
      hcallee0
  have htarget :
    (B + 56) +
        signExtend21
          (jalOff GuestAddrs.rlp_list_nth_item
            (RlpFieldToU256BeOfflineAddrs.rlp_field_to_u256_be + 56)) =
      K20B :=
    by
    unfold B K20B
    decide
  have hmem :
    ∀ a i,
      CodeReq.singleton (B + 56)
            (.JAL .x1
              (jalOff GuestAddrs.rlp_list_nth_item
                (RlpFieldToU256BeOfflineAddrs.rlp_field_to_u256_be + 56)))
            a =
          some i →
        code a = some i :=
    by
    intro a i hi
    exact
      wrapperCode_mono a i
        (CodeReq.ofProg_mem_at B (B + 56) rlpFieldToU256Be_prog 14
          (.JAL .x1
            (jalOff GuestAddrs.rlp_list_nth_item
              (RlpFieldToU256BeOfflineAddrs.rlp_field_to_u256_be + 56)))
          (by bv_omega) (by rw [program_length]; decide) rfl (by rw [program_length]; decide) a i
          hi)
  have hcall :=
    callWithin_spec (B + 56) K20B vOld
      (jalOff GuestAddrs.rlp_list_nth_item (RlpFieldToU256BeOfflineAddrs.rlp_field_to_u256_be + 56))
      ((12 + ((85 + 93 * (index + 2)) + 6)) + 9) htarget hmem
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
      hcallee
  dsimp [saved] at hcall
  exact hcall


-- @@ L178-178 verbatim
end EvmAsm.Codegen.RlpFieldToU256BeSAsm
