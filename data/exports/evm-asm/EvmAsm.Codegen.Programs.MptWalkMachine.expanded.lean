/-
  Machine geometry for `mpt_walk` (#11799).

  Frame: sp-80, saves ra/s0-s8 (x1, x8, x9, x18-x24) — 10 slots.
  Body 294 insn between 11-insn prologue and 12-insn epilogue.
  First machine milestone: frame + setup + `mpt_node_kind` callWithin
  (callee already `.proven` via #11964). `fullCode` carries callee images for
  every cross-`jal`: kind∪count∪nth, `hp_decode_nibbles`, and
  `witness_lookup_by_hash` (#12144 — without `wlhCr` the residual
  `wlCallWithinShape` was vacuous). Hit-domain wl residual still needs a
  hit triple; empty-section miss is dischargeable via
  `WitnessLookupByHashSpec`.

  Domain gate (`.conditional`): MptNode v1 hash-or-empty children;
  inlined sub-32 EXCLUDED BY GATE; see `MptWalkSpec` header.
-/

import EvmAsm.Codegen.Programs.MptWalkSpec
import EvmAsm.Codegen.Programs.MptNodeKindMachine
import EvmAsm.Codegen.Programs.RlpListCountItemsSAsm
import EvmAsm.Codegen.Programs.RlpListNthItemSAsm
import EvmAsm.Codegen.Programs.HpDecodeNibblesSAsm
import EvmAsm.Codegen.Programs.MptWitnessLookup
import EvmAsm.Codegen.Programs.WitnessLookupByHashIndexedSpec
import EvmAsm.Codegen.Programs.Mpt
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Rv64.SAsm.FramePort
import EvmAsm.Rv64.SAsm.AbiFrameCall


-- @@ L30-30 verbatim
namespace EvmAsm.Codegen.MptWalkSpec


-- @@ L32-32 verbatim
open EvmAsm.Rv64 EvmAsm.Rv64.SAsm

-- @@ L33-33 verbatim
open EvmAsm.Codegen

-- @@ L34-34 verbatim
open EvmAsm.Codegen.MptNodeKindSpec

-- @@ L35-35 verbatim
open EvmAsm.Codegen.RlpListCountItemsSAsm

-- @@ L36-36 verbatim
open EvmAsm.Codegen.RlpListNthItemSAsm

-- @@ L37-37 verbatim
open EvmAsm.Codegen.HpDecodeNibblesSAsm


-- @@ L39-39 verbatim
abbrev walkB : Word := BitVec.ofNat 64 GuestAddrs.mpt_walk

-- @@ L40-40 verbatim
abbrev kindB : Word := BitVec.ofNat 64 GuestAddrs.mpt_node_kind

-- @@ L41-41 verbatim
abbrev MwLookupHash : Word := BitVec.ofNat 64 GuestAddrs.mw_lookup_hash

-- @@ L42-42 verbatim
abbrev MwLookupOff : Word := BitVec.ofNat 64 GuestAddrs.mw_lookup_offset

-- @@ L43-43 verbatim
abbrev MwLookupLen : Word := BitVec.ofNat 64 GuestAddrs.mw_lookup_length

-- @@ L44-44 verbatim
abbrev MwChildOff : Word := BitVec.ofNat 64 GuestAddrs.mw_child_offset

-- @@ L45-45 verbatim
abbrev MwChildLen : Word := BitVec.ofNat 64 GuestAddrs.mw_child_length

-- @@ L46-46 verbatim
abbrev MwPathOff : Word := BitVec.ofNat 64 GuestAddrs.mw_path_offset

-- @@ L47-47 verbatim
abbrev MwPathLen : Word := BitVec.ofNat 64 GuestAddrs.mw_path_length

-- @@ L48-48 verbatim
abbrev MwNibbleBuf : Word := BitVec.ofNat 64 GuestAddrs.mw_nibble_buf

-- @@ L49-49 verbatim
abbrev MwNibbleCount : Word := BitVec.ofNat 64 GuestAddrs.mw_nibble_count

-- @@ L50-50 verbatim
abbrev MwIsLeaf : Word := BitVec.ofNat 64 GuestAddrs.mw_is_leaf

-- @@ L51-51 verbatim
abbrev MwValueOff : Word := BitVec.ofNat 64 GuestAddrs.mw_value_offset

-- @@ L52-52 verbatim
abbrev MwValueLen : Word := BitVec.ofNat 64 GuestAddrs.mw_value_length

-- @@ L53-53 verbatim
abbrev NthB : Word := BitVec.ofNat 64 GuestAddrs.rlp_list_nth_item

-- @@ L54-54 verbatim
abbrev HpDecodeB : Word := BitVec.ofNat 64 GuestAddrs.hp_decode_nibbles



-- @@ L57-60 verbatim
/-- Frame: ra@0, s0@8, s1@16, s2..s8 @24..72. -/
def walkFrame : FrameDesc :=
  [(.x1, 0), (.x8, 8), (.x9, 16), (.x18, 24), (.x19, 32),
   (.x20, 40), (.x21, 48), (.x22, 56), (.x23, 64), (.x24, 72)]


-- @@ L62-72 verbatim
structure WalkSaved where
  ra : Word
  s0 : Word
  s1 : Word
  s2 : Word
  s3 : Word
  s4 : Word
  s5 : Word
  s6 : Word
  s7 : Word
  s8 : Word


-- @@ L74-85 verbatim
def walkSavedVals (s : WalkSaved) : Reg → Word
  | .x1 => s.ra
  | .x8 => s.s0
  | .x9 => s.s1
  | .x18 => s.s2
  | .x19 => s.s3
  | .x20 => s.s4
  | .x21 => s.s5
  | .x22 => s.s6
  | .x23 => s.s7
  | .x24 => s.s8
  | _ => 0


-- @@ L87-87 verbatim
theorem walkFrame_length : walkFrame.length = 10 := by decide


-- @@ L89-95 verbatim
theorem regsAt_walkFrame (s : WalkSaved) :
    regsAt walkFrame (walkSavedVals s) =
      ((.x1 ↦ᵣ s.ra) ** (.x8 ↦ᵣ s.s0) ** (.x9 ↦ᵣ s.s1) **
        (.x18 ↦ᵣ s.s2) ** (.x19 ↦ᵣ s.s3) ** (.x20 ↦ᵣ s.s4) **
        (.x21 ↦ᵣ s.s5) ** (.x22 ↦ᵣ s.s6) ** (.x23 ↦ᵣ s.s7) **
        (.x24 ↦ᵣ s.s8)) := by
  simp [walkFrame, regsAt, walkSavedVals, sepConj_emp_right']


-- @@ L97-102 verbatim
def walkSavedFrame (newSp : Word) (s : WalkSaved) : Assertion :=
  (newSp ↦ₘ s.ra) ** ((newSp + 8) ↦ₘ s.s0) ** ((newSp + 16) ↦ₘ s.s1) **
  ((newSp + 24) ↦ₘ s.s2) ** ((newSp + 32) ↦ₘ s.s3) **
  ((newSp + 40) ↦ₘ s.s4) ** ((newSp + 48) ↦ₘ s.s5) **
  ((newSp + 56) ↦ₘ s.s6) ** ((newSp + 64) ↦ₘ s.s7) **
  ((newSp + 72) ↦ₘ s.s8)


-- @@ L104-109 verbatim
set_option maxRecDepth 8000 in
theorem frameSlotsSaved_walkFrame (newSp : Word) (s : WalkSaved) :
    frameSlotsSaved walkFrame newSp (walkSavedVals s) =
      walkSavedFrame newSp s := by
  simp [walkFrame, frameSlotsSaved, walkSavedFrame, walkSavedVals,
    sepConj_emp_right', signExtend12]


-- @@ L111-112 verbatim
/-- Prologue ADDI+10 SD; body 294; epilogue 10 LD + ADDI + JALR. -/
def walkPrologue : List Instr := mptWalk_prog.take 11

-- @@ L113-113 verbatim
def walkBody : List Instr := mptWalk_prog.drop 11 |>.take 294

-- @@ L114-114 verbatim
def walkEpilogue : List Instr := mptWalk_prog.drop 305


-- @@ L116-116 verbatim
#guard walkPrologue.length = 11

-- @@ L117-117 verbatim
#guard walkBody.length = 294

-- @@ L118-118 verbatim
#guard walkEpilogue.length = 12


-- @@ L120-123 verbatim
set_option maxRecDepth 8000 in
theorem walk_parts_cover_prog :
    walkPrologue ++ walkBody ++ walkEpilogue = mptWalk_prog := by
  decide


-- @@ L125-125 verbatim
/-! Byte-tie: 80-byte frame around body = emitted prog. -/

-- @@ L126-130 verbatim
set_option maxRecDepth 8000 in
theorem walk_abiFrame_byte_tie :
    abiFrameProg (-80 : BitVec 12) (80 : BitVec 12) walkFrame walkBody =
      mptWalk_prog := by
  decide


-- @@ L132-132 verbatim
/-! ## Linked code image: walk ∪ kind∪count∪nth ∪ hp_decode ∪ wlh -/


-- @@ L134-134 verbatim
private abbrev walkProg : List Instr := mptWalk_prog


-- @@ L136-136 verbatim
def wrapperCode : CodeReq := CodeReq.ofProg walkB walkProg


-- @@ L138-139 verbatim
/-- Kind-family image (kind∪count∪nth) before adding hp/wlh. -/
def kindFullCode : CodeReq := MptNodeKindSpec.fullCode


-- @@ L141-142 verbatim
/-- `witness_lookup_by_hash` image (same shape as `WitnessLookupByHashSpec.wlhCr`). -/
def WlhB : Word := BitVec.ofNat 64 GuestAddrs.witness_lookup_by_hash

-- @@ L143-143 verbatim
def wlhCr : CodeReq := CodeReq.ofProg WlhB witnessLookupByHash_prog


-- @@ L145-146 verbatim
/-- Indexed lookup image (#12183 enable=1 path nests into this). -/
def idxFullCode : CodeReq := WitnessLookupByHashIndexedSpec.fullCode


-- @@ L148-150 verbatim
/-- Core before indexed: `walk ∪ kindFull ∪ hdnCr ∪ wlhCr` (#12144). -/
def walkKindHpWlhCode : CodeReq :=
  ((wrapperCode.union kindFullCode).union (hdnCr HpDecodeB)).union wlhCr


-- @@ L152-154 verbatim
/-- `walk ∪ kindFull ∪ hdnCr ∪ wlhCr ∪ idxFull` (#12183 enable=1).
    Enables `enableFullCode ⊆ fullCode` for residual callWithin. -/
def fullCode : CodeReq := walkKindHpWlhCode.union idxFullCode


-- @@ L156-157 verbatim
set_option maxRecDepth 8000 in
theorem program_length : walkProg.length = 317 := by decide


-- @@ L159-160 verbatim
set_option maxRecDepth 8000 in
theorem hp_program_length : hpDecodeNibbles_prog.length = 51 := by decide


-- @@ L162-163 verbatim
set_option maxRecDepth 8000 in
theorem wlh_program_length : witnessLookupByHash_prog.length = 155 := by decide


-- @@ L165-172 verbatim
set_option maxRecDepth 8000 in
theorem wrapper_kindWrap_disjoint :
    wrapperCode.Disjoint MptNodeKindSpec.wrapperCode := by
  unfold wrapperCode MptNodeKindSpec.wrapperCode
  apply CodeReq.Disjoint.ofProg_ranges
  · rw [program_length]; decide
  · rw [MptNodeKindSpec.program_length]; decide
  · rw [program_length, MptNodeKindSpec.program_length]; decide


-- @@ L174-181 verbatim
set_option maxRecDepth 8000 in
theorem wrapper_count_disjoint :
    wrapperCode.Disjoint RlpListCountItemsSAsm.code := by
  unfold wrapperCode RlpListCountItemsSAsm.code
  apply CodeReq.Disjoint.ofProg_ranges
  · rw [program_length]; decide
  · rw [RlpListCountItemsSAsm.total_length]; decide
  · rw [program_length, RlpListCountItemsSAsm.total_length]; decide


-- @@ L183-190 verbatim
set_option maxRecDepth 8000 in
theorem wrapper_nth_disjoint :
    wrapperCode.Disjoint RlpListNthItemSAsm.code := by
  unfold wrapperCode RlpListNthItemSAsm.code
  apply CodeReq.Disjoint.ofProg_ranges
  · rw [program_length]; decide
  · rw [RlpListNthItemSAsm.total_length]; decide
  · rw [program_length, RlpListNthItemSAsm.total_length]; decide


-- @@ L192-196 verbatim
theorem wrapper_kindFull_disjoint :
    wrapperCode.Disjoint kindFullCode := by
  unfold kindFullCode MptNodeKindSpec.fullCode
  exact CodeReq.Disjoint.union_right wrapper_kindWrap_disjoint
    (CodeReq.Disjoint.union_right wrapper_count_disjoint wrapper_nth_disjoint)


-- @@ L198-205 verbatim
set_option maxRecDepth 8000 in
theorem wrapper_hp_disjoint :
    wrapperCode.Disjoint (hdnCr HpDecodeB) := by
  unfold wrapperCode hdnCr HpDecodeB
  apply CodeReq.Disjoint.ofProg_ranges
  · rw [program_length]; decide
  · rw [hp_program_length]; decide
  · rw [program_length, hp_program_length]; decide


-- @@ L207-214 verbatim
set_option maxRecDepth 8000 in
theorem kindWrap_hp_disjoint :
    MptNodeKindSpec.wrapperCode.Disjoint (hdnCr HpDecodeB) := by
  unfold MptNodeKindSpec.wrapperCode hdnCr HpDecodeB
  apply CodeReq.Disjoint.ofProg_ranges
  · rw [MptNodeKindSpec.program_length]; decide
  · rw [hp_program_length]; decide
  · rw [MptNodeKindSpec.program_length, hp_program_length]; decide


-- @@ L216-223 verbatim
set_option maxRecDepth 8000 in
theorem count_hp_disjoint :
    RlpListCountItemsSAsm.code.Disjoint (hdnCr HpDecodeB) := by
  unfold RlpListCountItemsSAsm.code hdnCr HpDecodeB
  apply CodeReq.Disjoint.ofProg_ranges
  · rw [RlpListCountItemsSAsm.total_length]; decide
  · rw [hp_program_length]; decide
  · rw [RlpListCountItemsSAsm.total_length, hp_program_length]; decide


-- @@ L225-232 verbatim
set_option maxRecDepth 8000 in
theorem nth_hp_disjoint :
    RlpListNthItemSAsm.code.Disjoint (hdnCr HpDecodeB) := by
  unfold RlpListNthItemSAsm.code hdnCr HpDecodeB
  apply CodeReq.Disjoint.ofProg_ranges
  · rw [RlpListNthItemSAsm.total_length]; decide
  · rw [hp_program_length]; decide
  · rw [RlpListNthItemSAsm.total_length, hp_program_length]; decide


-- @@ L234-238 verbatim
theorem kindFull_hp_disjoint :
    kindFullCode.Disjoint (hdnCr HpDecodeB) := by
  unfold kindFullCode MptNodeKindSpec.fullCode
  exact CodeReq.Disjoint.union_left kindWrap_hp_disjoint
    (CodeReq.Disjoint.union_left count_hp_disjoint nth_hp_disjoint)


-- @@ L240-242 verbatim
theorem walkKind_hp_disjoint :
    (wrapperCode.union kindFullCode).Disjoint (hdnCr HpDecodeB) :=
  CodeReq.Disjoint.union_left wrapper_hp_disjoint kindFull_hp_disjoint


-- @@ L244-251 verbatim
set_option maxRecDepth 8000 in
theorem wrapper_wlh_disjoint :
    wrapperCode.Disjoint wlhCr := by
  unfold wrapperCode wlhCr WlhB
  apply CodeReq.Disjoint.ofProg_ranges
  · rw [program_length]; decide
  · rw [wlh_program_length]; decide
  · rw [program_length, wlh_program_length]; decide


-- @@ L253-260 verbatim
set_option maxRecDepth 8000 in
theorem kindWrap_wlh_disjoint :
    MptNodeKindSpec.wrapperCode.Disjoint wlhCr := by
  unfold MptNodeKindSpec.wrapperCode wlhCr WlhB
  apply CodeReq.Disjoint.ofProg_ranges
  · rw [MptNodeKindSpec.program_length]; decide
  · rw [wlh_program_length]; decide
  · rw [MptNodeKindSpec.program_length, wlh_program_length]; decide


-- @@ L262-269 verbatim
set_option maxRecDepth 8000 in
theorem count_wlh_disjoint :
    RlpListCountItemsSAsm.code.Disjoint wlhCr := by
  unfold RlpListCountItemsSAsm.code wlhCr WlhB
  apply CodeReq.Disjoint.ofProg_ranges
  · rw [RlpListCountItemsSAsm.total_length]; decide
  · rw [wlh_program_length]; decide
  · rw [RlpListCountItemsSAsm.total_length, wlh_program_length]; decide


-- @@ L271-278 verbatim
set_option maxRecDepth 8000 in
theorem nth_wlh_disjoint :
    RlpListNthItemSAsm.code.Disjoint wlhCr := by
  unfold RlpListNthItemSAsm.code wlhCr WlhB
  apply CodeReq.Disjoint.ofProg_ranges
  · rw [RlpListNthItemSAsm.total_length]; decide
  · rw [wlh_program_length]; decide
  · rw [RlpListNthItemSAsm.total_length, wlh_program_length]; decide


-- @@ L280-284 verbatim
theorem kindFull_wlh_disjoint :
    kindFullCode.Disjoint wlhCr := by
  unfold kindFullCode MptNodeKindSpec.fullCode
  exact CodeReq.Disjoint.union_left kindWrap_wlh_disjoint
    (CodeReq.Disjoint.union_left count_wlh_disjoint nth_wlh_disjoint)


-- @@ L286-293 verbatim
set_option maxRecDepth 8000 in
theorem hp_wlh_disjoint :
    (hdnCr HpDecodeB).Disjoint wlhCr := by
  unfold hdnCr HpDecodeB wlhCr WlhB
  apply CodeReq.Disjoint.ofProg_ranges
  · rw [hp_program_length]; decide
  · rw [wlh_program_length]; decide
  · rw [hp_program_length, wlh_program_length]; decide


-- @@ L295-299 verbatim
theorem walkKindHp_wlh_disjoint :
    ((wrapperCode.union kindFullCode).union (hdnCr HpDecodeB)).Disjoint wlhCr :=
  CodeReq.Disjoint.union_left
    (CodeReq.Disjoint.union_left wrapper_wlh_disjoint kindFull_wlh_disjoint)
    hp_wlh_disjoint


-- @@ L301-303 verbatim
/-- Core image before wlh (walk ∪ kind ∪ hp). -/
def walkKindHpCode : CodeReq :=
  (wrapperCode.union kindFullCode).union (hdnCr HpDecodeB)


-- @@ L305-317 verbatim
/-- Discharge one walk singleton into `fullCode`. -/
theorem walkMem (A : Word) (k : Nat) (ins : Instr)
    (hk : k < walkProg.length)
    (hA : A = walkB + BitVec.ofNat 64 (4 * k))
    (hins : walkProg[k]'hk = ins) :
    ∀ a i, CodeReq.singleton A ins a = some i → fullCode a = some i := by
  intro a i hs
  unfold fullCode walkKindHpWlhCode
  have hL := CodeReq.ofProg_mem_at walkB A walkProg k ins hA hk hins
    (by rw [program_length]; norm_num) a i hs
  exact CodeReq.union_mono_left a i
    (CodeReq.union_mono_left a i
      (CodeReq.union_mono_left a i (CodeReq.union_mono_left a i hL)))


-- @@ L319-327 verbatim
/-- Kind (with count∪nth) membership into walk fullCode. -/
theorem kindCalleeMem : ∀ a i,
    MptNodeKindSpec.fullCode a = some i → fullCode a = some i := by
  intro a i hi
  unfold fullCode walkKindHpWlhCode kindFullCode
  have hK := CodeReq.mono_union_right wrapper_kindFull_disjoint
    (fun _ _ h => h) a i hi
  exact CodeReq.union_mono_left a i
    (CodeReq.union_mono_left a i (CodeReq.union_mono_left a i hK))


-- @@ L329-334 verbatim
/-- Direct nth membership via kind fullCode. -/
theorem nthCalleeMem : ∀ a i,
    RlpListNthItemSAsm.code a = some i → fullCode a = some i := by
  intro a i hi
  apply kindCalleeMem
  exact MptNodeKindSpec.nthCalleeMem a i hi


-- @@ L336-343 verbatim
/-- hp_decode_nibbles membership into walk fullCode. -/
theorem hpCalleeMem : ∀ a i,
    hdnCr HpDecodeB a = some i → fullCode a = some i := by
  intro a i hi
  unfold fullCode walkKindHpWlhCode
  have hH := CodeReq.mono_union_right walkKind_hp_disjoint
    (fun _ _ h => h) a i hi
  exact CodeReq.union_mono_left a i (CodeReq.union_mono_left a i hH)


-- @@ L345-352 verbatim
/-- witness_lookup_by_hash membership into walk fullCode (#12144). -/
theorem wlhCalleeMem : ∀ a i,
    wlhCr a = some i → fullCode a = some i := by
  intro a i hi
  unfold fullCode walkKindHpWlhCode
  have hW := CodeReq.mono_union_right walkKindHp_wlh_disjoint
    (fun _ _ h => h) a i hi
  exact CodeReq.union_mono_left a i hW


-- @@ L354-354 verbatim
/-! ## Disjoint walkKindHpWlh ↔ indexed fullCode (#12183) -/


-- @@ L356-363 verbatim
set_option maxRecDepth 8000 in
theorem wrapper_idxWrap_disjoint :
    wrapperCode.Disjoint WitnessLookupByHashIndexedSpec.wrapperCode := by
  unfold wrapperCode WitnessLookupByHashIndexedSpec.wrapperCode
  apply CodeReq.Disjoint.ofProg_ranges
  · rw [program_length]; decide
  · rw [WitnessLookupByHashIndexedSpec.indexed_prog_length]; decide
  · rw [program_length, WitnessLookupByHashIndexedSpec.indexed_prog_length]; decide


-- @@ L365-372 verbatim
set_option maxRecDepth 8000 in
theorem wrapper_idx_record_ptr_disjoint :
    wrapperCode.Disjoint WitnessLookupByHashIndexedSpec.recordPtrCode := by
  unfold wrapperCode WitnessLookupByHashIndexedSpec.recordPtrCode
  apply CodeReq.Disjoint.ofProg_ranges
  · rw [program_length]; decide
  · rw [WitnessLookupByHashIndexedSpec.record_ptr_prog_length]; decide
  · rw [program_length, WitnessLookupByHashIndexedSpec.record_ptr_prog_length]; decide


-- @@ L374-381 verbatim
set_option maxRecDepth 8000 in
theorem wrapper_idx_cmp32_disjoint :
    wrapperCode.Disjoint WitnessLookupByHashIndexedSpec.cmp32Code := by
  unfold wrapperCode WitnessLookupByHashIndexedSpec.cmp32Code
  apply CodeReq.Disjoint.ofProg_ranges
  · rw [program_length]; decide
  · rw [WitnessLookupByHashIndexedSpec.cmp32_prog_length]; decide
  · rw [program_length, WitnessLookupByHashIndexedSpec.cmp32_prog_length]; decide


-- @@ L383-388 verbatim
theorem wrapper_idxFull_disjoint : wrapperCode.Disjoint idxFullCode := by
  unfold idxFullCode WitnessLookupByHashIndexedSpec.fullCode
  exact CodeReq.Disjoint.union_right
    (CodeReq.Disjoint.union_right wrapper_idxWrap_disjoint
      wrapper_idx_record_ptr_disjoint)
    wrapper_idx_cmp32_disjoint


-- @@ L390-398 verbatim
set_option maxRecDepth 8000 in
theorem kindWrap_idxWrap_disjoint :
    MptNodeKindSpec.wrapperCode.Disjoint
      WitnessLookupByHashIndexedSpec.wrapperCode := by
  unfold MptNodeKindSpec.wrapperCode WitnessLookupByHashIndexedSpec.wrapperCode
  apply CodeReq.Disjoint.ofProg_ranges
  · rw [MptNodeKindSpec.program_length]; decide
  · rw [WitnessLookupByHashIndexedSpec.indexed_prog_length]; decide
  · rw [MptNodeKindSpec.program_length, WitnessLookupByHashIndexedSpec.indexed_prog_length]; decide


-- @@ L400-408 verbatim
set_option maxRecDepth 8000 in
theorem kindWrap_idx_record_ptr_disjoint :
    MptNodeKindSpec.wrapperCode.Disjoint
      WitnessLookupByHashIndexedSpec.recordPtrCode := by
  unfold MptNodeKindSpec.wrapperCode WitnessLookupByHashIndexedSpec.recordPtrCode
  apply CodeReq.Disjoint.ofProg_ranges
  · rw [MptNodeKindSpec.program_length]; decide
  · rw [WitnessLookupByHashIndexedSpec.record_ptr_prog_length]; decide
  · rw [MptNodeKindSpec.program_length, WitnessLookupByHashIndexedSpec.record_ptr_prog_length]; decide


-- @@ L410-418 verbatim
set_option maxRecDepth 8000 in
theorem kindWrap_idx_cmp32_disjoint :
    MptNodeKindSpec.wrapperCode.Disjoint
      WitnessLookupByHashIndexedSpec.cmp32Code := by
  unfold MptNodeKindSpec.wrapperCode WitnessLookupByHashIndexedSpec.cmp32Code
  apply CodeReq.Disjoint.ofProg_ranges
  · rw [MptNodeKindSpec.program_length]; decide
  · rw [WitnessLookupByHashIndexedSpec.cmp32_prog_length]; decide
  · rw [MptNodeKindSpec.program_length, WitnessLookupByHashIndexedSpec.cmp32_prog_length]; decide


-- @@ L420-426 verbatim
theorem kindWrap_idxFull_disjoint :
    MptNodeKindSpec.wrapperCode.Disjoint idxFullCode := by
  unfold idxFullCode WitnessLookupByHashIndexedSpec.fullCode
  exact CodeReq.Disjoint.union_right
    (CodeReq.Disjoint.union_right kindWrap_idxWrap_disjoint
      kindWrap_idx_record_ptr_disjoint)
    kindWrap_idx_cmp32_disjoint


-- @@ L428-436 verbatim
set_option maxRecDepth 8000 in
theorem count_idxWrap_disjoint :
    RlpListCountItemsSAsm.code.Disjoint
      WitnessLookupByHashIndexedSpec.wrapperCode := by
  unfold RlpListCountItemsSAsm.code WitnessLookupByHashIndexedSpec.wrapperCode
  apply CodeReq.Disjoint.ofProg_ranges
  · rw [RlpListCountItemsSAsm.total_length]; decide
  · rw [WitnessLookupByHashIndexedSpec.indexed_prog_length]; decide
  · rw [RlpListCountItemsSAsm.total_length, WitnessLookupByHashIndexedSpec.indexed_prog_length]; decide


-- @@ L438-446 verbatim
set_option maxRecDepth 8000 in
theorem count_idx_record_ptr_disjoint :
    RlpListCountItemsSAsm.code.Disjoint
      WitnessLookupByHashIndexedSpec.recordPtrCode := by
  unfold RlpListCountItemsSAsm.code WitnessLookupByHashIndexedSpec.recordPtrCode
  apply CodeReq.Disjoint.ofProg_ranges
  · rw [RlpListCountItemsSAsm.total_length]; decide
  · rw [WitnessLookupByHashIndexedSpec.record_ptr_prog_length]; decide
  · rw [RlpListCountItemsSAsm.total_length, WitnessLookupByHashIndexedSpec.record_ptr_prog_length]; decide


-- @@ L448-456 verbatim
set_option maxRecDepth 8000 in
theorem count_idx_cmp32_disjoint :
    RlpListCountItemsSAsm.code.Disjoint
      WitnessLookupByHashIndexedSpec.cmp32Code := by
  unfold RlpListCountItemsSAsm.code WitnessLookupByHashIndexedSpec.cmp32Code
  apply CodeReq.Disjoint.ofProg_ranges
  · rw [RlpListCountItemsSAsm.total_length]; decide
  · rw [WitnessLookupByHashIndexedSpec.cmp32_prog_length]; decide
  · rw [RlpListCountItemsSAsm.total_length, WitnessLookupByHashIndexedSpec.cmp32_prog_length]; decide


-- @@ L458-464 verbatim
theorem count_idxFull_disjoint :
    RlpListCountItemsSAsm.code.Disjoint idxFullCode := by
  unfold idxFullCode WitnessLookupByHashIndexedSpec.fullCode
  exact CodeReq.Disjoint.union_right
    (CodeReq.Disjoint.union_right count_idxWrap_disjoint
      count_idx_record_ptr_disjoint)
    count_idx_cmp32_disjoint


-- @@ L466-474 verbatim
set_option maxRecDepth 8000 in
theorem nth_idxWrap_disjoint :
    RlpListNthItemSAsm.code.Disjoint
      WitnessLookupByHashIndexedSpec.wrapperCode := by
  unfold RlpListNthItemSAsm.code WitnessLookupByHashIndexedSpec.wrapperCode
  apply CodeReq.Disjoint.ofProg_ranges
  · rw [RlpListNthItemSAsm.total_length]; decide
  · rw [WitnessLookupByHashIndexedSpec.indexed_prog_length]; decide
  · rw [RlpListNthItemSAsm.total_length, WitnessLookupByHashIndexedSpec.indexed_prog_length]; decide


-- @@ L476-484 verbatim
set_option maxRecDepth 8000 in
theorem nth_idx_record_ptr_disjoint :
    RlpListNthItemSAsm.code.Disjoint
      WitnessLookupByHashIndexedSpec.recordPtrCode := by
  unfold RlpListNthItemSAsm.code WitnessLookupByHashIndexedSpec.recordPtrCode
  apply CodeReq.Disjoint.ofProg_ranges
  · rw [RlpListNthItemSAsm.total_length]; decide
  · rw [WitnessLookupByHashIndexedSpec.record_ptr_prog_length]; decide
  · rw [RlpListNthItemSAsm.total_length, WitnessLookupByHashIndexedSpec.record_ptr_prog_length]; decide


-- @@ L486-494 verbatim
set_option maxRecDepth 8000 in
theorem nth_idx_cmp32_disjoint :
    RlpListNthItemSAsm.code.Disjoint
      WitnessLookupByHashIndexedSpec.cmp32Code := by
  unfold RlpListNthItemSAsm.code WitnessLookupByHashIndexedSpec.cmp32Code
  apply CodeReq.Disjoint.ofProg_ranges
  · rw [RlpListNthItemSAsm.total_length]; decide
  · rw [WitnessLookupByHashIndexedSpec.cmp32_prog_length]; decide
  · rw [RlpListNthItemSAsm.total_length, WitnessLookupByHashIndexedSpec.cmp32_prog_length]; decide


-- @@ L496-502 verbatim
theorem nth_idxFull_disjoint :
    RlpListNthItemSAsm.code.Disjoint idxFullCode := by
  unfold idxFullCode WitnessLookupByHashIndexedSpec.fullCode
  exact CodeReq.Disjoint.union_right
    (CodeReq.Disjoint.union_right nth_idxWrap_disjoint
      nth_idx_record_ptr_disjoint)
    nth_idx_cmp32_disjoint


-- @@ L504-507 verbatim
theorem kindFull_idxFull_disjoint : kindFullCode.Disjoint idxFullCode := by
  unfold kindFullCode MptNodeKindSpec.fullCode
  exact CodeReq.Disjoint.union_left kindWrap_idxFull_disjoint
    (CodeReq.Disjoint.union_left count_idxFull_disjoint nth_idxFull_disjoint)


-- @@ L509-516 verbatim
set_option maxRecDepth 8000 in
theorem hp_idxWrap_disjoint :
    (hdnCr HpDecodeB).Disjoint WitnessLookupByHashIndexedSpec.wrapperCode := by
  unfold hdnCr HpDecodeB WitnessLookupByHashIndexedSpec.wrapperCode
  apply CodeReq.Disjoint.ofProg_ranges
  · rw [hp_program_length]; decide
  · rw [WitnessLookupByHashIndexedSpec.indexed_prog_length]; decide
  · rw [hp_program_length, WitnessLookupByHashIndexedSpec.indexed_prog_length]; decide


-- @@ L518-525 verbatim
set_option maxRecDepth 8000 in
theorem hp_idx_record_ptr_disjoint :
    (hdnCr HpDecodeB).Disjoint WitnessLookupByHashIndexedSpec.recordPtrCode := by
  unfold hdnCr HpDecodeB WitnessLookupByHashIndexedSpec.recordPtrCode
  apply CodeReq.Disjoint.ofProg_ranges
  · rw [hp_program_length]; decide
  · rw [WitnessLookupByHashIndexedSpec.record_ptr_prog_length]; decide
  · rw [hp_program_length, WitnessLookupByHashIndexedSpec.record_ptr_prog_length]; decide


-- @@ L527-534 verbatim
set_option maxRecDepth 8000 in
theorem hp_idx_cmp32_disjoint :
    (hdnCr HpDecodeB).Disjoint WitnessLookupByHashIndexedSpec.cmp32Code := by
  unfold hdnCr HpDecodeB WitnessLookupByHashIndexedSpec.cmp32Code
  apply CodeReq.Disjoint.ofProg_ranges
  · rw [hp_program_length]; decide
  · rw [WitnessLookupByHashIndexedSpec.cmp32_prog_length]; decide
  · rw [hp_program_length, WitnessLookupByHashIndexedSpec.cmp32_prog_length]; decide


-- @@ L536-540 verbatim
theorem hp_idxFull_disjoint : (hdnCr HpDecodeB).Disjoint idxFullCode := by
  unfold idxFullCode WitnessLookupByHashIndexedSpec.fullCode
  exact CodeReq.Disjoint.union_right
    (CodeReq.Disjoint.union_right hp_idxWrap_disjoint hp_idx_record_ptr_disjoint)
    hp_idx_cmp32_disjoint


-- @@ L542-549 verbatim
set_option maxRecDepth 8000 in
theorem wlh_idxWrap_disjoint :
    wlhCr.Disjoint WitnessLookupByHashIndexedSpec.wrapperCode := by
  unfold wlhCr WlhB WitnessLookupByHashIndexedSpec.wrapperCode
  apply CodeReq.Disjoint.ofProg_ranges
  · rw [wlh_program_length]; decide
  · rw [WitnessLookupByHashIndexedSpec.indexed_prog_length]; decide
  · rw [wlh_program_length, WitnessLookupByHashIndexedSpec.indexed_prog_length]; decide


-- @@ L551-558 verbatim
set_option maxRecDepth 8000 in
theorem wlh_idx_record_ptr_disjoint :
    wlhCr.Disjoint WitnessLookupByHashIndexedSpec.recordPtrCode := by
  unfold wlhCr WlhB WitnessLookupByHashIndexedSpec.recordPtrCode
  apply CodeReq.Disjoint.ofProg_ranges
  · rw [wlh_program_length]; decide
  · rw [WitnessLookupByHashIndexedSpec.record_ptr_prog_length]; decide
  · rw [wlh_program_length, WitnessLookupByHashIndexedSpec.record_ptr_prog_length]; decide


-- @@ L560-567 verbatim
set_option maxRecDepth 8000 in
theorem wlh_idx_cmp32_disjoint :
    wlhCr.Disjoint WitnessLookupByHashIndexedSpec.cmp32Code := by
  unfold wlhCr WlhB WitnessLookupByHashIndexedSpec.cmp32Code
  apply CodeReq.Disjoint.ofProg_ranges
  · rw [wlh_program_length]; decide
  · rw [WitnessLookupByHashIndexedSpec.cmp32_prog_length]; decide
  · rw [wlh_program_length, WitnessLookupByHashIndexedSpec.cmp32_prog_length]; decide


-- @@ L569-573 verbatim
theorem wlh_idxFull_disjoint : wlhCr.Disjoint idxFullCode := by
  unfold idxFullCode WitnessLookupByHashIndexedSpec.fullCode
  exact CodeReq.Disjoint.union_right
    (CodeReq.Disjoint.union_right wlh_idxWrap_disjoint wlh_idx_record_ptr_disjoint)
    wlh_idx_cmp32_disjoint


-- @@ L575-580 verbatim
theorem walkKindHp_idxFull_disjoint :
    ((wrapperCode.union kindFullCode).union (hdnCr HpDecodeB)).Disjoint
      idxFullCode :=
  CodeReq.Disjoint.union_left
    (CodeReq.Disjoint.union_left wrapper_idxFull_disjoint kindFull_idxFull_disjoint)
    hp_idxFull_disjoint


-- @@ L582-585 verbatim
theorem walkKindHpWlh_idxFull_disjoint :
    walkKindHpWlhCode.Disjoint idxFullCode := by
  unfold walkKindHpWlhCode
  exact CodeReq.Disjoint.union_left walkKindHp_idxFull_disjoint wlh_idxFull_disjoint


-- @@ L587-593 verbatim
/-- Indexed fullCode membership into walk fullCode (#12183). -/
theorem idxCalleeMem : ∀ a i,
    idxFullCode a = some i → fullCode a = some i := by
  intro a i hi
  unfold fullCode
  exact CodeReq.mono_union_right walkKindHpWlh_idxFull_disjoint
    (fun _ _ h => h) a i hi


-- @@ L595-596 verbatim
/-- Local mirror of `WitnessLookupByHashSpec.enableFullCode` (avoid import cycle). -/
def enableFullCodeLocal : CodeReq := wlhCr.union idxFullCode


-- @@ L598-609 verbatim
/-- enableFullCode (wlh ∪ indexed) ⊆ walk fullCode (#12183). -/
theorem enableFull_in_walk_fullCode :
    ∀ a i, enableFullCodeLocal a = some i → fullCode a = some i := by
  intro a i hi
  simp only [enableFullCodeLocal, CodeReq.union] at hi
  cases hw : wlhCr a with
  | some j =>
    simp [hw] at hi
    exact wlhCalleeMem a i (by rw [hw, hi])
  | none =>
    simp [hw] at hi
    exact idxCalleeMem a i hi


-- @@ L611-611 verbatim
/-! Blocker-1 negation: callee entry is constrained by walk `fullCode`. -/

-- @@ L612-614 verbatim
set_option maxRecDepth 8000 in
theorem wlh_entry_in_walk_fullCode : fullCode WlhB ≠ none := by
  unfold fullCode walkKindHpWlhCode wlhCr WlhB; decide


-- @@ L616-617 verbatim
/-- Body PC pins (instruction index → absolute). -/
def pc (n : Nat) : Word := walkB + BitVec.ofNat 64 (4 * n)


-- @@ L619-620 verbatim
theorem pc_succ (n : Nat) : pc n + 4 = pc (n + 1) := by
  unfold pc; bv_omega


-- @@ L622-622 verbatim
theorem pc_eq_walkB (n : Nat) : pc n = walkB + BitVec.ofNat 64 (4 * n) := rfl


-- @@ L624-625 verbatim
/-- First `mpt_node_kind` call site (prog idx 47 = walk+188). -/
def kindCallPc : Word := pc 47



-- @@ L628-629 verbatim
theorem kindCallPc_eq : kindCallPc = walkB + 188 := by
  unfold kindCallPc pc walkB; decide


-- @@ L631-631 verbatim
end EvmAsm.Codegen.MptWalkSpec
