/-
  Caller-side plumbing for the unified parent-hash contract (#12346 item 8).

  The parent-hash call is made after the validate-header prologue has
  installed the parent RLP pointer in x20.  The continuation ambient therefore
  owns the child-frame stack and scratch/BSS regions, but deliberately leaves
  x20 to the route's post-prologue register assertion.  This prevents the
  ambient from claiming an entry-time x20 that the caller does not provide.
-/

import EvmAsm.Codegen.Programs.ValidateHeaderParentHashAdapter


-- @@ L13-13 verbatim
namespace EvmAsm.Codegen.ValidateHeaderCompose


-- @@ L15-15 verbatim
open EvmAsm EvmAsm.Rv64 EvmAsm.Rv64.SAsm

-- @@ L16-16 verbatim
open EvmAsm.Codegen.ValidateHeaderCorrespondence

-- @@ L17-17 verbatim
open EvmAsm.Codegen.ValidateHeaderParentHashCorrespondence

-- @@ L18-18 verbatim
open EvmAsm.Codegen.HeaderValidateParentHashSpec

-- @@ L19-19 verbatim
open EvmAsm.Codegen.Proofs

-- @@ L20-20 verbatim
open EvmAsm.Rv64.RLP


-- @@ L22-22 verbatim
noncomputable section


-- @@ L24-39 verbatim
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
      | exact pcFree_frameSlotsSaved _ _ _
      | exact pcFree_stackFree _ _
      | exact pcFree_regOwns _)


-- @@ L41-51 verbatim
/-- The unified continuation ambient after the caller has supplied x20.

`hvphSuccKeccakAmb` also owns x20.  At the H+244 call seam that cell is
already produced by `postMerge_status0_to_parent_hash_args`, so this residual
form is what can actually be framed through that caller route. -/
def hvphSuccKeccakTail
    (spC : Word) (os out0 : List (BitVec 8)) (F : Assertion) : Assertion :=
  stackFree spC 4 **
  regOwns [.x14, .x15, .x16, .x17] **
  bytesRegion (BitVec.ofNat 64 GuestAddrs.zk3_state) os **
  bytesRegion Computed out0 ** F


-- @@ L53-58 expanded
theorem hvphSuccKeccakTail_pcFree (spC : Word) (os out0 : List (BitVec 8)) (F : Assertion)
    (hF : F.pcFree) : (hvphSuccKeccakTail spC os out0 F).pcFree :=
  by
  unfold hvphSuccKeccakTail
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
  exact hF


-- @@ L60-66 verbatim
/-! ## The real H+196 → H+248 caller seam

The theorem below is intentionally a direct consumer of
`validate_header_parent_hash_unified_call_spec_within`.  The route carries the
physical claimed/computed/zk3 resources and child-frame stack from the
post-prologue seam; it does not replace them by an unconstrained `G`.
-/


-- @@ L68-159 expanded
set_option maxRecDepth 8000 in
theorem postMerge_status0_to_parent_hash_unified_call {cr calleeCode : CodeReq} {n : Nat}
    (spC childSp header headerLen s4 s5 oldRa : Word) (vals : Reg → Word)
    (thisBytes parentBytes C0 : List (BitVec 8)) (N rem : Nat) (os : List (BitVec 8))
    (G : Assertion) (hG : G.pcFree) (hchild : childSp = spC + signExtend12 (-32 : BitVec 12))
    (hvals8 : vals .x8 = header) (hvals9 : vals .x9 = headerLen) (hvals18 : vals .x18 = s4)
    (hdisj :
      (CodeReq.singleton ValidateHeaderParentHashCorrespondence.A
            (.JAL .x1
              (jalOff GuestAddrs.header_validate_parent_hash
                (GuestAddrs.validate_header + 244)))).Disjoint
        calleeCode)
    (hcallerDisj : parentHashRouteFrameCaller.Disjoint calleeCode)
    (hcode : ∀ a i, (parentHashRouteFrameCaller.union calleeCode) a = some i → cr a = some i)
    (hcallee :
      cpsTripleWithin n ValidateHeaderParentHashCorrespondence.Callee
        ValidateHeaderParentHashCorrespondence.Ret calleeCode
        ((.x1 ↦ᵣ ValidateHeaderParentHashCorrespondence.Ret) **
          ValidateHeaderParentHashCorrespondence.hvphEntryRest spC header headerLen s4 s5 vals
              thisBytes parentBytes **
            claimedOwn C0 ** hvphSuccKeccakAmb childSp s4 os (List.replicate 32 0) G)
        (hvphUnifiedPost spC childSp ValidateHeaderParentHashCorrespondence.Ret header s4 s5 vals s4
          thisBytes parentBytes C0 N rem os G)) :
    cpsTripleWithin (5 + (1 + n)) (parentHashRouteFrameH + 196)
      ValidateHeaderParentHashCorrespondence.Ret cr
      ((.x10 ↦ᵣ (0 : Word)) **
        (.x0 ↦ᵣ (0 : Word)) **
          (.x8 ↦ᵣ header) **
            (.x9 ↦ᵣ headerLen) **
              (.x20 ↦ᵣ s4) **
                (.x21 ↦ᵣ s5) **
                  (.x11 ↦ᵣ (0 : Word)) **
                    (.x12 ↦ᵣ (0 : Word)) **
                      (.x13 ↦ᵣ (0 : Word)) **
                        parentHashRouteFrame spC oldRa header s4 vals thisBytes parentBytes **
                          claimedOwn C0 ** hvphSuccKeccakTail childSp os (List.replicate 32 0) G)
      ((.x21 ↦ᵣ s5) **
        hvphUnifiedPost spC childSp ValidateHeaderParentHashCorrespondence.Ret header s4 s5 vals s4
          thisBytes parentBytes C0 N rem os G) :=
  by
  let tail := hvphSuccKeccakTail childSp os (List.replicate 32 0) G
  let F :=
    parentHashRouteFrame spC oldRa header s4 vals thisBytes parentBytes ** claimedOwn C0 ** tail
  have hF : F.pcFree := by
    dsimp [F, tail]
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
    exact hG
  have hroute :=
    postMerge_status0_to_parent_hash_args (header := header) (headerLen := headerLen) (s4 := s4)
      (s5 := s5) (F := F) hF
  have hcallerCode : ∀ a i, parentHashRouteFrameCaller a = some i → cr a = some i :=
    by
    intro a i hi
    exact hcode a i (CodeReq.union_mono_left a i hi)
  have hrouteC := cpsTripleWithin_extend_code hcallerCode hroute
  have hcall :=
    validate_header_parent_hash_unified_call_spec_within (cr := cr) (calleeCode := calleeCode) (n :=
      n) spC childSp header headerLen s4 s5 oldRa vals thisBytes parentBytes C0 N rem os s4 G hG
      hdisj hcallerDisj hcode hcallee
  have hx21 : ((.x21 ↦ᵣ s5) : Assertion).pcFree := pcFree_regIs
  have hcallF := cpsTripleWithin_frameR ((.x21 ↦ᵣ s5) : Assertion) hx21 hcall
  have hseq :=
    cpsTripleWithin_seq_perm_same_cr
      (fun _ hp => by
        unfold F tail hvphSuccKeccakTail at hp
        unfold parentHashRouteFrame at hp
        unfold ValidateHeaderParentHashCorrespondence.hvphEntryRest hvphSuccKeccakAmb
        have hneg : signExtend12 (-32 : BitVec 12) = signExtend12 (BitVec.ofNat 12 4064) := by
          decide
        have hbase :
          spC + signExtend12 (-32 : BitVec 12) = spC + signExtend12 (BitVec.ofNat 12 4064) := by
          rw [hneg]
        rw [hchild] at hp
        rw [hchild] at ⊢
        rw [hbase] at ⊢
        rw [hbase] at hp
        rw [hvals18] at hp
        simp [hvals8, hvals9, hvals18, ValidateHeaderParentHashCorrespondence.hvphSavedFrame,
          EvmAsm.Rv64.SAsm.regsAt, EvmAsm.Rv64.SAsm.regOwns, HeaderValidateParentHashSpec.Computed,
          sepConj_emp_right'] at hp ⊢
        xperm_hyp hp)
      hrouteC hcallF
  refine
    cpsTripleWithin_weaken (fun _ hp => by simpa [F, tail, sepConj_assoc'] using hp)
      (fun _ hq => by xperm_hyp hq) hseq


-- @@ L161-165 verbatim
/-! The fully applied variant discharges the callee premise from the already
    proven whole-routine unified parent-hash contract.  Keeping this wrapper
    separate from the seam theorem makes the two obligations visible: the
    seam still accepts an arbitrary `hcallee`, while this theorem supplies it
    from the concrete header/parent/keccak side conditions. -/


-- @@ L167-250 verbatim
set_option maxRecDepth 8000 in
theorem postMerge_status0_to_parent_hash_unified_call_from_spec
    {cr : CodeReq} {n : Nat}
    (spC childSp header headerLen s4 s5 oldRa : Word)
    (vals : Reg → Word)
    (thisBytes parentBytes C0 : List (BitVec 8)) (N rem : Nat)
    (os : List (BitVec 8)) (G : Assertion)
    (hG : G.pcFree)
    (hchild : childSp = spC + signExtend12 (-32 : BitVec 12))
    (hvals8 : vals .x8 = header)
    (hvals9 : vals .x9 = headerLen)
    (hvals18 : vals .x18 = s4)
    (hlenW : thisBytes.length = headerLen.toNat)
    (hlen3 : 3 ≤ thisBytes.length)
    (hclaim0 : C0.length = 32)
    (hHeaderAlign : header.toNat % 8 = 0)
    (hsover : header.toNat + thisBytes.length ≤ 2 ^ 64)
    (hsvalid : ∀ k, k < thisBytes.length →
      isValidByteAccess (header + BitVec.ofNat 64 k) = true)
    (hplen : s5 = BitVec.ofNat 64
      (EvmAsm.Codegen.Proofs.keccakAbsorbStep * N + rem))
    (hlen : parentBytes.length = EvmAsm.Codegen.Proofs.keccakAbsorbStep * N + rem)
    (hrem_le : rem ≤ 135)
    (hos : os.length = 200)
    (halign_zk : (BitVec.ofNat 64 GuestAddrs.zk3_state).toNat % 8 = 0)
    (hover : (BitVec.ofNat 64 GuestAddrs.zk3_state).toNat + 200 < 2 ^ 64)
    (hNbound : EvmAsm.Codegen.Proofs.keccakAbsorbStep * N + rem < 2 ^ 63)
    (hrem64 : rem < 2 ^ 64)
    (hb8i : (EvmAsm.Codegen.Proofs.keccakAbsorbCursor s4 N).toNat % 8 = 0)
    (hovers : ∀ n, n < rem →
      (BitVec.ofNat 64 GuestAddrs.zk3_state).toNat + (rem - (n + 1)) < 2 ^ 64)
    (hoveri : ∀ n, n < rem →
      (EvmAsm.Codegen.Proofs.keccakAbsorbCursor s4 N).toNat +
        (rem - (n + 1)) < 2 ^ 64)
    (hvalids : ∀ n, n < rem →
      isValidByteAccess
        (BitVec.ofNat 64 GuestAddrs.zk3_state + BitVec.ofNat 64 (rem - (n + 1))) = true)
    (hvalidi : ∀ n, n < rem →
      isValidByteAccess
        (EvmAsm.Codegen.Proofs.keccakAbsorbCursor s4 N +
          BitVec.ofNat 64 (rem - (n + 1))) = true)
    (hvalidRem : isValidByteAccess
      (BitVec.ofNat 64 GuestAddrs.zk3_state + BitVec.ofNat 64 rem) = true)
    (hvalid135 : isValidByteAccess
      (BitVec.ofNat 64 GuestAddrs.zk3_state + BitVec.ofNat 64 135) = true)
    (hvalidMem : ∀ j, j < 200 →
      isValidMemAddr
        (BitVec.ofNat 64 GuestAddrs.zk3_state + BitVec.ofNat 64 j) = true)
    (hbound : 40 + 312 + nKeccak N rem ≤ n)
    (hdisj : (CodeReq.singleton
      ValidateHeaderParentHashCorrespondence.A
      (.JAL .x1 (jalOff GuestAddrs.header_validate_parent_hash
        (GuestAddrs.validate_header + 244)))).Disjoint
      HeaderValidateParentHashSpec.fullCode)
    (hcallerDisj : parentHashRouteFrameCaller.Disjoint
      HeaderValidateParentHashSpec.fullCode)
    (hcode : ∀ a i,
      (parentHashRouteFrameCaller.union HeaderValidateParentHashSpec.fullCode) a = some i →
      cr a = some i) :
    cpsTripleWithin (5 + (1 + n))
      (parentHashRouteFrameH + 196)
      ValidateHeaderParentHashCorrespondence.Ret cr
      ((.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x8 ↦ᵣ header) ** (.x9 ↦ᵣ headerLen) **
        (.x20 ↦ᵣ s4) ** (.x21 ↦ᵣ s5) **
        (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (0 : Word)) **
        (.x13 ↦ᵣ (0 : Word)) **
        parentHashRouteFrame spC oldRa header s4 vals thisBytes parentBytes **
        claimedOwn C0 **
        hvphSuccKeccakTail childSp os (List.replicate 32 0) G)
      ((.x21 ↦ᵣ s5) **
        hvphUnifiedPost spC childSp
          ValidateHeaderParentHashCorrespondence.Ret header s4 s5 vals s4
          thisBytes parentBytes C0 N rem os G) := by
  have hcallee0 := header_validate_parent_hash_hcallee_from_spec
    spC childSp ValidateHeaderParentHashCorrespondence.Ret header headerLen s4 s5
    vals s4 thisBytes parentBytes C0 N rem os G hG (by decide) hchild hlenW hlen3
    hclaim0 hHeaderAlign hsover hsvalid hplen hlen hrem_le hos halign_zk
    hover hNbound hrem64 hb8i hovers hoveri hvalids hvalidi hvalidRem hvalid135
    hvalidMem
  have hcallee := header_validate_parent_hash_hcallee_mono_fuel hbound hcallee0
  exact postMerge_status0_to_parent_hash_unified_call
    spC childSp header headerLen s4 s5 oldRa vals thisBytes parentBytes C0 N rem os G
    hG hchild hvals8 hvals9 hvals18 hdisj hcallerDisj hcode hcallee


-- @@ L252-262 verbatim
/-! ## Applied-ambient non-vacuity witness

The route's new resources are not merely names in a postcondition.  The
concrete witness below supplies the post-prologue `x20`, four free stack cells,
the four temporary registers, the 32-byte `Claimed` region, the 200-byte
`zk3_state` arena, and the four dwords of `Computed`.  The 200-byte witness
must include the 25th dword at `zk3_state + 192`; omitting it would only prove
a shorter, degenerate shape.  The final theorem combines this ambient with
the existing `hvphEntryRest_inhabited` witness, so the complete unified-call
precondition is inhabited at one concrete frame.
-/


-- @@ L264-268 verbatim
private inductive item8Atom where
  | regVal (r : Reg) (v : Word)
  | regOwn (r : Reg)
  | memVal (a v : Word) (hvalid : isValidDwordAccess a = true)
  | memOwn (a : Word) (hvalid : isValidDwordAccess a = true)


-- @@ L270-273 verbatim
private inductive item8Resource where
  | reg (r : Reg)
  | mem (a : Word)
  deriving DecidableEq


-- @@ L275-279 verbatim
private def item8AtomResource : item8Atom → item8Resource
  | .regVal r _ => .reg r
  | .regOwn r => .reg r
  | .memVal a _ _ => .mem a
  | .memOwn a _ => .mem a


-- @@ L281-285 verbatim
private def item8AtomAssertion : item8Atom → Assertion
  | .regVal r v => r ↦ᵣ v
  | .regOwn r => regOwn r
  | .memVal a v _ => a ↦ₘ v
  | .memOwn a _ => memOwn a


-- @@ L287-291 verbatim
private def item8AtomHeap : item8Atom → PartialState
  | .regVal r v => PartialState.singletonReg r v
  | .regOwn r => PartialState.singletonReg r 0
  | .memVal a v _ => PartialState.singletonMem a v
  | .memOwn a _ => PartialState.singletonMem a 0


-- @@ L293-293 verbatim
private abbrev item8SpC : Word := 0xFE8

-- @@ L294-294 verbatim
private abbrev item8ChildSp : Word := 0xFC8

-- @@ L295-295 verbatim
private abbrev item8S4 : Word := 0x3000

-- @@ L296-296 verbatim
private abbrev item8C0 : List (BitVec 8) := List.replicate 32 0

-- @@ L297-297 verbatim
private abbrev item8Os : List (BitVec 8) := List.replicate 200 0

-- @@ L298-298 verbatim
private abbrev item8Out0 : List (BitVec 8) := List.replicate 32 0


-- @@ L300-339 verbatim
private def item8Atoms : List item8Atom :=
  [ .memVal (BitVec.ofNat 64 GuestAddrs.hvph_claimed) 0 (by decide)
  , .memVal (BitVec.ofNat 64 GuestAddrs.hvph_claimed + 8) 0 (by decide)
  , .memVal (BitVec.ofNat 64 GuestAddrs.hvph_claimed + 16) 0 (by decide)
  , .memVal (BitVec.ofNat 64 GuestAddrs.hvph_claimed + 24) 0 (by decide)
  , .regVal .x20 item8S4
  , .memOwn (item8ChildSp - BitVec.ofNat 64 32) (by decide)
  , .memOwn (item8ChildSp - BitVec.ofNat 64 24) (by decide)
  , .memOwn (item8ChildSp - BitVec.ofNat 64 16) (by decide)
  , .memOwn (item8ChildSp - BitVec.ofNat 64 8) (by decide)
  , .regOwn .x14, .regOwn .x15, .regOwn .x16, .regOwn .x17
  , .memVal (BitVec.ofNat 64 GuestAddrs.zk3_state) 0 (by decide)
  , .memVal (BitVec.ofNat 64 GuestAddrs.zk3_state + 8) 0 (by decide)
  , .memVal (BitVec.ofNat 64 GuestAddrs.zk3_state + 16) 0 (by decide)
  , .memVal (BitVec.ofNat 64 GuestAddrs.zk3_state + 24) 0 (by decide)
  , .memVal (BitVec.ofNat 64 GuestAddrs.zk3_state + 32) 0 (by decide)
  , .memVal (BitVec.ofNat 64 GuestAddrs.zk3_state + 40) 0 (by decide)
  , .memVal (BitVec.ofNat 64 GuestAddrs.zk3_state + 48) 0 (by decide)
  , .memVal (BitVec.ofNat 64 GuestAddrs.zk3_state + 56) 0 (by decide)
  , .memVal (BitVec.ofNat 64 GuestAddrs.zk3_state + 64) 0 (by decide)
  , .memVal (BitVec.ofNat 64 GuestAddrs.zk3_state + 72) 0 (by decide)
  , .memVal (BitVec.ofNat 64 GuestAddrs.zk3_state + 80) 0 (by decide)
  , .memVal (BitVec.ofNat 64 GuestAddrs.zk3_state + 88) 0 (by decide)
  , .memVal (BitVec.ofNat 64 GuestAddrs.zk3_state + 96) 0 (by decide)
  , .memVal (BitVec.ofNat 64 GuestAddrs.zk3_state + 104) 0 (by decide)
  , .memVal (BitVec.ofNat 64 GuestAddrs.zk3_state + 112) 0 (by decide)
  , .memVal (BitVec.ofNat 64 GuestAddrs.zk3_state + 120) 0 (by decide)
  , .memVal (BitVec.ofNat 64 GuestAddrs.zk3_state + 128) 0 (by decide)
  , .memVal (BitVec.ofNat 64 GuestAddrs.zk3_state + 136) 0 (by decide)
  , .memVal (BitVec.ofNat 64 GuestAddrs.zk3_state + 144) 0 (by decide)
  , .memVal (BitVec.ofNat 64 GuestAddrs.zk3_state + 152) 0 (by decide)
  , .memVal (BitVec.ofNat 64 GuestAddrs.zk3_state + 160) 0 (by decide)
  , .memVal (BitVec.ofNat 64 GuestAddrs.zk3_state + 168) 0 (by decide)
  , .memVal (BitVec.ofNat 64 GuestAddrs.zk3_state + 176) 0 (by decide)
  , .memVal (BitVec.ofNat 64 GuestAddrs.zk3_state + 184) 0 (by decide)
  , .memVal (BitVec.ofNat 64 GuestAddrs.zk3_state + 192) 0 (by decide)
  , .memVal (BitVec.ofNat 64 GuestAddrs.hvph_computed) 0 (by decide)
  , .memVal (BitVec.ofNat 64 GuestAddrs.hvph_computed + 8) 0 (by decide)
  , .memVal (BitVec.ofNat 64 GuestAddrs.hvph_computed + 16) 0 (by decide)
  , .memVal (BitVec.ofNat 64 GuestAddrs.hvph_computed + 24) 0 (by decide) ]


-- @@ L341-342 verbatim
private def item8AtomsAssertion : Assertion :=
  item8Atoms.foldr (fun x acc => item8AtomAssertion x ** acc) empAssertion


-- @@ L344-345 verbatim
private def item8AtomsHeap : PartialState :=
  item8Atoms.foldr (fun x acc => (item8AtomHeap x).union acc) PartialState.empty


-- @@ L347-359 verbatim
private theorem item8RegRegDisjoint {r1 r2 : Reg} {v1 v2 : Word}
    (hne : r1 ≠ r2) :
    (PartialState.singletonReg r1 v1).Disjoint
      (PartialState.singletonReg r2 v2) := by
  refine ⟨?_, fun _ => Or.inl rfl, fun _ => Or.inl rfl,
    Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl⟩
  intro r
  by_cases h : r = r1
  · subst r
    right
    simp [PartialState.singletonReg, hne]
  · left
    simp [PartialState.singletonReg, h]


-- @@ L361-373 verbatim
private theorem item8MemMemDisjoint {a1 a2 v1 v2 : Word}
    (hne : a1 ≠ a2) :
    (PartialState.singletonMem a1 v1).Disjoint
      (PartialState.singletonMem a2 v2) := by
  refine ⟨fun _ => Or.inl rfl, ?_, fun _ => Or.inl rfl,
    Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl⟩
  intro a
  by_cases h : a = a1
  · subst a
    right
    simp [PartialState.singletonMem, hne]
  · left
    simp [PartialState.singletonMem, h]


-- @@ L375-379 verbatim
private theorem item8RegMemDisjoint {r : Reg} {a v w : Word} :
    (PartialState.singletonReg r v).Disjoint
      (PartialState.singletonMem a w) :=
  ⟨fun _ => Or.inr rfl, fun _ => Or.inl rfl, fun _ => Or.inl rfl,
    Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl⟩


-- @@ L381-408 verbatim
private theorem item8AtomHeapDisjoint_of_resource_ne {x y : item8Atom}
    (h : item8AtomResource x ≠ item8AtomResource y) :
    (item8AtomHeap x).Disjoint (item8AtomHeap y) := by
  cases x <;> cases y
  · apply item8RegRegDisjoint
    simpa [item8AtomResource] using h
  · apply item8RegRegDisjoint
    simpa [item8AtomResource] using h
  · exact item8RegMemDisjoint
  · exact item8RegMemDisjoint
  · apply item8RegRegDisjoint
    simpa [item8AtomResource] using h
  · apply item8RegRegDisjoint
    simpa [item8AtomResource] using h
  · exact item8RegMemDisjoint
  · exact item8RegMemDisjoint
  · exact item8RegMemDisjoint.symm
  · exact item8RegMemDisjoint.symm
  · apply item8MemMemDisjoint
    simpa [item8AtomResource] using h
  · apply item8MemMemDisjoint
    simpa [item8AtomResource] using h
  · exact item8RegMemDisjoint.symm
  · exact item8RegMemDisjoint.symm
  · apply item8MemMemDisjoint
    simpa [item8AtomResource] using h
  · apply item8MemMemDisjoint
    simpa [item8AtomResource] using h


-- @@ L410-422 verbatim
private theorem item8Atoms_sat : item8AtomsAssertion item8AtomsHeap := by
  apply sepConj_foldr_satisfiable item8AtomAssertion item8AtomHeap item8Atoms
  · intro x hx
    cases x with
    | regVal r v => rfl
    | regOwn r => exact ⟨0, rfl⟩
    | memVal a v hvalid => exact ⟨rfl, hvalid⟩
    | memOwn a hvalid => exact ⟨0, rfl, hvalid⟩
  · have hpair : item8Atoms.Pairwise
        (fun x y => item8AtomResource x ≠ item8AtomResource y) := by
      decide
    exact List.Pairwise.imp
      (fun {_ _} h => item8AtomHeapDisjoint_of_resource_ne h) hpair


-- @@ L424-438 verbatim
set_option maxRecDepth 8000 in
private theorem item8Atoms_assertion_eq :
    item8AtomsAssertion =
      (claimedOwn item8C0 ** (.x20 ↦ᵣ item8S4) ** stackFree item8ChildSp 4 **
        regOwns [.x14, .x15, .x16, .x17] **
        bytesRegion (BitVec.ofNat 64 GuestAddrs.zk3_state) item8Os **
        bytesRegion (BitVec.ofNat 64 GuestAddrs.hvph_computed) item8Out0) := by
  funext h
  have hzero :
      packBytes ([0#8, 0#8, 0#8, 0#8, 0#8, 0#8, 0#8, 0#8] :
        List (BitVec 8)) = (0 : Word) := by decide
  simp [item8AtomsAssertion, item8Atoms, item8AtomAssertion, stackFree,
    regOwns, bytesRegion, bytesRegionAux, item8C0, item8Os, item8Out0,
    hzero, BitVec.add_assoc, sepConj_emp_right',
    sepConj_assoc']


-- @@ L440-447 verbatim
theorem parentHashUnifiedAmbient_inhabited :
    ∃ h : PartialState,
      (claimedOwn item8C0 **
        hvphSuccKeccakAmb item8ChildSp item8S4 item8Os item8Out0 empAssertion) h := by
  refine ⟨item8AtomsHeap, ?_⟩
  have hsat := item8Atoms_sat
  rw [item8Atoms_assertion_eq] at hsat
  simpa [hvphSuccKeccakAmb, sepConj_emp_left', sepConj_emp_right'] using hsat


-- @@ L449-449 verbatim
end


-- @@ L451-451 verbatim
end EvmAsm.Codegen.ValidateHeaderCompose
