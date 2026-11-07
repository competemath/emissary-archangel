/-
  EvmAsm.Codegen.Programs.Step2ParentHashLayout

  Declaration facts for the Step-2 parent-hash scratch.  These are kept
  separate from the producer and caller contracts: the data declarations
  determine capacities and linked addresses, while a producer contract is
  responsible for showing that a runtime byte list still has that capacity.
-/

import EvmAsm.Codegen.Programs.Step2Verdict
import EvmAsm.Codegen.Programs.HeadersParentHashSpec


-- @@ L13-13 verbatim
namespace EvmAsm.Codegen


-- @@ L15-15 verbatim
open EvmAsm EvmAsm.Rv64


-- @@ L17-19 verbatim
/-! The source declarations are the evidence for these capacities.  The
    `#guard`s intentionally check the emitted data strings, rather than
    silently duplicating the numbers in a comment or theorem name. -/


-- @@ L21-21 verbatim
#guard ziskStep2VerdictDataSection.contains "hvph_claimed:\n  .zero 32\n"

-- @@ L22-22 verbatim
#guard ziskStep2VerdictDataSection.contains "hvph_computed:\n  .zero 32\n"

-- @@ L23-23 verbatim
#guard ziskMptWalkDataSection.contains "zk3_state:\n  .zero 200\n"


-- @@ L25-30 verbatim
/-- The zero-initialized image represented by the `hvph_claimed` declaration.

    This is the declaration's initial image, not a claim that a later
    producer's runtime contents are all zero.  A producer contract must keep
    the length invariant when it replaces these bytes. -/
abbrev step2HvphClaimedImage : List (BitVec 8) := List.replicate 32 0


-- @@ L32-33 verbatim
/-- The zero-initialized image represented by the `zk3_state` declaration. -/
abbrev step2Zk3StateImage : List (BitVec 8) := List.replicate 200 0


-- @@ L35-36 verbatim
theorem step2HvphClaimedImage_length : step2HvphClaimedImage.length = 32 := by
  simp only [step2HvphClaimedImage, List.length_replicate]


-- @@ L38-39 verbatim
theorem step2Zk3StateImage_length : step2Zk3StateImage.length = 200 := by
  simp only [step2Zk3StateImage, List.length_replicate]


-- @@ L41-42 verbatim
/-- Linked address of the 32-byte claimed parent-hash slot. -/
abbrev step2HvphClaimedBase : Word := BitVec.ofNat 64 GuestAddrs.hvph_claimed


-- @@ L44-45 verbatim
/-- Linked address of the 200-byte MPT/withdrawals scratch arena. -/
abbrev step2Zk3StateBase : Word := BitVec.ofNat 64 GuestAddrs.zk3_state


-- @@ L47-49 verbatim
theorem step2HvphClaimedBase_toNat :
    step2HvphClaimedBase.toNat = GuestAddrs.hvph_claimed := by
  exact hphClaimed_toNat


-- @@ L51-52 verbatim
theorem step2HvphClaimedBase_aligned : step2HvphClaimedBase.toNat % 8 = 0 := by
  exact hphClaimed_align


-- @@ L54-56 verbatim
theorem step2HvphClaimedBase_range (i : Nat) (hi : i < 32) :
    step2HvphClaimedBase.toNat + i < 2 ^ 64 := by
  exact hphClaimed_over i hi


-- @@ L58-60 verbatim
theorem step2HvphClaimedBase_valid_byte (i : Nat) (hi : i < 32) :
    isValidByteAccess (step2HvphClaimedBase + BitVec.ofNat 64 i) = true := by
  exact hphClaimed_valid i hi


-- @@ L62-64 verbatim
theorem step2Zk3StateBase_toNat :
    step2Zk3StateBase.toNat = GuestAddrs.zk3_state := by
  decide


-- @@ L66-67 verbatim
theorem step2Zk3StateBase_aligned : step2Zk3StateBase.toNat % 8 = 0 := by
  decide


-- @@ L69-71 verbatim
theorem step2Zk3StateBase_range :
    step2Zk3StateBase.toNat + 200 < 2 ^ 64 := by
  decide


-- @@ L73-90 verbatim
private theorem ram_byte_valid_of_range (base i : Nat)
    (hbase : 0xa0000000 ≤ base)
    (hend : base + i ≤ 0xc0000000) :
    isValidByteAccess (BitVec.ofNat 64 base + BitVec.ofNat 64 i) = true := by
  have hbase64 : base < 2 ^ 64 := by omega
  have hi64 : i < 2 ^ 64 := by omega
  have hsum64 : base + i < 2 ^ 64 := by omega
  have hto :
      (BitVec.ofNat 64 base + BitVec.ofNat 64 i).toNat = base + i := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hbase64, Nat.mod_eq_of_lt hi64,
      Nat.mod_eq_of_lt hsum64]
  simp only [isValidByteAccess, isValidMemAddr, hto,
    Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  show ((0x20 ≤ base + i ∧ base + i ≤ 0x78000000) ∨
      (0x40000000 ≤ base + i ∧ base + i ≤ 0x40002000)) ∨
    (0xa0000000 ≤ base + i ∧ base + i ≤ 0xc0000000)
  exact Or.inr ⟨by omega, hend⟩


-- @@ L92-99 verbatim
theorem step2Zk3StateBase_valid_byte (i : Nat) (hi : i < 200) :
    isValidByteAccess (step2Zk3StateBase + BitVec.ofNat 64 i) = true := by
  rw [show step2Zk3StateBase = BitVec.ofNat 64 GuestAddrs.zk3_state by rfl]
  have hlb : 0xa0000000 ≤ GuestAddrs.zk3_state := by decide
  have hub : GuestAddrs.zk3_state + 199 ≤ 0xc0000000 := by decide
  apply ram_byte_valid_of_range GuestAddrs.zk3_state i
  · omega
  · omega


-- @@ L101-103 verbatim
theorem step2Zk3StateBase_valid_mem (i : Nat) (hi : i < 200) :
    isValidMemAddr (step2Zk3StateBase + BitVec.ofNat 64 i) = true := by
  exact step2Zk3StateBase_valid_byte i hi


-- @@ L105-105 verbatim
end EvmAsm.Codegen
