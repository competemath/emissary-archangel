/-
  EvmAsm.Evm64.SMod.AddrNorm

  Address-normalization simp set for SMOD composition proofs.

  The base `signExtend12` literals live in `Rv64.AddrNorm`; this module
  re-tags the SMOD stack-slot subset and records the composed address
  equalities that recur in the SMOD bridge layer.
-/

module

public import EvmAsm.Rv64.AddrNorm
public import EvmAsm.Evm64.SMod.AddrNormAttr
public import EvmAsm.Evm64.SMod.Program
meta import EvmAsm.Rv64.AddrNorm
meta import EvmAsm.Evm64.SMod.AddrNormAttr
meta import EvmAsm.Evm64.SMod.Program


-- @@ L20-20 verbatim
public section


-- @@ L22-22 verbatim
namespace EvmAsm.Evm64.SMod.AddrNorm


-- @@ L24-24 verbatim
open EvmAsm.Rv64


-- @@ L26-34 verbatim
attribute [smod_addr]
  EvmAsm.Rv64.AddrNorm.se12_0
  EvmAsm.Rv64.AddrNorm.se12_8
  EvmAsm.Rv64.AddrNorm.se12_16
  EvmAsm.Rv64.AddrNorm.se12_24
  EvmAsm.Rv64.AddrNorm.se12_32
  EvmAsm.Rv64.AddrNorm.se12_40
  EvmAsm.Rv64.AddrNorm.se12_48
  EvmAsm.Rv64.AddrNorm.se12_56


-- @@ L36-36 verbatim
@[smod_addr, grind =] 
-- @@ L36-39 verbatim
theorem stackSlot0 (sp : Word) :
    (sp + EvmAsm.Rv64.signExtend12 (0 : BitVec 12) : Word) = sp := by
  rw [EvmAsm.Rv64.AddrNorm.se12_0]
  simp


-- @@ L41-41 verbatim
@[smod_addr, grind =] 
-- @@ L41-43 verbatim
theorem stackSlot8 (sp : Word) :
    (sp + EvmAsm.Rv64.signExtend12 (8 : BitVec 12) : Word) = sp + 8 := by
  rw [EvmAsm.Rv64.AddrNorm.se12_8]


-- @@ L45-45 verbatim
@[smod_addr, grind =] 
-- @@ L45-47 verbatim
theorem stackSlot16 (sp : Word) :
    (sp + EvmAsm.Rv64.signExtend12 (16 : BitVec 12) : Word) = sp + 16 := by
  rw [EvmAsm.Rv64.AddrNorm.se12_16]


-- @@ L49-49 verbatim
@[smod_addr, grind =] 
-- @@ L49-51 verbatim
theorem stackSlot24 (sp : Word) :
    (sp + EvmAsm.Rv64.signExtend12 (24 : BitVec 12) : Word) = sp + 24 := by
  rw [EvmAsm.Rv64.AddrNorm.se12_24]


-- @@ L53-53 verbatim
@[smod_addr, grind =] 
-- @@ L53-55 verbatim
theorem stackSlot32 (sp : Word) :
    (sp + EvmAsm.Rv64.signExtend12 (32 : BitVec 12) : Word) = sp + 32 := by
  rw [EvmAsm.Rv64.AddrNorm.se12_32]


-- @@ L57-57 verbatim
@[smod_addr, grind =] 
-- @@ L57-59 verbatim
theorem stackSlot40 (sp : Word) :
    (sp + EvmAsm.Rv64.signExtend12 (40 : BitVec 12) : Word) = sp + 40 := by
  rw [EvmAsm.Rv64.AddrNorm.se12_40]


-- @@ L61-61 verbatim
@[smod_addr, grind =] 
-- @@ L61-63 verbatim
theorem stackSlot48 (sp : Word) :
    (sp + EvmAsm.Rv64.signExtend12 (48 : BitVec 12) : Word) = sp + 48 := by
  rw [EvmAsm.Rv64.AddrNorm.se12_48]


-- @@ L65-65 verbatim
@[smod_addr, grind =] 
-- @@ L65-67 verbatim
theorem stackSlot56 (sp : Word) :
    (sp + EvmAsm.Rv64.signExtend12 (56 : BitVec 12) : Word) = sp + 56 := by
  rw [EvmAsm.Rv64.AddrNorm.se12_56]


-- @@ L69-69 verbatim
@[smod_addr, grind =] 
-- @@ L69-71 verbatim
theorem divisorBaseSlot0 (sp : Word) :
    (sp + EvmAsm.Rv64.signExtend12 (32 : BitVec 12) : Word) = sp + 32 := by
  exact stackSlot32 sp


-- @@ L73-73 verbatim
@[smod_addr, grind =] 
-- @@ L73-76 verbatim
theorem divisorBaseSlot8 (sp : Word) :
    (sp + EvmAsm.Rv64.signExtend12 (40 : BitVec 12) : Word) = (sp + 32) + 8 := by
  rw [EvmAsm.Rv64.AddrNorm.se12_40]
  bv_omega


-- @@ L78-78 verbatim
@[smod_addr, grind =] 
-- @@ L78-81 verbatim
theorem divisorBaseSlot16 (sp : Word) :
    (sp + EvmAsm.Rv64.signExtend12 (48 : BitVec 12) : Word) = (sp + 32) + 16 := by
  rw [EvmAsm.Rv64.AddrNorm.se12_48]
  bv_omega


-- @@ L83-83 verbatim
@[smod_addr, grind =] 
-- @@ L83-86 verbatim
theorem divisorBaseSlot24 (sp : Word) :
    (sp + EvmAsm.Rv64.signExtend12 (56 : BitVec 12) : Word) = (sp + 32) + 24 := by
  rw [EvmAsm.Rv64.AddrNorm.se12_56]
  bv_omega


-- @@ L88-88 verbatim
@[smod_addr, grind =] 
-- @@ L88-92 verbatim
theorem dividendTopSlot (sp : Word) :
    (sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_smodDividendTopLimbOff : Word) =
      sp + 24 := by
  unfold EvmAsm.Evm64.evm_smodDividendTopLimbOff
  exact stackSlot24 sp


-- @@ L94-94 verbatim
@[smod_addr, grind =] 
-- @@ L94-101 verbatim
theorem divisorTopSlot (sp : Word) :
    (sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_smodDivisorTopLimbOff : Word) =
      sp + 56 := by
  unfold EvmAsm.Evm64.evm_smodDivisorTopLimbOff
  exact stackSlot56 sp

-- The variable-head LHS is deliberate: this is the `smod_addr` set's start-of-
-- program normalization anchor, so the (v4.31+) varHead lint is expected here.

-- @@ L102-107 verbatim
set_option warning.simp.varHead false in
/-- The wrapper starts at the enclosing SMOD program base. -/
@[smod_addr]
theorem wrapperStart_addr (base : Word) :
    base = base + BitVec.ofNat 64 (4 * 0) := by
  bv_omega


-- @@ L109-115 verbatim
/-- The appended unsigned MOD callable starts after the 71-instruction wrapper,
    at byte offset 284 from the enclosing SMOD program base. -/
@[smod_addr]
theorem modCallableStart_addr (base : Word) :
    base + (284 : Word) =
      base + BitVec.ofNat 64 (4 * 71) := by
  bv_omega


-- @@ L117-117 verbatim
end EvmAsm.Evm64.SMod.AddrNorm
