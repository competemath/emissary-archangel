/-
  EvmAsm.Evm64.DivMod.AddrNorm

  Address-normalization simp set and `divmod_addr` tactic for DivMod composition
  proofs. Resolves issue #263.

  The DivMod composition proofs contain ~112 one-off address-equality lemmas,
  each of the form
      `(sp + signExtend12 N₁ ± k <<< 3) ± signExtend12 N₂ = sp + signExtend12 N₃`
  and closed by
      `simp only [<atomic signExtend12/shift/toNat facts>]; bv_omega`.

  This file centralizes the atomic facts as the `divmod_addr` simp set (and
  `@[grind =]`-registers them for `grind`-based closing), then exposes a
  `divmod_addr` tactic that tries `grind` first and falls back to
  `simp only [divmod_addr]; bv_omega`.

  The atomic `signExtend12 N` and `(N : BitVec 6).toNat` facts were promoted
  to `Rv64/AddrNorm.lean` by issue #493 (so Shift/SignExtend/Byte can use them
  without pulling in DivMod). They are re-tagged with `@[divmod_addr]` here so
  the `divmod_addr` grindset keeps the same coverage.

  Adding a new concrete DivMod-specific offset or shift amount is one line
  here — every downstream proof that uses `by divmod_addr` picks it up
  automatically.
-/

module

public import EvmAsm.Rv64.AddrNorm
public import EvmAsm.Evm64.DivMod.AddrNormAttr
meta import EvmAsm.Rv64.AddrNorm
meta import EvmAsm.Evm64.DivMod.AddrNormAttr


-- @@ L35-35 verbatim
public section


-- @@ L37-37 verbatim
namespace EvmAsm.Evm64.DivMod.AddrNorm


-- @@ L39-46 verbatim
open EvmAsm.Rv64

-- ============================================================================
-- Re-tag Rv64 atomic `signExtend12` / `BitVec 6.toNat` facts with
-- `@[divmod_addr]` so the DivMod grindset keeps the same coverage after the
-- promotion to `Rv64/AddrNorm.lean` (issue #493). Kernel-level definitions
-- still live in `Rv64.AddrNorm`; we only attach the additional attribute.
-- ============================================================================


-- @@ L48-95 verbatim
attribute [divmod_addr]
  EvmAsm.Rv64.AddrNorm.se12_0
  EvmAsm.Rv64.AddrNorm.se12_1
  EvmAsm.Rv64.AddrNorm.se12_2
  EvmAsm.Rv64.AddrNorm.se12_3
  EvmAsm.Rv64.AddrNorm.se12_4
  EvmAsm.Rv64.AddrNorm.se12_8
  EvmAsm.Rv64.AddrNorm.se12_12
  EvmAsm.Rv64.AddrNorm.se12_16
  EvmAsm.Rv64.AddrNorm.se12_24
  EvmAsm.Rv64.AddrNorm.se12_32
  EvmAsm.Rv64.AddrNorm.se12_40
  EvmAsm.Rv64.AddrNorm.se12_48
  EvmAsm.Rv64.AddrNorm.se12_56
  EvmAsm.Rv64.AddrNorm.se12_3944
  EvmAsm.Rv64.AddrNorm.se12_3952
  EvmAsm.Rv64.AddrNorm.se12_3960
  EvmAsm.Rv64.AddrNorm.se12_3968
  EvmAsm.Rv64.AddrNorm.se12_3976
  EvmAsm.Rv64.AddrNorm.se12_3984
  EvmAsm.Rv64.AddrNorm.se12_3992
  EvmAsm.Rv64.AddrNorm.se12_4000
  EvmAsm.Rv64.AddrNorm.se12_4008
  EvmAsm.Rv64.AddrNorm.se12_4016
  EvmAsm.Rv64.AddrNorm.se12_4024
  EvmAsm.Rv64.AddrNorm.se12_4032
  EvmAsm.Rv64.AddrNorm.se12_4040
  EvmAsm.Rv64.AddrNorm.se12_4048
  EvmAsm.Rv64.AddrNorm.se12_4056
  EvmAsm.Rv64.AddrNorm.se12_4064
  EvmAsm.Rv64.AddrNorm.se12_4072
  EvmAsm.Rv64.AddrNorm.se12_4080
  EvmAsm.Rv64.AddrNorm.se12_4088
  EvmAsm.Rv64.AddrNorm.se12_4095
  EvmAsm.Rv64.AddrNorm.bv6_toNat_2
  EvmAsm.Rv64.AddrNorm.bv6_toNat_3
  EvmAsm.Rv64.AddrNorm.bv6_toNat_4
  EvmAsm.Rv64.AddrNorm.bv6_toNat_8
  EvmAsm.Rv64.AddrNorm.bv6_toNat_16
  EvmAsm.Rv64.AddrNorm.bv6_toNat_32
  EvmAsm.Rv64.AddrNorm.bv6_toNat_48
  EvmAsm.Rv64.AddrNorm.bv6_toNat_56
  EvmAsm.Rv64.AddrNorm.bv6_toNat_60
  EvmAsm.Rv64.AddrNorm.bv6_toNat_62
  EvmAsm.Rv64.AddrNorm.bv6_toNat_63

-- Export them under `EvmAsm.Evm64.DivMod.AddrNorm` so existing `open` clauses
-- that reference e.g. `EvmAsm.Evm64.DivMod.AddrNorm (se12_32 …)` keep working.

-- @@ L96-108 verbatim
export EvmAsm.Rv64.AddrNorm
  (se12_0 se12_1 se12_2 se12_3 se12_4 se12_8 se12_12 se12_16 se12_24
   se12_32 se12_40 se12_48 se12_56
   se12_3944 se12_3952 se12_3960 se12_3968 se12_3976 se12_3984 se12_3992
   se12_4000 se12_4008 se12_4016 se12_4024 se12_4032 se12_4040 se12_4048
   se12_4056 se12_4064 se12_4072 se12_4080 se12_4088 se12_4095
   bv6_toNat_2 bv6_toNat_3 bv6_toNat_4 bv6_toNat_8 bv6_toNat_16 bv6_toNat_32
   bv6_toNat_48 bv6_toNat_56 bv6_toNat_60 bv6_toNat_62 bv6_toNat_63)

-- ============================================================================
-- Atomic `(k : Word) <<< 3` evaluations
-- (k ∈ {0..4} is the range actually used by DivMod u-base offsets.)
-- ============================================================================


-- @@ L110-110 verbatim
@[divmod_addr, grind =] 
-- @@ L110-110 verbatim
theorem word_shl3_0 : (0 : Word) <<< 3 = (0  : Word) := by decide

-- @@ L111-111 verbatim
@[divmod_addr, grind =] 
-- @@ L111-111 verbatim
theorem word_shl3_1 : (1 : Word) <<< 3 = (8  : Word) := by decide

-- @@ L112-112 verbatim
@[divmod_addr, grind =] 
-- @@ L112-112 verbatim
theorem word_shl3_2 : (2 : Word) <<< 3 = (16 : Word) := by decide

-- @@ L113-113 verbatim
@[divmod_addr, grind =] 
-- @@ L113-113 verbatim
theorem word_shl3_3 : (3 : Word) <<< 3 = (24 : Word) := by decide

-- @@ L114-114 verbatim
@[divmod_addr, grind =] 
-- @@ L114-119 verbatim
theorem word_shl3_4 : (4 : Word) <<< 3 = (32 : Word) := by decide

-- ============================================================================
-- Algebraic identities for Word (needed when simp evaluates signExtend12
-- to a concrete literal, leaving `0 + literal` behind).
-- ============================================================================


-- @@ L121-121 verbatim
@[divmod_addr, grind =] 
-- @@ L121-128 verbatim
theorem word_zero_add {x : Word} : (0 : Word) + x = x := BitVec.zero_add x

-- ============================================================================
-- Loop-counter positivity: after `ADDI j j -1` (ie. `j + signExtend12 4095`),
-- `j - 1 ≥ 0` for `j ∈ {1, 2, 3}`. Used by the `hj_pos` hypotheses in
-- LoopIterN1/{Max,MaxBeq,Call,CallBeq} and LoopIterN{2,3} to discharge the
-- BLT-not-taken side condition (the 4-bit signed encoding of j − 1).
-- ============================================================================


-- @@ L130-130 verbatim
@[divmod_addr, grind =] 
-- @@ L130-131 verbatim
theorem slt_jpos_1 :
    BitVec.slt ((1 : Word) + signExtend12 4095) 0 = false := by decide

-- @@ L132-132 verbatim
@[divmod_addr, grind =] 
-- @@ L132-133 verbatim
theorem slt_jpos_2 :
    BitVec.slt ((2 : Word) + signExtend12 4095) 0 = false := by decide

-- @@ L134-134 verbatim
@[divmod_addr, grind =] 
-- @@ L134-141 verbatim
theorem slt_jpos_3 :
    BitVec.slt ((3 : Word) + signExtend12 4095) 0 = false := by decide

-- ============================================================================
-- Concrete value of j − 1 after `ADDI j j -1` (i.e. `j + signExtend12 4095`)
-- for j ∈ {1, 2, 3}. Used by `hj' : (j : Word) + signExtend12 4095 = (j-1)`
-- sites in LoopUnified / LoopCompose files.
-- ============================================================================


-- @@ L143-143 verbatim
@[divmod_addr, grind =] 
-- @@ L143-144 verbatim
theorem jpred_1 :
    (1 : Word) + signExtend12 4095 = (0 : Word) := by decide

-- @@ L145-145 verbatim
@[divmod_addr, grind =] 
-- @@ L145-146 verbatim
theorem jpred_2 :
    (2 : Word) + signExtend12 4095 = (1 : Word) := by decide

-- @@ L147-147 verbatim
@[divmod_addr, grind =] 
-- @@ L147-157 verbatim
theorem jpred_3 :
    (3 : Word) + signExtend12 4095 = (2 : Word) := by decide

-- ============================================================================
-- `divmod_addr` tactic
--
-- Primary: `grind` (sees all @[grind =]-registered atomic facts).
-- Fallback: `simp only [divmod_addr]; bv_omega` (matches hand-written shape;
-- tiny proof term). The fallback covers edge cases where grind's closure
-- doesn't fully land.
-- ============================================================================


-- @@ L159-165 verbatim
/-- Close a DivMod address-arithmetic equality. Tries `grind` first (fastest,
    most resilient — picks up any `@[grind =]` fact in `AddrNorm`), then falls
    back to `simp only [divmod_addr]; bv_omega` for edge shapes. -/
macro "divmod_addr" : tactic =>
  `(tactic| first
    | grind
    | (simp only [divmod_addr]; bv_omega))


-- @@ L167-167 verbatim
end EvmAsm.Evm64.DivMod.AddrNorm
