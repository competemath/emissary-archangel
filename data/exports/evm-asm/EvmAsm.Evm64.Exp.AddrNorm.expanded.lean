/-
  EvmAsm.Evm64.Exp.AddrNorm

  Address-normalization simp set for EXP composition proofs.

  Skeleton placeholder (GH #92, beads slice evm-asm-cf2c). The
  `@[exp_addr, grind =]`-tagged atomic facts will be added once the
  Compose layer (Exp/Compose/Loop.lean) starts emitting concrete address
  arithmetic. For now this file just imports the shared `Rv64.AddrNorm`
  base and the attribute declaration so downstream files can already
  open the namespace.
-/

module

public import EvmAsm.Rv64.AddrNorm
public import EvmAsm.Rv64.SignExtendSimproc
public import EvmAsm.Rv64.BitAux
public import EvmAsm.Evm64.Exp.AddrNormAttr
public import EvmAsm.Evm64.Exp.Program
meta import EvmAsm.Rv64.AddrNorm
meta import EvmAsm.Rv64.SignExtendSimproc
meta import EvmAsm.Rv64.BitAux
meta import EvmAsm.Evm64.Exp.AddrNormAttr
meta import EvmAsm.Evm64.Exp.Program


-- @@ L27-27 verbatim
public section


-- @@ L29-29 verbatim
namespace EvmAsm.Evm64.Exp.AddrNorm


-- @@ L31-35 verbatim
/-- Kernel-checkable closer for the concrete address-arithmetic facts in this
    file: delegates to the shared `signext` tactic, which evaluates concrete
    `signExtend12/13/21` offsets via the `reduceSignExtend*` simprocs and
    closes the residual linear `BitVec` arithmetic with `bv_omega`. -/
local macro "addrclose" : tactic => `(tactic| signext)


-- @@ L37-42 verbatim
/-- Bit-0 parity helper: if `base` is 2-byte aligned (`base &&& 1 = 0`) and `K`
    has a clear bit 0, then `base + K` is still aligned. Kernel-checkable
    replacement for `bv_decide` on the `(base + K) &&& 1 = 0` mask facts. -/
private theorem addrAligned {base K : Word} (hbase : base &&& 1 = 0)
    (hK : K.getLsbD 0 = false) : (base + K) &&& 1 = 0 :=
  EvmAsm.Rv64.BitAux.word_add_even_and_one hbase hK


-- @@ L44-44 verbatim
@[exp_addr, grind =] 
-- @@ L44-45 verbatim
theorem exp_se13_108 :
    EvmAsm.Rv64.signExtend13 (108 : BitVec 13) = (108 : Word) := by decide


-- @@ L47-47 verbatim
@[exp_addr, grind =] 
-- @@ L47-48 verbatim
theorem exp_se13_neg228 :
    EvmAsm.Rv64.signExtend13 ((-228 : BitVec 13)) = (18446744073709551388 : Word) := by decide


-- @@ L50-50 verbatim
@[exp_addr, grind =] 
-- @@ L50-51 verbatim
theorem exp_se12_neg64 :
    EvmAsm.Rv64.signExtend12 ((-64 : BitVec 12)) = (18446744073709551552 : Word) := by decide


-- @@ L53-53 verbatim
@[exp_addr, grind =] 
-- @@ L53-54 verbatim
theorem exp_se12_neg56 :
    EvmAsm.Rv64.signExtend12 ((-56 : BitVec 12)) = (18446744073709551560 : Word) := by decide


-- @@ L56-56 verbatim
@[exp_addr, grind =] 
-- @@ L56-57 verbatim
theorem exp_se12_neg48 :
    EvmAsm.Rv64.signExtend12 ((-48 : BitVec 12)) = (18446744073709551568 : Word) := by decide


-- @@ L59-59 verbatim
@[exp_addr, grind =] 
-- @@ L59-60 verbatim
theorem exp_se12_neg40 :
    EvmAsm.Rv64.signExtend12 ((-40 : BitVec 12)) = (18446744073709551576 : Word) := by decide


-- @@ L62-62 verbatim
@[exp_addr, grind =] 
-- @@ L62-63 verbatim
theorem exp_se12_neg32 :
    EvmAsm.Rv64.signExtend12 ((-32 : BitVec 12)) = (18446744073709551584 : Word) := by decide


-- @@ L65-65 verbatim
@[exp_addr, grind =] 
-- @@ L65-66 verbatim
theorem exp_se12_256 :
    EvmAsm.Rv64.signExtend12 (256 : BitVec 12) = (256 : Word) := by decide


-- @@ L68-84 verbatim
attribute [exp_addr]
  EvmAsm.Rv64.signExtend12_0 EvmAsm.Rv64.signExtend12_1
  EvmAsm.Rv64.signExtend12_8 EvmAsm.Rv64.signExtend12_16
  EvmAsm.Rv64.signExtend12_24 EvmAsm.Rv64.signExtend12_32
  EvmAsm.Rv64.signExtend12_40 EvmAsm.Rv64.signExtend12_48
  EvmAsm.Rv64.signExtend12_56 EvmAsm.Rv64.signExtend12_64
  EvmAsm.Rv64.signExtend12_neg16
  EvmAsm.Rv64.signExtend12_4095 EvmAsm.Rv64.signExtend12_4088
  EvmAsm.Rv64.signExtend12_4080 EvmAsm.Rv64.signExtend12_4072
  EvmAsm.Rv64.signExtend12_4064 EvmAsm.Rv64.signExtend12_4056
  EvmAsm.Rv64.signExtend12_4048 EvmAsm.Rv64.signExtend12_4040
  EvmAsm.Rv64.signExtend12_4032 EvmAsm.Rv64.signExtend12_4024
  EvmAsm.Rv64.signExtend12_4016 EvmAsm.Rv64.signExtend12_4008
  EvmAsm.Rv64.signExtend12_4000 EvmAsm.Rv64.signExtend12_3992
  EvmAsm.Rv64.signExtend12_3984 EvmAsm.Rv64.signExtend12_3976
  EvmAsm.Rv64.signExtend12_3968 EvmAsm.Rv64.signExtend12_3960
  EvmAsm.Rv64.signExtend12_3952 EvmAsm.Rv64.signExtend12_3944


-- @@ L86-86 verbatim
@[exp_addr, grind =] 
-- @@ L86-88 verbatim
theorem expAddr0 (addr : Word) :
    (addr + EvmAsm.Rv64.signExtend12 0#12 : Word) = addr := by
  addrclose


-- @@ L90-90 verbatim
@[exp_addr, grind =] 
-- @@ L90-92 verbatim
theorem expAddr8 (addr : Word) :
    (addr + EvmAsm.Rv64.signExtend12 8#12 : Word) = addr + 8#64 := by
  addrclose


-- @@ L94-94 verbatim
@[exp_addr, grind =] 
-- @@ L94-96 verbatim
theorem expAddr16 (addr : Word) :
    (addr + EvmAsm.Rv64.signExtend12 16#12 : Word) = addr + 16#64 := by
  addrclose


-- @@ L98-98 verbatim
@[exp_addr, grind =] 
-- @@ L98-100 verbatim
theorem expAddr24 (addr : Word) :
    (addr + EvmAsm.Rv64.signExtend12 24#12 : Word) = addr + 24#64 := by
  addrclose


-- @@ L102-102 verbatim
@[exp_addr, grind =] 
-- @@ L102-104 verbatim
theorem expAddr32 (addr : Word) :
    (addr + EvmAsm.Rv64.signExtend12 32#12 : Word) = addr + 32#64 := by
  addrclose


-- @@ L106-106 verbatim
@[exp_addr, grind =] 
-- @@ L106-108 verbatim
theorem expAddr40 (addr : Word) :
    (addr + EvmAsm.Rv64.signExtend12 40#12 : Word) = addr + 40#64 := by
  addrclose


-- @@ L110-110 verbatim
@[exp_addr, grind =] 
-- @@ L110-112 verbatim
theorem expAddr48 (addr : Word) :
    (addr + EvmAsm.Rv64.signExtend12 48#12 : Word) = addr + 48#64 := by
  addrclose


-- @@ L114-114 verbatim
@[exp_addr, grind =] 
-- @@ L114-116 verbatim
theorem expAddr56 (addr : Word) :
    (addr + EvmAsm.Rv64.signExtend12 56#12 : Word) = addr + 56#64 := by
  addrclose


-- @@ L118-118 verbatim
@[exp_addr, grind =] 
-- @@ L118-120 verbatim
theorem expAdd32Add8 (addr : Word) :
    (addr + 32#64 + 8 : Word) = addr + 40#64 := by
  addrclose


-- @@ L122-122 verbatim
@[exp_addr, grind =] 
-- @@ L122-124 verbatim
theorem expAdd32Add16 (addr : Word) :
    (addr + 32#64 + 16 : Word) = addr + 48#64 := by
  addrclose


-- @@ L126-126 verbatim
@[exp_addr, grind =] 
-- @@ L126-128 verbatim
theorem expAdd32Add24 (addr : Word) :
    (addr + 32#64 + 24 : Word) = addr + 56#64 := by
  addrclose


-- @@ L130-130 verbatim
@[exp_addr, grind =] 
-- @@ L130-132 verbatim
theorem expFullLoopCondMulCallAddr (base : Word) :
    (base + 148 : Word) = base + 144 + 4 := by
  addrclose


-- @@ L134-134 verbatim
@[exp_addr, grind =] 
-- @@ L134-136 verbatim
theorem expSavedBitCondMulTakenAddr (base : Word) :
    (base + 152 : Word) = base + 148 + 4 := by
  addrclose


-- @@ L138-138 verbatim
@[exp_addr, grind =] 
-- @@ L138-140 verbatim
theorem expSavedBitTwoMulCondMulTakenAddr (base : Word) :
    (base + 152 : Word) = (base + 28) + 120 + 4 := by
  addrclose


-- @@ L142-142 verbatim
@[exp_addr, grind =] 
-- @@ L142-144 verbatim
theorem expTwoMulSkipLoopBackNextPc (base : Word) :
    ((base + 256 : Word) + 8) = base + 264 := by
  addrclose


-- @@ L146-146 verbatim
@[exp_addr, grind =] 
-- @@ L146-148 verbatim
theorem expTwoMulCondMulCallExitPc (base : Word) :
    ((base + 152 : Word) + 104) = base + 256 := by
  addrclose


-- @@ L150-150 verbatim
@[exp_addr, grind =] 
-- @@ L150-152 verbatim
theorem expLoopBackNextPc (base : Word) :
    ((base + 24 : Word) + 8) = base + 32 := by
  addrclose


-- @@ L154-154 verbatim
@[exp_addr, grind =] 
-- @@ L154-156 verbatim
theorem expLoopSquareReturnPc (base : Word) :
    ((base + 12 : Word) + 4) = base + 16 := by
  addrclose


-- @@ L158-158 verbatim
@[exp_addr, grind =] 
-- @@ L158-160 verbatim
theorem expLoopCondMulReturnPc (base : Word) :
    ((base + 16 : Word) + 8) = base + 24 := by
  addrclose


-- @@ L162-162 verbatim
@[exp_addr, grind =] 
-- @@ L162-164 verbatim
theorem expSavedBitSquaringPrefixExitPc (base : Word) :
    ((base + 44 : Word) + 104) = base + 148 := by
  addrclose


-- @@ L166-166 verbatim
@[exp_addr, grind =] 
-- @@ L166-168 verbatim
theorem expSavedBitBitTestNextPc (base : Word) :
    ((base + 28 : Word) + 12) = base + 40 := by
  addrclose


-- @@ L170-170 verbatim
@[exp_addr, grind =] 
-- @@ L170-172 verbatim
theorem expSavedBitSaveNextPc (base : Word) :
    ((base + 40 : Word) + 4) = base + 44 := by
  addrclose


-- @@ L174-174 verbatim
@[exp_addr, grind =] 
-- @@ L174-176 verbatim
theorem expSavedBitCondMulBeqNextPc (base : Word) :
    ((base + 148 : Word) + 4) = base + 152 := by
  addrclose


-- @@ L178-178 verbatim
@[exp_addr, grind =] 
-- @@ L178-180 verbatim
theorem expSavedBitLoopBackNextPc (base : Word) :
    ((base + 256 : Word) + 8) = base + 264 := by
  addrclose


-- @@ L182-182 verbatim
@[exp_addr, grind =] 
-- @@ L182-184 verbatim
theorem expSavedBitSaveEntryAddr (base : Word) :
    (base + 40 : Word) = (base + 28) + 12 := by
  addrclose


-- @@ L186-186 verbatim
@[exp_addr, grind =] 
-- @@ L186-188 verbatim
theorem expSavedBitCondMulBeqEntryAddr (base : Word) :
    (base + 148 : Word) = (base + 28) + 120 := by
  addrclose


-- @@ L190-190 verbatim
@[exp_addr, grind =] 
-- @@ L190-192 verbatim
theorem expSavedBitSquaringEntryAddr (base : Word) :
    (base + 44 : Word) = (base + 28) + 16 := by
  addrclose


-- @@ L194-194 verbatim
@[exp_addr, grind =] 
-- @@ L194-196 verbatim
theorem expTopPointerAdvanceNextPc (base : Word) :
    ((base + 24 : Word) + 4) = base + 28 := by
  addrclose


-- @@ L198-198 verbatim
@[exp_addr, grind =] 
-- @@ L198-200 verbatim
theorem expTopPointerRestoreNextPc (base : Word) :
    ((base + 260 : Word) + 4) = base + 264 := by
  addrclose


-- @@ L202-202 verbatim
@[exp_addr, grind =] 
-- @@ L202-204 verbatim
theorem expTopEpilogueNextPc (base : Word) :
    ((base + 264 : Word) + 36) = base + 300 := by
  addrclose


-- @@ L206-206 verbatim
@[exp_addr, grind =] 
-- @@ L206-208 verbatim
theorem expTopSavedBitEpilogueEntryNextPc (base : Word) :
    ((base + 264 : Word) + 4) = base + 268 := by
  addrclose


-- @@ L210-210 verbatim
@[exp_addr, grind =] 
-- @@ L210-212 verbatim
theorem expTopSavedBitEpilogueNextPc (base : Word) :
    ((base + 268 : Word) + 36) = base + 304 := by
  addrclose


-- @@ L214-214 verbatim
@[exp_addr, grind =] 
-- @@ L214-216 verbatim
theorem expTopIterBitTestNextPc (base : Word) :
    ((base + 28 : Word) + 12) = base + 40 := by
  addrclose


-- @@ L218-218 verbatim
@[exp_addr, grind =] 
-- @@ L218-220 verbatim
theorem expTopSavedBitSaveNextPc (base : Word) :
    ((base + 40 : Word) + 4) = base + 44 := by
  addrclose


-- @@ L222-222 verbatim
@[exp_addr, grind =] 
-- @@ L222-224 verbatim
theorem expTopLoopBackNextPc (base : Word) :
    ((base + 252 : Word) + 8) = base + 260 := by
  addrclose


-- @@ L226-226 verbatim
@[exp_addr, grind =] 
-- @@ L226-228 verbatim
theorem expTopCondMulBeqNextPc (base : Word) :
    ((base + 144 : Word) + 4) = base + 148 := by
  addrclose


-- @@ L230-230 verbatim
@[exp_addr, grind =] 
-- @@ L230-232 verbatim
theorem expTopSavedBitCondMulBeqNextPc (base : Word) :
    ((base + 148 : Word) + 4) = base + 152 := by
  addrclose


-- @@ L234-234 verbatim
@[exp_addr, grind =] 
-- @@ L234-236 verbatim
theorem expTopCondMulMarshalPairNextPc (base : Word) :
    ((base + 148 : Word) + 64) = base + 212 := by
  addrclose


-- @@ L238-238 verbatim
@[exp_addr, grind =] 
-- @@ L238-240 verbatim
theorem expTopSquaringSquareReturnPc (base : Word) :
    ((base + 104 : Word) + 4) = base + 108 := by
  addrclose


-- @@ L242-242 verbatim
@[exp_addr, grind =] 
-- @@ L242-244 verbatim
theorem expTopCondMulSquareReturnPc (base : Word) :
    ((base + 212 : Word) + 4) = base + 216 := by
  addrclose


-- @@ L246-246 verbatim
@[exp_addr, grind =] 
-- @@ L246-248 verbatim
theorem expTopSquaringFactor1ExitPc (base : Word) :
    ((base + 40 : Word) + 32) = base + 72 := by
  addrclose


-- @@ L250-250 verbatim
@[exp_addr, grind =] 
-- @@ L250-252 verbatim
theorem expTopSquaringFactor2ExitPc (base : Word) :
    ((base + 72 : Word) + 32) = base + 104 := by
  addrclose


-- @@ L254-254 verbatim
@[exp_addr, grind =] 
-- @@ L254-256 verbatim
theorem expTopSquaringRestoreExitPc (base : Word) :
    ((base + 108 : Word) + 36) = base + 144 := by
  addrclose


-- @@ L258-258 verbatim
@[exp_addr, grind =] 
-- @@ L258-260 verbatim
theorem expTopCondMulFactor1ExitPc (base : Word) :
    ((base + 148 : Word) + 32) = base + 180 := by
  addrclose


-- @@ L262-262 verbatim
@[exp_addr, grind =] 
-- @@ L262-264 verbatim
theorem expTopCondMulFactor2ExitPc (base : Word) :
    ((base + 180 : Word) + 32) = base + 212 := by
  addrclose


-- @@ L266-266 verbatim
@[exp_addr, grind =] 
-- @@ L266-268 verbatim
theorem expTopCondMulRestoreExitPc (base : Word) :
    ((base + 216 : Word) + 36) = base + 252 := by
  addrclose


-- @@ L270-270 verbatim
@[exp_addr, grind =] 
-- @@ L270-272 verbatim
theorem expTopSquaringMarshalPairReturnPc (base : Word) :
    ((base + 40 : Word) + 68) = base + 108 := by
  addrclose


-- @@ L274-274 verbatim
@[exp_addr, grind =] 
-- @@ L274-276 verbatim
theorem expTopSquaringMarshalPairTargetPc (base : Word) :
    ((base + 40 : Word) + 64) = base + 104 := by
  addrclose


-- @@ L278-278 verbatim
@[exp_addr, grind =] 
-- @@ L278-280 verbatim
theorem expTopIterSquaringAddr (base : Word) :
    (base + 40 : Word) = base + 28 + 12 := by
  addrclose


-- @@ L282-282 verbatim
@[exp_addr, grind =] 
-- @@ L282-284 verbatim
theorem expTopIterCondMulAddr (base : Word) :
    (base + 144 : Word) = base + 28 + 116 := by
  addrclose


-- @@ L286-286 verbatim
@[exp_addr, grind =] 
-- @@ L286-288 verbatim
theorem expTopIterSavedBitSquaringAddr (base : Word) :
    (base + 44 : Word) = base + 28 + 16 := by
  addrclose


-- @@ L290-290 verbatim
@[exp_addr, grind =] 
-- @@ L290-292 verbatim
theorem expTopIterSavedBitCondMulAddr (base : Word) :
    (base + 148 : Word) = base + 28 + 120 := by
  addrclose


-- @@ L294-294 verbatim
@[exp_addr, grind =] 
-- @@ L294-296 verbatim
theorem expTopIterSavedBitLoopBackAddr (base : Word) :
    (base + 256 : Word) = base + 28 + 228 := by
  addrclose


-- @@ L298-298 verbatim
@[exp_addr, grind =] 
-- @@ L298-300 verbatim
theorem expTopIterLoopBackAddr (base : Word) :
    (base + 252 : Word) = base + 28 + 224 := by
  addrclose


-- @@ L302-302 verbatim
@[exp_addr, grind =] 
-- @@ L302-304 verbatim
theorem expTopSquaringFactor2Addr (base : Word) :
    (base + 72 : Word) = base + 40 + 32 := by
  addrclose


-- @@ L306-306 verbatim
@[exp_addr, grind =] 
-- @@ L306-308 verbatim
theorem expTopSquaringSquareAddr (base : Word) :
    (base + 104 : Word) = base + 40 + 64 := by
  addrclose


-- @@ L310-310 verbatim
@[exp_addr, grind =] 
-- @@ L310-312 verbatim
theorem expTopSquaringRestoreAddr (base : Word) :
    (base + 108 : Word) = base + 40 + 68 := by
  addrclose


-- @@ L314-314 verbatim
@[exp_addr, grind =] 
-- @@ L314-316 verbatim
theorem expTopCondMulCallStartAddr (base : Word) :
    (base + 148 : Word) = base + 144 + 4 := by
  addrclose


-- @@ L318-318 verbatim
@[exp_addr, grind =] 
-- @@ L318-320 verbatim
theorem expTopCondMulFactor2Addr (base : Word) :
    (base + 180 : Word) = base + 148 + 32 := by
  addrclose


-- @@ L322-322 verbatim
@[exp_addr, grind =] 
-- @@ L322-324 verbatim
theorem expTopCondMulFactor2Addr_symm (base : Word) :
    ((base + 148 : Word) + 32) = base + 180 := by
  addrclose


-- @@ L326-326 verbatim
@[exp_addr, grind =] 
-- @@ L326-328 verbatim
theorem expTopCondMulSquareAddr (base : Word) :
    (base + 212 : Word) = base + 148 + 64 := by
  addrclose


-- @@ L330-330 verbatim
@[exp_addr, grind =] 
-- @@ L330-332 verbatim
theorem expTopCondMulRestoreAddr (base : Word) :
    (base + 216 : Word) = base + 148 + 68 := by
  addrclose


-- @@ L334-334 verbatim
@[exp_addr, grind =] 
-- @@ L334-336 verbatim
theorem expBoundaryEpilogueExitPc (base : Word) :
    (base + 24 : Word) + 36 = base + 60 := by
  addrclose


-- @@ L338-338 verbatim
@[exp_addr, grind =] 
-- @@ L338-342 verbatim
theorem expBoundaryProgramEpilogueAddr (base : Word) :
    (base + 24 : Word) =
      base + BitVec.ofNat 64 (4 * EvmAsm.Evm64.exp_prologue.length) := by
  rw [EvmAsm.Evm64.exp_prologue_length]
  addrclose


-- @@ L344-344 verbatim
@[exp_addr, grind =] 
-- @@ L344-346 verbatim
theorem expTopPointerAdvanceProgramAddr (base : Word) :
    (base + 24 : Word) = base + BitVec.ofNat 64 (4 * 6) := by
  addrclose


-- @@ L348-348 verbatim
@[exp_addr, grind =] 
-- @@ L348-350 verbatim
theorem expTopIterBodyProgramAddr (base : Word) :
    (base + 28 : Word) = base + BitVec.ofNat 64 (4 * 7) := by
  addrclose


-- @@ L352-352 verbatim
@[exp_addr, grind =] 
-- @@ L352-354 verbatim
theorem expTopPointerRestoreProgramAddr (base : Word) :
    (base + 260 : Word) = base + BitVec.ofNat 64 (4 * 65) := by
  addrclose


-- @@ L356-356 verbatim
@[exp_addr, grind =] 
-- @@ L356-358 verbatim
theorem expTopEpilogueProgramAddr (base : Word) :
    (base + 264 : Word) = base + BitVec.ofNat 64 (4 * 66) := by
  addrclose


-- @@ L360-360 verbatim
@[exp_addr, grind =] 
-- @@ L360-362 verbatim
theorem expLoopSquareProgramAddr (base : Word) :
    (base + 12 : Word) = base + BitVec.ofNat 64 (4 * 3) := by
  addrclose


-- @@ L364-364 verbatim
@[exp_addr, grind =] 
-- @@ L364-366 verbatim
theorem expLoopCondMulProgramAddr (base : Word) :
    (base + 16 : Word) = base + BitVec.ofNat 64 (4 * 4) := by
  addrclose


-- @@ L368-368 verbatim
@[exp_addr, grind =] 
-- @@ L368-370 verbatim
theorem expLoopBackProgramAddr (base : Word) :
    (base + 24 : Word) = base + BitVec.ofNat 64 (4 * 6) := by
  addrclose


-- @@ L372-376 verbatim
theorem expIterBodyCode_bit_test_square_disjoint_addr
    (base : Word) {k1 k2 : Nat} (hk1 : k1 < 3) (hk2 : k2 < 1) :
    base + BitVec.ofNat 64 (4 * k1) ≠
      base + 12 + BitVec.ofNat 64 (4 * k2) := by
  bv_omega


-- @@ L378-382 verbatim
theorem expIterBodyCode_bit_test_cond_mul_disjoint_addr
    (base : Word) {k1 k2 : Nat} (hk1 : k1 < 3) (hk2 : k2 < 2) :
    base + BitVec.ofNat 64 (4 * k1) ≠
      base + 16 + BitVec.ofNat 64 (4 * k2) := by
  bv_omega


-- @@ L384-388 verbatim
theorem expIterBodyCode_square_cond_mul_disjoint_addr
    (base : Word) {k1 k2 : Nat} (hk1 : k1 < 1) (hk2 : k2 < 2) :
    base + 12 + BitVec.ofNat 64 (4 * k1) ≠
      base + 16 + BitVec.ofNat 64 (4 * k2) := by
  bv_omega


-- @@ L390-394 verbatim
theorem expOneIterCode_bit_test_loop_back_disjoint_addr
    (base : Word) {k1 k2 : Nat} (hk1 : k1 < 3) (hk2 : k2 < 2) :
    base + BitVec.ofNat 64 (4 * k1) ≠
      base + 24 + BitVec.ofNat 64 (4 * k2) := by
  bv_omega


-- @@ L396-400 verbatim
theorem expOneIterCode_square_loop_back_disjoint_addr
    (base : Word) {k1 k2 : Nat} (hk1 : k1 < 1) (hk2 : k2 < 2) :
    base + 12 + BitVec.ofNat 64 (4 * k1) ≠
      base + 24 + BitVec.ofNat 64 (4 * k2) := by
  bv_omega


-- @@ L402-406 verbatim
theorem expOneIterCode_cond_mul_loop_back_disjoint_addr
    (base : Word) {k1 k2 : Nat} (hk1 : k1 < 2) (hk2 : k2 < 2) :
    base + 16 + BitVec.ofNat 64 (4 * k1) ≠
      base + 24 + BitVec.ofNat 64 (4 * k2) := by
  bv_omega


-- @@ L408-412 verbatim
theorem expBoundaryCode_prologue_epilogue_disjoint_addr
    (base : Word) {k1 k2 : Nat} (hk1 : k1 < 6) (hk2 : k2 < 9) :
    base + BitVec.ofNat 64 (4 * k1) ≠
      base + 24 + BitVec.ofNat 64 (4 * k2) := by
  bv_omega


-- @@ L414-418 verbatim
theorem evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode_disjoint_addr
    (base : Word) {k1 k2 : Nat} (hk1 : k1 < 76) (hk2 : k2 < 64) :
    base + BitVec.ofNat 64 (4 * k1) ≠
      base + 304 + BitVec.ofNat 64 (4 * k2) := by
  bv_omega


-- @@ L420-424 verbatim
theorem expCallBlock_factor1_factor2_disjoint_addr
    (base : Word) {k1 k2 : Nat} (hk1 : k1 < 8) (hk2 : k2 < 8) :
    base + BitVec.ofNat 64 (4 * k1) ≠
      base + 32 + BitVec.ofNat 64 (4 * k2) := by
  bv_omega


-- @@ L426-430 verbatim
theorem expCallBlock_factor1_square_disjoint_addr
    (base : Word) {k1 k2 : Nat} (hk1 : k1 < 8) (hk2 : k2 < 1) :
    base + BitVec.ofNat 64 (4 * k1) ≠
      base + 64 + BitVec.ofNat 64 (4 * k2) := by
  bv_omega


-- @@ L432-436 verbatim
theorem expCallBlock_factor2_square_disjoint_addr
    (base : Word) {k1 k2 : Nat} (hk1 : k1 < 8) (hk2 : k2 < 1) :
    base + 32 + BitVec.ofNat 64 (4 * k1) ≠
      base + 64 + BitVec.ofNat 64 (4 * k2) := by
  bv_omega


-- @@ L438-442 verbatim
theorem expCallBlock_factor1_restore_disjoint_addr
    (base : Word) {k1 k2 : Nat} (hk1 : k1 < 8) (hk2 : k2 < 9) :
    base + BitVec.ofNat 64 (4 * k1) ≠
      base + 68 + BitVec.ofNat 64 (4 * k2) := by
  bv_omega


-- @@ L444-448 verbatim
theorem expCallBlock_factor2_restore_disjoint_addr
    (base : Word) {k1 k2 : Nat} (hk1 : k1 < 8) (hk2 : k2 < 9) :
    base + 32 + BitVec.ofNat 64 (4 * k1) ≠
      base + 68 + BitVec.ofNat 64 (4 * k2) := by
  bv_omega


-- @@ L450-454 verbatim
theorem expCallBlock_square_restore_disjoint_addr
    (base : Word) {k1 k2 : Nat} (hk1 : k1 < 1) (hk2 : k2 < 9) :
    base + 64 + BitVec.ofNat 64 (4 * k1) ≠
      base + 68 + BitVec.ofNat 64 (4 * k2) := by
  bv_omega


-- @@ L456-458 verbatim
theorem expCallBlock_factor2_end_addr (base : Word) :
    (base + 32 : Word) + BitVec.ofNat 64 (4 * 8) = base + 64 := by
  bv_omega


-- @@ L460-460 verbatim
@[exp_addr, grind =] 
-- @@ L460-462 verbatim
theorem expMarshalPairExitPc (base : Word) :
    ((base + 32 : Word) + 32) = base + 64 := by
  addrclose


-- @@ L464-466 verbatim
theorem expCallBlock_square_end_addr (base : Word) :
    (base + 64 : Word) + BitVec.ofNat 64 (4 * 1) = base + 68 := by
  bv_omega


-- @@ L468-468 verbatim
@[exp_addr, grind =] 
-- @@ L468-470 verbatim
theorem expSavedBitCondMulProgramAddr (base : Word) :
    (base + 120 : Word) = base + BitVec.ofNat 64 (4 * 30) := by
  addrclose


-- @@ L472-472 verbatim
@[exp_addr, grind =] 
-- @@ L472-474 verbatim
theorem expSavedBitLoopBackProgramAddr (base : Word) :
    (base + 228 : Word) = base + BitVec.ofNat 64 (4 * 57) := by
  addrclose


-- @@ L476-476 verbatim
@[exp_addr, grind =] 
-- @@ L476-478 verbatim
theorem expSavedBitEpilogueProgramAddr (base : Word) :
    (base + 268 : Word) = base + BitVec.ofNat 64 (4 * 67) := by
  addrclose


-- @@ L480-480 verbatim
@[exp_addr, grind =] 
-- @@ L480-482 verbatim
theorem expCallBlockRestoreExitPc (base : Word) :
    ((base + 68 : Word) + 36) = base + 104 := by
  addrclose


-- @@ L484-484 verbatim
@[exp_addr, grind =] 
-- @@ L484-486 verbatim
theorem expCondMulCallSkipCallProgramAddr (base : Word) :
    (base + 4 : Word) = base + BitVec.ofNat 64 (4 * 1) := by
  addrclose


-- @@ L488-488 verbatim
@[exp_addr, grind =] 
-- @@ L488-490 verbatim
theorem expSingleInstrNextPc (base : Word) :
    ((base + 4 : Word) + 4) = base + 8 := by
  addrclose


-- @@ L492-493 verbatim
theorem expBase_ne_add4 (base : Word) : base ≠ base + 4 := by
  bv_omega


-- @@ L495-495 verbatim
@[exp_addr, grind =] 
-- @@ L495-497 verbatim
theorem expSquaringCallFactor2ProgramAddr (base : Word) :
    (base + 32 : Word) = base + BitVec.ofNat 64 (4 * 8) := by
  addrclose


-- @@ L499-499 verbatim
@[exp_addr, grind =] 
-- @@ L499-501 verbatim
theorem expSquaringCallSquareProgramAddr (base : Word) :
    (base + 64 : Word) = base + BitVec.ofNat 64 (4 * 16) := by
  addrclose


-- @@ L503-503 verbatim
@[exp_addr, grind =] 
-- @@ L503-505 verbatim
theorem expSquaringCallRestoreProgramAddr (base : Word) :
    (base + 68 : Word) = base + BitVec.ofNat 64 (4 * 17) := by
  addrclose


-- @@ L507-507 verbatim
@[exp_addr, grind =] 
-- @@ L507-509 verbatim
theorem expFullIterCondMulProgramAddr (base : Word) :
    (base + 116 : Word) = base + BitVec.ofNat 64 (4 * 29) := by
  addrclose


-- @@ L511-511 verbatim
@[exp_addr, grind =] 
-- @@ L511-516 verbatim
theorem expFullIterLoopBackProgramAddr (base : Word) :
    (base + 224 : Word) = base + BitVec.ofNat 64 (4 * 56) := by
  addrclose

-- The variable-head LHS is deliberate: this is the `exp_addr` set's start-of-
-- program normalization anchor, so the (v4.31+) varHead lint is expected here.

-- @@ L517-520 verbatim
set_option warning.simp.varHead false in
@[exp_addr] theorem expProgramStartAddr (base : Word) :
    base = base + BitVec.ofNat 64 (4 * (0 : Nat)) := by
  addrclose


-- @@ L522-522 verbatim
@[exp_addr, grind =] 
-- @@ L522-524 verbatim
theorem expBaseAdd40Aligned
    (base : Word) (hbase : base &&& 1 = 0) :
    (base + 40 : Word) &&& 1 = 0 := addrAligned hbase (by decide)


-- @@ L526-526 verbatim
@[exp_addr, grind =] 
-- @@ L526-528 verbatim
theorem expBaseAdd44Aligned
    (base : Word) (hbase : base &&& 1 = 0) :
    (base + 44 : Word) &&& 1 = 0 := addrAligned hbase (by decide)


-- @@ L530-530 verbatim
@[exp_addr, grind =] 
-- @@ L530-532 verbatim
theorem expBaseAdd148Aligned
    (base : Word) (hbase : base &&& 1 = 0) :
    (base + 148 : Word) &&& 1 = 0 := addrAligned hbase (by decide)


-- @@ L534-534 verbatim
@[exp_addr, grind =] 
-- @@ L534-536 verbatim
theorem expBaseAdd152Aligned
    (base : Word) (hbase : base &&& 1 = 0) :
    (base + 152 : Word) &&& 1 = 0 := addrAligned hbase (by decide)


-- @@ L538-538 verbatim
end EvmAsm.Evm64.Exp.AddrNorm
