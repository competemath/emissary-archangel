/-
  EvmAsm.Evm64.SMod.Compose.AbsComponents

  Shared signed-absolute-value component abbreviations for SMOD mod-call
  handoff proofs.
-/

module

public import EvmAsm.Evm64.SMod.Compose.QuadMemBridges
public import EvmAsm.Evm64.SMod.Compose.Words


-- @@ L13-13 verbatim
public section


-- @@ L15-15 verbatim
namespace EvmAsm.Evm64.SMod.Compose


-- @@ L17-18 verbatim
abbrev smodAbsSign (top : Word) : Word :=
  top >>> (63 : BitVec 6).toNat


-- @@ L20-21 verbatim
abbrev smodAbsMask (top : Word) : Word :=
  (0 : Word) - smodAbsSign top


-- @@ L23-24 verbatim
abbrev smodAbsSum0 (limb0 top : Word) : Word :=
  (limb0 ^^^ smodAbsMask top) + smodAbsSign top


-- @@ L26-27 verbatim
abbrev smodAbsCarry0 (limb0 top : Word) : Word :=
  if BitVec.ult (smodAbsSum0 limb0 top) (smodAbsSign top) then (1 : Word) else 0


-- @@ L29-30 verbatim
abbrev smodAbsSum1 (limb0 limb1 top : Word) : Word :=
  (limb1 ^^^ smodAbsMask top) + smodAbsCarry0 limb0 top


-- @@ L32-36 verbatim
abbrev smodAbsCarry1 (limb0 limb1 top : Word) : Word :=
  if BitVec.ult (smodAbsSum1 limb0 limb1 top) (smodAbsCarry0 limb0 top) then
    (1 : Word)
  else
    0


-- @@ L38-39 verbatim
abbrev smodAbsSum2 (limb0 limb1 limb2 top : Word) : Word :=
  (limb2 ^^^ smodAbsMask top) + smodAbsCarry1 limb0 limb1 top


-- @@ L41-46 verbatim
abbrev smodAbsCarry2 (limb0 limb1 limb2 top : Word) : Word :=
  if BitVec.ult (smodAbsSum2 limb0 limb1 limb2 top)
      (smodAbsCarry1 limb0 limb1 top) then
    (1 : Word)
  else
    0


-- @@ L48-49 verbatim
abbrev smodAbsSum3 (limb0 limb1 limb2 top : Word) : Word :=
  (top ^^^ smodAbsMask top) + smodAbsCarry2 limb0 limb1 limb2 top


-- @@ L51-56 verbatim
abbrev smodAbsCarry3 (limb0 limb1 limb2 top : Word) : Word :=
  if BitVec.ult (smodAbsSum3 limb0 limb1 limb2 top)
      (smodAbsCarry2 limb0 limb1 limb2 top) then
    (1 : Word)
  else
    0


-- @@ L58-67 verbatim
theorem smodAbsDividendWord_eq_components
    (limb0 limb1 limb2 top : Word) :
    smodAbsDividendWord limb0 limb1 limb2 top =
      EvmWord.fromLimbs fun i : Fin 4 =>
        match i with
        | 0 => smodAbsSum0 limb0 top
        | 1 => smodAbsSum1 limb0 limb1 top
        | 2 => smodAbsSum2 limb0 limb1 limb2 top
        | 3 => smodAbsSum3 limb0 limb1 limb2 top := by
  rfl


-- @@ L69-78 verbatim
theorem smodAbsDivisorWord_eq_components
    (limb0 limb1 limb2 top : Word) :
    smodAbsDivisorWord limb0 limb1 limb2 top =
      EvmWord.fromLimbs fun i : Fin 4 =>
        match i with
        | 0 => smodAbsSum0 limb0 top
        | 1 => smodAbsSum1 limb0 limb1 top
        | 2 => smodAbsSum2 limb0 limb1 limb2 top
        | 3 => smodAbsSum3 limb0 limb1 limb2 top := by
  rfl


-- @@ L80-85 verbatim
theorem smodAbsDividendWord_getLimbN_0
    (limb0 limb1 limb2 top : Word) :
    (smodAbsDividendWord limb0 limb1 limb2 top).getLimbN 0 =
      smodAbsSum0 limb0 top := by
  rw [smodAbsDividendWord_eq_components, EvmWord.getLimbN_lt _ 0 (by decide)]
  exact EvmWord.getLimb_fromLimbs


-- @@ L87-92 verbatim
theorem smodAbsDividendWord_getLimbN_1
    (limb0 limb1 limb2 top : Word) :
    (smodAbsDividendWord limb0 limb1 limb2 top).getLimbN 1 =
      smodAbsSum1 limb0 limb1 top := by
  rw [smodAbsDividendWord_eq_components, EvmWord.getLimbN_lt _ 1 (by decide)]
  exact EvmWord.getLimb_fromLimbs


-- @@ L94-99 verbatim
theorem smodAbsDividendWord_getLimbN_2
    (limb0 limb1 limb2 top : Word) :
    (smodAbsDividendWord limb0 limb1 limb2 top).getLimbN 2 =
      smodAbsSum2 limb0 limb1 limb2 top := by
  rw [smodAbsDividendWord_eq_components, EvmWord.getLimbN_lt _ 2 (by decide)]
  exact EvmWord.getLimb_fromLimbs


-- @@ L101-106 verbatim
theorem smodAbsDividendWord_getLimbN_3
    (limb0 limb1 limb2 top : Word) :
    (smodAbsDividendWord limb0 limb1 limb2 top).getLimbN 3 =
      smodAbsSum3 limb0 limb1 limb2 top := by
  rw [smodAbsDividendWord_eq_components, EvmWord.getLimbN_lt _ 3 (by decide)]
  exact EvmWord.getLimb_fromLimbs


-- @@ L108-113 verbatim
theorem smodAbsDivisorWord_getLimbN_0
    (limb0 limb1 limb2 top : Word) :
    (smodAbsDivisorWord limb0 limb1 limb2 top).getLimbN 0 =
      smodAbsSum0 limb0 top := by
  rw [smodAbsDivisorWord_eq_components, EvmWord.getLimbN_lt _ 0 (by decide)]
  exact EvmWord.getLimb_fromLimbs


-- @@ L115-120 verbatim
theorem smodAbsDivisorWord_getLimbN_1
    (limb0 limb1 limb2 top : Word) :
    (smodAbsDivisorWord limb0 limb1 limb2 top).getLimbN 1 =
      smodAbsSum1 limb0 limb1 top := by
  rw [smodAbsDivisorWord_eq_components, EvmWord.getLimbN_lt _ 1 (by decide)]
  exact EvmWord.getLimb_fromLimbs


-- @@ L122-127 verbatim
theorem smodAbsDivisorWord_getLimbN_2
    (limb0 limb1 limb2 top : Word) :
    (smodAbsDivisorWord limb0 limb1 limb2 top).getLimbN 2 =
      smodAbsSum2 limb0 limb1 limb2 top := by
  rw [smodAbsDivisorWord_eq_components, EvmWord.getLimbN_lt _ 2 (by decide)]
  exact EvmWord.getLimb_fromLimbs


-- @@ L129-134 verbatim
theorem smodAbsDivisorWord_getLimbN_3
    (limb0 limb1 limb2 top : Word) :
    (smodAbsDivisorWord limb0 limb1 limb2 top).getLimbN 3 =
      smodAbsSum3 limb0 limb1 limb2 top := by
  rw [smodAbsDivisorWord_eq_components, EvmWord.getLimbN_lt _ 3 (by decide)]
  exact EvmWord.getLimb_fromLimbs


-- @@ L136-149 verbatim
theorem smodAbsDividendWord_evmWordIs_sp_components_smodOffsets
    (sp limb0 limb1 limb2 top : Word) :
    evmWordIs sp (smodAbsDividendWord limb0 limb1 limb2 top) =
      (((sp + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)) ↦ₘ smodAbsSum0 limb0 top) **
       ((sp + EvmAsm.Rv64.signExtend12 (8 : BitVec 12)) ↦ₘ
         smodAbsSum1 limb0 limb1 top) **
       ((sp + EvmAsm.Rv64.signExtend12 (16 : BitVec 12)) ↦ₘ
         smodAbsSum2 limb0 limb1 limb2 top) **
       ((sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_smodDividendTopLimbOff) ↦ₘ
         smodAbsSum3 limb0 limb1 limb2 top)) := by
  rw [smodAbsDividendWord_eq_components]
  exact (evmWordIs_eq_quadMem_smodDividend
    sp (smodAbsSum0 limb0 top) (smodAbsSum1 limb0 limb1 top)
    (smodAbsSum2 limb0 limb1 limb2 top) (smodAbsSum3 limb0 limb1 limb2 top)).symm


-- @@ L151-161 verbatim
open EvmAsm.Rv64 in
theorem smodAbsDividendWord_evmWordIs_sp_components_smodOffsets_right
    (sp limb0 limb1 limb2 top : Word) (Q : Assertion) :
    (((sp + signExtend12 (0 : BitVec 12)) ↦ₘ smodAbsSum0 limb0 top) **
     ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ smodAbsSum1 limb0 limb1 top) **
     ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ smodAbsSum2 limb0 limb1 limb2 top) **
     ((sp + signExtend12 EvmAsm.Evm64.evm_smodDividendTopLimbOff) ↦ₘ
       smodAbsSum3 limb0 limb1 limb2 top) ** Q) =
      (evmWordIs sp (smodAbsDividendWord limb0 limb1 limb2 top) ** Q) := by
  rw [smodAbsDividendWord_evmWordIs_sp_components_smodOffsets]
  rw [sepConj_assoc', sepConj_assoc', sepConj_assoc']


-- @@ L163-176 verbatim
theorem smodAbsDivisorWord_evmWordIs_sp32_components_smodOffsets
    (sp limb0 limb1 limb2 top : Word) :
    evmWordIs (sp + 32) (smodAbsDivisorWord limb0 limb1 limb2 top) =
      (((sp + EvmAsm.Rv64.signExtend12 (32 : BitVec 12)) ↦ₘ smodAbsSum0 limb0 top) **
       ((sp + EvmAsm.Rv64.signExtend12 (40 : BitVec 12)) ↦ₘ
         smodAbsSum1 limb0 limb1 top) **
       ((sp + EvmAsm.Rv64.signExtend12 (48 : BitVec 12)) ↦ₘ
         smodAbsSum2 limb0 limb1 limb2 top) **
       ((sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_smodDivisorTopLimbOff) ↦ₘ
         smodAbsSum3 limb0 limb1 limb2 top)) := by
  rw [smodAbsDivisorWord_eq_components]
  exact (evmWordIs_eq_quadMem_smodDivisor
    sp (smodAbsSum0 limb0 top) (smodAbsSum1 limb0 limb1 top)
    (smodAbsSum2 limb0 limb1 limb2 top) (smodAbsSum3 limb0 limb1 limb2 top)).symm


-- @@ L178-188 verbatim
open EvmAsm.Rv64 in
theorem smodAbsDivisorWord_evmWordIs_sp32_components_smodOffsets_right
    (sp limb0 limb1 limb2 top : Word) (Q : Assertion) :
    (((sp + signExtend12 (32 : BitVec 12)) ↦ₘ smodAbsSum0 limb0 top) **
     ((sp + signExtend12 (40 : BitVec 12)) ↦ₘ smodAbsSum1 limb0 limb1 top) **
     ((sp + signExtend12 (48 : BitVec 12)) ↦ₘ smodAbsSum2 limb0 limb1 limb2 top) **
     ((sp + signExtend12 EvmAsm.Evm64.evm_smodDivisorTopLimbOff) ↦ₘ
       smodAbsSum3 limb0 limb1 limb2 top) ** Q) =
      (evmWordIs (sp + 32) (smodAbsDivisorWord limb0 limb1 limb2 top) ** Q) := by
  rw [smodAbsDivisorWord_evmWordIs_sp32_components_smodOffsets]
  rw [sepConj_assoc', sepConj_assoc', sepConj_assoc']


-- @@ L190-190 verbatim
end EvmAsm.Evm64.SMod.Compose
