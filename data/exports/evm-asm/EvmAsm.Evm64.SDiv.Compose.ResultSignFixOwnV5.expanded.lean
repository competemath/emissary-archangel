/-
  EvmAsm.Evm64.SDiv.Compose.ResultSignFixOwnV5

  v5 SDIV result-sign-fix specs that progressively consume owned registers
  (`x10`, `x7`, `x11`), over `sdivCodeV5`.  Verbatim mirrors of the `sdivCodeV4`
  wrappers in `ResultSignFixOwn.lean`, chaining the v5 leaf
  `resultSignFix_spec_in_sdivCodeV5` (BaseResultSignFixBlockSpecV5).  The
  pre/post assertions are code-agnostic; only the code surface and the recursive
  dependency change v4 → v5.
-/

module

public import EvmAsm.Evm64.SDiv.Compose.ResultSignFixOwn
public import EvmAsm.Evm64.SDiv.Compose.BaseResultSignFixBlockSpecV5


-- @@ L17-17 verbatim
public section


-- @@ L19-19 verbatim
namespace EvmAsm.Evm64.SDiv.Compose


-- @@ L21-21 verbatim
open EvmAsm.Rv64


-- @@ L23-39 verbatim
/-- v5 SDIV result sign-fix spec that consumes owned `x10`. -/
theorem resultSignFix_regOwn_x10_spec_in_sdivCodeV5
    (sp sign valueOld carryOld limb0 limb1 limb2 limb3 : Word) (base : Word) :
    EvmAsm.Rv64.cpsTripleWithin 21 (base + resultSignFixOff)
      ((base + resultSignFixOff) + 84) (sdivCodeV5 base)
      (resultSignFixPreOwnX10 sp sign valueOld carryOld limb0 limb1 limb2 limb3)
      (resultSignFixPost sp sign limb0 limb1 limb2 limb3) := by
  rw [resultSignFixPreOwnX10_unfold]
  apply EvmAsm.Rv64.cpsTripleWithin_of_forall_regIs_to_regOwn
  intro maskOld
  exact EvmAsm.Rv64.cpsTripleWithin_weaken
    (fun _ hp => by
      rw [resultSignFixPre_unfold]
      xperm_hyp hp)
    (fun _ hq => hq)
    (resultSignFix_spec_in_sdivCodeV5 sp sign maskOld valueOld carryOld
      limb0 limb1 limb2 limb3 base)


-- @@ L41-57 verbatim
/-- v5 SDIV result sign-fix spec that consumes owned `x10` and `x7`. -/
theorem resultSignFix_regOwn_x10_x7_spec_in_sdivCodeV5
    (sp sign carryOld limb0 limb1 limb2 limb3 : Word) (base : Word) :
    EvmAsm.Rv64.cpsTripleWithin 21 (base + resultSignFixOff)
      ((base + resultSignFixOff) + 84) (sdivCodeV5 base)
      (resultSignFixPreOwnX10X7 sp sign carryOld limb0 limb1 limb2 limb3)
      (resultSignFixPost sp sign limb0 limb1 limb2 limb3) := by
  rw [resultSignFixPreOwnX10X7_unfold]
  apply EvmAsm.Rv64.cpsTripleWithin_of_forall_regIs_to_regOwn
  intro valueOld
  exact EvmAsm.Rv64.cpsTripleWithin_weaken
    (fun _ hp => by
      rw [resultSignFixPreOwnX10_unfold]
      xperm_hyp hp)
    (fun _ hq => hq)
    (resultSignFix_regOwn_x10_spec_in_sdivCodeV5 sp sign valueOld carryOld
      limb0 limb1 limb2 limb3 base)


-- @@ L59-75 verbatim
/-- v5 SDIV result sign-fix spec that consumes owned `x10`, `x7`, and `x11`. -/
theorem resultSignFix_regOwn_scratch_spec_in_sdivCodeV5
    (sp sign limb0 limb1 limb2 limb3 : Word) (base : Word) :
    EvmAsm.Rv64.cpsTripleWithin 21 (base + resultSignFixOff)
      ((base + resultSignFixOff) + 84) (sdivCodeV5 base)
      (resultSignFixPreOwnScratch sp sign limb0 limb1 limb2 limb3)
      (resultSignFixPost sp sign limb0 limb1 limb2 limb3) := by
  rw [resultSignFixPreOwnScratch_unfold]
  apply EvmAsm.Rv64.cpsTripleWithin_of_forall_regIs_to_regOwn
  intro carryOld
  exact EvmAsm.Rv64.cpsTripleWithin_weaken
    (fun _ hp => by
      rw [resultSignFixPreOwnX10X7_unfold]
      xperm_hyp hp)
    (fun _ hq => hq)
    (resultSignFix_regOwn_x10_x7_spec_in_sdivCodeV5 sp sign carryOld
      limb0 limb1 limb2 limb3 base)


-- @@ L77-77 verbatim
end EvmAsm.Evm64.SDiv.Compose
