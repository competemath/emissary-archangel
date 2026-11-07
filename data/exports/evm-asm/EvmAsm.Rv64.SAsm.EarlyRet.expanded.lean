/-
  EvmAsm.Rv64.SAsm.EarlyRet

  Minimal return-terminating SAsm demo: a conditional branch to two tail blocks,
  each ending in a real `ret` (`JALR x0 x1 0`).  This is the small mechanism
  test for multi-exit return soundness; larger loop-shaped predicate routines
  can build on the same return-terminating theorem without changing the legacy
  single-exit `Fn.Spec` path.
-/

import EvmAsm.Rv64.SAsm.StmtSound


-- @@ L13-13 verbatim
namespace EvmAsm.Rv64

-- @@ L14-14 verbatim
namespace SAsm

-- @@ L15-15 verbatim
namespace EarlyRet


-- @@ L17-17 verbatim
open Stmt


-- @@ L19-23 verbatim
/-- If `x5 = 0`, return `x10 = 1`; otherwise return `x10 = 2`. -/
def twoRetBody : Stmt :=
  .retIf "choose" (.beq .x5 .x0)
    (.block "one" [.LI .x10 (1 : Word)] ;;; .ret "ret_one")
    (.block "two" [.LI .x10 (2 : Word)] ;;; .ret "ret_two")


-- @@ L25-28 verbatim
def twoRetProg : Program := twoRetBody.flatten 0

-- Byte-identity pin for the two-tail-return layout: branch, else tail, then tail.
-- There is no dead `JAL` after either `ret`.

-- @@ L29-34 verbatim
theorem twoRetProg_eq : twoRetProg =
  [ .BEQ .x5 .x0 (12 : BitVec 13),
    .LI .x10 (2 : Word),
    .JALR .x0 .x1 (0 : BitVec 12),
    .LI .x10 (1 : Word),
    .JALR .x0 .x1 (0 : BitVec 12) ] := rfl


-- @@ L36-36 verbatim
#guard twoRetBody.retOffsetsOk

-- @@ L37-37 verbatim
#guard !twoRetBody.offsetsOk


-- @@ L39-41 verbatim
/-- Entry condition for the demo: the branch input is the ghost parameter `flag`. -/
def twoRetPre (flag : Word) : Reach :=
  fun rf _ _ => rf.get .x5 = flag


-- @@ L43-45 verbatim
/-- Genuine postcondition: the returned value depends on the branch input. -/
def twoRetPost (flag : Word) : Reach :=
  fun rf _ _ => rf.get .x10 = if flag = 0 then (1 : Word) else (2 : Word)


-- @@ L47-75 verbatim
private theorem twoRet_sp_post (flag : Word) :
    ∀ rf ws A,
      Stmt.sp Region.empty RwRegion.empty twoRetBody (twoRetPre flag) rf ws A →
        twoRetPost flag rf ws A := by
  intro rf ws A hsp
  unfold twoRetBody at hsp
  simp only [Stmt.sp] at hsp
  rcases hsp with hthen | helse
  · rcases hthen with ⟨rf0, ws0, hlen, hpre, hrf, hws⟩
    rcases hpre with ⟨hpre, hcond⟩
    unfold twoRetPre at hpre
    have hflag : flag = 0 := by simpa [Cond.holds, hpre] using hcond
    unfold twoRetPost
    subst hrf
    rw [hflag]
    simp [execBlock, execInstrRF, aluSem]
  · rcases helse with ⟨rf0, ws0, hlen, hpre, hrf, hws⟩
    rcases hpre with ⟨hpre, hcond⟩
    unfold twoRetPre at hpre
    have hflag : flag ≠ 0 := by
      intro hz
      apply hcond
      simp [Cond.holds, hpre, hz]
    unfold twoRetPost
    subst hrf
    by_cases hz : flag = 0
    · exact absurd hz hflag
    · simp [execBlock, execInstrRF, aluSem]
      exact hz


-- @@ L77-100 verbatim
/-- Return-terminating CPS spec for the minimal two-`ret` body. -/
theorem twoRet_spec (flag base ret : Word)
    (halign : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin twoRetBody.steps base ret (CodeReq.ofProg base (twoRetBody.flatten base))
      ((((.x1 : Reg) ↦ᵣ ret) ** asrtM Region.empty RwRegion.empty (twoRetPre flag)))
      ((((.x1 : Reg) ↦ᵣ ret) ** asrtM Region.empty RwRegion.empty (twoRetPost flag))) := by
  have hsound := Stmt.retSound Region.empty RwRegion.empty twoRetBody base ret
    "twoRet." (twoRetPre flag)
    Region.empty_wf RwRegion.empty_wf
    (by decide) (by decide) (by decide) halign
    (fun _ _ h => h)
    (by
      intro vc hvc
      unfold twoRetBody at hvc
      simp [Stmt.ret, Stmt.vcs] at hvc
      rcases hvc with rfl | hvc
      · decide
      rcases hvc with hmem | hvc
      · exact absurd hmem.1 (by decide)
      rcases hvc with rfl | hmem
      · decide
      · exact absurd hmem.1 (by decide))
  exact cpsTripleWithin_weaken (fun _ hp => hp)
    (sepConj_mono_right (asrtM_mono (twoRet_sp_post flag))) hsound



-- @@ L103-103 verbatim
end EarlyRet

-- @@ L104-104 verbatim
end SAsm

-- @@ L105-105 verbatim
end EvmAsm.Rv64
