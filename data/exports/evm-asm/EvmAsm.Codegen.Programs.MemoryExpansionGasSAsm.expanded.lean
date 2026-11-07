/-
  EvmAsm.Codegen.Programs.MemoryExpansionGasSAsm

  Byte-identical return-terminating SAsm proof for `memory_expansion_gas`.
  The emitted routine has an early zero-return tail, so this uses `Stmt.retIf`
  rather than the single-exit `Fn.Spec` path.
-/

import EvmAsm.Rv64.SAsm.StmtSound
import EvmAsm.Codegen.Programs.MemoryExpansionGas


-- @@ L12-12 verbatim
namespace EvmAsm.Codegen


-- @@ L14-14 verbatim
open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Rv64.SAsm.Stmt


-- @@ L16-16 verbatim
namespace MemoryExpansionGasSAsm


-- @@ L18-19 verbatim
def memoryExpansionWords (bytes : Word) : Word :=
  (bytes + signExtend12 (31 : BitVec 12)) >>> 5


-- @@ L21-23 verbatim
def memoryExpansionCost (bytes : Word) : Word :=
  let w := memoryExpansionWords bytes
  w * (3 : Word) + ((w * w) >>> 9)


-- @@ L25-29 verbatim
def memoryExpansionGasResult (oldBytes newBytes : Word) : Word :=
  if BitVec.ult oldBytes newBytes = true then
    memoryExpansionCost newBytes - memoryExpansionCost oldBytes
  else
    0


-- @@ L31-45 verbatim
def memoryExpansionGasCalcBlock : List Instr :=
  [ .ADDI .x5 .x10 (31 : BitVec 12),
    .SRLI .x5 .x5 (5 : BitVec 6),
    .ADDI .x6 .x11 (31 : BitVec 12),
    .SRLI .x6 .x6 (5 : BitVec 6),
    .LI .x7 (3 : Word),
    .MUL .x28 .x5 .x7,
    .MUL .x29 .x5 .x5,
    .SRLI .x29 .x29 (9 : BitVec 6),
    .ADD .x28 .x28 .x29,
    .MUL .x30 .x6 .x7,
    .MUL .x31 .x6 .x6,
    .SRLI .x31 .x31 (9 : BitVec 6),
    .ADD .x30 .x30 .x31,
    .SUB .x10 .x30 .x28 ]


-- @@ L47-50 verbatim
def memoryExpansionGasBody : Stmt :=
  .retIf "new_le_old" (.bgeu .x10 .x11)
    (.block "zero" [.LI .x10 (0 : Word)] ;;; .ret "ret_zero")
    (.block "calc" memoryExpansionGasCalcBlock ;;; .ret "ret_calc")


-- @@ L52-53 verbatim
def memoryExpansionGasPre (oldBytes newBytes : Word) : Reach :=
  fun rf _ _ => rf.get .x10 = oldBytes ∧ rf.get .x11 = newBytes


-- @@ L55-56 verbatim
def memoryExpansionGasPost (oldBytes newBytes : Word) : Reach :=
  fun rf _ _ => rf.get .x10 = memoryExpansionGasResult oldBytes newBytes


-- @@ L58-59 verbatim
def memoryExpansionGas_verified : Program :=
  memoryExpansionGasBody.flatten 0


-- @@ L61-61 verbatim
#guard (memoryExpansionGas_verified : List Instr).length = 18

-- @@ L62-62 verbatim
#guard memoryExpansionGasBody.retOffsetsOk

-- @@ L63-63 verbatim
#guard !memoryExpansionGasBody.offsetsOk

-- @@ L64-64 verbatim
#guard memoryExpansionGasBody.flatten 0 = memoryExpansionGas_prog


-- @@ L66-89 verbatim
private theorem memoryExpansionGas_sp_post (oldBytes newBytes : Word) :
    ∀ rf ws A,
      Stmt.sp Region.empty RwRegion.empty memoryExpansionGasBody
          (memoryExpansionGasPre oldBytes newBytes) rf ws A →
        memoryExpansionGasPost oldBytes newBytes rf ws A := by
  intro rf ws A hsp
  unfold memoryExpansionGasBody at hsp
  simp only [Stmt.sp] at hsp
  rcases hsp with hzero | hcalc
  · rcases hzero with ⟨rf0, ws0, hlen, hreach, hrf, hws⟩
    rcases hreach with ⟨hpre, hcond⟩
    rcases hpre with ⟨hx10, hx11⟩
    subst hrf
    unfold memoryExpansionGasPost memoryExpansionGasResult
    simp [execBlock, execInstrRF, aluSem, Cond.holds, hx10, hx11] at hcond ⊢
    simp [hcond]
  · rcases hcalc with ⟨rf0, ws0, hlen, hreach, hrf, hws⟩
    rcases hreach with ⟨hpre, hcond⟩
    rcases hpre with ⟨hx10, hx11⟩
    subst hrf
    unfold memoryExpansionGasPost memoryExpansionGasResult
    simp [execBlock, execInstrRF, aluSem, Cond.holds, memoryExpansionGasCalcBlock,
      memoryExpansionCost, memoryExpansionWords, hx10, hx11] at hcond ⊢
    simp [hcond]


-- @@ L91-113 verbatim
theorem memoryExpansionGas_spec (oldBytes newBytes base ret : Word)
    (halign : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin memoryExpansionGasBody.steps base ret
      (CodeReq.ofProg base (memoryExpansionGasBody.flatten base))
      ((((.x1 : Reg) ↦ᵣ ret) ** asrtM Region.empty RwRegion.empty
        (memoryExpansionGasPre oldBytes newBytes)))
      ((((.x1 : Reg) ↦ᵣ ret) ** asrtM Region.empty RwRegion.empty
        (memoryExpansionGasPost oldBytes newBytes))) := by
  have hsound := Stmt.retSound Region.empty RwRegion.empty memoryExpansionGasBody base ret
    "memoryExpansionGas." (memoryExpansionGasPre oldBytes newBytes)
    Region.empty_wf RwRegion.empty_wf
    (by decide) (by decide) (by decide) halign
    (fun _ _ h => h)
    (by
      intro vc hvc
      unfold memoryExpansionGasBody memoryExpansionGasCalcBlock at hvc
      simp [Stmt.ret, Stmt.vcs, hasLoad, loadSem, storeSem] at hvc
      rcases hvc with rfl | hvc
      · decide
      rcases hvc with rfl | hvc
      · decide)
  exact cpsTripleWithin_weaken (fun _ hp => hp)
    (sepConj_mono_right (asrtM_mono (memoryExpansionGas_sp_post oldBytes newBytes))) hsound


-- @@ L115-115 verbatim
end MemoryExpansionGasSAsm


-- @@ L117-117 verbatim
end EvmAsm.Codegen
