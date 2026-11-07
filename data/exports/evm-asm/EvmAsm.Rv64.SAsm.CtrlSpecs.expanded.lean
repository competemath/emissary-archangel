/-
  EvmAsm.Rv64.SAsm.CtrlSpecs

  Machine-level specs for the control instructions the SAsm flattener
  synthesizes, at reachable-set granularity: conditional branches split an
  `asrtOf reach` precondition by the condition's denotation, and `JAL x0`
  is a pure PC move.  Plus the offset arithmetic connecting flattener
  offsets (`brOfs`/`jFwd`/`jBack`) to address displacements.
-/

import EvmAsm.Rv64.ControlFlow
import EvmAsm.Rv64.SAsm.Vc


-- @@ L14-14 verbatim
namespace EvmAsm.Rv64

-- @@ L15-19 verbatim
namespace SAsm

-- ============================================================================
-- Condition denotation over an arbitrary valuation, matching execInstrBr
-- ============================================================================


-- @@ L21-21 verbatim
namespace Cond


-- @@ L23-31 verbatim
/-- Condition denotation over an arbitrary register valuation, phrased
    exactly as the `execInstrBr` branch guards. -/
def holdsG : Cond → (Reg → Word) → Prop
  | beq  rs1 rs2, g => (g rs1 == g rs2) = true
  | bne  rs1 rs2, g => (g rs1 != g rs2) = true
  | blt  rs1 rs2, g => BitVec.slt (g rs1) (g rs2) = true
  | bge  rs1 rs2, g => ¬ (BitVec.slt (g rs1) (g rs2) = true)
  | bltu rs1 rs2, g => BitVec.ult (g rs1) (g rs2) = true
  | bgeu rs1 rs2, g => ¬ (BitVec.ult (g rs1) (g rs2) = true)


-- @@ L33-34 verbatim
instance (c : Cond) (g : Reg → Word) : Decidable (c.holdsG g) := by
  cases c <;> simp only [holdsG] <;> infer_instance


-- @@ L36-38 verbatim
theorem holds_iff_holdsG (c : Cond) (rf : RegFile) :
    c.holds rf ↔ c.holdsG rf.get := by
  cases c <;> simp [holds, holdsG]


-- @@ L40-47 verbatim
/-- `holdsG` depends only on the (exposed-or-x0) registers a well-formed
    condition reads. -/
theorem holdsG_agree {c : Cond} (hwf : c.wf = true) {g g' : Reg → Word}
    (hag : ∀ r, (Reg.isExposed r || r == .x0) = true → g r = g' r) :
    c.holdsG g ↔ c.holdsG g' := by
  cases c <;>
    (simp only [wf, regs, Bool.and_eq_true] at hwf;
     rw [holdsG, holdsG, hag _ hwf.1, hag _ hwf.2])


-- @@ L49-53 verbatim
/-- Branch instructions are never ECALL/EBREAK and touch no memory. -/
theorem toInstr_not_special (c : Cond) (ofs : BitVec 13) :
    c.toInstr ofs ≠ .ECALL ∧ c.toInstr ofs ≠ .EBREAK ∧
      (c.toInstr ofs).isMemAccess = false := by
  cases c <;> exact ⟨by nofun, by nofun, rfl⟩


-- @@ L55-60 verbatim
/-- The machine's branch execution, phrased through `holdsG`. -/
theorem execInstrBr_cond (c : Cond) (ofs : BitVec 13) (s : MachineState) :
    execInstrBr s (c.toInstr ofs) =
      if c.holdsG s.getReg then s.setPC (s.pc + signExtend13 ofs)
      else s.setPC (s.pc + 4) := by
  cases c <;> rfl


-- @@ L62-66 verbatim
end Cond

-- ============================================================================
-- Reach-level branch and jump specs
-- ============================================================================


-- @@ L68-113 verbatim
/-- Conditional-branch spec at reachable-set granularity: the branch splits
    `asrtOf rw reach` by the condition's denotation over the current register
    file, changing nothing but the PC. -/
theorem branch_spec_asrt (c : Cond) (ofs : BitVec 13) (rw : RwRegion)
    (reach : Reach) (base : Word)
    (hwf : c.wf = true) :
    cpsBranchWithin 1 base (CodeReq.singleton base (c.toInstr ofs))
      (asrtOf rw reach)
      (base + signExtend13 ofs)
        (asrtOf rw fun rf ws A => reach rf ws A ∧ c.holds rf)
      (base + 4) (asrtOf rw fun rf ws A => reach rf ws A ∧ ¬ c.holds rf) := by
  intro R hR s hcr hPR hpc; subst hpc
  have hfetch : s.code s.pc = some (c.toInstr ofs) :=
    CodeReq.singleton_satisfiedBy.mp hcr
  obtain ⟨hnec, hneb, hnm⟩ := Cond.toInstr_not_special c ofs
  have hstep' : step s = some (execInstrBr s (c.toInstr ofs)) :=
    step_non_ecall_non_mem hfetch hnec hneb hnm
  obtain ⟨hp, hcompat, h1, h2, hd, hu, ⟨rf, ws, A, hlen, hApc, hreach, hsts⟩, hR2⟩ := hPR
  have hPR' : ((regFileIs rf) ** (bytesRegion rw.base ws ** (A ** R))).holdsFor s := by
    have h0 : ((((regFileIs rf) ** bytesRegion rw.base ws) ** A) ** R).holdsFor s :=
      ⟨hp, hcompat, h1, h2, hd, hu, hsts, hR2⟩
    rwa [sepConj_assoc' ((regFileIs rf) ** bytesRegion rw.base ws) A R,
      sepConj_assoc'] at h0
  have hgeq : c.holdsG s.getReg ↔ c.holds rf := by
    rw [Cond.holds_iff_holdsG]
    exact Cond.holdsG_agree hwf
      (fun r hr => holdsFor_regFileIs_agree hPR' hr)
  have hpcfree_t : ((asrtOf rw fun rf ws A => reach rf ws A ∧ c.holds rf) ** R).pcFree :=
    pcFree_sepConj (pcFree_asrtOf _ _) hR
  have hpcfree_f : ((asrtOf rw fun rf ws A => reach rf ws A ∧ ¬ c.holds rf) ** R).pcFree :=
    pcFree_sepConj (pcFree_asrtOf _ _) hR
  by_cases hc : c.holds rf
  · have hexec : execInstrBr s (c.toInstr ofs) = s.setPC (s.pc + signExtend13 ofs) := by
      rw [Cond.execInstrBr_cond, if_pos (hgeq.mpr hc)]
    refine ⟨1, Nat.le_refl 1, s.setPC (s.pc + signExtend13 ofs), ?_, Or.inl ⟨rfl, ?_⟩⟩
    · show (step s).bind (stepN 0) = some _
      rw [hstep', hexec]; rfl
    · exact holdsFor_pcFree_setPC hpcfree_t
        ⟨hp, hcompat, h1, h2, hd, hu, ⟨rf, ws, A, hlen, hApc, ⟨hreach, hc⟩, hsts⟩, hR2⟩
  · have hexec : execInstrBr s (c.toInstr ofs) = s.setPC (s.pc + 4) := by
      rw [Cond.execInstrBr_cond, if_neg (fun h => hc (hgeq.mp h))]
    refine ⟨1, Nat.le_refl 1, s.setPC (s.pc + 4), ?_, Or.inr ⟨rfl, ?_⟩⟩
    · show (step s).bind (stepN 0) = some _
      rw [hstep', hexec]; rfl
    · exact holdsFor_pcFree_setPC hpcfree_f
        ⟨hp, hcompat, h1, h2, hd, hu, ⟨rf, ws, A, hlen, hApc, ⟨hreach, hc⟩, hsts⟩, hR2⟩


-- @@ L115-132 verbatim
/-- `JAL x0` at pc-free-assertion granularity: a pure PC move. -/
theorem jal0_spec_pcFree (ofs : BitVec 21) (base : Word) {P : Assertion}
    (hP : P.pcFree) :
    cpsTripleWithin 1 base (base + signExtend21 ofs)
      (CodeReq.singleton base (.JAL .x0 ofs)) P P := by
  intro R hR s hcr hPR hpc; subst hpc
  have hfetch : s.code s.pc = some (.JAL .x0 ofs) :=
    CodeReq.singleton_satisfiedBy.mp hcr
  have hstep' : step s = some (execInstrBr s (.JAL .x0 ofs)) :=
    step_non_ecall_non_mem hfetch (by nofun) (by nofun) rfl
  refine ⟨1, Nat.le_refl 1, s.setPC (s.pc + signExtend21 ofs), ?_, rfl, ?_⟩
  · show (step s).bind (stepN 0) = some _
    rw [hstep', execInstrBr_jal_x0]; rfl
  · exact holdsFor_pcFree_setPC (pcFree_sepConj hP hR) hPR

-- ============================================================================
-- Offset arithmetic for the flattener's synthesized offsets
-- ============================================================================


-- @@ L134-136 verbatim
theorem signExtend13_brOfs {n : Nat} (h : 4 * n < 2 ^ 12) :
    signExtend13 (Stmt.brOfs n) = BitVec.ofNat 64 (4 * n) :=
  signExtend13_ofNat_small h


-- @@ L138-140 verbatim
theorem signExtend21_jFwd {n : Nat} (h : 4 * n < 2 ^ 20) :
    signExtend21 (Stmt.jFwd n) = BitVec.ofNat 64 (4 * n) :=
  signExtend21_ofNat_small h


-- @@ L142-159 verbatim
/-- A backward jump of `n` instructions undoes an `n`-instruction advance. -/
theorem add_jBack (a : Word) (n : Nat) (h0 : 0 < n) (h2 : 4 * n ≤ 2 ^ 20) :
    (a + BitVec.ofNat 64 (4 * n)) + signExtend21 (Stmt.jBack n) = a := by
  have hmsb : (Stmt.jBack n).msb = true := by
    rw [BitVec.msb_eq_true_iff_two_mul_ge]
    unfold Stmt.jBack
    simp only [BitVec.toNat_ofNat]
    omega
  have htoNat : (signExtend21 (Stmt.jBack n)).toNat = 2 ^ 64 - 4 * n := by
    unfold signExtend21 Stmt.jBack
    rw [BitVec.toNat_signExtend]
    rw [show (BitVec.ofNat 21 (2 ^ 21 - 4 * n)).msb = true from hmsb]
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, if_true]
    omega
  apply BitVec.eq_of_toNat_eq
  have ha := a.isLt
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, htoNat]
  omega


-- @@ L161-180 verbatim
/-- A backward conditional branch of `n` instructions undoes an
    `n`-instruction advance (the `brOfs`-family 13-bit analogue of
    `add_jBack`; the `doWhile` back-edge is a guard branch, not a `JAL`). -/
theorem add_brOfsBack (a : Word) (n : Nat) (h0 : 0 < n) (h2 : 4 * n ≤ 2 ^ 12) :
    (a + BitVec.ofNat 64 (4 * n)) + signExtend13 (Stmt.brOfsBack n) = a := by
  have hmsb : (Stmt.brOfsBack n).msb = true := by
    rw [BitVec.msb_eq_true_iff_two_mul_ge]
    unfold Stmt.brOfsBack
    simp only [BitVec.toNat_ofNat]
    omega
  have htoNat : (signExtend13 (Stmt.brOfsBack n)).toNat = 2 ^ 64 - 4 * n := by
    unfold signExtend13 Stmt.brOfsBack
    rw [BitVec.toNat_signExtend]
    rw [show (BitVec.ofNat 13 (2 ^ 13 - 4 * n)).msb = true from hmsb]
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, if_true]
    omega
  apply BitVec.eq_of_toNat_eq
  have ha := a.isLt
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, htoNat]
  omega


-- @@ L182-185 verbatim
/-- Nat-displacement associativity for instruction addresses. -/
theorem addr_shift (a : Word) (m n : Nat) :
    (a + BitVec.ofNat 64 m) + BitVec.ofNat 64 n = a + BitVec.ofNat 64 (m + n) := by
  bv_omega


-- @@ L187-187 verbatim
end SAsm

-- @@ L188-188 verbatim
end EvmAsm.Rv64
