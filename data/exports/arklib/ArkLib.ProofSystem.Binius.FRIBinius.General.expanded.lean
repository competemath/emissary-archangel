/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/
module

public import ArkLib.OracleReduction.Composition.Sequential.NoAmbient
public import ArkLib.OracleReduction.Composition.Sequential.OracleCompleteness
public import ArkLib.ProofSystem.Binius.BinaryBasefold.QueryPhase
public import ArkLib.ProofSystem.Binius.FRIBinius.CoreInteractionPhase
public import ArkLib.ProofSystem.RingSwitching.Packing.BatchingPhase


-- @@ L14-29 verbatim
/-!
# FRI-Binius IOPCS

The FRI-Binius IOPCS consists of the following phases:
1. **Batching Phase**: polynomial packing and batching via tensor algebra operations
2. **Core Interaction Phase**: Interactive sumcheck + FRI folding over ℓ' rounds
3. **Query Phase**: FRI-style proximity testing with γ repetitions

## References
- State RBR KS

## References

- [DP24] Diamond, Benjamin E., and Jim Posen. "Polylogarithmic Proofs for Multilinears over Binary
  Towers." Cryptology ePrint Archive (2024).
-/


-- @@ L31-31 verbatim
@[expose] public section


-- @@ L33-33 verbatim
namespace Binius.FRIBinius.FullFRIBinius

-- @@ L34-34 verbatim
noncomputable section


-- @@ L36-37 verbatim
open Polynomial MvPolynomial OracleSpec OracleComp ProtocolSpec Finset AdditiveNTT Module
  Binius

-- @@ L38-38 verbatim
open Binius.BinaryBasefold RingSwitching


-- @@ L40-40 verbatim
variable (κ : ℕ) [NeZero κ]

-- @@ L41-42 verbatim
variable (L : Type) [Field L] [Fintype L] [DecidableEq L] [CharP L 2]
  [SampleableType L]

-- @@ L43-43 verbatim
variable (K : Type) [Field K] [Fintype K] [DecidableEq K]

-- @@ L44-44 verbatim
variable [h_Fq_char_prime : Fact (Nat.Prime (ringChar K))] [hF₂ : Fact (Fintype.card K = 2)]

-- @@ L45-45 verbatim
variable [Algebra K L]

-- @@ L46-47 verbatim
variable (β : Basis (Fin (2 ^ κ)) K L)
  [h_β₀_eq_1 : Fact (β 0 = 1)]

-- @@ L48-48 verbatim
variable (ℓ ℓ' 𝓡 ϑ γ_repetitions : ℕ) [NeZero ℓ] [NeZero ℓ'] [NeZero 𝓡] [NeZero ϑ]

-- @@ L49-49 verbatim
variable (h_ℓ_add_R_rate : ℓ' + 𝓡 < 2 ^ κ)

-- @@ L50-50 verbatim
variable (h_l : ℓ = ℓ' + κ)

-- @@ L51-51 verbatim
variable [hdiv : Fact (ϑ ∣ ℓ')]


-- @@ L53-57 verbatim
/-- The Binius ring-switching profile, built from the boolean-hypercube basis derived from `β`.
Kept defeq to `binaryTowerProfile … (booleanHypercubeBasis …)` so all downstream RingSwitching
semantics and axioms are preserved. -/
def biniusProfile : RingSwitching.RingSwitchingProfile K L κ :=
  RingSwitching.binaryTowerProfile κ K L (booleanHypercubeBasis κ L K β)


-- @@ L59-59 verbatim
section Pspec


-- @@ L61-62 verbatim
def batchingCorePspec := (RingSwitching.pSpecBatching κ L K (biniusProfile κ L K β)) ++ₚ
  (BinaryBasefold.pSpecCoreInteraction K β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate))


-- @@ L64-65 verbatim
def fullPspec := (batchingCorePspec κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate) ++ₚ
  (BinaryBasefold.pSpecQuery K β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate))


-- @@ L67-71 verbatim
instance : ∀ j, OracleInterface ((batchingCorePspec κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate).Message j) :=
  instOracleInterfaceMessageAppend
    (pSpec₁ := RingSwitching.pSpecBatching κ L K (biniusProfile κ L K β))
    (pSpec₂ := BinaryBasefold.pSpecCoreInteraction K β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate))


-- @@ L73-77 verbatim
instance : ∀ j, SampleableType ((batchingCorePspec κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate).Challenge j) :=
  instSampleableTypeChallengeAppend
    (pSpec₁ := RingSwitching.pSpecBatching κ L K (biniusProfile κ L K β))
    (pSpec₂ := BinaryBasefold.pSpecCoreInteraction K β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate))


-- @@ L79-82 verbatim
instance : ∀ j, OracleInterface ((fullPspec κ L K β ℓ' 𝓡 ϑ γ_repetitions
    h_ℓ_add_R_rate).Message j) :=
  instOracleInterfaceMessageAppend (pSpec₁ := batchingCorePspec κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate)
    (pSpec₂ := BinaryBasefold.pSpecQuery K β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate))


-- @@ L84-87 verbatim
instance : ∀ j, SampleableType ((fullPspec κ L K β ℓ' 𝓡 ϑ γ_repetitions
    h_ℓ_add_R_rate).Challenge j) :=
  instSampleableTypeChallengeAppend (pSpec₁ := batchingCorePspec κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate)
    (pSpec₂ := BinaryBasefold.pSpecQuery K β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate))


-- @@ L89-89 verbatim
end Pspec


-- @@ L91-103 verbatim
def batchingCoreVerifier :=
  OracleVerifier.append (oSpec:=[]ₒ)
    (V₁:= RingSwitching.BatchingPhase.oracleVerifier κ L K (biniusProfile κ L K β)
      ℓ ℓ' h_l (aOStmtIn := BinaryBasefoldAbstractOStmtIn κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate))
    (pSpec₁ := RingSwitching.pSpecBatching κ L K (biniusProfile κ L K β))
    (pSpec₂:=BinaryBasefold.pSpecCoreInteraction K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (OStmt₁ := (BinaryBasefoldAbstractOStmtIn κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate).OStmtIn)
    (OStmt₂ := BinaryBasefold.OracleStatement K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ 0)
    (OStmt₃ := BinaryBasefold.OracleStatement K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ'))
    (V₂:= FRIBinius.CoreInteractionPhase.coreInteractionOracleVerifier κ L K
      β ℓ ℓ' 𝓡 ϑ h_ℓ_add_R_rate h_l )


-- @@ L105-118 verbatim
def batchingCoreReduction :=
  OracleReduction.append (oSpec:=[]ₒ)
    (R₁ := RingSwitching.BatchingPhase.batchingOracleReduction κ L K
      (biniusProfile κ L K β) ℓ ℓ' h_l
      (aOStmtIn := BinaryBasefoldAbstractOStmtIn κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate))
    (pSpec₁ := RingSwitching.pSpecBatching κ L K (biniusProfile κ L K β))
    (pSpec₂:=BinaryBasefold.pSpecCoreInteraction K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (OStmt₁ := (BinaryBasefoldAbstractOStmtIn κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate).OStmtIn)
    (OStmt₂ := BinaryBasefold.OracleStatement K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ 0)
    (OStmt₃ := BinaryBasefold.OracleStatement K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ'))
    (R₂ := FRIBinius.CoreInteractionPhase.coreInteractionOracleReduction κ L K
      β ℓ ℓ' 𝓡 ϑ h_ℓ_add_R_rate h_l )


-- @@ L120-141 verbatim
/-- The oracle verifier for the full Binary Basefold protocol -/
@[reducible]
noncomputable def fullOracleVerifier :
  OracleProofVerifier (oSpec:=[]ₒ)
    (Statement := BatchingStmtIn (L := L) (ℓ:=ℓ))
    (OStatement := (BinaryBasefoldAbstractOStmtIn κ L K β ℓ' 𝓡 ϑ
      h_ℓ_add_R_rate).OStmtIn)
    (pSpec := fullPspec κ L K β ℓ' 𝓡 ϑ γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) :=
  OracleVerifier.append (oSpec:=[]ₒ)
    (Stmt₁ := BatchingStmtIn (L := L) (ℓ:=ℓ))
    (Stmt₂ := BinaryBasefold.FinalSumcheckStatementOut (L:=L) (ℓ:=ℓ'))
    (Stmt₃ := Bool)
    (OStmt₁ := (BinaryBasefoldAbstractOStmtIn κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate).OStmtIn)
    (OStmt₂ := BinaryBasefold.OracleStatement K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ'))
    (OStmt₃ := fun _ : Empty => Unit)
    (pSpec₁ := batchingCorePspec κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate)
    (pSpec₂ := BinaryBasefold.pSpecQuery K β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (Oₛ₃ := fun i : Empty => nomatch i)
    (V₁ := batchingCoreVerifier κ L K β ℓ ℓ' 𝓡 ϑ h_ℓ_add_R_rate h_l )
    (V₂ := QueryPhase.queryOracleVerifier K β γ_repetitions
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ:=ϑ))


-- @@ L143-169 verbatim
/-- The reduction for the full Binary Basefold protocol -/
@[reducible]
noncomputable def fullOracleReduction :
  OracleProof (oSpec:=[]ₒ)
    (Statement := BatchingStmtIn (L := L) (ℓ:=ℓ))
    (OStatement := (BinaryBasefoldAbstractOStmtIn κ L K β ℓ' 𝓡 ϑ
      h_ℓ_add_R_rate).OStmtIn)
    (Witness := BatchingWitIn L K ℓ ℓ')
    (pSpec := fullPspec κ L K β ℓ' 𝓡 ϑ γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) :=
  OracleReduction.append (oSpec:=[]ₒ)
    (Stmt₁ := BatchingStmtIn (L := L) (ℓ:=ℓ))
    (Stmt₂ := BinaryBasefold.FinalSumcheckStatementOut (L:=L) (ℓ:=ℓ'))
    (Stmt₃ := Bool)
    (Wit₁ := BatchingWitIn L K ℓ ℓ')
    (Wit₂ := Unit)
    (Wit₃ := Unit)
    (OStmt₁ := (BinaryBasefoldAbstractOStmtIn κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate).OStmtIn)
    (OStmt₂ := BinaryBasefold.OracleStatement K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ'))
    (OStmt₃ := fun _ : Empty => Unit)
    (pSpec₁ := batchingCorePspec κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate)
    (pSpec₂ := BinaryBasefold.pSpecQuery K β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (Oₛ₃ := fun i : Empty => nomatch i)
    (R₁ := batchingCoreReduction κ L K β ℓ ℓ' 𝓡 ϑ h_ℓ_add_R_rate h_l
    )
    (R₂ := QueryPhase.queryOracleReduction K β γ_repetitions
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ:=ϑ))


-- @@ L171-179 verbatim
/-- The full Binary Basefold protocol as a Proof -/
@[reducible]
noncomputable def fullOracleProof :
  OracleProof []ₒ
    (Statement := BatchingStmtIn (L := L) (ℓ:=ℓ))
    (OStatement := (BinaryBasefoldAbstractOStmtIn κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate).OStmtIn)
    (Witness := BatchingWitIn L K ℓ ℓ')
    (pSpec:= fullPspec κ L K β ℓ' 𝓡 ϑ γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) :=
  fullOracleReduction κ L K β ℓ ℓ' 𝓡 ϑ γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate) h_l


-- @@ L181-183 verbatim
/-!
## Security Properties
-/


-- @@ L185-185 verbatim
variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl []ₒ (StateT σ ProbComp)}


-- @@ L187-242 verbatim
/-- The full FRI-Binius oracle proof is perfectly complete. -/
theorem fullOracleReduction_perfectCompleteness :
    OracleProof.perfectCompleteness
      (oracleProof := fullOracleReduction κ L K β ℓ ℓ' 𝓡 ϑ γ_repetitions
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) h_l )
      (relation := BatchingPhase.batchingInputRelation κ L K (biniusProfile κ L K β)
        ℓ ℓ' h_l (BinaryBasefoldAbstractOStmtIn κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate))
      (init := init)
      (impl := impl) :=
  OracleReduction.append_perfectCompleteness_of_guarded_verifiers
    (R₁ := batchingCoreReduction κ L K β ℓ ℓ' 𝓡 ϑ h_ℓ_add_R_rate h_l )
    (R₂ := QueryPhase.queryOracleReduction K β γ_repetitions
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ:=ϑ))
    (OStmt₁ := (BinaryBasefoldAbstractOStmtIn κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate).OStmtIn)
    (OStmt₂ := BinaryBasefold.OracleStatement K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ'))
    (OStmt₃ := fun _ : Empty => Unit)
    (Oₛ₁:= (BinaryBasefoldAbstractOStmtIn κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate).Oₛᵢ)
    (Oₛ₂:=Binius.BinaryBasefold.instOracleStatementBinaryBasefold K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ := ϑ) (i := Fin.last ℓ'))
    (Oₛ₃ := fun i : Empty => nomatch i)
    (pSpec₁ := batchingCorePspec κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate)
    (pSpec₂ := BinaryBasefold.pSpecQuery K β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (rel₁ := BatchingPhase.batchingInputRelation κ L K (biniusProfile κ L K β)
      ℓ ℓ' h_l (BinaryBasefoldAbstractOStmtIn κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate))
    (rel₂ := BinaryBasefold.finalSumcheckRelOut K β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (rel₃ := acceptRejectOracleRel)
    (V₁ := Verifier.GuardedForm.ofEmpty _ (fun _ =>
      (⟨⟨0, fun _ => 0, ⟨0, 0⟩⟩, 0⟩, fun _ _ => 0)))
    (V₂ := Verifier.GuardedForm.ofEmpty _ (fun _ => (false, fun i => nomatch i)))
    (hSeam := fun _ => Or.inl inferInstance)
    (h₁ := by
      apply OracleReduction.append_perfectCompleteness_of_guarded_verifiers
        (rel₁ := BatchingPhase.batchingInputRelation κ L K (biniusProfile κ L K β)
          ℓ ℓ' h_l (BinaryBasefoldAbstractOStmtIn κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate))
        (rel₂ := RingSwitching.sumcheckRoundRelation κ L K (biniusProfile κ L K β)
        ℓ ℓ' h_l (aOStmtIn := BinaryBasefoldAbstractOStmtIn κ L K β ℓ'
          𝓡 ϑ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) 0)
        (rel₃ := BinaryBasefold.finalSumcheckRelOut K β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
        (V₁ := Verifier.GuardedForm.ofEmpty _ (fun input =>
          (⟨0, fun _ => 0,
            ⟨⟨input.1.t_eval_point, input.1.original_claim⟩, 0, 0⟩⟩, input.2)))
        (V₂ := Verifier.GuardedForm.ofEmpty _ (fun _ =>
          (⟨⟨0, fun _ => 0, ⟨0, 0⟩⟩, 0⟩, fun _ _ => 0)))
        (hSeam := fun _ => Or.inl inferInstance)
      · apply BatchingPhase.batchingReduction_perfectCompleteness κ L K
          (biniusProfile κ L K β) ℓ ℓ' h_l
          (BinaryBasefoldAbstractOStmtIn κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate)
      · intro s
        apply CoreInteractionPhase.coreInteractionOracleReduction_perfectCompleteness
          κ L K β ℓ ℓ' 𝓡 ϑ h_ℓ_add_R_rate h_l
    )
    (h₂ := fun s => QueryPhase.queryOracleProof_perfectCompleteness K β γ_repetitions
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ:=ϑ) (pure s) impl)

-- TODO: state RBR KS


-- @@ L244-244 verbatim
end

-- @@ L245-245 verbatim
end Binius.FRIBinius.FullFRIBinius
