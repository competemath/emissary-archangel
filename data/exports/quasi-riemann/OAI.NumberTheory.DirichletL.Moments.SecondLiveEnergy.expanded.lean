import OAI.NumberTheory.DirichletL.Moments.SecondSectorEnergy
import OAI.NumberTheory.DirichletL.Moments.SecondSourceMask


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
noncomputable section

-- @@ L7-7 verbatim
open scoped BigOperators Classical SchwartzMap


-- @@ L9-9 verbatim
namespace SevenEighths.CenteredMomentSecondLiveEnergy

-- @@ L10-10 verbatim
open HeckeFamily CanonicalQuadraticSieve CenteredMomentSourceRow

-- @@ L11-11 verbatim
open CenteredMomentHeckeColumnWindow CenteredMomentSecondSectorEnergy CenteredMomentSecondSectorColumns

-- @@ L12-12 verbatim
open CenteredMomentSecondScaled CenteredMomentChildAssembly CenteredMomentRestrictedSource

-- @@ L13-13 verbatim
open CenteredMomentRestrictedEnergy CenteredMomentSourceLiveColumn CenteredMomentSourceProfileMass

-- @@ L14-14 verbatim
open CenteredMomentSourceMass CenteredMomentAddedZeroUniform CenteredMomentCommonAllocationSum

-- @@ L15-15 verbatim
open CenteredMomentAmplificationLiveMask CenteredMomentFirstSectors RayFourExpansion

-- @@ L16-16 verbatim
local notation "O" => ActualEisensteinCubic.O

-- @@ L17-17 verbatim
variable {ι : Type*} [Fintype ι]

-- @@ L18-18 verbatim
local instance : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _


-- @@ L20-35 verbatim
theorem live_divisor_energy (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (B : Tuple ι) (hB : ∀ i,B i≠0) (C R L : Ideal O)
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O)
    (f : Ideal O → ℂ) (keep : O → Prop) (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    sourceRestrictedEnergy keep (finiteColumns (liveBox S B hB))
      (finiteColumnCoefficient (liveBox S B hB) (liveProfile B C R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂))
      (fun I => (if L∣I then 1 else 0)*f I) W K=
    sourceRestrictedEnergy keep (finiteColumns (liveBox S B hB))
      (finiteColumnCoefficient (liveBox S B hB) (maskedLiveProfile B C R L ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂)) f W K := by
  unfold sourceRestrictedEnergy
  congr 1
  funext I
  rw [maskedLiveProfile,column_mask]
  dsimp only [liveProfile]
  ring


-- @@ L37-77 verbatim
theorem actual_second_child_live_energy (η τ : Character) (χ : RayCharacter) (A : O)
    (hτ : ∀ I : Ideal O,Supported I → ∀ t : ℝ,
      heightCoeff τ t I=heightCoeff η t I*CanonicalRowCompletion.idealRowHom A I*
        rayCharacter χ (CompletedGauss.primaryGenerator I))
    (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (hS : ∀ i,∀ I∈S i,I≠0) (hp : ∀ i,∀ I∈S (Sum.inl i),Prime I)
    (C R s : Ideal O) (hC : Supported C) (hsC : s∣C)
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ L : Ideal O) (t : ℝ)
    (keep : O → Prop) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K)
    (hW : ∀ z : O,0≤(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) :
    let Q := finiteColumns (Fintype.piFinset S)
    let β := finiteColumnCoefficient (Fintype.piFinset S)
      (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s)
    restrictedEnergy keep Finset.univ (sectorElement C hC.1 Q)
      (divisorCoefficient L (sectorElement C hC.1 Q)
        (movingCoefficient A (sectorElement C hC.1 Q)
          (fun J : sectorPool C hC.1 Q => β (C*J)*heightCoeff η t J)) χ) W K≤
      ((actualAllocations S C).card:ℝ)*∑ B : actualAllocations S C,
        ‖frozenCoefficient B C R ν Wslot P‖^2*
          sourceRestrictedEnergy keep
            (finiteColumns (liveBox S B (allocation_data S C B (Finset.mem_filter.mp B.property).1).1))
            (finiteColumnCoefficient
              (liveBox S B (allocation_data S C B (Finset.mem_filter.mp B.property).1).1)
              (maskedLiveProfile B C R L ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂))
            (heightCoeff τ t) W K := by
  dsimp only
  rw [sector_child_energy η τ χ A hτ (finiteColumns (Fintype.piFinset S))
    (finiteColumnCoefficient (Fintype.piFinset S)
      (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s)) C hC L t keep W K]
  have he := original_restricted_child_energy S hS hp C R s hC hsC
    ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂
    (fun I => (if L∣I then 1 else 0)*heightCoeff τ t I) keep W K hK hW
  simp_rw [live_divisor_energy] at he
  refine le_trans ?_ he
  apply le_of_eq
  unfold sourceRestrictedEnergy
  congr 1
  funext I
  dsimp only
  split_ifs <;> simp_all


-- @@ L79-79 verbatim
end SevenEighths.CenteredMomentSecondLiveEnergy


-- @@ L81-81 verbatim
end


-- @@ L83-83 verbatim
end OAI
