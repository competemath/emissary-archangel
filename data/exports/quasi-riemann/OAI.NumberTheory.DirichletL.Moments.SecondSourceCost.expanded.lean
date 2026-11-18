import OAI.NumberTheory.DirichletL.Moments.SecondLiveEnergy
import OAI.NumberTheory.DirichletL.Moments.RestrictedSourceNormalization


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
noncomputable section

-- @@ L7-7 verbatim
open scoped BigOperators Classical SchwartzMap


-- @@ L9-9 verbatim
namespace SevenEighths.CenteredMomentSecondSourceCost

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
open CenteredMomentSecondLiveEnergy CenteredMomentRestrictedSourceNormalization

-- @@ L17-17 verbatim
local notation "O" => ActualEisensteinCubic.O

-- @@ L18-18 verbatim
variable {ι : Type*} [Fintype ι]

-- @@ L19-19 verbatim
local instance : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _


-- @@ L21-59 verbatim
theorem source_divisor_common_saving (τ : Character)
    (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (hS : ∀ i,∀ I∈S i,I≠0) (hp : ∀ i,∀ I∈S (Sum.inl i),Prime I)
    (C R s : Ideal O) (hC : Supported C) (hsC : s∣C)
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ L : Ideal O) (t : ℝ)
    (Traw : ℝ) (hTraw : 0<Traw) (hP : ∀ i,0<P i)
    (M : ι → ℝ) (hν : ∀ i I,‖ν i I‖≤1) (hWnorm : ∀ i x,‖Wslot i x‖≤M i)
    (hM : ∀ i,1≤M i) (a b : ℝ) (ha : 0<a)
    (hslot : ∀ i,Function.support (Wslot i)⊆Set.Icc a b)
    (keep : O → Prop) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K)
    (hW : ∀ z : O,0≤(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) :
    let Q := finiteColumns (Fintype.piFinset S)
    let β := finiteColumnCoefficient (Fintype.piFinset S)
      (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s)
    sourceRestrictedEnergy keep (residualPool C hC.1 Q)
      (fun I=>if IsCoprime C I ∧ L∣I then β (C*I) else 0)
      (heightCoeff τ t) W K/(Traw*∏ i,P i)≤
      ((actualAllocations S C).card:ℝ)*
        (((∏ i,M i)^2*(max 1 b)^Fintype.card ι)/(Ideal.absNorm C:ℝ))*
          ∑ B : actualAllocations S C, (sourceRestrictedEnergy keep
            (finiteColumns (liveBox S B (allocation_data S C B (Finset.mem_filter.mp B.property).1).1))
            (finiteColumnCoefficient
              (liveBox S B (allocation_data S C B (Finset.mem_filter.mp B.property).1).1)
              (maskedLiveProfile B C R L ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂))
            (heightCoeff τ t) W K)/CenteredMomentCommonRawScale.remainingRaw B Traw P := by
  dsimp only
  have he := restricted_child_common_saving S hS hp C R s hC hsC
    ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ Traw hTraw hP M hν hWnorm hM a b ha hslot
    (fun I => (if L∣I then 1 else 0)*heightCoeff τ t I) keep W K hK hW
  simp_rw [live_divisor_energy] at he
  refine le_trans ?_ he
  apply le_of_eq
  congr 1
  unfold sourceRestrictedEnergy
  congr 1
  funext I
  dsimp only
  split_ifs <;> simp_all


-- @@ L61-61 verbatim
end SevenEighths.CenteredMomentSecondSourceCost


-- @@ L63-63 verbatim
end


-- @@ L65-65 verbatim
end OAI
