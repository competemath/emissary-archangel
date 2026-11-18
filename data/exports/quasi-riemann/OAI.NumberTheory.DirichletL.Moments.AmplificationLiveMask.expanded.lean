import OAI.NumberTheory.DirichletL.Moments.OriginalChildEnergy


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section

-- @@ L6-6 verbatim
open scoped BigOperators Classical


-- @@ L8-8 verbatim
namespace SevenEighths.CenteredMomentAmplificationLiveMask

-- @@ L9-9 verbatim
open CenteredMomentSourceLiveColumn CenteredMomentSourceProfileMass CenteredMomentSourceMass

-- @@ L10-10 verbatim
open CenteredMomentAddedZeroUniform CenteredMomentCommonAllocationSum

-- @@ L11-11 verbatim
open CenteredMomentOriginalChildEnergy CenteredMomentRemainingBox CenteredMomentCommonProfile

-- @@ L12-12 verbatim
local notation "O" => ActualEisensteinCubic.O

-- @@ L13-13 verbatim
variable {ι : Type*} [Fintype ι]

-- @@ L14-14 verbatim
local instance : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

 
-- @@ L16-22 verbatim
theorem profile_mask (R : Ideal O) (ν : ι → Ideal O → ℂ)
    (Wslot : ι → ℝ → ℂ) (P : ι → ℝ) (W₁ W₂ : ℝ → ℂ)
    (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ s : Ideal O) (v : Tuple ι) :
    profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v=
      profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ 1 v*
        (if s∣finiteTupleProduct v then 1 else 0) := by
  simp only [profileCoefficient,one_dvd,ite_true,mul_one]


-- @@ L24-36 verbatim
theorem column_mask (S : Finset (Tuple ι)) (R : Ideal O) (ν : ι → Ideal O → ℂ)
    (Wslot : ι → ℝ → ℂ) (P : ι → ℝ) (W₁ W₂ : ℝ → ℂ)
    (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ s I : Ideal O) :
    finiteColumnCoefficient S
      (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s) I=
      finiteColumnCoefficient S
        (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ 1) I*
          (if s∣I then 1 else 0) := by
  unfold finiteColumnCoefficient
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro v hv
  rw [profile_mask,(Finset.mem_filter.mp hv).2]

 
-- @@ L38-44 verbatim
def maskedLiveProfile (B : Tuple ι) (C R s : Ideal O)
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O) :
    Tuple (liveIndices B) → ℂ :=
  profileCoefficient (R*C) (fun i : liveIndices B => ν i.val)
    (fun i => Wslot i.val) (fun i => P i.val) W₁ W₂ X₁ X₂ Y₁ Y₂
    (B₁*B (Sum.inr 0)) (B₂*B (Sum.inr 1)) s


-- @@ L46-67 verbatim
theorem original_masked_live_column (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (hS : ∀ i,∀ I∈S i,I≠0) (hp : ∀ i,∀ I∈S (Sum.inl i),Prime I)
    (C R s I : Ideal O) (hC : C≠0) (hI : I≠0) (hsc : IsCoprime s C)
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O) :
    (if IsCoprime C I then finiteColumnCoefficient (Fintype.piFinset S)
      (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s) (C*I) else 0)=
      ∑ B : actualAllocations S C,frozenCoefficient B C R ν Wslot P*
        finiteColumnCoefficient (liveBox S B (allocation_data S C B (Finset.mem_filter.mp B.property).1).1)
          (maskedLiveProfile B C R s ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂) I := by
  have he := original_source_punctured_column S hS hp C R 1 I hC hI (one_dvd C)
    ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂
  rw [column_mask,hsc.dvd_mul_left_iff]
  have hh := congrArg (fun z : ℂ => z*(if s∣I then 1 else 0)) he
  rw [Finset.sum_mul] at hh
  convert hh using 1
  · split_ifs <;> simp
  · apply Finset.sum_congr rfl
    intro B hB
    rw [maskedLiveProfile,column_mask]
    dsimp only [liveProfile]
    ring


-- @@ L69-69 verbatim
end SevenEighths.CenteredMomentAmplificationLiveMask


-- @@ L71-71 verbatim
end


-- @@ L73-73 verbatim
end OAI
