import OAI.NumberTheory.DirichletL.Moments.CommonHeightEnvelope
import OAI.NumberTheory.DirichletL.Moments.AllocatedNaturalSource
import OAI.NumberTheory.DirichletL.Moments.AmplificationFamilyEnergy


-- @@ L5-5 verbatim
namespace OAI


-- @@ L7-7 verbatim
noncomputable section

-- @@ L8-8 verbatim
open scoped Classical BigOperators SchwartzMap

-- @@ L9-9 verbatim
namespace SevenEighths.CenteredMomentSlotClassTransport

-- @@ L10-10 verbatim
open HeckeFamily CenteredMomentCommonRadialData CenteredMomentCommonHeightEnvelope

-- @@ L11-11 verbatim
open CenteredMomentAllocatedNaturalSource CenteredMomentCommonAllocationSum

-- @@ L12-12 verbatim
open CenteredMomentDivisorAllocation CenteredMomentDivisorRetained

-- @@ L13-13 verbatim
open CenteredMomentRetainedEnergy

-- @@ L14-14 verbatim
local notation "O"=>ActualEisensteinCubic.O

-- @@ L15-15 verbatim
variable {ι : Type*} [Fintype ι] [DecidableEq ι]


-- @@ L17-25 verbatim
omit [DecidableEq ι] in
theorem common_fixed_slot_coefficient (s : Input ι) (ν : ι→Character)
    (hν : ∀i I,s.ν i I=idealCoeff (ν i) I)
    (τ : Character) (v : ℝ) (C R : Ideal O) (B : actualAllocations s.pools C)
    (i : CenteredMomentCommonProfile.liveIndices B.val) (I : Ideal O) :
    (commonData (withHeight s τ v) C R B).coefficient i I=
      idealCoeff (ν i.val) I*s.W i.val ((I.absNorm:ℝ)/s.P i.val) := by
  change s.ν i.val I*s.W i.val ((I.absNorm:ℝ)/s.P i.val)=_
  rw [hν]


-- @@ L27-35 verbatim
omit [DecidableEq ι] in
theorem commonSlots_fixed_coefficient (s : Input ι) (ν : ι→Character)
    (hν : ∀i I,s.ν i I=idealCoeff (ν i) I)
    (τ : Character) (v : ℝ) (C : Ideal O) (B : actualAllocations s.pools C)
    (i : CenteredMomentCommonProfile.liveIndices B.val) (I : Ideal O) :
    (commonSlots (withHeight s τ v) C B).coefficient i I=
      idealCoeff (ν i.val) I*s.W i.val ((I.absNorm:ℝ)/s.P i.val) := by
  change s.ν i.val I*s.W i.val ((I.absNorm:ℝ)/s.P i.val)=_
  rw [hν]


-- @@ L37-47 verbatim
theorem allocated_fixed_character_gate (s : Input ι) (ν : ι→Character)
    (Q : Ideal O) (hQ : ∀i,Q≤(ν i).modulus)
    (τ : Character) (v : ℝ) (C R L : Ideal O) (B : actualAllocations s.pools C)
    (a : Allocation L (Finset.univ : Finset
      ((CenteredMomentCommonProfile.liveIndices B.val)⊕Fin 2)))
    (i : CenteredMomentDivisorRaw.liveIndices L a) :
    Q≤(ν i.val.val).modulus ∧
    (commonData (withHeight s τ v) C R B).slots i.val=s.slots i.val.val ∧
    (commonData (withHeight s τ v) C R B).P i.val=s.P i.val.val ∧
    (commonData (withHeight s τ v) C R B).W i.val=s.W i.val.val :=
  ⟨hQ _,rfl,rfl,rfl⟩


-- @@ L49-75 verbatim
theorem allocated_positive_fixed_characters (s : Input ι) (ν : ι→Character)
    (hν : ∀i I,s.ν i I=idealCoeff (ν i) I)
    (τ : Character) (v : ℝ) (C R L : Ideal O) (B : actualAllocations s.pools C)
    (a : Allocation L (Finset.univ : Finset
      ((CenteredMomentCommonProfile.liveIndices B.val)⊕Fin 2)))
    (z : O) (W₁ W₂ : ℝ→ℂ) (X₁ X₂ : ℝ) :
    let d:=commonData (withHeight s τ v) C R B
    allocatedPositiveRow d.η d.m d.A z d.t d.slots d.coefficient d.P L a W₁ W₂ X₁ X₂=
      retainedPositiveRow τ
        (CenteredMomentSecondHeightFamily.fixedBadMask*ConcretePrimeRowBridge.idealGenerator (R*C))
        1 z W₁ W₂
        (fun i : CenteredMomentDivisorRaw.liveIndices L a=>s.slots i.val.val)
        (fun i : CenteredMomentDivisorRaw.liveIndices L a=>fun I=>
          idealCoeff (ν i.val.val) I*s.W i.val.val ((I.absNorm:ℝ)/s.P i.val.val))
        (fun i : CenteredMomentDivisorRaw.liveIndices L a=>s.P i.val.val) v
        (X₁/Ideal.absNorm (CenteredMomentDivisorRectangle.selectedPlain L a 0))
        (X₂/Ideal.absNorm (CenteredMomentDivisorRectangle.selectedPlain L a 1)) := by
  dsimp only
  unfold allocatedPositiveRow
  have he : (fun i : CenteredMomentDivisorRaw.liveIndices L a=>
      (commonData (withHeight s τ v) C R B).coefficient i.val)=
    (fun i : CenteredMomentDivisorRaw.liveIndices L a=>fun I=>
      idealCoeff (ν i.val.val) I*s.W i.val.val ((I.absNorm:ℝ)/s.P i.val.val)) := by
    funext i I
    exact common_fixed_slot_coefficient s ν hν τ v C R B i.val I
  rw [he]
  rfl


-- @@ L77-77 verbatim
end SevenEighths.CenteredMomentSlotClassTransport


-- @@ L79-79 verbatim
end


-- @@ L81-81 verbatim
end OAI
