import OAI.NumberTheory.DirichletL.Moments.NaturalFixedRaySourceProduct


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section

-- @@ L6-6 verbatim
open scoped Classical BigOperators ComplexConjugate


-- @@ L8-8 verbatim
namespace SevenEighths.CenteredMomentNaturalFixedRaySource

-- @@ L9-9 verbatim
open HeckeFamily HeckePrimeAnnular ConcretePrimeRowBridge

-- @@ L10-10 verbatim
open CenteredMomentNaturalRowSource CenteredMomentSecondHeightFamily

-- @@ L11-11 verbatim
open CenteredMomentRetainedEnergy CenteredMomentHeckeSlots CenteredMomentPrimeSlot

-- @@ L12-12 verbatim
open CenteredMomentDetectorDictionary

-- @@ L13-13 verbatim
local notation "O" => HeckeFamily.O

-- @@ L14-14 verbatim
variable (M : Ideal O) [NeZero M]

-- @@ L15-15 verbatim
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

-- @@ L16-16 verbatim
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

-- @@ L17-17 verbatim
variable {ι : Type*} [Fintype ι] [DecidableEq ι]


-- @@ L19-41 verbatim
theorem natural_physical_product {η : Character} {z : O} (F : NaturalRow η z)
    (η₀ : Character) (R : Ideal O) (hR : R≠0) (W₁ W₂ : ℝ→ℂ)
    (V : ι→ℝ→ℂ) (b P : ι→ℝ) (external : ι→ℂ) (t X₁ X₂ : ℝ)
    (hX : 0≤X₁*X₂) (hP : ∀i,0<P i) :
    positiveSlotRow η (fixedBadMask*idealGenerator R) 1 z W₁ W₂
      (fun i=>primePool M H (b i) (P i))
      (fun i=>physicalSlotCoefficient η₀ (V i) (P i) (external i)) P t X₁ X₂=
      averageWeight (ι:=ι) M H*∑θ : ι→RayQuotient.Characters M H,
        sectorValue M H hH F.character η₀ R W₁ W₂ (fun i x=>conj (V i x)) b P
          (fun i=>1-(external i).re) (fun i=>-(external i).im) t X₁ X₂ θ := by
  have hslot (i : ι) : rowSlot η (fixedBadMask*idealGenerator R) 1 z
      (primePool M H (b i) (P i)) (physicalSlotCoefficient η₀ (V i) (P i) (external i)) t=
      rowSlot η (fixedBadMask*idealGenerator R) 1 z (primePool M H (b i) (P i))
        (fun I=>idealCoeff η₀.inverse I*annularWeight (fun x=>conj (V i x))
          (P i) (1-(external i).re) (-(external i).im) I) t := by
    unfold rowSlot
    apply Finset.sum_congr rfl
    intro I hI
    rw [physicalSlotCoefficient_annular η₀ (V i) (P i) (external i) I
      (Finset.mem_filter.mp hI).2.1.ne_zero (hP i)]
  simpa only [positiveSlotRow,hslot] using natural_relative_product M H hH F η₀ R hR W₁ W₂
    (fun i x=>conj (V i x)) b P (fun i=>1-(external i).re) (fun i=>-(external i).im)
    t X₁ X₂ hX hP


-- @@ L43-54 verbatim
theorem natural_physical_energy {η : Character} {z : O} (F : NaturalRow η z)
    (η₀ : Character) (R : Ideal O) (hR : R≠0) (W₁ W₂ : ℝ→ℂ)
    (V : ι→ℝ→ℂ) (b P : ι→ℝ) (external : ι→ℂ) (t X₁ X₂ : ℝ)
    (hX : 0≤X₁*X₂) (hP : ∀i,0<P i) :
    ‖positiveSlotRow η (fixedBadMask*idealGenerator R) 1 z W₁ W₂
      (fun i=>primePool M H (b i) (P i))
      (fun i=>physicalSlotCoefficient η₀ (V i) (P i) (external i)) P t X₁ X₂‖^2≤
      ∑θ : ι→RayQuotient.Characters M H,‖averageWeight (ι:=ι) M H‖*
        ‖sectorValue M H hH F.character η₀ R W₁ W₂ (fun i x=>conj (V i x)) b P
          (fun i=>1-(external i).re) (fun i=>-(external i).im) t X₁ X₂ θ‖^2 := by
  rw [natural_physical_product M H hH F η₀ R hR W₁ W₂ V b P external t X₁ X₂ hX hP]
  exact sector_average_energy M H _


-- @@ L56-56 verbatim
end SevenEighths.CenteredMomentNaturalFixedRaySource


-- @@ L58-58 verbatim
end


-- @@ L60-60 verbatim
end OAI
