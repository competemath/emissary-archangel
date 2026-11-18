import OAI.NumberTheory.DirichletL.Moments.NaturalFixedRaySourceNaturalPrime


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section

-- @@ L6-6 verbatim
open scoped Classical BigOperators ContDiff Topology

-- @@ L7-7 verbatim
open Filter


-- @@ L9-9 verbatim
namespace SevenEighths.CenteredMomentNaturalFixedRaySource

-- @@ L10-10 verbatim
open HeckeFamily HeckeZeroSupremum CenteredMomentNaturalRowSource

-- @@ L11-11 verbatim
open CenteredExceptionalProfile CenteredMomentSecondHeightFamily

-- @@ L12-12 verbatim
open CenteredMomentWholeSlotDeletion CenteredMomentPrimeSlot

-- @@ L13-13 verbatim
local notation "O" => HeckeFamily.O

-- @@ L14-14 verbatim
variable (M : Ideal O) [NeZero M]

-- @@ L15-15 verbatim
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

-- @@ L16-16 verbatim
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)


-- @@ L18-43 verbatim
theorem natural_ray_slots_uniform (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hWs : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (Lmod Lslot loss lo hi κ : ℝ) (hLm : 0≤Lmod) (hLs : 0≤Lslot) (hloss : 0<loss)
    (hbeta : (51/100:ℝ)≤beta) (hκ : 2*beta-1≤κ) :
    ∃degree : ℕ,∃C : ℝ,0<C ∧ ∀η₀ : Character,∀ᶠZ : ℝ in atTop,
      ∀θ : RayQuotient.Characters M H,
      ∀P : ℝ,1≤P → P≤Z^Lslot → ∀η : Character,∀z : O,z≠0 →
      ∀F : NaturalRow η z,(F.character.modulus.absNorm:ℝ)≤Z^Lmod →
      ∀Q : Ideal O,Q≤M → ¬FixedInducingRow η (internalQ Q η₀) fixedBadMask 1 z →
      ∀σ t v : ℝ,lo≤σ → σ≤hi →
      ‖normalizedSlot η fixedBadMask 1 z (primePool M H b P)
        (fun I=>idealCoeff (relativeCharacter M H hH η₀ θ) I*
          HeckePrimeAnnular.annularWeight W P σ v I) t P‖^2≤
        C*(1+|t|+|v|)^degree*Z^loss*P^κ := by
  obtain ⟨degree,C,hC,hbound⟩:=natural_character_slot_bound M H hH W a b ha hWs hW
    Lmod Lslot loss lo hi κ hLm hLs hloss hbeta hκ
  refine ⟨degree,C,hC,?_⟩
  intro η₀
  have hall:=Filter.eventually_all.mpr (fun θ : RayQuotient.Characters M H=>
    hbound (relativeCharacter M H hH η₀ θ))
  filter_upwards [hall] with Z hz
  intro θ P hP hPcap η z hz0 F hcond Q hQM hex σ t v hσ hσhi
  exact hz θ P hP hPcap η z hz0 F hcond (internalQ Q η₀)
    (inf_le_left.trans hQM)
    (relativeCharacter_fixedQ M H hH η₀ θ (internalQ Q η₀) (inf_le_left.trans hQM) inf_le_right)
    hex σ t v hσ hσhi


-- @@ L45-45 verbatim
end SevenEighths.CenteredMomentNaturalFixedRaySource


-- @@ L47-47 verbatim
end


-- @@ L49-49 verbatim
end OAI
