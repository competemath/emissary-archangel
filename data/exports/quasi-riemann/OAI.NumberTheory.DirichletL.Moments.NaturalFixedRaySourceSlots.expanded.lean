import OAI.NumberTheory.DirichletL.Moments.NaturalFixedRaySourceCharacters


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section

-- @@ L6-6 verbatim
open scoped Classical BigOperators


-- @@ L8-8 verbatim
namespace SevenEighths.CenteredMomentNaturalFixedRaySource

-- @@ L9-9 verbatim
open HeckeFamily HeckePrimeRay HeckePrimeAnnular ConcretePrimeRowBridge

-- @@ L10-10 verbatim
open CenteredMomentNaturalRowSource CenteredMomentSecondHeightFamily

-- @@ L11-11 verbatim
open CenteredMomentHeckeSlots CenteredMomentWholeSlotDeletion CenteredMomentPrimeSlot

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


-- @@ L18-23 verbatim
lemma averaged_sector_coefficient (χ η₀ : Character) (R : Ideal O) (hR : R≠0)
    (θ : RayQuotient.Characters M H) (I : Ideal O) :
    idealCoeff (twistedFamily M H hH ((excluded χ R).product η₀.inverse) θ) I=
      idealCoeff (excluded (χ.product (relativeCharacter M H hH η₀ θ)) R) I := by
  simp only [twistedFamily,relativeCharacter,idealCoeff_product,excluded_ideal _ R hR]
  split_ifs <;> ring


-- @@ L25-33 verbatim
lemma averaged_sector_polynomial (χ η₀ : Character) (R : Ideal O) (hR : R≠0)
    (θ : RayQuotient.Characters M H) (W : ℝ→ℂ) (b D σ t : ℝ) :
    primePolynomial (twistedFamily M H hH ((excluded χ R).product η₀.inverse) θ) W b D σ t=
      primePolynomial (excluded (χ.product (relativeCharacter M H hH η₀ θ)) R) W b D σ t := by
  unfold primePolynomial
  congr 1
  apply Finset.sum_congr rfl
  intro I hI
  rw [averaged_sector_coefficient M H hH χ η₀ R hR θ I]


-- @@ L35-48 verbatim
theorem natural_relative_slot {η : Character} {z : O} (F : NaturalRow η z)
    (η₀ : Character) (R : Ideal O) (hR : R≠0) (W : ℝ→ℂ) (b D σ t v : ℝ) (hD : 0<D) :
    normalizedSlot η (fixedBadMask*idealGenerator R) 1 z (primePool M H b D)
      (fun I=>idealCoeff η₀.inverse I*annularWeight W D σ v I) t D=
      (D:ℂ)^(Complex.I*t)*((RayQuotient.classNumber M H:ℂ)⁻¹*
        ∑θ : RayQuotient.Characters M H,
          primePolynomial (excluded (F.character.product (relativeCharacter M H hH η₀ θ)) R)
            W b D σ (t+v)) := by
  rw [relative_normalizedSlot_eq_ray M H η (excluded F.character R) η₀.inverse
    (fixedBadMask*idealGenerator R) 1 z
    (by simpa only [one_mul] using F.masked_element R hR) W b D σ t v hD,
    rayPrimePolynomial_eq_average M H hH]
  congr 2
  exact Finset.sum_congr rfl (fun θ _=>averaged_sector_polynomial M H hH F.character η₀ R hR θ W b D σ (t+v))


-- @@ L50-50 verbatim
end SevenEighths.CenteredMomentNaturalFixedRaySource


-- @@ L52-52 verbatim
end


-- @@ L54-54 verbatim
end OAI
