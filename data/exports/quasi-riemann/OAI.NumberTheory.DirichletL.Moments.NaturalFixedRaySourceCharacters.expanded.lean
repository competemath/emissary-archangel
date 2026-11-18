import OAI.NumberTheory.DirichletL.Moments.NaturalRowSourceDictionary
import OAI.NumberTheory.DirichletL.Moments.DetectorDictionaryRelativeSlots
import OAI.NumberTheory.DirichletL.Moments.FixedRayInducingTransport
import OAI.NumberTheory.DirichletL.Hecke.PrimeScale


-- @@ L6-6 verbatim
namespace OAI


-- @@ L8-8 verbatim
noncomputable section

-- @@ L9-9 verbatim
open scoped Classical BigOperators


-- @@ L11-11 verbatim
namespace SevenEighths.CenteredMomentNaturalFixedRaySource

-- @@ L12-12 verbatim
open HeckeFamily HeckeRowClosure ConcretePrimeRowBridge CanonicalRowCompletion

-- @@ L13-13 verbatim
open CenteredMomentNaturalRowSource CenteredMomentSecondHeightFamily

-- @@ L14-14 verbatim
open CenteredMomentFixedRayInducingTransport CenteredMomentFixedRowMask CenteredExceptionalProfile

-- @@ L15-15 verbatim
local notation "O" => HeckeFamily.O

-- @@ L16-16 verbatim
variable (M : Ideal O) [NeZero M]

-- @@ L17-17 verbatim
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

-- @@ L18-18 verbatim
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)


-- @@ L20-21 verbatim
def relativeCharacter (η₀ : Character) (θ : RayQuotient.Characters M H) : Character :=
  (HeckeRayQuotient.character M H hH θ).product η₀.inverse


-- @@ L23-26 verbatim
lemma relativeCharacter_ideal (η₀ : Character) (θ : RayQuotient.Characters M H) (I : Ideal O) :
    idealCoeff (relativeCharacter M H hH η₀ θ) I=
      idealCoeff (HeckeRayQuotient.character M H hH θ) I*idealCoeff η₀.inverse I :=
  idealCoeff_product _ _ _


-- @@ L28-29 verbatim
lemma relativeCharacter_norm (η₀ : Character) (θ : RayQuotient.Characters M H) (I : Ideal O) :
    ‖idealCoeff (relativeCharacter M H hH η₀ θ) I‖≤1 := idealCoeff_norm_le_one _ _


-- @@ L31-33 verbatim
lemma relativeCharacter_modulus (η₀ : Character) (θ : RayQuotient.Characters M H) :
    (relativeCharacter M H hH η₀ θ).modulus.absNorm≤M.absNorm*η₀.modulus.absNorm :=
  HeckePrimeScale.product_modulus_bound _ _


-- @@ L35-37 verbatim
lemma relativeCharacter_fixedQ (η₀ : Character) (θ : RayQuotient.Characters M H)
    (Q : Ideal O) (hQM : Q≤M) (hQη : Q≤η₀.modulus) :
    Q≤(relativeCharacter M H hH η₀ θ).modulus := le_inf hQM hQη


-- @@ L39-42 verbatim
lemma excluded_product_ideal (χ ν : Character) (R : Ideal O) (hR : R≠0) (I : Ideal O) :
    idealCoeff (excluded χ R) I*idealCoeff ν I=idealCoeff (excluded (χ.product ν) R) I := by
  rw [excluded_ideal χ R hR,excluded_ideal (χ.product ν) R hR,idealCoeff_product]
  split_ifs <;> simp


-- @@ L44-50 verbatim
lemma sector_element {η : Character} {z : O} (F : NaturalRow η z)
    (η₀ : Character) (θ : RayQuotient.Characters M H) (n : O) :
    elementCoeff (F.character.product (relativeCharacter M H hH η₀ θ)) n=
      rowTwist (elementHom (η.product (relativeCharacter M H hH η₀ θ))) fixedBadMask 1 z n := by
  simpa only [one_mul] using CenteredMomentDetectorDictionary.product_row_presentation η F.character
    (relativeCharacter M H hH η₀ θ) fixedBadMask 1 z
    (by simpa only [one_mul] using F.element) n


-- @@ L52-63 verbatim
theorem sector_fixedQ_iff (η η₀ : Character) (θ : RayQuotient.Characters M H)
    (Q R : Ideal O) (z : O) (hQM : Q≤M) (hQη : Q≤η₀.modulus)
    (hR : R≠0) (hz : z≠0) :
    FixedInducingRow (η.product (relativeCharacter M H hH η₀ θ)) Q
      (fixedBadMask*idealGenerator R) 1 z ↔
    FixedInducingRow η Q (fixedBadMask*idealGenerator R) 1 z :=
  fixedInducingRow_product_iff η (relativeCharacter M H hH η₀ θ) Q
    (fixedBadMask*idealGenerator R) 1 z
    (relativeCharacter_fixedQ M H hH η₀ θ Q hQM hQη)
    (mul_ne_zero fixedBadMask_ne_zero (idealGenerator_ne_zero R hR)) one_ne_zero hz
    ((dvd_mul_right _ _).trans (dvd_mul_right _ _))
    ((dvd_mul_left _ _).trans (dvd_mul_right _ _))


-- @@ L65-78 verbatim
theorem sector_nonprincipal {η : Character} {z : O} (F : NaturalRow η z)
    (η₀ : Character) (θ : RayQuotient.Characters M H) (Q R : Ideal O)
    (hQM : Q≤M) (hQη : Q≤η₀.modulus) (hR : R≠0) (hz : z≠0)
    (hex : ¬FixedInducingRow η Q (fixedBadMask*idealGenerator R) 1 z) :
    (F.character.product (relativeCharacter M H hH η₀ θ)).residue≠1 := by
  have hbase : ¬FixedInducingRow η Q fixedBadMask 1 z := by
    intro h
    exact hex ((fixedInducingRow_mul_mask_iff η Q fixedBadMask (idealGenerator R) 1 z
      fixedBadMask_ne_zero (idealGenerator_ne_zero R hR) one_ne_zero hz
      (dvd_mul_right _ _) (dvd_mul_left _ _)).mpr h)
  exact CenteredMomentRayNonprincipal.actual_row_twist_nonprincipal η F.character
    (relativeCharacter M H hH η₀ θ) Q fixedBadMask 1 z
    (by simpa only [one_mul] using F.element)
    (relativeCharacter_fixedQ M H hH η₀ θ Q hQM hQη) hbase


-- @@ L80-80 verbatim
end SevenEighths.CenteredMomentNaturalFixedRaySource


-- @@ L82-82 verbatim
end


-- @@ L84-84 verbatim
end OAI
