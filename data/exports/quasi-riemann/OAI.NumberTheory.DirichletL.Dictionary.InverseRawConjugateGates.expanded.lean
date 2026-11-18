import OAI.NumberTheory.DirichletL.Dictionary.InverseRawInitialGates
import OAI.NumberTheory.DirichletL.Inversion.InitialProfileBounds


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
noncomputable section


-- @@ L8-8 verbatim
open scoped Classical BigOperators

-- @@ L9-9 verbatim
namespace SevenEighths.DetectorDictionaryInverseRawConjugateGates

-- @@ L10-10 verbatim
open CanonicalRowCompletion

-- @@ L11-11 verbatim
open HeckeFamily HeckeDyadic HeckeInverseAmplification InverseInitialConjugateEnergy

-- @@ L12-12 verbatim
open InverseInitialRayAttachment InverseInitialExcludedPeriod CanonicalCoefficientClass

-- @@ L13-13 verbatim
open DetectorDictionaryInverseRawInitialGates InverseInitialExcludedPool

-- @@ L14-14 verbatim
open InverseInitialExcludedOverlap InverseMoment InverseInitialProfile

-- @@ L15-15 verbatim
local notation "O"=>HeckeFamily.O


-- @@ L17-18 verbatim
theorem conjugate_element_apply (η:Ideal O→*ℂ)(x:O):
    elementCharacter (conjugateIdealCharacter η) x=star (elementCharacter η x):=rfl


-- @@ L20-24 verbatim
theorem conjugate_element_factors (η:Ideal O→*ℂ)(Q:Ideal O)
    (h:FactorsModulo Q (elementCharacter η)):
    FactorsModulo Q (elementCharacter (conjugateIdealCharacter η)):=by
  intro x y hxy
  exact congrArg star (h x y hxy)


-- @@ L26-28 verbatim
theorem conjugate_element_norm (η:Ideal O→*ℂ)(x:O):
    ‖elementCharacter (conjugateIdealCharacter η) x‖=‖elementCharacter η x‖:=by
  rw [conjugate_element_apply,norm_star]


-- @@ L30-41 verbatim
theorem raw_conjugate_base_gates (data:RowData):
    deletedPeriod (basePeriod data)≠0 ∧
    reflectionExcludedPrimes (deletedPeriod (basePeriod data))=excluded data ∧
    (∀x,‖elementCharacter (conjugateIdealCharacter
      (idealCoeff (deletedBase data)).toMonoidHom) x‖≤1) ∧
    FactorsModulo (fixedBaseConductor (deletedPeriod (basePeriod data)))
      (elementCharacter (conjugateIdealCharacter (idealCoeff (deletedBase data)).toMonoidHom)):=by
  obtain ⟨hq,he,hn,hp⟩:=raw_base_gates data
  refine ⟨hq,he,?_,conjugate_element_factors _ _ hp⟩
  intro x
  rw [conjugate_element_norm]
  exact hn x


-- @@ L43-49 verbatim
theorem raw_conjugate_zero_outside (data:RowData)(I:Ideal O)
    (hI:¬outside (excluded data) I):
    conjugateIdealCharacter (idealCoeff (deletedBase data)).toMonoidHom I=0:=by
  change star (idealCoeff (deletedBase data) I)=0
  rw [show idealCoeff (deletedBase data) I=0 from
    deleted_zero_outside (InverseInitialDetectorSource.baseCharacter data)
      (excluded data) (reflectionExcludedPrimes_prime (basePeriod data)) I hI,star_zero]


-- @@ L51-55 verbatim
theorem childLogTest_conjugate (W:ℝ→ℂ)(θ:ℝ):
    (fun x=>star (childLogTest W θ x))=childLogTest (fun x=>star (W x)) (-θ):=by
  funext x
  simp only [childLogTest,star_mul,SecondPassIntegration.logPhase_conjugate]
  ring


-- @@ L57-59 verbatim
theorem childLogTest_conjugate_norm (W:ℝ→ℂ)(θ x:ℝ):
    ‖childLogTest (fun x=>star (W x)) (-θ) x‖=‖W x‖:=by
  rw [InverseInitialProfileBounds.childLogTest_norm,norm_star]


-- @@ L61-66 verbatim
theorem childLogTest_physical_profiles (W:ℝ→ℂ)(θ:ℝ):
    (fun x=>star (childLogTest W θ x))=clippedSource (fun x=>star (W x)) 1 (-θ) ∧
    childLogTest W θ=clippedSource W 1 θ:=by
  rw [childLogTest_conjugate]
  exact ⟨InverseInitialProfileBounds.childLogTest_eq_clipped _ _,
    InverseInitialProfileBounds.childLogTest_eq_clipped _ _⟩


-- @@ L68-68 verbatim
end SevenEighths.DetectorDictionaryInverseRawConjugateGates


-- @@ L70-70 verbatim
end


-- @@ L72-72 verbatim
end OAI
