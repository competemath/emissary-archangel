import OAI.NumberTheory.DirichletL.Detector.PhysicalRows


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section

-- @@ L6-6 verbatim
open scoped Classical

-- @@ L7-7 verbatim
namespace SevenEighths.ProbePhysical

-- @@ L8-8 verbatim
open ProbeCompleted ProbeRow CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion

-- @@ L9-9 verbatim
open RayFourExpansion CanonicalCoefficientClass

-- @@ L10-10 verbatim
local notation "O" => ActualEisensteinCubic.O

-- @@ L11-11 verbatim
local notation "Id" => Ideal O


-- @@ L13-13 verbatim
abbrev PhysicalRayElement := {s : O // Supported (Ideal.span {s})}


-- @@ L15-15 verbatim
def physicalRay (s : O) : RayRing := Ideal.Quotient.mk (Ideal.span {(4:O)}) s


-- @@ L17-22 verbatim
def physicalRayRepresentative (σ : RayRing) : PhysicalRayElement :=
  if h : ∃s : PhysicalRayElement,physicalRay s.val=σ then Classical.choose h
  else ⟨1,by
    simp [Supported,Ideal.span_singleton_one,←Ideal.one_eq_top]
    change (1:Id)≠0
    exact one_ne_zero⟩


-- @@ L24-28 verbatim
lemma physicalRayRepresentative_spec (s : PhysicalRayElement) :
    physicalRay (physicalRayRepresentative (physicalRay s.val)).val=physicalRay s.val := by
  have hh : ∃r : PhysicalRayElement,physicalRay r.val=physicalRay s.val := ⟨s,rfl⟩
  simp only [physicalRayRepresentative,dite_eq_left hh]
  exact Classical.choose_spec hh


-- @@ L30-40 verbatim
lemma rowCoefficient_congr_ray (η : HeckeFamily.Character) (Xi : O→*ℂ)
    (s r : PhysicalRayElement) (h : physicalRay s.val=physicalRay r.val) (m : O) :
    rowCoefficient η Xi s.val s.property m=rowCoefficient η Xi r.val r.property m := by
  apply MonoidHom.ext
  intro n
  rw [rowCoefficient_apply,rowCoefficient_apply]
  have hd : (4:O)∣s.val-r.val := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp h)
  have he : sexticReciprocityPhase s.val n=sexticReciprocityPhase r.val n := by
    unfold sexticReciprocityPhase
    rw [QuadraticGaussRay.residue_eq_of_four_dvd_sub s.val r.val hd]
  rw [he]


-- @@ L42-44 verbatim
def physicalRayRowMonoid (η : HeckeFamily.Character) (C : CalibrationData)
    (σ : RayRing) (m : O) : O→*ℂ :=
  rowCoefficient η C.Xi (physicalRayRepresentative σ).val (physicalRayRepresentative σ).property m


-- @@ L46-46 verbatim
def physicalIdealRay (s : {I : Id // Supported I}) : RayRing := physicalRay (primaryGenerator s.val)


-- @@ L48-53 verbatim
lemma physicalRowMonoid_eq_ray (η : HeckeFamily.Character) (C : CalibrationData) (r : PhysicalRowIndex) :
    physicalRowMonoid η C r=physicalRayRowMonoid η C (physicalIdealRay r.1) r.2 := by
  let s : PhysicalRayElement :=
    ⟨primaryGenerator r.1.val,(supported_span_primaryGenerator_iff r.1.val).mpr r.1.property⟩
  exact rowCoefficient_congr_ray η C.Xi s (physicalRayRepresentative (physicalRay s.val))
    (physicalRayRepresentative_spec s).symm r.2


-- @@ L55-57 verbatim
lemma physicalRayRowMonoid_norm (η : HeckeFamily.Character) (C : CalibrationData)
    (σ : RayRing) (m n : O) : ‖physicalRayRowMonoid η C σ m n‖≤1 :=
  rowCoefficient_norm_le_one η C.Xi C.Xi_norm_le_one _ _ m n


-- @@ L59-63 verbatim
def physicalRayPeriodicBase (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (σ : RayRing) (χ : RayCharacter) : O→*ℂ :=
  lowPeriodicBase η (calibrationForSet S hS) (calibrationForSet S hS).generator
    (calibrationLowData S hS) (physicalRayRepresentative σ).val
      (physicalRayRepresentative σ).property χ


-- @@ L65-73 verbatim
theorem physicalRayPeriodicBase_uniform (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) :
    ∃L : Id,L≠0 ∧ ∀σ : RayRing,∀χ : RayCharacter,
      FactorsModulo L (physicalRayPeriodicBase η S hS σ χ) ∧
      ∀n : O,‖physicalRayPeriodicBase η S hS σ χ n‖≤1 := by
  refine ⟨lowBaseModulus η (calibrationForSet S hS) (calibrationForSet S hS).generator (calibrationLowData S hS),
    lowBaseModulus_ne_zero η _ _ (calibrationForSet S hS).generator_ne_zero _,?_⟩
  intro σ χ
  exact ⟨lowPeriodicBase_periodic η _ _ _ _ _ χ,lowPeriodicBase_norm η _ _ _ _ _ χ⟩


-- @@ L75-86 verbatim
theorem physicalRayRow_eq_periodic_inverse (η : HeckeFamily.Character)
    (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S)
    (σ : RayRing) (m : O) (D : Id) (W : ℝ→ℂ) (hW : HasCompactSupport W)
    (T : ℝ) (hT : 0<T) :
    correctedCompletedT S D (physicalRayRowMonoid η (calibrationForSet S hS) σ m) W T=
      ∑χ : RayCharacter,correctionCoeff χ*
        InverseMoment.markedCompletedT
          (rowTwist (physicalRayPeriodicBase η S hS σ χ) (calibrationForSet S hS).generator 1 m)
          W T (fun A=>if D∣A then (1:ℂ) else 0) :=
  correctedPhysicalRow_eq_periodic_inverse η S hS hbad
    (physicalRayRepresentative σ).val (physicalRayRepresentative σ).property m D W hW T hT
      (calibrationLowData S hS)


-- @@ L88-88 verbatim
end SevenEighths.ProbePhysical

-- @@ L89-89 verbatim
end


-- @@ L91-91 verbatim
end OAI
