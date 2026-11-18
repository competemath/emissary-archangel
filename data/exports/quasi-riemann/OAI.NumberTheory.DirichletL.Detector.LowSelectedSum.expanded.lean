import OAI.NumberTheory.DirichletL.Detector.LowCompensation


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section

-- @@ L6-6 verbatim
open scoped Classical ContDiff

-- @@ L7-7 verbatim
open MeasureTheory CompletedGauss

-- @@ L8-8 verbatim
namespace SevenEighths.ProbePhysical

-- @@ L9-9 verbatim
open CanonicalQuadraticSieve RayFourExpansion

-- @@ L10-10 verbatim
local notation "O" => ActualEisensteinCubic.O

-- @@ L11-11 verbatim
local notation "Id" => Ideal O


-- @@ L13-28 verbatim
lemma lowSeparatedIntegrand_finite_sum {α : Type*} (F : Finset α) (c : α→ℂ)
    (C : CalibrationData) (W0 W1 Ω : ℝ→ℂ) (hW1 : HasCompactSupport W1) (hΩ : HasCompactSupport Ω)
    (X Y : ℝ) (hX : 0<X) (hY : 0<Y) (B : α→RayRing→O→ℂ) (v : ℝ) :
    (∑k∈F,c k*lowSeparatedIntegrand C W0 W1 Ω X Y (B k) v)=
      lowSeparatedIntegrand C W0 W1 Ω X Y (fun σ m=>∑k∈F,c k*B k σ m) v := by
  simp_rw [←lowSeparatedIntegrand_eq C W0 W1 Ω hW1 hΩ X Y hX hY]
  simp_rw [←tsum_mul_left]
  rw [←Summable.tsum_finsetSum (fun k _=>
    (lowRowMellinIntegrand_mul_summable C W0 W1 Ω hW1 hΩ X Y hX hY v
      (fun r=>B k (physicalIdealRay r.1) r.2)).mul_left (c k))]
  apply tsum_congr
  intro r
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  ring


-- @@ L30-42 verbatim
lemma lowSeparatedIntegral_finite_sum {α : Type*} (F : Finset α) (c : α→ℂ)
    (C : CalibrationData) (W0 W1 Ω : ℝ→ℂ)
    (a0 b0 : ℝ) (ha0 : 0<a0) (hW0 : Function.support W0⊆Set.Icc a0 b0)
    (hWs : ContDiff ℝ ∞ W0) (hW1 : HasCompactSupport W1)
    (hΩ : HasCompactSupport Ω) (hΩ0 : Ω 0=0)
    (X Y : ℝ) (hX : 0<X) (hY : 0<Y) (B : α→RayRing→O→ℂ) :
    (∑k∈F,c k*∫v : ℝ,lowSeparatedIntegrand C W0 W1 Ω X Y (B k) v)=
      ∫v : ℝ,lowSeparatedIntegrand C W0 W1 Ω X Y (fun σ m=>∑k∈F,c k*B k σ m) v := by
  simp_rw [←integral_const_mul]
  rw [←integral_finsetSum F (fun k _=>(lowSeparatedIntegrand_integrable C W0 W1 Ω
    a0 b0 ha0 hW0 hWs hW1 hΩ hΩ0 X Y hX hY (B k)).const_mul (c k))]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun v=>lowSeparatedIntegrand_finite_sum F c C W0 W1 Ω hW1 hΩ X Y hX hY B v)


-- @@ L44-47 verbatim
def lowSelectedInverseRow {α : Type*} (F : Finset α) (c : α→ℂ)
    (η : HeckeFamily.Character) (S : Finset Id) (hS : ∀P∈S,P.IsMaximal)
    (D : α→Id) (T t : ℝ) (σ : RayRing) (m : O) : ℂ :=
  ∑k∈F,c k*lowMarkedInverseRow η S hS (D k) T t σ m


-- @@ L49-66 verbatim
lemma lowSelectedInverseRow_correction {α : Type*} (F : Finset α) (c : α→ℂ)
    (η : HeckeFamily.Character) (S : Finset Id) (hS : ∀P∈S,P.IsMaximal)
    (D : α→Id) (T t : ℝ) (σ : RayRing) (m : O) :
    lowSelectedInverseRow F c η S hS D T t σ m=
      ∑χ : RayCharacter,ProbeCompleted.correctionCoeff χ*
        ∑k∈F,c k*InverseMoment.markedCompletedT
          (CanonicalRowCompletion.rowTwist (physicalRayPeriodicBase η S hS σ χ)
            (calibrationForSet S hS).generator 1 m)
          (CompletedHeight.normTwistedSource gaussianFixedWindow t) T
          (fun A=>if D k∣A then (1:ℂ) else 0) := by
  unfold lowSelectedInverseRow lowMarkedInverseRow
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro χ hχ
  apply Finset.sum_congr rfl
  intro k hk
  ring


-- @@ L68-68 verbatim
end SevenEighths.ProbePhysical

-- @@ L69-69 verbatim
end


-- @@ L71-71 verbatim
end OAI
