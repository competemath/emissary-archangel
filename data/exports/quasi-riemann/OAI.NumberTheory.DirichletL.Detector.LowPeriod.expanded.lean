import OAI.NumberTheory.DirichletL.Detector.LowRow
import OAI.NumberTheory.DirichletL.Detector.PhysicalAnalytic


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
noncomputable section

-- @@ L7-7 verbatim
open scoped Classical

-- @@ L8-8 verbatim
namespace SevenEighths.ProbePhysical

-- @@ L9-9 verbatim
open ProbeRow CanonicalRowCompletion CanonicalQuadraticSieve CompletedGauss

-- @@ L10-10 verbatim
open RayFourExpansion InitialMeanSquare SecondPassArithmetic CanonicalCoefficientClass

-- @@ L11-11 verbatim
local notation "O" => ActualEisensteinCubic.O

-- @@ L12-12 verbatim
local notation "Id" => Ideal O

-- @@ L13-13 verbatim
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda


-- @@ L15-16 verbatim
def calibrationRowModulus (C : CalibrationData) (B : O) (D : GoodMaskRowData B 1 C.generator) : Id :=
  1*Ideal.span {B}*Ideal.span {(72:O)}*Ideal.span {D.numeratorGood}


-- @@ L18-20 verbatim
def periodicCalibrationXi (C : CalibrationData) (B : O) (D : GoodMaskRowData B 1 C.generator) : O→*ℂ :=
  C.residueMonoid*actualPeriodicRow 1 B D.numeratorUnit D.numeratorLambda D.numeratorTwo
    D.numeratorGood D.numeratorSupported


-- @@ L22-30 verbatim
lemma calibrationRowModulus_ne_zero (C : CalibrationData) (B : O) (hB : B≠0)
    (D : GoodMaskRowData B 1 C.generator) : calibrationRowModulus C B D≠0 := by
  unfold calibrationRowModulus
  apply mul_ne_zero
  · apply mul_ne_zero
    · exact mul_ne_zero one_ne_zero (Ideal.span_singleton_eq_bot.not.mpr hB)
    · apply Ideal.span_singleton_eq_bot.not.mpr
      norm_num
  · exact D.numeratorSupported.1


-- @@ L32-36 verbatim
lemma periodicCalibrationXi_norm (C : CalibrationData) (B : O)
    (D : GoodMaskRowData B 1 C.generator) (a : O) : ‖periodicCalibrationXi C B D a‖≤1 := by
  rw [periodicCalibrationXi,MonoidHom.mul_apply,norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) (C.residueMonoid_norm_le_one a)).trans (actualPeriodicRow_norm 1 (fun _=>by simp) B D.numeratorUnit D.numeratorLambda D.numeratorTwo
      D.numeratorGood D.numeratorSupported a)


-- @@ L38-48 verbatim
lemma periodicCalibrationXi_periodic (C : CalibrationData) (B : O)
    (D : GoodMaskRowData B 1 C.generator) :
    FactorsModulo (Ideal.span {C.generator}*calibrationRowModulus C B D) (periodicCalibrationXi C B D) := by
  have hp := actualPeriodicRow_periodic (1:O→*ℂ) 1 (fun _ _ _=>rfl)
    B D.numeratorUnit D.numeratorLambda D.numeratorTwo D.numeratorGood D.numeratorSupported
  intro x y hxy
  change C.residueMonoid x*_ = C.residueMonoid y*_
  congr 1
  · apply congrArg C.residue
    exact Ideal.Quotient.eq.mpr (Ideal.mul_le_left hxy)
  · exact hp x y (Ideal.mul_le_right hxy)


-- @@ L50-63 verbatim
lemma periodicCalibrationXi_eq_primary (C : CalibrationData) (B : O)
    (D : GoodMaskRowData B 1 C.generator) (hBL : λ₀∣B) (hB2 : (2:O)∣B)
    (n : O) (hn : Supported (Ideal.span {n})) (hpn : λ₀^2∣n-1) (hc : IsCoprime B n) :
    periodicCalibrationXi C B D n=C.Xi n := by
  have he := rowTwist_eq_actualPeriodicRow_primary (1:O→*ℂ) B 1 C.generator hBL hB2
    D.numeratorUnit D.numeratorLambda D.numeratorTwo D.numeratorGood D.numeratorSupported
    D.numeratorPrimary D.numeratorFactor n hpn
  rw [rowTwist_extract_sixth_mask _ _ _ _ _ hn] at he
  have hmask : coprimalityMask B n=(1:ℂ) := by
    change (if IsCoprime B n then (1:ℂ) else 0)=1
    rw [ite_eq_left hc]
  simp only [MonoidHom.one_apply,hmask,one_mul,one_pow] at he
  change C.residueMonoid n*_ = C.residueMonoid n*idealRowHom C.generator (Ideal.span {n})
  rw [←he]


-- @@ L65-68 verbatim
def lowPeriodicBase (η : HeckeFamily.Character) (C : CalibrationData) (B : O)
    (D : GoodMaskRowData B 1 C.generator) (s : O) (hs : Supported (Ideal.span {s}))
    (χ : RayCharacter) : O→*ℂ :=
  rayMonoid χ*targetMonoid η*conjugateMonoid (periodicCalibrationXi C B D)*reciprocityPhaseMonoid s hs


-- @@ L70-72 verbatim
def lowBaseModulus (η : HeckeFamily.Character) (C : CalibrationData) (B : O)
    (D : GoodMaskRowData B 1 C.generator) : Id :=
  η.modulus*(Ideal.span {C.generator}*calibrationRowModulus C B D)*Ideal.span {(4:O)}


-- @@ L74-81 verbatim
lemma lowBaseModulus_ne_zero (η : HeckeFamily.Character) (C : CalibrationData) (B : O) (hB : B≠0)
    (D : GoodMaskRowData B 1 C.generator) : lowBaseModulus η C B D≠0 := by
  unfold lowBaseModulus
  apply mul_ne_zero
  · exact mul_ne_zero η.modulus_ne_bot (mul_ne_zero (Ideal.span_singleton_eq_bot.not.mpr C.generator_ne_zero)
      (calibrationRowModulus_ne_zero C B hB D))
  · apply Ideal.span_singleton_eq_bot.not.mpr
    norm_num


-- @@ L83-97 verbatim
lemma lowPeriodicBase_periodic (η : HeckeFamily.Character) (C : CalibrationData) (B : O)
    (D : GoodMaskRowData B 1 C.generator) (s : O) (hs : Supported (Ideal.span {s})) (χ : RayCharacter) :
    FactorsModulo (lowBaseModulus η C B D) (lowPeriodicBase η C B D s hs χ) := by
  intro x y hxy
  have h4 : (4:O)∣x-y := Ideal.mem_span_singleton.mp (Ideal.mul_le_right hxy)
  have hη : targetMonoid η x=targetMonoid η y := by
    apply congrArg η.residue
    exact Ideal.Quotient.eq.mpr (Ideal.mul_le_left (Ideal.mul_le_left hxy))
  have hc := periodicCalibrationXi_periodic C B D x y (Ideal.mul_le_right (Ideal.mul_le_left hxy))
  change ((rayMonoid χ x*targetMonoid η x)*star (periodicCalibrationXi C B D x))*
      sexticReciprocityPhase s x=
    ((rayMonoid χ y*targetMonoid η y)*star (periodicCalibrationXi C B D y))*sexticReciprocityPhase s y
  rw [hη,hc,sexticReciprocityPhase_congr_right s x y h4]
  have hr : rayMonoid χ x=rayMonoid χ y := rayCharacter_eq_of_mod_four χ x y h4
  rw [hr]


-- @@ L99-105 verbatim
lemma lowPeriodicBase_norm (η : HeckeFamily.Character) (C : CalibrationData) (B : O)
    (D : GoodMaskRowData B 1 C.generator) (s : O) (hs : Supported (Ideal.span {s}))
    (χ : RayCharacter) (a : O) : ‖lowPeriodicBase η C B D s hs χ a‖≤1 := by
  have hr : ‖rayMonoid χ a‖≤1 := FiniteRayExpansion.norm_char_le_one χ _
  change ‖((rayMonoid χ a*targetMonoid η a)*star (periodicCalibrationXi C B D a))*sexticReciprocityPhase s a‖≤1
  simp only [norm_mul,norm_star]
  exact (mul_le_of_le_one_left (norm_nonneg _) ((mul_le_of_le_one_left (norm_nonneg _) ((mul_le_of_le_one_left (norm_nonneg _) hr).trans (targetMonoid_norm_le_one η a))).trans (periodicCalibrationXi_norm C B D a))).trans (sexticReciprocityPhase_norm s a)


-- @@ L107-115 verbatim
lemma lowPeriodicBase_eq_primary (η : HeckeFamily.Character) (C : CalibrationData) (B : O)
    (D : GoodMaskRowData B 1 C.generator) (hBL : λ₀∣B) (hB2 : (2:O)∣B)
    (s : O) (hs : Supported (Ideal.span {s})) (χ : RayCharacter)
    (n : O) (hn : Supported (Ideal.span {n})) (hpn : λ₀^2∣n-1) (hc : IsCoprime B n) :
    lowPeriodicBase η C B D s hs χ n=(rayMonoid χ*physicalRowBase η C.Xi s hs) n := by
  change ((rayMonoid χ n*targetMonoid η n)*star (periodicCalibrationXi C B D n))*sexticReciprocityPhase s n=
    rayMonoid χ n*((targetMonoid η n*star (C.Xi n))*sexticReciprocityPhase s n)
  rw [periodicCalibrationXi_eq_primary C B D hBL hB2 n hn hpn hc]
  ring


-- @@ L117-117 verbatim
end SevenEighths.ProbePhysical

-- @@ L118-118 verbatim
end


-- @@ L120-120 verbatim
end OAI
