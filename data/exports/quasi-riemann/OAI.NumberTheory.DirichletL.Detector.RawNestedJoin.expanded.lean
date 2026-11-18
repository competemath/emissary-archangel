import OAI.NumberTheory.DirichletL.Detector.RawRadialJoin
import OAI.NumberTheory.DirichletL.Detector.OuterIndex


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
noncomputable section

-- @@ L7-7 verbatim
open scoped Classical

-- @@ L8-8 verbatim
open MeasureTheory

-- @@ L9-9 verbatim
namespace SevenEighths.ProbePhysical

-- @@ L10-10 verbatim
open CompletedGauss CanonicalQuadraticSieve ProbeRow CubicEisenstein

-- @@ L11-11 verbatim
local notation "O" => ActualEisensteinCubic.O


-- @@ L13-17 verbatim
def rawNestedPhysicalProbe (η : HeckeFamily.Character) (C : CalibrationData)
    (D : Ideal O) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z ξ υ : ℝ) : ℂ :=
  ∑'K : SourceOuter C.excluded,verticalIntegral υ (fun w=>verticalIntegral 4 (fun t=>
    ∑'IJ : CompletedPair,verticalIntegral ξ (fun z=>∑'H : NonzeroFrequency,
      rawPhysicalMellinTerm η C C.excluded D IJ.1 IJ.2 K.val K.property.1 W0 W1 X Y Z H.val t w z)))


-- @@ L19-41 verbatim
theorem nestedMellinPhysicalProbe_eq_raw (η : HeckeFamily.Character) (C : CalibrationData)
    (D : Ideal O) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z ξ υ : ℝ) :
    nestedMellinPhysicalProbe η C D W0 W1 X Y Z ξ υ=
      rawNestedPhysicalProbe η C D W0 W1 X Y Z ξ υ := by
  unfold nestedMellinPhysicalProbe rawNestedPhysicalProbe
  rw [sourceOuter_tsum]
  apply tsum_congr
  intro K
  dsimp only
  simp_rw [rawPhysicalMellinTerm_radial_join,tsum_mul_left]
  apply congrArg (verticalIntegral υ)
  funext w
  unfold rawRadialOuterFactor
  simp only [fullIdealWeight,ite_eq_right K.property.1.1]
  unfold verticalIntegral
  simp_rw [mul_assoc,integral_const_mul]
  simp only [Complex.ofReal_natCast]
  ring_nf
  congr 1
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro a
  ring_nf


-- @@ L43-43 verbatim
end SevenEighths.ProbePhysical

-- @@ L44-44 verbatim
end


-- @@ L46-46 verbatim
end OAI
