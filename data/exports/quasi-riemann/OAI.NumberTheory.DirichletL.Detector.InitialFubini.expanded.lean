import OAI.NumberTheory.DirichletL.Detector.InitialIntegral
import OAI.NumberTheory.DirichletL.Detector.InitialScales


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
noncomputable section

-- @@ L7-7 verbatim
open MeasureTheory

-- @@ L8-8 verbatim
namespace SevenEighths.ProbePhysical

-- @@ L9-9 verbatim
open ProbeMellinBoundary

-- @@ L10-10 verbatim
local notation "O" => ActualEisensteinCubic.O


-- @@ L12-27 verbatim
theorem source_initial_integral_tsum (S : Finset (Ideal O)) (D : Ideal O) (η : HeckeFamily.Character)
    (mask : NonzeroFrequency→ℂ) (hm : ∀H,‖mask H‖≤1)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ)
    (ha0 : 0<a0) (ha1 : 0<a1) (hW0 : Function.support W0⊆Set.Icc a0 b0)
    (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z)
    (σ υ ξ : ℝ) (hσ : 3/2<σ) (hυ : 2<υ) (hξ : 1<ξ) :
    (∫p : HeightSpace,∑'i : FullHighIndex, initialHighOnLines S D η mask σ υ ξ i p*
      sourceMellinWeight W0 W1 X Y Z ((σ:ℂ)+p.1.1*Complex.I)
        ((υ:ℂ)+p.2*Complex.I) ((ξ:ℂ)+p.1.2*Complex.I) ∂heightMeasure)=
      ∑'i : FullHighIndex, ∫p : HeightSpace,initialHighOnLines S D η mask σ υ ξ i p*
        sourceMellinWeight W0 W1 X Y Z ((σ:ℂ)+p.1.1*Complex.I)
          ((υ:ℂ)+p.2*Complex.I) ((ξ:ℂ)+p.1.2*Complex.I) ∂heightMeasure := by
  exact initialHigh_integral_tsum_test S D η mask hm σ υ ξ hσ hυ hξ _
    (sourceMellinWeight_initial_integrable W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
      X Y Z hX hY hZ σ ξ υ (by linarith))


-- @@ L29-29 verbatim
end SevenEighths.ProbePhysical

-- @@ L30-30 verbatim
end


-- @@ L32-32 verbatim
end OAI
