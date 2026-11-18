import OAI.NumberTheory.DirichletL.Detector.RawMellinTerm
import OAI.NumberTheory.DirichletL.Detector.NestedMellin


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
open CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion ProbeCompleted ProbeRow CubicEisenstein

-- @@ L11-11 verbatim
open EisensteinSchwartzPoisson

-- @@ L12-12 verbatim
local notation "O" => ActualEisensteinCubic.O


-- @@ L14-18 verbatim
lemma verticalIntegral_const_mul (σ : ℝ) (F : ℂ→ℂ) (c : ℂ) :
    verticalIntegral σ (fun z=>c*F z)=c*verticalIntegral σ F := by
  unfold verticalIntegral
  rw [integral_const_mul]
  ring


-- @@ L20-25 verbatim
def rawRadialOuterFactor (C : CalibrationData) (K : Ideal O)
    (W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (t w : ℂ) : ℂ :=
  (Y:ℂ)^(w-1)*fullIdealWeight w K*mellin W1 w*
    (idealRowHom C.generator K /
      (C.tau*C.residueMonoid (primaryGenerator K)*(Real.sqrt (elementNorm C.generator*(Ideal.absNorm K:ℝ)*X):ℂ)))*
    (Real.sqrt (Ideal.absNorm K):ℂ)⁻¹*((Z:ℂ)^t*Complex.exp (t^2))


-- @@ L27-79 verbatim
lemma rawPhysicalMellinTerm_radial_join (η : HeckeFamily.Character) (C : CalibrationData)
    (S : Finset (Ideal O)) (D I J K : Ideal O) (hK : Supported K)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z ξ : ℝ) (t w : ℂ) :
    verticalIntegral ξ (fun z=>∑'H : NonzeroFrequency,
      rawPhysicalMellinTerm η C S D I J K hK W0 W1 X Y Z H.val t w z)=
    rawRadialOuterFactor C K W1 X Y Z t w*
      radialMellinSpectralTerm η C S D (primaryGenerator K)
        ((supported_span_primaryGenerator_iff K).mpr hK) W0
          (elementNorm C.generator*(Ideal.absNorm K:ℝ)*X) ξ t I J := by
  have hgen := (primaryGenerator_spec K (supported_primaryGenerator_ne_zero K hK)).1
  have hn : elementNorm (primaryGenerator K)=(Ideal.absNorm K:ℝ) := by
    unfold elementNorm
    rw [hgen]
  unfold rawPhysicalMellinTerm physicalMellinCoefficientTerm radialMellinSpectralTerm
  split_ifs with hA
  · dsimp only
    simp only [hn,hgen]
    let c := rawRadialOuterFactor C K W1 X Y Z t w *
      (spectralSummand S D (baseRowCoefficient η C.Xi (primaryGenerator K)
        ((supported_span_primaryGenerator_iff K).mpr hK)) t I J *
        ((elementNorm C.generator*(Ideal.absNorm K:ℝ)*X/elementNorm (C.generator*completedIndex I J):ℝ):ℂ))
    have hp (z : ℂ) (H : NonzeroFrequency) :
        idealRowHom C.generator K /
          (C.tau*C.residueMonoid (primaryGenerator K)*
            (Real.sqrt (elementNorm C.generator*(Ideal.absNorm K:ℝ)*X):ℂ)) *
          (Real.sqrt (Ideal.absNorm K):ℂ)⁻¹ *
          spectralSummand S D (baseRowCoefficient η C.Xi (primaryGenerator K)
            ((supported_span_primaryGenerator_iff K).mpr hK)) t I J *
          ((elementNorm C.generator*(Ideal.absNorm K:ℝ)*X/elementNorm (C.generator*completedIndex I J):ℝ):ℂ) *
          actualCongruenceCoefficient C (completedIndex I J) (primaryGenerator K) hA H.val *
          ((elementNorm C.generator*(Ideal.absNorm K:ℝ)*X*elementNorm H.val /
            elementNorm ((C.generator*completedIndex I J)*primaryGenerator K):ℝ):ℂ)^(-z) *
          fullIdealWeight w K*(Y:ℂ)^(w-1)*(Z:ℂ)^t*Complex.exp (t^2)*
          mellin (paperRadialFourier W0) z*mellin W1 w =
        c*(actualCongruenceCoefficient C (completedIndex I J) (primaryGenerator K) hA H.val *
          ((elementNorm C.generator*(Ideal.absNorm K:ℝ)*X*elementNorm H.val /
            elementNorm ((C.generator*completedIndex I J)*primaryGenerator K):ℝ):ℂ)^(-z)*
          mellin (paperRadialFourier W0) z) := by
      dsimp only [c,rawRadialOuterFactor]
      ring
    simp only [Complex.ofReal_mul,Complex.ofReal_div] at hp ⊢
    simp_rw [hp,tsum_mul_left]
    rw [verticalIntegral_const_mul]
    dsimp only [c]
    simp only [Complex.ofReal_mul,Complex.ofReal_div]
    ring_nf
    congr 1
    apply congrArg (verticalIntegral ξ)
    funext z
    apply tsum_congr
    intro H
    congr 1 ; congr 1 ; ring_nf
  · simp only [zero_mul,tsum_zero,verticalIntegral,integral_zero,mul_zero]


-- @@ L81-81 verbatim
end SevenEighths.ProbePhysical

-- @@ L82-82 verbatim
end


-- @@ L84-84 verbatim
end OAI
