import OAI.NumberTheory.DirichletL.Detector.GaussianDecomposition
import OAI.NumberTheory.DirichletL.Detector.LowCompletion


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
noncomputable section

-- @@ L7-7 verbatim
open scoped Classical

-- @@ L8-8 verbatim
namespace SevenEighths.ProbePhysical

-- @@ L9-9 verbatim
open ProbeRow ProbeCompleted CanonicalQuadraticSieve RayFourExpansion

-- @@ L10-10 verbatim
local notation "O" => ActualEisensteinCubic.O

-- @@ L11-11 verbatim
local notation "Id" => Ideal O


-- @@ L13-14 verbatim
def gaussianDyadicSchwartz (Z : ℝ) (hZ : 0<Z) (j : ℕ) : SchwartzMap ℝ ℂ :=
  (gaussianDyadicProfile_compact Z j).toSchwartzMap (gaussianDyadicProfile_contDiff Z hZ j)


-- @@ L16-38 verbatim
theorem physicalSpectralRow_eq_dyadic_inverse (η : HeckeFamily.Character)
    (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S)
    (s : O) (hs : Supported (Ideal.span {s})) (z : O) (D : Id)
    (Z : ℝ) (hZ : 0<Z) :
    verticalIntegral 4 (fun t=>(Z:ℂ)^t*Complex.exp (t^2)*
      spectralRow S D (rowCoefficient η (calibrationForSet S hS).Xi s hs z) t)=
      ∑'j : ℕ,∑χ : RayCharacter,correctionCoeff χ*
        InverseMoment.markedCompletedT
          (CanonicalRowCompletion.rowTwist
            (lowPeriodicBase η (calibrationForSet S hS) (calibrationForSet S hS).generator
              (calibrationLowData S hS) s hs χ)
            (calibrationForSet S hS).generator 1 z)
          (gaussianDyadicSchwartz Z hZ j) ((2:ℝ)^j)
          (fun A=>if D∣A then (1:ℂ) else 0) := by
  have hΨ := rowCoefficient_norm_le_one η (calibrationForSet S hS).Xi
    (calibrationForSet S hS).Xi_norm_le_one s hs z
  rw [spectralRow_eq_gaussianCompleted _ _ _ hΨ 4 (by norm_num) Z hZ,
    correctedGaussian_eq_tsum_dyadic _ _ _ hΨ Z hZ]
  apply tsum_congr
  intro j
  exact correctedPhysicalRow_eq_periodic_inverse η S hS hbad s hs z D
    (gaussianDyadicProfile Z j) (gaussianDyadicProfile_compact Z j) ((2:ℝ)^j)
    (by positivity) (calibrationLowData S hS)


-- @@ L40-40 verbatim
end SevenEighths.ProbePhysical

-- @@ L41-41 verbatim
end


-- @@ L43-43 verbatim
end OAI
