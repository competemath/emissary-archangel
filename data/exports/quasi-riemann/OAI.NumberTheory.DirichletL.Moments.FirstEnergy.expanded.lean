import OAI.NumberTheory.DirichletL.Moments.CanonicalFirst
import OAI.NumberTheory.DirichletL.Moments.SourceRow


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
noncomputable section

-- @@ L7-7 verbatim
open scoped BigOperators Classical SchwartzMap


-- @@ L9-9 verbatim
namespace SevenEighths.CenteredMomentFirstEnergy

-- @@ L10-10 verbatim
open CenteredMomentCanonicalFirst CenteredMomentSourceRow CenteredMomentRowNorm

-- @@ L11-11 verbatim
open CenteredMomentHeckeExpansion HeckeFamily ConcretePrimeRowBridge

-- @@ L12-12 verbatim
local notation "O" => ActualEisensteinCubic.O


-- @@ L14-34 verbatim
theorem finiteHeckeEnergy_reduced_poisson (η : Character) (m A : O) (t : ℝ)
    (hmLam : goodLambda∣m) (hm2 : (2:O)∣m)
    (S : Finset (Ideal O)) (c : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) :
    finiteHeckeEnergy η m A t S c W K =
      ∑ I : supportedColumns S,∑ J : supportedColumns S,
        ((c I*rowWeight η m A 1 t I)*star (c J*rowWeight η m A 1 t J))*
          reducedFirstSum I J (Finset.mem_filter.mp I.property).2
            (Finset.mem_filter.mp J.property).2 W K := by
  rw [finiteHeckeEnergy_eq η m A t hmLam hm2 S c W K,
    rowEnergy_expand Finset.univ (sourceGenerator S)
      (fun I : supportedColumns S => c I*rowWeight η m A 1 t I)
      (sourceGenerator_supported S) W K hK]
  apply Finset.sum_congr rfl
  intro I hI
  apply Finset.sum_congr rfl
  intro J hJ
  rw [sourceGenerator,sourceGenerator,
    primary_span_supported I (Finset.mem_filter.mp I.property).2,
    primary_span_supported J (Finset.mem_filter.mp J.property).2,
    canonical_pair_reduced_poisson]
  exact hK


-- @@ L36-36 verbatim
end SevenEighths.CenteredMomentFirstEnergy


-- @@ L38-38 verbatim
end


-- @@ L40-40 verbatim
end OAI
