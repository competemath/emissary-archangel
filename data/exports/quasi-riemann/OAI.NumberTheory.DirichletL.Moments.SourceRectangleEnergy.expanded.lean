import OAI.NumberTheory.DirichletL.Moments.SourceRectangleMask
import OAI.NumberTheory.DirichletL.Moments.SecondHeightFamily
import OAI.NumberTheory.DirichletL.Moments.RestrictedSource


-- @@ L5-5 verbatim
namespace OAI


-- @@ L7-7 verbatim
noncomputable section

-- @@ L8-8 verbatim
open scoped BigOperators Classical SchwartzMap


-- @@ L10-10 verbatim
namespace SevenEighths.CenteredMomentSourceRectangleEnergy

-- @@ L11-11 verbatim
open HeckeFamily CanonicalRowCompletion CanonicalQuadraticSieve ConcretePrimeRowBridge

-- @@ L12-12 verbatim
open CenteredMomentSourceRow CenteredMomentHeckeExpansion CenteredMomentSecondHeightFamily

-- @@ L13-13 verbatim
open CenteredMomentRestrictedDomain CenteredMomentRestrictedSource CenteredMomentRestrictedEnergy

-- @@ L14-14 verbatim
open CenteredMomentRowNorm CenteredMomentHeckeColumnWindow CenteredMomentSourceRectangle

-- @@ L15-15 verbatim
open CenteredMomentSourceRectangleMask CenteredMomentSourceMass CenteredMomentSourceProfileMass

-- @@ L16-16 verbatim
open CenteredMomentDivisorRowEnergy CenteredMomentDivisorRetained

-- @@ L17-17 verbatim
local notation "O" => ActualEisensteinCubic.O


-- @@ L19-36 verbatim
theorem height_source_row (η : Character) (t : ℝ) (S : Finset (Ideal O))
    (β : Ideal O→ℂ) (z : O) :
    rowPolynomial Finset.univ (sourceGenerator S)
      (fun I : supportedColumns S=>β I*heightCoeff η t I) z=
      ∑ I∈S,β I*rowWeight η fixedBadMask 1 z t I := by
  rw [source_rowPolynomial S (fun I=>β I*heightCoeff η t I) z]
  calc
    _ = ∑ I∈supportedColumns S,β I*rowWeight η fixedBadMask 1 z t I := by
      apply Finset.sum_congr rfl
      intro I hI
      rw [heightCoeff_eq_fixed_rowWeight η t I (Finset.mem_filter.mp hI).2,
        rowWeight_split η fixedBadMask 1 z t I]
      ring
    _ = _ := Finset.sum_filter_of_ne (fun I hI hn => by
      by_contra hs
      apply hn
      rw [rowWeight_zero_of_not_supported η fixedBadMask 1 z t
        (dvd_mul_right _ _) (dvd_mul_left _ _) I hs,mul_zero])


-- @@ L38-61 verbatim
theorem source_restricted_energy_eq_rectangle {ι : Type*} [Fintype ι] [DecidableEq ι]
    (η : Character) (t : ℝ) (keep : O→Prop)
    (slots : ι→Finset (Ideal O)) (S₁ S₂ : Finset (Ideal O))
    (R L : Ideal O) (ν : ι→Ideal O→ℂ) (Wslot : ι→ℝ→ℂ) (P : ι→ℝ)
    (W₁ W₂ : ℝ→ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O)
    (h₁ : PlainCoverage S₁ W₁ B₁ X₁ Y₁) (h₂ : PlainCoverage S₂ W₂ B₂ X₂ Y₂)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    sourceRestrictedEnergy keep (finiteColumns (tuplePool slots S₁ S₂))
      (finiteColumnCoefficient (tuplePool slots S₁ S₂)
        (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ L))
      (heightCoeff η t) W K=
      ∑' z : O,if keep z then
        ‖maskedRectangle η (fixedBadMask*idealGenerator R) 1 z t slots
          (fun i I=>ν i I*Wslot i ((Ideal.absNorm I:ℝ)/P i)) L W₁ W₂
          (X₁/Ideal.absNorm B₁) (X₂/Ideal.absNorm B₂)
          (Y₁/Ideal.absNorm B₁) (Y₂/Ideal.absNorm B₂)‖^2*
        (W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re else 0 := by
  unfold sourceRestrictedEnergy restrictedEnergy
  apply tsum_congr
  intro z
  rw [height_source_row]
  rw [CenteredMomentSourceRectangleMask.source_polynomial_eq_maskedRectangle
    η fixedBadMask 1 z t (dvd_mul_right _ _) (dvd_mul_left _ _)
    slots S₁ S₂ R L ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ h₁ h₂]


-- @@ L63-63 verbatim
end SevenEighths.CenteredMomentSourceRectangleEnergy


-- @@ L65-65 verbatim
end


-- @@ L67-67 verbatim
end OAI
