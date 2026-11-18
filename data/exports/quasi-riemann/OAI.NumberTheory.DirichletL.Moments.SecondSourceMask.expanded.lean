import OAI.NumberTheory.DirichletL.Moments.SecondSectorColumns
import OAI.NumberTheory.DirichletL.Moments.AmplificationLiveMask


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
noncomputable section

-- @@ L7-7 verbatim
open scoped BigOperators Classical


-- @@ L9-9 verbatim
namespace SevenEighths.CenteredMomentSecondSourceMask

-- @@ L10-10 verbatim
open CanonicalQuadraticSieve CenteredMomentSecondSectorColumns CenteredMomentFirstSectors

-- @@ L11-11 verbatim
open CenteredMomentSourceRow CenteredMomentSourceProfileMass CenteredMomentSourceMass

-- @@ L12-12 verbatim
open CenteredMomentAddedZeroUniform CenteredMomentAmplificationLiveMask

-- @@ L13-13 verbatim
open CenteredMomentCompleteCommon

-- @@ L14-14 verbatim
local notation "O" => ActualEisensteinCubic.O


-- @@ L16-25 verbatim
theorem divisor_dvd_common (C D a b s : Ideal O)
    (hC : C≠0) (hD : D≠0) (ha : a≠0) (hb : b≠0)
    (hCD : CompletedGauss.primeSupport C=CompletedGauss.primeSupport D)
    (hCa : IsCoprime C a) (hCb : IsCoprime C b) (hab : IsCoprime a b)
    (hsI : s∣C*a) (hsJ : s∣D*b) : s∣C ∧ s∣D := by
  have hDa := (coprime_of_same_support C D a hC hD ha hCD).mp hCa
  have hDb := (coprime_of_same_support C D b hC hD hb hCD).mp hCb
  have hsa : IsCoprime s a := ((hDa.symm.mul_right hab).of_isCoprime_of_dvd_right hsJ).symm
  have hsb : IsCoprime s b := ((hCb.symm.mul_right hab.symm).of_isCoprime_of_dvd_right hsI).symm
  exact ⟨hsa.dvd_mul_right_iff.mp hsI,hsb.dvd_mul_right_iff.mp hsJ⟩


-- @@ L27-27 verbatim
variable {ι : Type*} [Fintype ι]


-- @@ L29-36 verbatim
theorem column_nonzero_divisor (S : Finset (Tuple ι)) (R : Ideal O)
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ s I : Ideal O)
    (h : finiteColumnCoefficient S
      (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s) I≠0) : s∣I := by
  rw [column_mask] at h
  by_contra hn
  exact h (by rw [ite_eq_right hn,mul_zero])


-- @@ L38-50 verbatim
theorem source_pair_divisor_common (S : Finset (Tuple ι)) (R : Ideal O)
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ s C D a b : Ideal O)
    (hC : C≠0) (hD : D≠0) (ha : a≠0) (hb : b≠0)
    (hCD : CompletedGauss.primeSupport C=CompletedGauss.primeSupport D)
    (hCa : IsCoprime C a) (hCb : IsCoprime C b) (hab : IsCoprime a b)
    (hleft : finiteColumnCoefficient S
      (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s) (C*a)≠0)
    (hright : finiteColumnCoefficient S
      (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s) (D*b)≠0) : s∣C ∧ s∣D :=
  divisor_dvd_common C D a b s hC hD ha hb hCD hCa hCb hab
    (column_nonzero_divisor S R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s _ hleft)
    (column_nonzero_divisor S R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s _ hright)


-- @@ L52-52 verbatim
end SevenEighths.CenteredMomentSecondSourceMask


-- @@ L54-54 verbatim
end


-- @@ L56-56 verbatim
end OAI
