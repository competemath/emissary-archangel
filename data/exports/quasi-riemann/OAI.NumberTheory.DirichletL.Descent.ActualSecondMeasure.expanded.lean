import OAI.NumberTheory.DirichletL.Descent.ActualSecondProfile
import OAI.NumberTheory.DirichletL.Descent.ProfileIntegral


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
namespace SevenEighths.InverseMoment

-- @@ L7-7 verbatim
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff

-- @@ L8-8 verbatim
open MeasureTheory FourierBridge JointLogSeparation

-- @@ L9-9 verbatim
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic

-- @@ L10-10 verbatim
noncomputable section

-- @@ L11-11 verbatim
local notation "Eis" => ActualEisensteinCubic.O


-- @@ L13-16 verbatim
def secondProfileIndices {κ ι : Type*} [DecidableEq ι]
    (source : Finset κ) (F : Finset ι) (x : κ → SecondProfileData ι) :
    Finset (Σ _ : κ, Finset ι × Finset ι) :=
  source.sigma (fun j => (F \ (x j).overlap).powerset ×ˢ (F \ (x j).overlap).powerset)


-- @@ L18-23 verbatim
lemma mem_secondProfileIndices {κ ι : Type*} [DecidableEq ι]
    (source : Finset κ) (F : Finset ι) (x : κ → SecondProfileData ι)
    (j : Σ _ : κ, Finset ι × Finset ι) : j ∈ secondProfileIndices source F x ↔
      j.1 ∈ source ∧ j.2.1 ∈ (F \ (x j.1).overlap).powerset ∧
        j.2.2 ∈ (F \ (x j.1).overlap).powerset := by
  simp only [secondProfileIndices,Finset.mem_sigma,Finset.mem_product]


-- @@ L25-40 verbatim
theorem actualSecondProfileRows_eq_indexed {κ ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
    (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
    (source : Finset κ) (F : Finset ι) (x : κ → SecondProfileData ι) (w : κ → ℂ)
    (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (Y X : ℝ) :
    (∑ j ∈ source, w j * actualSecondProfileRow p hp hcop hg F (x j)
      slots₁ slots₂ lists₁ lists₂ a₁ a₂ W₁ W₂ Φ Y X) =
    ∑ j ∈ secondProfileIndices source F x,
      (w j.1 * secondActualCoefficient p hp hcop hg (x j.1)
        slots₁ slots₂ lists₁ lists₂ a₁ a₂ j.2.1 j.2.2) *
      secondNormProfile (fun z => star (W₁ (z/X))) (fun z => W₂ (z/X)) Φ (fun _ _ => 1) Y
        (secondActualNorms p (x j.1) j.2.1 j.2.2) := by
  simp only [actualSecondProfileRow_eq_whole,secondProfileIndices,Finset.sum_sigma,
    Finset.sum_product,Finset.mul_sum,mul_assoc]


-- @@ L42-75 verbatim
theorem actualSecondProfileRows_integral {κ ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
    (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
    (source : Finset κ) (F : Finset ι) (x : κ → SecondProfileData ι) (w : κ → ℂ)
    (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (Y G₀ E₀ V₀ K₀ X₀ : ℝ)
    (g : Fin 6 → 𝓢(ℝ,ℂ)) (b₁ b₂ b₃ : 𝓢(ℝ,ℂ))
    (he : ∀ j ∈ secondProfileIndices source F x,
      secondNormProfile (fun z => star (W₁ (z/(G₀*V₀*X₀))))
        (fun z => W₂ (z/(G₀*V₀*X₀))) Φ (fun _ _ => 1) Y (secondActualNorms p (x j.1) j.2.1 j.2.2) =
      ((E₀*V₀*X₀ : ℝ):ℂ)⁻¹ *
        ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ, ∫ u : Fin 6 → ℝ,
          fullProfileDensity g b₁ b₂ b₃ ((t₁,t₂,t₃),u) *
            (∏ i, logPhase (profileHeight secondLeftSlope secondRightSlope secondKernelSlope
              (t₁,t₂,t₃) u i) (secondRelativeLog (secondActualNorms p (x j.1) j.2.1 j.2.2)
                G₀ E₀ V₀ K₀ X₀ i))) :
    (∑ j ∈ source, w j * actualSecondProfileRow p hp hcop hg F (x j)
      slots₁ slots₂ lists₁ lists₂ a₁ a₂ W₁ W₂ Φ Y (G₀*V₀*X₀)) =
      ((E₀*V₀*X₀ : ℝ):ℂ)⁻¹ * ∫ v : Frequency × (Fin 6 → ℝ),
        fullProfileDensity g b₁ b₂ b₃ v *
          ∑ j ∈ secondProfileIndices source F x,
            (w j.1 * secondActualCoefficient p hp hcop hg (x j.1)
              slots₁ slots₂ lists₁ lists₂ a₁ a₂ j.2.1 j.2.2) *
            pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope
              (secondRelativeLog (secondActualNorms p (x j.1) j.2.1 j.2.2) G₀ E₀ V₀ K₀ X₀) v.1 v.2 := by
  rw [actualSecondProfileRows_eq_indexed]
  rw [← full_density_finite_sum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [he j hj, full_density_mode_fubini]
  simp only [pureProfileMode_height]
  ring


-- @@ L77-77 verbatim
end

-- @@ L78-78 verbatim
end SevenEighths.InverseMoment


-- @@ L80-80 verbatim
end OAI
