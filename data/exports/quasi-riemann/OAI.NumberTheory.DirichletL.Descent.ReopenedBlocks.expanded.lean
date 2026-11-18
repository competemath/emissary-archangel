import OAI.NumberTheory.DirichletL.Descent.ReopenedSource


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
namespace SevenEighths.InverseMoment

-- @@ L6-6 verbatim
open scoped BigOperators Classical SchwartzMap

-- @@ L7-7 verbatim
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic

-- @@ L8-8 verbatim
open ConcreteTraceCRT (eisEmbedding)

-- @@ L9-9 verbatim
open ConcretePrimeRowBridge (idealGenerator)

-- @@ L10-10 verbatim
noncomputable section

-- @@ L11-11 verbatim
local notation "O" => ActualEisensteinCubic.O


-- @@ L13-23 verbatim
def varyingCanonicalSourceTotal {ι : Type*} [DecidableEq ι]
    (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
    (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (labels : Finset (Ideal O))
    (β : Ideal O→(ι→₀ℕ)→ℂ) (Ψ : O→*ℂ) (m : O)
    (H : Ideal O→(ι→₀ℕ)→Finset ι→ℂ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) : ℂ :=
  ∑b∈reopenedCubeFamily Q,∑C∈(pool\b.support).powerset,∑I∈labels,
    reopenedPairCoefficient β b C I *
      canonicalCubeBeforePoisson p hp hcop hg pool b C Ψ Ψ m m (idealGenerator I)
        (H I b.rightExponent) (H I b.leftExponent) W K


-- @@ L25-71 verbatim
theorem varying_reopened_smoothed_source {ι : Type*} [DecidableEq ι]
    (p : ι → ActualEisensteinCubic.O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    (pool : Finset ι) (Q : Finset (ι →₀ ℕ)) (hQ : ∀ v ∈ Q,v.support ⊆ pool)
    (labels : Finset (Ideal ActualEisensteinCubic.O)) (β : Ideal ActualEisensteinCubic.O → (ι →₀ ℕ) → ℂ)
    (Ψ : ActualEisensteinCubic.O →* ℂ) (m : ActualEisensteinCubic.O) (H : Ideal O→(ι→₀ℕ)→Finset ι→ℂ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0 < K) :
    (∑ I ∈ labels,∑' z : ActualEisensteinCubic.O,W (‖eisEmbedding z‖^2/K)*
      (‖varyingReopenedRow p hp hcop hg pool Q (β I) Ψ m (idealGenerator I)
        (H I) z‖^2 : ℝ)) =
    varyingCanonicalSourceTotal p hp hcop hg pool Q labels β Ψ m H W K := by
  rw [varyingCanonicalSourceTotal,sum_reopenedCubeFamily]
  simp only [reopenedPairCoefficient,CubeCoordinates.support]
  calc
    _ = ∑ I ∈ labels,∑ v₂ ∈ Q,∑ v₁ ∈ Q,(star (β I v₂)*β I v₁)*
        canonicalCubeCorrelation p hp hcop hg pool (v₁.support∪v₂.support) v₁ v₂
          Ψ Ψ m m (idealGenerator I) (H I v₂)
          (H I v₁) W K := by
      apply Finset.sum_congr rfl
      intro I hI
      exact varying_reopened_smoothed_expand p hp hcop hg pool Q hQ (β I) Ψ m
        (idealGenerator I) (H I) W K hK
    _ = ∑ v₂ ∈ Q,∑ v₁ ∈ Q,∑ I ∈ labels,(star (β I v₂)*β I v₁)*
        canonicalCubeCorrelation p hp hcop hg pool (v₁.support∪v₂.support) v₁ v₂
          Ψ Ψ m m (idealGenerator I) (H I v₂)
          (H I v₁) W K := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro v₂ hv₂
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro v₂ hv₂
      apply Finset.sum_congr rfl
      intro v₁ hv₁
      have hs : v₁.support∪v₂.support ⊆ pool := Finset.union_subset (hQ v₁ hv₁) (hQ v₂ hv₂)
      simp_rw [canonicalCubeCorrelation_eq_blocks p hp hcop hg hinj hpr pool v₁ v₂ hs,
        Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro A₂ hA₂
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro A₁ hA₁
      rw [Finset.sum_comm]


-- @@ L73-73 verbatim
end

-- @@ L74-74 verbatim
end SevenEighths.InverseMoment


-- @@ L76-76 verbatim
end OAI
