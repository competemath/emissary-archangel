import OAI.NumberTheory.DirichletL.Reflection.MarkedRestriction


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
namespace SevenEighths.InverseReflectedPhase

-- @@ L6-6 verbatim
open scoped Classical BigOperators ContDiff

-- @@ L7-7 verbatim
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment

-- @@ L8-8 verbatim
noncomputable section

-- @@ L9-9 verbatim
local notation "Eis" => ActualEisensteinCubic.O

-- @@ L10-10 verbatim
namespace PrimeFamily

-- @@ L11-11 verbatim
variable {ι : Type*} [Fintype ι] (P : PrimeFamily ι)


-- @@ L13-41 verbatim
lemma fixed_active_sum_eq_mixed
    (hP : Pairwise (Function.onFun IsCoprime P.ideal)) (j : ι→ℕ) (S : Finset ι)
    (φ : Eis→*ℂ) (c : Eis) (hc : c≠0) [Fintype (Eis⧸Ideal.span {c})]
    (G : ∀ h : Eis⧸Ideal.span {c}, FixedFourierGeometry c h)
    (N : Eis) (hN : ∀ h, (9:Eis)*(G h).c0∣N)
    (hNp : ∀ i, IsCoprime (Ideal.span {N}) (P.ideal i)) (W : ℝ→ℂ) (X : ℝ) :
    (∑ t : FixedActiveCuspIndex c P.generator,
      fixedActiveFunctionWeight P.generator P.generator_ne_zero
        (mixedPrimeFunction P.generator P.generator_good j S) c hc φ t *
      (fixedActiveCuspDatum P.generator P.generator_ne_zero P.generator_primary c G N hN
        (P.activeControlled hP c G N hN hNp) t).smoothedKernel W X)=
    ∑ h : Eis⧸Ideal.span {c}, fixedThetaRowCoeff c hc φ h *
      ∑ A : Finset ι,
        localInactiveWeight P.generator P.generator_ne_zero (mixedPrimeFunction P.generator P.generator_good j S) A *
        mixedSmoothedValue (P.activeControlled hP c G N hN hNp h A) (hN h)
          (P.restrict A).generator_product_primary (G h).primary (G h).shape
          (P.restrict A).generator_ne_zero (G h).denominator_ne_zero (P.restrict A).generator_good
          (fun i => j i.val) (activeMarks A S) W X := by
  simp only [FixedActiveCuspIndex,Fintype.sum_sigma,fixedActiveFunctionWeight,fixedActiveCuspDatum,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h hh
  apply Finset.sum_congr rfl
  intro A hA
  rw [← active_sum_eq_mixed P j S hP c G N hN hNp h A W X]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr (by ext v; simp only [Finset.mem_univ])
  intro v hv
  ring


-- @@ L43-86 verbatim
theorem marked_reflected_source
    (hP : Pairwise (Function.onFun IsCoprime P.ideal))
    (hodd : ∀ i, ringChar (Eis⧸P.ideal i)≠2) (j : ι→ℕ) (hj : ∀ i, j i<6) (S : Finset ι)
    (φ : Eis→*ℂ) (hφnorm : ∀ n, ‖φ n‖≤1)
    (Q : Ideal Eis) (hQ : Q≠0) (hφperiod : CanonicalCoefficientClass.FactorsModulo Q φ)
    (c : Eis) (hc : c≠0) [Fintype (Eis⧸Ideal.span {c})]
    (hcQ : Ideal.span {c}≤Ideal.span {(9:Eis)}*Q)
    (G : ∀ h : Eis⧸Ideal.span {c}, FixedFourierGeometry c h)
    (N : Eis) (hN : ∀ h, (9:Eis)*(G h).c0∣N)
    (hNp : ∀ i, IsCoprime (Ideal.span {N}) (P.ideal i))
    (W : ℝ→ℂ) (hWcompact : HasCompactSupport W)
    (lo hi : ℝ) (hlo : 0<lo) (hsupp : Function.support W⊆Set.Icc lo hi)
    (hW : ContDiff ℝ ∞ W) (X : ℝ) (hX : 0<X) :
    markedCompletedT (φ*unmarkedSexticTwist P.generator P.generator_good j S) W X
      (fun A => ∏ i∈S, if Ideal.span {P.generator i}∣A then 1 else 0)=
    thetaDerivativeScalar⁻¹*∑ h : Eis⧸Ideal.span {c}, fixedThetaRowCoeff c hc φ h *
      ∑ A : Finset ι,
        localInactiveWeight P.generator P.generator_ne_zero (mixedPrimeFunction P.generator P.generator_good j S) A *
        mixedReflectedValue (P.activeControlled hP c G N hN hNp h A) (G h).shape
          (P.restrict A).generator_ne_zero (G h).denominator_ne_zero (P.restrict A).generator_good
          (fun i => j i.val) (activeMarks A S) W X := by
  rw [P.marked_source hP j S φ hφnorm Q hQ hφperiod c hc hcQ G N hN hNp
    W hWcompact lo hi hlo hsupp hW X hX,
    P.fixed_active_sum_eq_mixed hP j S φ c hc G N hN hNp W X]
  congr 1
  apply Finset.sum_congr rfl
  intro h hh
  congr 1
  apply Finset.sum_congr rfl
  intro A hA
  congr 1
  apply mixed_smoothed_eq_reflected
  · intro i k hik
    change IsCoprime (Ideal.span {P.generator i.val}) (Ideal.span {P.generator k.val})
    rw [P.generator_span,P.generator_span]
    exact hP (fun he => hik (Subtype.ext he))
  · intro i
    rw [P.generator_span]
    exact hodd i.val
  · exact fun i => hj i.val
  · exact hlo
  · exact hsupp
  · exact hW
  · exact hX

-- @@ L87-87 verbatim
end PrimeFamily

-- @@ L88-88 verbatim
end

-- @@ L89-89 verbatim
end SevenEighths.InverseReflectedPhase


-- @@ L91-91 verbatim
end OAI
