import OAI.NumberTheory.DirichletL.Reflection.MarkedJoined


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
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda


-- @@ L12-12 verbatim
namespace PrimeFamily

-- @@ L13-13 verbatim
variable {ι : Type*} (P : PrimeFamily ι)

-- @@ L14-15 verbatim
lemma generator_prime (i : ι) : Prime (P.generator i) :=
  (Ideal.span_singleton_prime (P.generator_ne_zero i)).mp inferInstance


-- @@ L17-20 verbatim
def restrict (A : Finset ι) : PrimeFamily A where
  ideal i := P.ideal i.val
  maximal i := P.maximal i.val
  good i := P.good i.val


-- @@ L22-25 verbatim
lemma restrict_pairwise (hP : Pairwise (Function.onFun IsCoprime P.ideal)) (A : Finset ι) :
    Pairwise (Function.onFun IsCoprime (P.restrict A).ideal) := by
  intro i k hik
  exact hP (fun h => hik (Subtype.ext h))


-- @@ L27-36 verbatim
def activeControlled [Fintype ι]
    (hP : Pairwise (Function.onFun IsCoprime P.ideal))
    (c : Eis) (G : ∀ h : Eis⧸Ideal.span {c}, FixedFourierGeometry c h)
    (N : Eis) (hN : ∀ h, (9:Eis)*(G h).c0∣N)
    (hNp : ∀ i, IsCoprime (Ideal.span {N}) (P.ideal i))
    (h : Eis⧸Ideal.span {c}) (A : Finset ι) :
    ControlledStratumArithmetic (fun i : A => P.generator i.val) N (G h).a0 (G h).c0 (G h).mode :=
  Classical.choice ((P.restrict A).exists_controlled N (G h).a0 (G h).c0 (G h).mode
    (G h).denominator_ne_zero (hN h) (G h).primary (G h).coprime
    (P.restrict_pairwise hP A) (fun i => hNp i.val))


-- @@ L38-75 verbatim
theorem marked_source [Fintype ι]
    (hP : Pairwise (Function.onFun IsCoprime P.ideal)) (j : ι→ℕ) (S : Finset ι)
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
    thetaDerivativeScalar⁻¹*∑ t : FixedActiveCuspIndex c P.generator,
      fixedActiveFunctionWeight P.generator P.generator_ne_zero
        (mixedPrimeFunction P.generator P.generator_good j S) c hc φ t *
      (fixedActiveCuspDatum P.generator P.generator_ne_zero P.generator_primary c G N hN
        (P.activeControlled hP c G N hN hNp) t).smoothedKernel W X := by
  let Qall := (Q*Ideal.span {∏ i, P.generator i})*Ideal.span {∏ i∈S, P.generator i}
  have hprod : (∏ i, P.generator i)≠0 := Finset.prod_ne_zero_iff.mpr (fun i _ => P.generator_ne_zero i)
  have hmark : (∏ i∈S, P.generator i)≠0 := Finset.prod_ne_zero_iff.mpr (fun i _ => P.generator_ne_zero i)
  have hQall : Qall≠0 := mul_ne_zero (mul_ne_zero hQ
    (by simpa only [ne_eq,Ideal.zero_eq_bot,Ideal.span_singleton_eq_bot] using hprod))
    (by simpa only [ne_eq,Ideal.zero_eq_bot,Ideal.span_singleton_eq_bot] using hmark)
  let call := ConcretePrimeRowBridge.idealGenerator (Ideal.span {(9:Eis)}*Qall)
  have hcall : call≠0 := by
    apply ConcretePrimeRowBridge.idealGenerator_ne_zero
    apply mul_ne_zero _ hQall
    simp only [ne_eq,Ideal.zero_eq_bot,Ideal.span_singleton_eq_bot]
    norm_num
  let : Finite (Eis⧸Ideal.span {call}) := ConcreteTraceCRT.finite_quotient_span hcall
  let : Fintype (Eis⧸Ideal.span {call}) := Fintype.ofFinite _
  have hcallQ : Ideal.span {call}≤Ideal.span {(9:Eis)}*Qall := by
    rw [ConcretePrimeRowBridge.span_idealGenerator]
  exact markedCompletedT_fixed_active_strata P.generator P.generator_ne_zero P.generator_prime
    P.generator_primary P.generator_good j S φ hφnorm Q hφperiod c hc hcQ G N hN
    (P.activeControlled hP c G N hN hNp) call hcall hcallQ W hWcompact lo hi hlo hsupp hW X hX

-- @@ L76-76 verbatim
end PrimeFamily

-- @@ L77-77 verbatim
end

-- @@ L78-78 verbatim
end SevenEighths.InverseReflectedPhase


-- @@ L80-80 verbatim
end OAI
