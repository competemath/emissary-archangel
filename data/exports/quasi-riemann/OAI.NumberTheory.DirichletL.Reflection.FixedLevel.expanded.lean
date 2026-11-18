import OAI.NumberTheory.DirichletL.Reflection.MarkedLevel


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
namespace SevenEighths.InverseReflectedPhase

-- @@ L6-6 verbatim
open scoped Classical BigOperators

-- @@ L7-7 verbatim
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion

-- @@ L8-8 verbatim
noncomputable section

-- @@ L9-9 verbatim
local notation "Eis" => ActualEisensteinCubic.O


-- @@ L11-12 verbatim
def reflectionSourceConductor (Q : Ideal Eis) : Eis :=
  ConcretePrimeRowBridge.idealGenerator (Ideal.span {(9:Eis)}*(Q*Ideal.span {(72:Eis)}))


-- @@ L14-16 verbatim
lemma reflectionSourceConductor_span (Q : Ideal Eis) :
    Ideal.span {reflectionSourceConductor Q}=Ideal.span {(9:Eis)}*(Q*Ideal.span {(72:Eis)}) :=
  ConcretePrimeRowBridge.span_idealGenerator _


-- @@ L18-22 verbatim
lemma reflectionSourceConductor_ne_zero (Q : Ideal Eis) (hQ : Q≠0) :
    reflectionSourceConductor Q≠0 := by
  apply ConcretePrimeRowBridge.idealGenerator_ne_zero
  apply mul_ne_zero _ (mul_ne_zero hQ _)
  all_goals simp only [ne_eq,Ideal.zero_eq_bot,Ideal.span_singleton_eq_bot]; norm_num


-- @@ L24-24 verbatim
def reflectionSourceLevel (Q : Ideal Eis) : Eis := (9:Eis)*reflectionSourceConductor Q


-- @@ L26-27 verbatim
lemma reflectionSourceLevel_ne_zero (Q : Ideal Eis) (hQ : Q≠0) :
    reflectionSourceLevel Q≠0 := mul_ne_zero (by norm_num) (reflectionSourceConductor_ne_zero Q hQ)


-- @@ L29-33 verbatim
lemma reflectionSourceGeometry_level (Q : Ideal Eis) (hQ : Q≠0)
    (h : Eis⧸Ideal.span {reflectionSourceConductor Q}) :
    (9:Eis)*(fixedFourierGeometry (reflectionSourceConductor Q)
      (reflectionSourceConductor_ne_zero Q hQ) h).c0∣reflectionSourceLevel Q :=
  mul_dvd_mul_left (9:Eis) (fixedFourierGeometry _ _ h).denominator_dvd


-- @@ L35-39 verbatim
lemma reflectionSourceLevel_original_period {σ : Type*} {m f z : Eis}
    (D : GoodMaskRowData m f z) (S : PrimeFamily σ) (Q : Ideal Eis)
    (hS : ∀ i, IsCoprime (Q*Ideal.span {(72:Eis)}) (S.ideal i)) :
    ∀ i, IsCoprime (Ideal.span {reflectionSourceLevel Q}) ((markedRowFamily D S Q).ideal i) :=
  markedRowFamily_period D S Q hS (reflectionSourceConductor Q) (reflectionSourceConductor_span Q)


-- @@ L41-43 verbatim
lemma reflectionSourceLevel_ray_finite (Q : Ideal Eis) (hQ : Q≠0) :
    Finite (Eis⧸Ideal.span {(reflectionSourceLevel Q)^2}) :=
  ConcreteTraceCRT.finite_quotient_span (pow_ne_zero 2 (reflectionSourceLevel_ne_zero Q hQ))


-- @@ L45-45 verbatim
end

-- @@ L46-46 verbatim
end SevenEighths.InverseReflectedPhase


-- @@ L48-48 verbatim
end OAI
