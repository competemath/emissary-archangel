import OAI.NumberTheory.DirichletL.Reflection.MarkedSource
import OAI.NumberTheory.DirichletL.Descent.ReflectedDual


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
namespace SevenEighths.InverseReflectedPhase

-- @@ L7-7 verbatim
open scoped Classical BigOperators ContDiff

-- @@ L8-8 verbatim
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment

-- @@ L9-9 verbatim
noncomputable section

-- @@ L10-10 verbatim
local notation "Eis" => ActualEisensteinCubic.O


-- @@ L12-12 verbatim
variable {ι : Type*} [Fintype ι]

-- @@ L13-13 verbatim
def activeMarks (A S : Finset ι) : Finset A := Finset.univ.filter (fun i => i.val∈S)


-- @@ L15-17 verbatim
omit [Fintype ι] in
lemma mem_activeMarks (A S : Finset ι) (i : A) : i∈activeMarks A S ↔ i.val∈S := by
  simp [activeMarks]


-- @@ L19-26 verbatim
omit [Fintype ι] in
lemma mixedPrimeFunction_restrict (P : PrimeFamily ι) (j : ι→ℕ) (A S : Finset ι)
    (i : A) (x : Eis⧸Ideal.span {P.generator i.val}) :
    mixedPrimeFunction (P.restrict A).generator (P.restrict A).generator_good
      (fun i => j i.val) (activeMarks A S) i x =
    mixedPrimeFunction P.generator P.generator_good j S i.val x := by
  simp only [mixedPrimeFunction,mem_activeMarks]
  rfl


-- @@ L28-41 verbatim
omit [Fintype ι] in
lemma localActiveWeight_restrict (P : PrimeFamily ι) (j : ι→ℕ) (A S : Finset ι)
    (v : ∀ i : A, (Eis⧸Ideal.span {P.generator i.val})ˣ) :
    localActiveWeight P.generator P.generator_ne_zero
      (mixedPrimeFunction P.generator P.generator_good j S) A v =
    fullLocalFourierWeight (P.restrict A).generator_ne_zero
      (mixedPrimeFunction (P.restrict A).generator (P.restrict A).generator_good
        (fun i => j i.val) (activeMarks A S)) v := by
  unfold localActiveWeight fullLocalFourierWeight
  apply Finset.prod_congr rfl
  intro i hi
  congr 1
  funext x
  exact (mixedPrimeFunction_restrict P j A S i x).symm


-- @@ L43-63 verbatim
lemma active_sum_eq_mixed (P : PrimeFamily ι) (j : ι→ℕ) (S : Finset ι)
    (hP : Pairwise (Function.onFun IsCoprime P.ideal))
    (c : Eis) (G : ∀ h : Eis⧸Ideal.span {c}, FixedFourierGeometry c h)
    (N : Eis) (hN : ∀ h, (9:Eis)*(G h).c0∣N)
    (hNp : ∀ i, IsCoprime (Ideal.span {N}) (P.ideal i))
    (h : Eis⧸Ideal.span {c}) (A : Finset ι) (W : ℝ→ℂ) (X : ℝ) :
    (∑ v : ∀ i : A, (Eis⧸Ideal.span {P.generator i.val})ˣ,
      localActiveWeight P.generator P.generator_ne_zero
        (mixedPrimeFunction P.generator P.generator_good j S) A v *
      (activeStratumDatum P.generator P.generator_ne_zero P.generator_primary
        (P.activeControlled hP c G N hN hNp h) (hN h) (G h).denominator_ne_zero
        (G h).primary (G h).shape A v).smoothedKernel W X)=
    mixedSmoothedValue (P.activeControlled hP c G N hN hNp h A) (hN h)
      (P.restrict A).generator_product_primary (G h).primary (G h).shape
      (P.restrict A).generator_ne_zero (G h).denominator_ne_zero (P.restrict A).generator_good
      (fun i => j i.val) (activeMarks A S) W X := by
  unfold mixedSmoothedValue
  apply Finset.sum_congr (by ext v; simp only [Finset.mem_univ])
  intro v hv
  rw [localActiveWeight_restrict]
  rfl

-- @@ L64-64 verbatim
end

-- @@ L65-65 verbatim
end SevenEighths.InverseReflectedPhase


-- @@ L67-67 verbatim
end OAI
