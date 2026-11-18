import OAI.NumberTheory.DirichletL.Descent.SecondPuncture


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
namespace SevenEighths.InverseMoment

-- @@ L6-6 verbatim
noncomputable section

-- @@ L7-7 verbatim
open scoped BigOperators Classical

-- @@ L8-8 verbatim
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic CompletedGauss

-- @@ L9-9 verbatim
open InverseInitialArithmetic (sourceIdeal)

-- @@ L10-10 verbatim
local notation "O" => ActualEisensteinCubic.O

-- @@ L11-14 verbatim
variable {ι σ : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})


-- @@ L16-19 verbatim
def actualSecondRawInheritedPuncture {Jo Jn : ℕ} (m : O) (x : MarkedSecondSource ι Jo Jn) : O :=
  ((m*ConcretePrimeRowBridge.idealGenerator x.quotient)*b0Label p x.cube.support
    (fun i=>x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)*
    secondExpansionQuotient p x.second


-- @@ L21-46 verbatim
omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem actual_parent_deleted_prime_killed {Jo Jn : ℕ}
    (x : MarkedSecondSource ι Jo Jn) (_hb : x.cube.Admissible)
    (hE : x.second.divisor⊆x.second.sourceCommon) (m : O) (i : ι)
    (hi : i∈x.cube.support∪x.firstCommon ∨ (Ideal.span {p i}:Ideal O)∣x.quotient) :
    actualSecondRawInheritedPuncture p m x*actualSecondRawLabel p x∈Ideal.span {p i} := by
  rcases hi with hi|hi
  · have hv : ∀ j∈x.cube.support,0<x.cube.leftExponent j+x.cube.rightExponent j := by
      intro j hj
      simp only [CubeCoordinates.support,Finset.mem_union,Finsupp.mem_support_iff] at hj
      omega
    have hk := actual_second_extracted_support_killed p
      x.cube.support x.firstCommon x.second.sourceCommon x.second.divisor x.second.overlap
      (x.cube.support∪x.firstCommon) hE Finset.subset_union_left
      (fun j=>x.cube.leftExponent j+x.cube.rightExponent j) x.cube.leftBit x.cube.rightBit hv
      (m*ConcretePrimeRowBridge.idealGenerator x.quotient) i hi
    simpa only [actualSecondRawInheritedPuncture,actualSecondRawLabel,
      secondExpansionQuotient_of_subset p x.second hE] using hk
  · have hq : ConcretePrimeRowBridge.idealGenerator x.quotient∈Ideal.span {p i} := by
      apply (Ideal.dvd_iff_le.mp hi)
      have hmem : ConcretePrimeRowBridge.idealGenerator x.quotient∈
          Ideal.span {ConcretePrimeRowBridge.idealGenerator x.quotient} := Ideal.subset_span (by simp)
      simpa only [ConcretePrimeRowBridge.span_idealGenerator] using hmem
    unfold actualSecondRawInheritedPuncture
    exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _
      (Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ hq)))


-- @@ L48-62 verbatim
theorem actual_second_parent_lists_restore {Jo Jn : ℕ}
    (x : MarkedSecondSource ι Jo Jn) (hb : x.cube.Admissible)
    (hE : x.second.divisor⊆x.second.sourceCommon)
    (deleted : Finset ι)
    (hdeleted : ∀ i∈deleted,i∈x.cube.support∪x.firstCommon ∨ (Ideal.span {p i}:Ideal O)∣x.quotient)
    (pool : Finset ι) (Ψ : O→*ℂ) (m k : O) (slots : Finset σ)
    (lists : σ→Finset ι) (a : σ→ι→ℂ) (W : ℝ→ℂ) (X : ℝ) :
    finiteCanonicalMarkedRow p hp hcop hg pool Ψ
      (actualSecondRawInheritedPuncture p m x) (actualSecondRawLabel p x) k
      slots (fun j=>lists j\deleted) a W X =
    finiteCanonicalMarkedRow p hp hcop hg pool Ψ
      (actualSecondRawInheritedPuncture p m x) (actualSecondRawLabel p x) k
      slots lists a W X := by
  apply finiteCanonicalMarkedRow_restore_lists p hp hcop hg
  exact fun i hi=>actual_parent_deleted_prime_killed p x hb hE m i (hdeleted i hi)


-- @@ L64-83 verbatim
theorem actual_second_parent_lists_restore_quotient {Jo Jn : ℕ}
    (x : MarkedSecondSource ι Jo Jn) (hb : x.cube.Admissible)
    (hE : x.second.divisor⊆x.second.sourceCommon) (D : Finset ι)
    (hq : x.quotient=sourceIdeal p D) (deleted : Finset ι)
    (hdeleted : deleted⊆(x.cube.support∪x.firstCommon)∪D)
    (pool : Finset ι) (Ψ : O→*ℂ) (m k : O) (slots : Finset σ)
    (lists : σ→Finset ι) (a : σ→ι→ℂ) (W : ℝ→ℂ) (X : ℝ) :
    finiteCanonicalMarkedRow p hp hcop hg pool Ψ
      (actualSecondRawInheritedPuncture p m x) (actualSecondRawLabel p x) k
      slots (fun j=>lists j\deleted) a W X =
    finiteCanonicalMarkedRow p hp hcop hg pool Ψ
      (actualSecondRawInheritedPuncture p m x) (actualSecondRawLabel p x) k
      slots lists a W X := by
  apply actual_second_parent_lists_restore p hp hcop hg x hb hE deleted
  intro i hi
  rcases Finset.mem_union.mp (hdeleted hi) with hi|hi
  · exact Or.inl hi
  · right
    rw [hq]
    exact InverseInitialArithmetic.source_prime_dvd p D i hi


-- @@ L85-85 verbatim
end

-- @@ L86-86 verbatim
end SevenEighths.InverseMoment


-- @@ L88-88 verbatim
end OAI
