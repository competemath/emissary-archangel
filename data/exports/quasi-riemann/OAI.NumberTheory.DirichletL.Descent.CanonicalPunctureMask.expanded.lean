import OAI.NumberTheory.DirichletL.Descent.ActualChildStatePuncture
import OAI.NumberTheory.DirichletL.Inversion.InitialClippedColumns


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
noncomputable section

-- @@ L7-7 verbatim
open scoped BigOperators Classical

-- @@ L8-8 verbatim
namespace SevenEighths.InverseMoment

-- @@ L9-9 verbatim
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic CompletedGauss

-- @@ L10-10 verbatim
open CanonicalRowCompletion ConcretePrimeRowBridge CanonicalQuadraticSieve

-- @@ L11-11 verbatim
open InverseInitialClippedColumns

-- @@ L12-12 verbatim
local notation "Eis" => ActualEisensteinCubic.O


-- @@ L14-14 verbatim
section General

-- @@ L15-18 verbatim
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀ i,goodLambda∉Ideal.span {p i})


-- @@ L20-31 verbatim
omit [DecidableEq ι] in
theorem rowCoprimeMask_redundant_mul (S : Finset ι) (m c : Eis)
    (hc : ∀ i∈S,c∈Ideal.span {p i}→m∈Ideal.span {p i}) :
    rowCoprimeMask (fun i=>Ideal.span {p i}) S (m*c)=
      rowCoprimeMask (fun i=>Ideal.span {p i}) S m := by
  have he : (∃i∈S,m*c∈Ideal.span {p i}) ↔ ∃i∈S,m∈Ideal.span {p i} := by
    constructor
    · rintro ⟨i,hi,hm⟩
      exact ⟨i,hi,((inferInstance : (Ideal.span {p i}).IsPrime).mem_or_mem hm).elim id (hc i hi)⟩
    · rintro ⟨i,hi,hm⟩
      exact ⟨i,hi,Ideal.mul_mem_right _ _ hm⟩
  simp only [rowCoprimeMask,he]


-- @@ L33-45 verbatim
omit [DecidableEq σ] in
theorem finiteCanonicalMarkedRow_redundant_puncture
    (pool : Finset ι) (Ψ : Eis →* ℂ) (m c f k : Eis)
    (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ) (W : ℝ→ℂ) (X : ℝ)
    (hc : ∀ i∈pool,c∈Ideal.span {p i}→m∈Ideal.span {p i}) :
    finiteCanonicalMarkedRow p hp hcop hg pool Ψ (m*c) f k slots lists a W X=
      finiteCanonicalMarkedRow p hp hcop hg pool Ψ m f k slots lists a W X := by
  unfold finiteCanonicalMarkedRow fixedChildRow
  apply Finset.sum_congr rfl
  intro S hS
  have hm := rowCoprimeMask_redundant_mul p S m c
    (fun i hi=>hc i (Finset.mem_powerset.mp hS hi))
  simp only [secondChildColumn,hm]


-- @@ L47-57 verbatim
omit [DecidableEq σ] in
theorem normalizedColumnEnergy_redundant_puncture
    (pool : Finset ι) (Ψ : Eis →* ℂ) (m c : Eis)
    (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (labels : Finset (Ideal Eis)) (rows : Finset Eis) (D : Ideal Eis→ℝ)
    (W : ℝ→ℂ) (X Z F : ℝ)
    (hc : ∀ i∈pool,c∈Ideal.span {p i}→m∈Ideal.span {p i}) :
    normalizedColumnEnergy p hp hcop hg pool Ψ (m*c) slots lists a labels rows D W X Z F=
      normalizedColumnEnergy p hp hcop hg pool Ψ m slots lists a labels rows D W X Z F := by
  simp only [normalizedColumnEnergy,finiteCanonicalMarkedRow_redundant_puncture
    p hp hcop hg pool Ψ m c _ _ slots lists a W X hc]


-- @@ L59-67 verbatim
omit [DecidableEq ι] in
theorem puncture_mem_of_radical_dvd (m c : Eis)
    (hc : (Ideal.span {c}:Ideal Eis).radical∣(Ideal.span {m}:Ideal Eis).radical)
    (i : ι) (hi : c∈Ideal.span {p i}) : m∈Ideal.span {p i} := by
  rw [←Ideal.span_singleton_le_iff_mem]
  apply Ideal.le_radical.trans
  apply (Ideal.dvd_iff_le.mp hc).trans
  exact (inferInstance : (Ideal.span {p i}).IsPrime).radical_le_iff.mpr
    (by rwa [Ideal.span_singleton_le_iff_mem])


-- @@ L69-79 verbatim
omit [DecidableEq ι] in
theorem inherited_puncture_redundant_mem (m c : Eis)
    (γ : InverseSecondFibers.OuterTriple)
    (hc : (Ideal.span {c}:Ideal Eis).radical∣Ideal.span {m})
    (i : ι) (hi : c∈Ideal.span {p i}) :
    actualSecondInheritedRadicalPuncture m γ∈Ideal.span {p i} := by
  have hd := actual_inherited_radical_preserves_fixed m γ (Ideal.span {c}).radical
    (Ideal.radical_idem _) hc
  apply puncture_mem_of_radical_dvd p _ c _ i hi
  rw [actual_inherited_radical_is_radical]
  exact hd


-- @@ L81-81 verbatim
end General


-- @@ L83-108 verbatim
theorem outside_pool_redundant_puncture {σ : Type*} [DecidableEq σ]
    (S : Finset (Ideal Eis)) (D : ℕ) (hbad : fixedBadPrimes⊆S)
    (hSp : ∀P∈S,Prime P)
    (pool : Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)))
    (Ψ : Eis →* ℂ) (m f k : Eis) (slots : Finset σ)
    (lists : σ→Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)))
    (a : σ→primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)→ℂ)
    (W : ℝ→ℂ) (X : ℝ) :
    let F:=InitialMeanSquare.outsideSquarefreeIdeals S D
    let hF:=InitialMeanSquare.outsideSquarefree_admissible S D hbad
    letI : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=
      fun i=>by rw [poolPrimary_span F hF i];infer_instance
    finiteCanonicalMarkedRow (poolPrimary F) (poolPrimary_ne_zero F hF)
      (poolPrimary_coprime F hF) (poolPrimary_good F hF) pool Ψ
      (m*excludedGenerator S) f k slots lists a W X=
    finiteCanonicalMarkedRow (poolPrimary F) (poolPrimary_ne_zero F hF)
      (poolPrimary_coprime F hF) (poolPrimary_good F hF) pool Ψ m f k slots lists a W X := by
  let F:=InitialMeanSquare.outsideSquarefreeIdeals S D
  have hF:=InitialMeanSquare.outsideSquarefree_admissible S D hbad
  let : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=
    fun i=>by rw [poolPrimary_span F hF i];infer_instance
  dsimp only
  apply finiteCanonicalMarkedRow_redundant_puncture
  intro i hi hc
  rw [poolPrimary_span _ (InitialMeanSquare.outsideSquarefree_admissible S D hbad)] at hc
  exact False.elim (excludedGenerator_not_mem_pool S D hSp i hc)


-- @@ L110-110 verbatim
end SevenEighths.InverseMoment

-- @@ L111-111 verbatim
end


-- @@ L113-113 verbatim
end OAI
