import OAI.NumberTheory.DirichletL.Descent.CanonicalPunctureMask


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section

-- @@ L6-6 verbatim
open scoped BigOperators Classical

-- @@ L7-7 verbatim
namespace SevenEighths.InverseMoment

-- @@ L8-8 verbatim
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion ConcretePrimeRowBridge

-- @@ L9-9 verbatim
open CanonicalQuadraticSieve InverseInitialClippedColumns

-- @@ L10-10 verbatim
local notation "Eis" => ActualEisensteinCubic.O


-- @@ L12-39 verbatim
theorem outside_pool_redundant_energy {σ : Type*} [DecidableEq σ]
    (S : Finset (Ideal Eis)) (D : ℕ) (hbad : fixedBadPrimes⊆S)
    (hSp : ∀P∈S,Prime P)
    (pool : Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)))
    (Ψ : Eis →* ℂ) (m : Eis) (slots : Finset σ)
    (lists : σ→Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)))
    (a : σ→primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)→ℂ)
    (labels : Finset (Ideal Eis)) (rows : Finset Eis) (weight : Ideal Eis→ℝ)
    (W : ℝ→ℂ) (X Z Fexp : ℝ) :
    let F:=InitialMeanSquare.outsideSquarefreeIdeals S D
    let hF:=InitialMeanSquare.outsideSquarefree_admissible S D hbad
    letI : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=
      fun i=>by rw [poolPrimary_span F hF i];infer_instance
    normalizedColumnEnergy (poolPrimary F) (poolPrimary_ne_zero F hF)
      (poolPrimary_coprime F hF) (poolPrimary_good F hF) pool Ψ
      (m*excludedGenerator S) slots lists a labels rows weight W X Z Fexp=
    normalizedColumnEnergy (poolPrimary F) (poolPrimary_ne_zero F hF)
      (poolPrimary_coprime F hF) (poolPrimary_good F hF) pool Ψ
      m slots lists a labels rows weight W X Z Fexp := by
  let F:=InitialMeanSquare.outsideSquarefreeIdeals S D
  have hF:=InitialMeanSquare.outsideSquarefree_admissible S D hbad
  let : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=
    fun i=>by rw [poolPrimary_span F hF i];infer_instance
  dsimp only
  apply normalizedColumnEnergy_redundant_puncture
  intro i hi hc
  rw [poolPrimary_span F hF i] at hc
  exact False.elim (excludedGenerator_not_mem_pool S D hSp i hc)


-- @@ L41-62 verbatim
theorem reflection_pool_mask_energy {σ : Type*} [DecidableEq σ]
    (q D : ℕ)
    (pool : Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals (reflectionExcludedPrimes q) D)))
    (Ψ : Eis →* ℂ) (m : Eis) (slots : Finset σ)
    (lists : σ→Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals (reflectionExcludedPrimes q) D)))
    (a : σ→primePool (InitialMeanSquare.outsideSquarefreeIdeals (reflectionExcludedPrimes q) D)→ℂ)
    (labels : Finset (Ideal Eis)) (rows : Finset Eis) (weight : Ideal Eis→ℝ)
    (W : ℝ→ℂ) (X Z Fexp : ℝ) :
    let S:=reflectionExcludedPrimes q
    let F:=InitialMeanSquare.outsideSquarefreeIdeals S D
    let hF:=InitialMeanSquare.outsideSquarefree_admissible S D (reflectionExcludedPrimes_bad q)
    letI : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=
      fun i=>by rw [poolPrimary_span F hF i];infer_instance
    normalizedColumnEnergy (poolPrimary F) (poolPrimary_ne_zero F hF)
      (poolPrimary_coprime F hF) (poolPrimary_good F hF) pool Ψ
      (ActualFiber.maskElement q m) slots lists a labels rows weight W X Z Fexp=
    normalizedColumnEnergy (poolPrimary F) (poolPrimary_ne_zero F hF)
      (poolPrimary_coprime F hF) (poolPrimary_good F hF) pool Ψ
      m slots lists a labels rows weight W X Z Fexp :=
  outside_pool_redundant_energy (reflectionExcludedPrimes q) D
    (reflectionExcludedPrimes_bad q) (reflectionExcludedPrimes_prime q)
    pool Ψ m slots lists a labels rows weight W X Z Fexp


-- @@ L64-79 verbatim
theorem inherited_radical_mask_energy {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
    (p : ι→Eis) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg : ∀i,goodLambda∉Ideal.span {p i})
    (pool : Finset ι) (Ψ : Eis→*ℂ) (m c : Eis) (γ : InverseSecondFibers.OuterTriple)
    (hc : (Ideal.span {c}:Ideal Eis).radical∣Ideal.span {m})
    (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (labels : Finset (Ideal Eis)) (rows : Finset Eis) (weight : Ideal Eis→ℝ)
    (W : ℝ→ℂ) (X Z Fexp : ℝ) :
    normalizedColumnEnergy p hp hcop hg pool Ψ
      (actualSecondInheritedRadicalPuncture m γ*c) slots lists a labels rows weight W X Z Fexp=
    normalizedColumnEnergy p hp hcop hg pool Ψ
      (actualSecondInheritedRadicalPuncture m γ) slots lists a labels rows weight W X Z Fexp :=
  normalizedColumnEnergy_redundant_puncture p hp hcop hg pool Ψ _ c
    slots lists a labels rows weight W X Z Fexp
    (fun i _=>inherited_puncture_redundant_mem p m c γ hc i)


-- @@ L81-81 verbatim
end SevenEighths.InverseMoment

-- @@ L82-82 verbatim
end


-- @@ L84-84 verbatim
end OAI
