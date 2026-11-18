import OAI.NumberTheory.DirichletL.Descent.CanonicalLongNormalization
import OAI.NumberTheory.DirichletL.Descent.CanonicalPunctureMaskEnergy
import OAI.NumberTheory.DirichletL.Descent.CompletedReopening


-- @@ L5-5 verbatim
namespace OAI


-- @@ L7-7 verbatim
noncomputable section


-- @@ L9-9 verbatim
open scoped BigOperators Classical

-- @@ L10-10 verbatim
namespace SevenEighths.InverseMoment

-- @@ L11-11 verbatim
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion ConcretePrimeRowBridge

-- @@ L12-12 verbatim
open CanonicalQuadraticSieve FirstPassCubeLabels SecondPassArithmetic InverseInitialClippedColumns

-- @@ L13-13 verbatim
local notation "O"=>ActualEisensteinCubic.O


-- @@ L15-37 verbatim
theorem normalizedColumnEnergy_eq_generator_sum {ι σ:Type*}[DecidableEq ι][DecidableEq σ]
    (p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
    (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg:∀i,goodLambda∉Ideal.span {p i})
    (pool:Finset ι)(Ψ:O→*ℂ)(m:O)(slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)
    (labels:Finset (Ideal O))(hlabels:∀I∈labels,primaryGenerator I≠0)
    (weight:Ideal O→ℝ)(W:ℝ→ℂ)(X Z F R:ℝ)(hZ:0<Z) :
    normalizedColumnEnergy p hp hcop hg pool Ψ m slots lists a labels
      (nonzeroChildFrequencyBall 1 R) weight W X Z F=
    Z^(-F)*(∑I∈labels,weight I*∑k∈nonzeroChildFrequencyBall 1 R,
      ‖finiteCanonicalMarkedRow p hp hcop hg pool Ψ m (idealGenerator I) k slots lists a W X‖^2) := by
  have hn:‖((Z^(-F/2):ℝ):ℂ)‖^2=Z^(-F) := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.rpow_pos_of_pos hZ _),
      ←Real.rpow_mul_natCast hZ.le]
    congr 1
    ring
  unfold normalizedColumnEnergy
  simp only [norm_mul,mul_pow,hn,←Finset.mul_sum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro I hI
  rw [canonical_ball_generator_energy p hp hcop hg pool Ψ m I (hlabels I hI)]
  ring


-- @@ L39-62 verbatim
theorem outside_complete_normalized_energy {σ:Type*}[DecidableEq σ]
    (S:Finset (Ideal O))(D:ℕ)(hbad:fixedBadPrimes⊆S)
    (Ψ:O→*ℂ)(m:O)(slots:Finset σ)
    (lists:σ→Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)))
    (a:σ→primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)→ℂ)
    (labels:Finset (Ideal O))(hlabels:∀I∈labels,Supported I)
    (weight:Ideal O→ℝ)(W:ℝ→ℂ)(X Z Fexp R:ℝ)(hZ:0<Z) :
    let F:=InitialMeanSquare.outsideSquarefreeIdeals S D
    let hF:=InitialMeanSquare.outsideSquarefree_admissible S D hbad
    letI : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=
      fun i=>by rw [poolPrimary_span F hF i];infer_instance
    Z^(-Fexp)*(∑I∈labels,weight I*∑k∈nonzeroChildFrequencyBall 1 R,
      ‖outsideCanonicalMarkedRow S D hbad Ψ m (idealGenerator I) k slots lists a W X‖^2)=
    normalizedColumnEnergy (poolPrimary F) (poolPrimary_ne_zero F hF)
      (poolPrimary_coprime F hF) (poolPrimary_good F hF) Finset.univ Ψ m slots lists a labels
      (nonzeroChildFrequencyBall 1 R) weight W X Z Fexp := by
  let F:=InitialMeanSquare.outsideSquarefreeIdeals S D
  have hF:=InitialMeanSquare.outsideSquarefree_admissible S D hbad
  let : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=
    fun i=>by rw [poolPrimary_span F hF i];infer_instance
  dsimp only
  exact (normalizedColumnEnergy_eq_generator_sum (poolPrimary F) (poolPrimary_ne_zero F hF)
    (poolPrimary_coprime F hF) (poolPrimary_good F hF) Finset.univ Ψ m slots lists a labels
    (fun I hI=>supported_primaryGenerator_ne_zero I (hlabels I hI)) weight W X Z Fexp R hZ).symm


-- @@ L64-85 verbatim
theorem reflection_complete_normalized_energy {σ:Type*}[DecidableEq σ]
    (q D:ℕ)(Ψ:O→*ℂ)(m:O)(slots:Finset σ)
    (lists:σ→Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals (reflectionExcludedPrimes q) D)))
    (a:σ→primePool (InitialMeanSquare.outsideSquarefreeIdeals (reflectionExcludedPrimes q) D)→ℂ)
    (labels:Finset (Ideal O))(hlabels:∀I∈labels,Supported I)
    (weight:Ideal O→ℝ)(W:ℝ→ℂ)(X Z Fexp R:ℝ)(hZ:0<Z) :
    let S:=reflectionExcludedPrimes q
    let F:=InitialMeanSquare.outsideSquarefreeIdeals S D
    let hF:=InitialMeanSquare.outsideSquarefree_admissible S D (reflectionExcludedPrimes_bad q)
    letI : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=
      fun i=>by rw [poolPrimary_span F hF i];infer_instance
    Z^(-Fexp)*(∑I∈labels,weight I*∑k∈nonzeroChildFrequencyBall 1 R,
      ‖outsideCanonicalMarkedRow S D (reflectionExcludedPrimes_bad q) Ψ m (idealGenerator I) k
        slots lists a W X‖^2)=
    normalizedColumnEnergy (poolPrimary F) (poolPrimary_ne_zero F hF)
      (poolPrimary_coprime F hF) (poolPrimary_good F hF) Finset.univ Ψ
      (ActualFiber.maskElement q m) slots lists a labels
      (nonzeroChildFrequencyBall 1 R) weight W X Z Fexp := by
  have h:=outside_complete_normalized_energy (reflectionExcludedPrimes q) D
    (reflectionExcludedPrimes_bad q) Ψ m slots lists a labels hlabels weight W X Z Fexp R hZ
  exact h.trans (reflection_pool_mask_energy q D Finset.univ Ψ m slots lists a labels
    (nonzeroChildFrequencyBall 1 R) weight W X Z Fexp).symm


-- @@ L87-87 verbatim
end SevenEighths.InverseMoment


-- @@ L89-89 verbatim
end


-- @@ L91-91 verbatim
end OAI
