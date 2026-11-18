import OAI.NumberTheory.DirichletL.Descent.ReopenedPhysicalSplit


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
namespace SevenEighths.InverseMoment

-- @@ L6-6 verbatim
noncomputable section

-- @@ L7-7 verbatim
open scoped BigOperators Classical SchwartzMap

-- @@ L8-8 verbatim
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic

-- @@ L9-9 verbatim
open ConcreteTraceCRT (eisEmbedding)

-- @@ L10-10 verbatim
open ConcretePrimeRowBridge (idealGenerator)

-- @@ L11-11 verbatim
local notation "O" => ActualEisensteinCubic.O

-- @@ L12-15 verbatim
variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})


-- @@ L17-28 verbatim
theorem rowFamilyEnergy_le_of_full_split (labels : Finset (Ideal O))
    (P : Ideal O→O→ℂ) (K : ℝ) (hK : 0<K) (A B C : ℂ)
    (he : (∑ I∈labels,∑' z:O,rowMajorant (‖eisEmbedding z‖^2/K)*(‖P I z‖^2:ℝ))=A+B+C) :
    CanonicalRowCompletion.rowFamilyEnergy labels P K ≤ ‖A‖+‖B‖+‖C‖ := by
  unfold CanonicalRowCompletion.rowFamilyEnergy
  simp only [nonzeroRowMajorantSum_eq_sub _ K hK,Finset.sum_sub_distrib,Complex.sub_re]
  rw [he]
  have hn : 0≤(∑ I∈labels,((‖P I 0‖^2:ℝ):ℂ)).re := by
    simp only [Complex.re_sum,Complex.ofReal_re]
    exact Finset.sum_nonneg (fun I hI=>sq_nonneg _)
  simp only [Complex.add_re]
  linarith [Complex.re_le_norm A,Complex.re_le_norm B,Complex.re_le_norm C]


-- @@ L30-56 verbatim
theorem original_reopened_physical_energy
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hc : ∀ i,ringChar (O⧸Ideal.span {p i})≠2)
    (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (hQ : ∀ v∈Q,v.support⊆pool)
    (labels : Finset (Ideal O)) (hlabels : ∀ I∈labels,I≠0)
    (β : Ideal O→(ι→₀ℕ)→ℂ) (Ψ : O→*ℂ) (m : O)
    (mark : Ideal O→(ι→₀ℕ)→Finset ι→ℂ) (W : ℝ→ℂ)
    (K : ℝ) (hK : 0<K) (R : CubeCoordinates ι→Finset ι→Ideal O→Finset ι→ℝ)
    (hR : ∀ b∈reopenedCubeFamily Q,∀ C∈(pool\b.support).powerset,∀ I∈labels,∀ D,0≤R b C I D) :
    CanonicalRowCompletion.rowFamilyEnergy labels (fun I z=>
      varyingReopenedRow p hp hcop hg pool Q (β I) Ψ m (idealGenerator I)
        (fun v U=>mark I v U*W (primeProductNorm p U)) z) K ≤
    ‖reopenedPhysicalSourceSum pool Q labels β (fun b C I=>
      canonicalCubeDualZero p hp hcop hg pool b C Ψ Ψ m m (idealGenerator I)
        (fun U=>mark I b.rightExponent U*W (primeProductNorm p U))
        (fun U=>mark I b.leftExponent U*W (primeProductNorm p U)) rowMajorant K)‖ +
    ‖reopenedPhysicalSourceSum pool Q labels β (fun b C I=>
      reopenedPhysicalRetained p hp hcop hg pool b C Ψ m I (mark I) W rowMajorant K (R b C I))‖ +
    ‖reopenedPhysicalSourceSum pool Q labels β (fun b C I=>
      canonicalCubeDualTail p hp hcop hg pool b C Ψ Ψ m m (idealGenerator I)
        (fun U=>mark I b.rightExponent U*W (primeProductNorm p U))
        (fun U=>mark I b.leftExponent U*W (primeProductNorm p U)) rowMajorant K
        (reopenedPhysicalCutoff p b I (R b C I)))‖ := by
  apply rowFamilyEnergy_le_of_full_split labels _ K hK
  exact original_reopened_physical_split p hp hcop hg hinj hc hpr pool Q hQ labels hlabels
    β Ψ m mark W rowMajorant K hK R hR


-- @@ L58-58 verbatim
end

-- @@ L59-59 verbatim
end SevenEighths.InverseMoment


-- @@ L61-61 verbatim
end OAI
