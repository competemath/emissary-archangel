import OAI.NumberTheory.DirichletL.Reflection.Canonical


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
namespace SevenEighths.InverseReflectedPhase

-- @@ L6-6 verbatim
open scoped Classical BigOperators

-- @@ L7-7 verbatim
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve

-- @@ L8-8 verbatim
noncomputable section

-- @@ L9-9 verbatim
local notation "Eis" => ActualEisensteinCubic.O

-- @@ L10-10 verbatim
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda


-- @@ L12-12 verbatim
namespace PrimeFamily

-- @@ L13-13 verbatim
variable {ι κ : Type*}


-- @@ L15-18 verbatim
def sum (G : PrimeFamily ι) (H : PrimeFamily κ) : PrimeFamily (ι ⊕ κ) where
  ideal := Sum.elim G.ideal H.ideal
  maximal i := by cases i with | inl i => exact G.maximal i | inr i => exact H.maximal i
  good i := by cases i with | inl i => exact G.good i | inr i => exact H.good i


-- @@ L20-22 verbatim
lemma sum_product [Fintype ι] [Fintype κ] (G : PrimeFamily ι) (H : PrimeFamily κ) :
    (∏ i, (G.sum H).ideal i) = (∏ i, G.ideal i)*(∏ i, H.ideal i) := by
  simp only [sum,Fintype.prod_sum_type,Sum.elim_inl,Sum.elim_inr]


-- @@ L24-36 verbatim
lemma sum_pairwise (G : PrimeFamily ι) (H : PrimeFamily κ)
    (hG : Pairwise (Function.onFun IsCoprime G.ideal))
    (hH : Pairwise (Function.onFun IsCoprime H.ideal))
    (hcross : ∀ i k, IsCoprime (G.ideal i) (H.ideal k)) :
    Pairwise (Function.onFun IsCoprime (G.sum H).ideal) := by
  intro i k hik
  cases i with
  | inl i => cases k with
    | inl k => exact hG (fun h => hik (congrArg Sum.inl h))
    | inr k => exact hcross i k
  | inr i => cases k with
    | inl k => exact (hcross k i).symm
    | inr k => exact hH (fun h => hik (congrArg Sum.inr h))


-- @@ L38-41 verbatim
def residual (K : Ideal Eis) (hK : Admissible K) : PrimeFamily (PrimeIndex K) where
  ideal := fun P => P.val
  maximal _P := inferInstance
  good := admissiblePrimeGood K hK


-- @@ L43-44 verbatim
lemma residual_product (K : Ideal Eis) (hK : Admissible K) :
    (∏ P, (residual K hK).ideal P) = K := admissible_primeIndex_product K hK


-- @@ L46-47 verbatim
lemma residual_dvd (K : Ideal Eis) (hK : Admissible K) (P : PrimeIndex K) : P.val ∣ K :=
  Ideal.dvd_iff_le.mpr (primeIndex_le K hK.1 P)


-- @@ L49-54 verbatim
lemma residual_pairwise (K : Ideal Eis) (hK : Admissible K) :
    Pairwise (Function.onFun IsCoprime (residual K hK).ideal) := by
  intro P Q hPQ
  apply Ideal.isCoprime_of_isMaximal
  intro h
  exact hPQ (Subtype.ext h)


-- @@ L56-57 verbatim
def reflected {φ σ : Type*} (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K)
    (S : PrimeFamily σ) : PrimeFamily (φ ⊕ (PrimeIndex K ⊕ σ)) := F.sum ((residual K hK).sum S)


-- @@ L59-63 verbatim
lemma reflected_product {φ σ : Type*} [Fintype φ] [Fintype σ]
    (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K) (S : PrimeFamily σ) :
    (∏ i, (F.reflected K hK S).ideal i) = (∏ i, F.ideal i)*K*(∏ i, S.ideal i) := by
  rw [reflected,sum_product,sum_product,residual_product]
  ring


-- @@ L65-81 verbatim
lemma reflected_pairwise {φ σ : Type*} [Fintype σ]
    (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K) (S : PrimeFamily σ)
    (hF : Pairwise (Function.onFun IsCoprime F.ideal))
    (hS : Pairwise (Function.onFun IsCoprime S.ideal))
    (hKS : IsCoprime K (∏ i, S.ideal i))
    (hFK : ∀ f, IsCoprime (F.ideal f) K)
    (hFS : ∀ f i, IsCoprime (F.ideal f) (S.ideal i)) :
    Pairwise (Function.onFun IsCoprime (F.reflected K hK S).ideal) := by
  apply sum_pairwise F _ hF
  · apply sum_pairwise _ S (residual_pairwise K hK) hS
    intro P i
    exact (hKS.of_isCoprime_of_dvd_left (residual_dvd K hK P)).of_isCoprime_of_dvd_right
      (Finset.dvd_prod_of_mem S.ideal (Finset.mem_univ i))
  · intro f i
    cases i with
    | inl P => exact (hFK f).of_isCoprime_of_dvd_right (residual_dvd K hK P)
    | inr i => exact hFS f i


-- @@ L83-94 verbatim
lemma reflected_period {φ σ : Type*}
    (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K) (S : PrimeFamily σ) (N : Eis)
    (hF : ∀ f, IsCoprime (Ideal.span {N}) (F.ideal f))
    (hK' : IsCoprime (Ideal.span {N}) K)
    (hS : ∀ i, IsCoprime (Ideal.span {N}) (S.ideal i)) :
    ∀ i, IsCoprime (Ideal.span {N}) ((F.reflected K hK S).ideal i) := by
  intro i
  cases i with
  | inl f => exact hF f
  | inr i => cases i with
    | inl P => exact hK'.of_isCoprime_of_dvd_right (residual_dvd K hK P)
    | inr i => exact hS i


-- @@ L96-96 verbatim
end PrimeFamily

-- @@ L97-97 verbatim
end

-- @@ L98-98 verbatim
end SevenEighths.InverseReflectedPhase


-- @@ L100-100 verbatim
end OAI
