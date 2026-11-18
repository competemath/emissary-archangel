import OAI.NumberTheory.DirichletL.Reflection.SupportedChoices
import OAI.NumberTheory.DirichletL.Reflection.TupleFamily


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
namespace SevenEighths.InverseReflectedPhase

-- @@ L7-7 verbatim
open scoped Classical BigOperators

-- @@ L8-8 verbatim
open ActualEisensteinCubic CanonicalQuadraticSieve InverseMoment

-- @@ L9-9 verbatim
noncomputable section

-- @@ L10-10 verbatim
local notation "Eis" => ActualEisensteinCubic.O

-- @@ L11-11 verbatim
variable {σ : Type*} [Fintype σ] [DecidableEq σ]


-- @@ L13-17 verbatim
lemma PrimeFamily.eq_of_ideal_eq {ι : Type*} (P Q : PrimeFamily ι) (h : P.ideal=Q.ideal) : P=Q := by
  cases P
  cases Q
  cases h
  rfl


-- @@ L19-25 verbatim
def slotChoiceFamily (L : σ→Finset (Ideal Eis))
    (hmax : ∀ i,∀ P∈L i,P.IsMaximal)
    (hgood : ∀ i,∀ P∈L i,ConcretePrimeRowBridge.goodLambda∉P)
    (p : ∀ i,L i) : PrimeFamily σ where
  ideal i := (p i).val
  maximal i := hmax i _ (p i).property
  good i := hgood i _ (p i).property


-- @@ L27-36 verbatim
omit [Fintype σ] in
lemma slotChoiceFamily_active (L : σ→Finset (Ideal Eis))
    (hmax : ∀ i,∀ P∈L i,P.IsMaximal)
    (hgood : ∀ i,∀ P∈L i,ConcretePrimeRowBridge.goodLambda∉P)
    (T : Finset σ) (a : ∀ i : T,L i.val) (b : ∀ i : {i // i∉T},L i.val) :
    (slotChoiceFamily L hmax hgood ((slotChoiceSplit L T).symm (a,b))).restrict T=
      slotChoiceFamily (fun i : T => L i.val) (fun i => hmax i.val) (fun i => hgood i.val) a := by
  apply PrimeFamily.eq_of_ideal_eq
  funext i
  exact congrArg Subtype.val (slotChoiceSplit_active L T a b i)


-- @@ L38-49 verbatim
lemma slot_coefficient_split (L : σ→Finset (Ideal Eis)) (T : Finset σ)
    (w : ∀ i,L i→ℂ) (a : ∀ i : T,L i.val) (b : ∀ i : {i // i∉T},L i.val) :
    (∏ i,w i ((slotChoiceSplit L T).symm (a,b) i))=
      (∏ i : T,w i.val (a i))*(∏ i : {i // i∉T},w i.val (b i)) := by
  have he := Fintype.prod_subtype_mul_prod_subtype (fun i : σ => i∈T)
    (fun i => w i ((slotChoiceSplit L T).symm (a,b) i))
  simp only [slotChoiceSplit_active,slotChoiceSplit_inactive] at he
  refine he.symm.trans ?_
  congr 1
  apply Finset.prod_congr (by ext; simp only [Finset.mem_univ])
  intro i hi
  rfl


-- @@ L51-55 verbatim
omit [DecidableEq σ] in
lemma slot_coefficient_norm (L : σ→Finset (Ideal Eis)) (w : ∀ i,L i→ℂ)
    (hw : ∀ i P,‖w i P‖≤1) (p : ∀ i,L i) : ‖∏ i,w i (p i)‖≤1 := by
  rw [norm_prod]
  exact Finset.prod_le_one₀ (fun i _ => norm_nonneg _) (fun i _ => hw i (p i))

-- @@ L56-56 verbatim
end

-- @@ L57-57 verbatim
end SevenEighths.InverseReflectedPhase


-- @@ L59-59 verbatim
end OAI
