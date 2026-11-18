import OAI.NumberTheory.DirichletL.Detector.LowSlotPolynomial
import OAI.NumberTheory.DirichletL.Detector.CanonicalSlots


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
noncomputable section

-- @@ L7-7 verbatim
open scoped Classical

-- @@ L8-8 verbatim
namespace SevenEighths.ProbePhysical

-- @@ L9-9 verbatim
open CanonicalQuadraticSieve

-- @@ L10-10 verbatim
local notation "O" => ActualEisensteinCubic.O

-- @@ L11-11 verbatim
local notation "Id" => Ideal O


-- @@ L13-17 verbatim
lemma lowSelectedIdeal_eq_product {K : ℕ} (slots : Fin K→Finset O) (J : Finset (Fin K))
    (b : LowSelectedTuple slots J) :
    lowSelectedIdeal slots J b=∏i : SelectedSlot J,Ideal.span {(b i).val} := by
  change CanonicalRowCompletion.principalIdealHom (∏i : SelectedSlot J,(b i).val)=_
  exact map_prod CanonicalRowCompletion.principalIdealHom _ _


-- @@ L19-27 verbatim
lemma lowSelectedIdeal_dvd_iff {K : ℕ} (slots : Fin K→Finset O) (J : Finset (Fin K))
    (b : LowSelectedTuple slots J)
    (hcop : Pairwise (fun i j : SelectedSlot J=>IsCoprime (Ideal.span {(b i).val}) (Ideal.span {(b j).val})))
    (A : Id) : lowSelectedIdeal slots J b∣A ↔ ∀i : SelectedSlot J,Ideal.span {(b i).val}∣A := by
  rw [lowSelectedIdeal_eq_product]
  constructor
  · intro h i
    exact (Finset.dvd_prod_of_mem (fun i : SelectedSlot J=>Ideal.span {(b i).val}) (Finset.mem_univ i)).trans h
  · exact Fintype.prod_dvd_of_coprime hcop


-- @@ L29-40 verbatim
lemma lowSelectedIdeal_mark {K : ℕ} (slots : Fin K→Finset O) (J : Finset (Fin K))
    (b : LowSelectedTuple slots J)
    (hcop : Pairwise (fun i j : SelectedSlot J=>IsCoprime (Ideal.span {(b i).val}) (Ideal.span {(b j).val})))
    (A : Id) :
    (if lowSelectedIdeal slots J b∣A then (1:ℂ) else 0)=
      ∏i : SelectedSlot J,if Ideal.span {(b i).val}∣A then (1:ℂ) else 0 := by
  rw [lowSelectedIdeal_dvd_iff slots J b hcop]
  by_cases h : ∀i : SelectedSlot J,Ideal.span {(b i).val}∣A
  · simp [h]
  · obtain ⟨i,hi⟩ := not_forall.mp h
    rw [ite_eq_right (fun hall=>hi (hall i))]
    exact (Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)).symm


-- @@ L42-45 verbatim
def lowCanonicalSelectedPrime {K : ℕ} (T : Fin K→Finset PrimeIdeal)
    (hT : ∀i P,P∈T i→Supported P.val) (J : Finset (Fin K))
    (b : LowSelectedTuple (fun i=>canonicalSlotSupport (T i)) J) (i : SelectedSlot J) : PrimeIdeal :=
  ((canonicalSlotEquiv (T i.val) (hT i.val)).symm (b i)).val


-- @@ L47-51 verbatim
lemma lowCanonicalSelectedPrime_mem {K : ℕ} (T : Fin K→Finset PrimeIdeal)
    (hT : ∀i P,P∈T i→Supported P.val) (J : Finset (Fin K))
    (b : LowSelectedTuple (fun i=>canonicalSlotSupport (T i)) J) (i : SelectedSlot J) :
    lowCanonicalSelectedPrime T hT J b i∈T i.val :=
  ((canonicalSlotEquiv (T i.val) (hT i.val)).symm (b i)).property


-- @@ L53-59 verbatim
lemma lowCanonicalSelectedPrime_span {K : ℕ} (T : Fin K→Finset PrimeIdeal)
    (hT : ∀i P,P∈T i→Supported P.val) (J : Finset (Fin K))
    (b : LowSelectedTuple (fun i=>canonicalSlotSupport (T i)) J) (i : SelectedSlot J) :
    Ideal.span {(b i).val}=(lowCanonicalSelectedPrime T hT J b i).val := by
  have hh := canonicalSlotEquiv_span (T i.val) (hT i.val)
    ((canonicalSlotEquiv (T i.val) (hT i.val)).symm (b i))
  simpa only [Equiv.apply_symm_apply,lowCanonicalSelectedPrime] using hh


-- @@ L61-69 verbatim
lemma lowCanonicalSelectedPrime_injective {K : ℕ} (T : Fin K→Finset PrimeIdeal)
    (hT : ∀i P,P∈T i→Supported P.val) (hdis : Pairwise (fun i j=>Disjoint (T i) (T j)))
    (J : Finset (Fin K)) (b : LowSelectedTuple (fun i=>canonicalSlotSupport (T i)) J) :
    Function.Injective (lowCanonicalSelectedPrime T hT J b) := by
  intro i j hij
  apply Subtype.ext
  by_contra hne
  exact Finset.disjoint_left.mp (hdis hne) (lowCanonicalSelectedPrime_mem T hT J b i)
    (hij.symm ▸ lowCanonicalSelectedPrime_mem T hT J b j)


-- @@ L71-77 verbatim
lemma lowCanonicalSelected_coprime {K : ℕ} (T : Fin K→Finset PrimeIdeal)
    (hT : ∀i P,P∈T i→Supported P.val) (hdis : Pairwise (fun i j=>Disjoint (T i) (T j)))
    (J : Finset (Fin K)) (b : LowSelectedTuple (fun i=>canonicalSlotSupport (T i)) J) :
    Pairwise (fun i j : SelectedSlot J=>IsCoprime (Ideal.span {(b i).val}) (Ideal.span {(b j).val})) := by
  intro i j hij
  rw [lowCanonicalSelectedPrime_span T hT J b i,lowCanonicalSelectedPrime_span T hT J b j]
  exact primeIdeal_coprime _ _ (fun h=>hij (lowCanonicalSelectedPrime_injective T hT hdis J b h))


-- @@ L79-85 verbatim
theorem lowCanonicalSelected_mark {K : ℕ} (T : Fin K→Finset PrimeIdeal)
    (hT : ∀i P,P∈T i→Supported P.val) (hdis : Pairwise (fun i j=>Disjoint (T i) (T j)))
    (J : Finset (Fin K)) (b : LowSelectedTuple (fun i=>canonicalSlotSupport (T i)) J) (A : Id) :
    (if lowSelectedIdeal (fun i=>canonicalSlotSupport (T i)) J b∣A then (1:ℂ) else 0)=
      ∏i : SelectedSlot J,if (lowCanonicalSelectedPrime T hT J b i).val∣A then (1:ℂ) else 0 := by
  rw [lowSelectedIdeal_mark _ J b (lowCanonicalSelected_coprime T hT hdis J b)]
  simp_rw [lowCanonicalSelectedPrime_span T hT J b]


-- @@ L87-87 verbatim
end SevenEighths.ProbePhysical

-- @@ L88-88 verbatim
end


-- @@ L90-90 verbatim
end OAI
