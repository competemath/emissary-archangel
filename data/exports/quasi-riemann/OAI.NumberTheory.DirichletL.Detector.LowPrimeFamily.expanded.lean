import OAI.NumberTheory.DirichletL.Detector.LowSlotMarks
import OAI.NumberTheory.DirichletL.Detector.LowSlotWeights
import OAI.NumberTheory.DirichletL.Reflection.Canonical


-- @@ L5-5 verbatim
namespace OAI


-- @@ L7-7 verbatim
noncomputable section

-- @@ L8-8 verbatim
open scoped Classical

-- @@ L9-9 verbatim
namespace SevenEighths.ProbePhysical

-- @@ L10-10 verbatim
open CanonicalQuadraticSieve CompletedGauss RayFourExpansion

-- @@ L11-11 verbatim
local notation "O" => ActualEisensteinCubic.O

-- @@ L12-12 verbatim
local notation "Id" => Ideal O


-- @@ L14-19 verbatim
lemma lowCanonicalSelectedPrime_maximal {K : ℕ} (T : Fin K→Finset PrimeIdeal)
    (hT : ∀i P,P∈T i→Supported P.val) (J : Finset (Fin K))
    (b : LowSelectedTuple (fun i=>canonicalSlotSupport (T i)) J) (i : SelectedSlot J) :
    (lowCanonicalSelectedPrime T hT J b i).val.IsMaximal :=
  (Ideal.isPrime_of_prime (lowCanonicalSelectedPrime T hT J b i).property).isMaximal
    (lowCanonicalSelectedPrime T hT J b i).property.ne_zero


-- @@ L21-28 verbatim
lemma lowCanonicalSelectedPrime_good {K : ℕ} (T : Fin K→Finset PrimeIdeal)
    (hT : ∀i P,P∈T i→Supported P.val) (J : Finset (Fin K))
    (b : LowSelectedTuple (fun i=>canonicalSlotSupport (T i)) J) (i : SelectedSlot J) :
    ConcretePrimeRowBridge.goodLambda∉(lowCanonicalSelectedPrime T hT J b i).val ∧
      ringChar (O⧸(lowCanonicalSelectedPrime T hT J b i).val)≠2 := by
  have hs := hT i.val _ (lowCanonicalSelectedPrime_mem T hT J b i)
  exact hs.2 _ ((Ideal.mem_normalizedFactors_iff hs.1).mpr
    ⟨Ideal.isPrime_of_prime (lowCanonicalSelectedPrime T hT J b i).property,le_rfl⟩)


-- @@ L30-36 verbatim
def lowCanonicalPrimeFamily {K : ℕ} (T : Fin K→Finset PrimeIdeal)
    (hT : ∀i P,P∈T i→Supported P.val) (J : Finset (Fin K))
    (b : LowSelectedTuple (fun i=>canonicalSlotSupport (T i)) J) :
    InverseReflectedPhase.PrimeFamily (SelectedSlot J) where
  ideal i := (lowCanonicalSelectedPrime T hT J b i).val
  maximal := lowCanonicalSelectedPrime_maximal T hT J b
  good i := (lowCanonicalSelectedPrime_good T hT J b i).1


-- @@ L38-46 verbatim
lemma lowCanonicalPrimeFamily_generator {K : ℕ} (T : Fin K→Finset PrimeIdeal)
    (hT : ∀i P,P∈T i→Supported P.val) (J : Finset (Fin K))
    (b : LowSelectedTuple (fun i=>canonicalSlotSupport (T i)) J) (i : SelectedSlot J) :
    (lowCanonicalPrimeFamily T hT J b).generator i=(b i).val := by
  let := lowCanonicalSelectedPrime_maximal T hT J b i
  change primaryPrime (lowCanonicalSelectedPrime T hT J b i).val=(b i).val
  rw [primaryPrime_eq_primaryGenerator]
  have hh := congrArg Subtype.val ((canonicalSlotEquiv (T i.val) (hT i.val)).apply_symm_apply (b i))
  simpa only [canonicalSlotEquiv_val,lowCanonicalSelectedPrime] using hh


-- @@ L48-53 verbatim
lemma lowCanonicalPrimeFamily_pairwise {K : ℕ} (T : Fin K→Finset PrimeIdeal)
    (hT : ∀i P,P∈T i→Supported P.val) (hdis : Pairwise (fun i j=>Disjoint (T i) (T j)))
    (J : Finset (Fin K)) (b : LowSelectedTuple (fun i=>canonicalSlotSupport (T i)) J) :
    Pairwise (Function.onFun IsCoprime (lowCanonicalPrimeFamily T hT J b).ideal) := by
  intro i j hij
  exact primeIdeal_coprime _ _ (fun h=>hij (lowCanonicalSelectedPrime_injective T hT hdis J b h))


-- @@ L55-59 verbatim
lemma lowCanonicalPrimeFamily_odd {K : ℕ} (T : Fin K→Finset PrimeIdeal)
    (hT : ∀i P,P∈T i→Supported P.val) (J : Finset (Fin K))
    (b : LowSelectedTuple (fun i=>canonicalSlotSupport (T i)) J) (i : SelectedSlot J) :
    ringChar (O⧸(lowCanonicalPrimeFamily T hT J b).ideal i)≠2 :=
  (lowCanonicalSelectedPrime_good T hT J b i).2


-- @@ L61-68 verbatim
lemma lowCanonicalPrimeFamily_product {K : ℕ} (T : Fin K→Finset PrimeIdeal)
    (hT : ∀i P,P∈T i→Supported P.val) (J : Finset (Fin K))
    (b : LowSelectedTuple (fun i=>canonicalSlotSupport (T i)) J) :
    lowSelectedIdeal (fun i=>canonicalSlotSupport (T i)) J b=
      ∏i : SelectedSlot J,(lowCanonicalPrimeFamily T hT J b).ideal i := by
  rw [lowSelectedIdeal_eq_product]
  simp_rw [lowCanonicalSelectedPrime_span T hT J b]
  rfl


-- @@ L70-87 verbatim
theorem lowCanonicalInverseRow_eq {K : ℕ} (η : HeckeFamily.Character)
    (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (T : Fin K→Finset PrimeIdeal)
    (hT : ∀i P,P∈T i→Supported P.val) (hdis : Pairwise (fun i j=>Disjoint (T i) (T j)))
    (J : Finset (Fin K)) (b : LowSelectedTuple (fun i=>canonicalSlotSupport (T i)) J)
    (R t : ℝ) (σ : RayRing) (m : O) :
    lowMarkedInverseRow η S hS (lowSelectedIdeal (fun i=>canonicalSlotSupport (T i)) J b) R t σ m=
      ∑χ : RayCharacter,ProbeCompleted.correctionCoeff χ*
        InverseMoment.markedCompletedT
          (CanonicalRowCompletion.rowTwist (physicalRayPeriodicBase η S hS σ χ)
            (calibrationForSet S hS).generator 1 m)
          (CompletedHeight.normTwistedSource gaussianFixedWindow t) R
          (fun A=>∏i : SelectedSlot J,if (lowCanonicalPrimeFamily T hT J b).ideal i∣A then (1:ℂ) else 0) := by
  unfold lowMarkedInverseRow
  have he : (fun A : Id=>if lowSelectedIdeal (fun i=>canonicalSlotSupport (T i)) J b∣A then (1:ℂ) else 0)=
      (fun A : Id=>∏i : SelectedSlot J,if (lowCanonicalPrimeFamily T hT J b).ideal i∣A then (1:ℂ) else 0) := by
    funext A
    exact lowCanonicalSelected_mark T hT hdis J b A
  rw [he]


-- @@ L89-89 verbatim
end SevenEighths.ProbePhysical

-- @@ L90-90 verbatim
end


-- @@ L92-92 verbatim
end OAI
