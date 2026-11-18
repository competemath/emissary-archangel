import OAI.NumberTheory.DirichletL.Reflection.OriginalFiber
import OAI.NumberTheory.DirichletL.Reflection.ActiveDictionary
import OAI.NumberTheory.DirichletL.Reflection.ReindexReflection


-- @@ L5-5 verbatim
namespace OAI


-- @@ L7-7 verbatim
namespace SevenEighths.InverseReflectedPhase

-- @@ L8-8 verbatim
open scoped Classical BigOperators

-- @@ L9-9 verbatim
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment

-- @@ L10-10 verbatim
noncomputable section

-- @@ L11-11 verbatim
local notation "Eis" => ActualEisensteinCubic.O


-- @@ L13-16 verbatim
def poolPrimeFamily (R Q Q₀ : Ideal Eis) : PrimeFamily (FreeReflection.pool R Q Q₀) where
  ideal P := P.val
  maximal P := FreeReflection.pool_maximal R Q Q₀ P
  good P := FreeReflection.pool_good R Q Q₀ P


-- @@ L18-18 verbatim
variable {σ : Type*} [Fintype σ] {m f z : Eis} (D : GoodMaskRowData m f z)

-- @@ L19-24 verbatim
variable (R I F Q₀ : Ideal Eis) (hR : R≠0) (hI : I≠0) (hF : Squarefree F)
    (hm : m≠0) (hf : Ideal.span {f}=F) (hz : Ideal.span {z}=I)
    (hbad : ∀ P∈fixedBadPrimes, P∣Ideal.span {m}*F)
    (hcop : IsCoprime Q₀ (rowResidualPart I (Ideal.span {m}*F)))
    (hpow : rowPowerfulPart R=rowPowerfulPart I)
    (hmask : rowMaskPart R (Ideal.span {m}*F)=rowMaskPart I (Ideal.span {m}*F))

-- @@ L25-25 verbatim
local notation "E" => D.primeFiberEquiv R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask

-- @@ L26-26 verbatim
local notation "K" => rowResidualPart I (Ideal.span (Set.singleton m)*F)

-- @@ L27-27 verbatim
local notation "hK" => rowResidualPart_admissible I (Ideal.span (Set.singleton m)*F) hbad


-- @@ L29-43 verbatim
lemma original_active_family_ideal (S : PrimeFamily σ)
    (B : Finset (FreeReflection.pool R (Ideal.span {m}*F) Q₀)) (T : Finset σ)
    (x : B⊕(PrimeIndex K⊕T)) :
    (((freePrimeFamily D.movingIdeal Q₀ D.movingSupported).sum S).restrict
      (markedActiveSet E B T)).ideal (markedActiveEquiv E B T x)=
    (((poolPrimeFamily R (Ideal.span {m}*F) Q₀).restrict B).reflected K hK (S.restrict T)).ideal x := by
  cases x with
  | inl b =>
    change (E (Sum.inr b.val)).val.val=b.val.val
    exact D.primeFiberEquiv_val R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask (Sum.inr b.val)
  | inr x => cases x with
    | inl a =>
      change (E (Sum.inl a)).val.val=a.val
      exact D.primeFiberEquiv_val R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask (Sum.inl a)
    | inr t => rfl


-- @@ L45-51 verbatim
lemma original_active_family_generator (S : PrimeFamily σ)
    (B : Finset (FreeReflection.pool R (Ideal.span {m}*F) Q₀)) (T : Finset σ)
    (x : B⊕(PrimeIndex K⊕T)) :
    (((freePrimeFamily D.movingIdeal Q₀ D.movingSupported).sum S).restrict
      (markedActiveSet E B T)).generator (markedActiveEquiv E B T x)=
    (((poolPrimeFamily R (Ideal.span {m}*F) Q₀).restrict B).reflected K hK (S.restrict T)).generator x :=
  congrArg primaryPrime (original_active_family_ideal D R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask S B T x)


-- @@ L53-65 verbatim
lemma original_active_exponent
    (B : Finset (FreeReflection.pool R (Ideal.span {m}*F) Q₀)) (T : Finset σ)
    (x : B⊕(PrimeIndex K⊕T)) :
    Sum.elim (fun P : FreePrimeIndex D.movingIdeal Q₀ =>
      (UniqueFactorizationMonoid.normalizedFactors D.movingIdeal).count P.val.val%6) (fun _ : σ => 0)
      (markedActiveEquiv E B T x).val =
    Sum.elim (fun b : B => completedLocalExponent R F b.val.val)
      (Sum.elim (fun _ : PrimeIndex K => 1) (fun _ : T => 0)) x := by
  cases x with
  | inl b => exact D.primeFiberEquiv_exponent R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask (Sum.inr b.val)
  | inr x => cases x with
    | inl a => exact D.primeFiberEquiv_exponent R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask (Sum.inl a)
    | inr t => rfl


-- @@ L67-78 verbatim
lemma original_active_marks
    (B : Finset (FreeReflection.pool R (Ideal.span {m}*F) Q₀)) (T : Finset σ) :
    reindexMarks (markedActiveEquiv E B T) (activeMarks (markedActiveSet E B T) markedSumSlots)=
    Finset.univ.filter (fun x : B⊕(PrimeIndex K⊕T) => match x with
      | Sum.inr (Sum.inr _) => True | _ => False) := by
  ext x
  simp only [mem_reindexMarks,mem_activeMarks,Finset.mem_filter,Finset.mem_univ,true_and]
  cases x with
  | inl b => simp [markedActiveEquiv_frozen,markedSumSlots]
  | inr x => cases x with
    | inl a => simp [markedActiveEquiv_residual,markedSumSlots]
    | inr t => simp [markedActiveEquiv_slot,markedSumSlots]

-- @@ L79-79 verbatim
end

-- @@ L80-80 verbatim
end SevenEighths.InverseReflectedPhase


-- @@ L82-82 verbatim
end OAI
