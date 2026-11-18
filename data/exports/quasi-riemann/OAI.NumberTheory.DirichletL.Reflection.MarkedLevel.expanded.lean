import OAI.NumberTheory.DirichletL.Reflection.MarkedActualSource


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
namespace SevenEighths.InverseReflectedPhase

-- @@ L6-6 verbatim
open scoped Classical BigOperators

-- @@ L7-7 verbatim
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment

-- @@ L8-8 verbatim
noncomputable section

-- @@ L9-9 verbatim
local notation "Eis" => ActualEisensteinCubic.O


-- @@ L11-20 verbatim
lemma PrimeFamily.level_coprime {ι : Type*} (P : PrimeFamily ι)
    (Q : Ideal Eis) (c : Eis) (hcQ : Ideal.span {c}=Ideal.span {(9:Eis)}*Q)
    (hQ : ∀ i, IsCoprime Q (P.ideal i)) (i : ι) :
    IsCoprime (Ideal.span {(9:Eis)*c}) (P.ideal i) := by
  have h9 : IsCoprime (Ideal.span {(9:Eis)}) (P.ideal i) := by
    rw [← P.generator_span i]
    apply (Ideal.isCoprime_span_singleton_iff _ _).mpr
    exact (ShortDraftCRT.primary_coprime_nine _ (P.generator_primary i)).symm
  rw [← Ideal.span_singleton_mul_span_singleton,hcQ]
  exact h9.mul_left (h9.mul_left (hQ i))


-- @@ L22-31 verbatim
lemma markedRowFamily_period {σ : Type*} {m f z : Eis}
    (D : GoodMaskRowData m f z) (S : PrimeFamily σ) (Q : Ideal Eis)
    (hS : ∀ i, IsCoprime (Q*Ideal.span {(72:Eis)}) (S.ideal i))
    (c : Eis) (hcQ : Ideal.span {c}=Ideal.span {(9:Eis)}*(Q*Ideal.span {(72:Eis)})) :
    ∀ i, IsCoprime (Ideal.span {(9:Eis)*c}) ((markedRowFamily D S Q).ideal i) := by
  apply PrimeFamily.level_coprime _ _ _ hcQ
  intro i
  cases i with
  | inl P => exact freePrimeIndex_coprime _ _ P
  | inr i => exact hS i


-- @@ L33-41 verbatim
lemma markedRowFamily_odd {σ : Type*} {m f z : Eis}
    (D : GoodMaskRowData m f z) (S : PrimeFamily σ) (Q : Ideal Eis)
    (hS : ∀ i, ringChar (Eis⧸S.ideal i)≠2) :
    ∀ i, ringChar (Eis⧸(markedRowFamily D S Q).ideal i)≠2 := by
  intro i
  cases i with
  | inl P => exact (supported_factors_good D.movingIdeal D.movingSupported P.val.val
      (Multiset.mem_toFinset.mp P.val.property)).2.2
  | inr i => exact hS i


-- @@ L43-49 verbatim
lemma markedRowExponent_lt {σ : Type*} {m f z : Eis}
    (D : GoodMaskRowData m f z) (Q : Ideal Eis) :
    ∀ i : FreePrimeIndex D.movingIdeal (Q*Ideal.span {(72:Eis)})⊕σ, markedRowExponent D Q i<6 := by
  intro i
  cases i with
  | inl P => exact Nat.mod_lt _ (by norm_num)
  | inr i => norm_num [markedRowExponent]

-- @@ L50-50 verbatim
end

-- @@ L51-51 verbatim
end SevenEighths.InverseReflectedPhase


-- @@ L53-53 verbatim
end OAI
