import OAI.NumberTheory.DirichletL.Detector.GramGcd


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section

-- @@ L6-6 verbatim
open scoped Classical

-- @@ L7-7 verbatim
namespace SevenEighths.ProbeGramCommon

-- @@ L8-8 verbatim
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss

-- @@ L9-9 verbatim
local notation "O" => ActualEisensteinCubic.O

-- @@ L10-10 verbatim
local notation "Id" => Ideal O


-- @@ L12-12 verbatim
abbrev DivisibleSupported (D : SupportedIdeal) := {I : SupportedIdeal // D.val∣I.val}


-- @@ L14-15 verbatim
def supportedIdealProduct (D J : SupportedIdeal) : SupportedIdeal :=
  ⟨D.val*J.val,(supported_mul_iff _ _).mpr ⟨D.property,J.property⟩⟩


-- @@ L17-26 verbatim
def supportedDilationEquiv (D : SupportedIdeal) : SupportedIdeal≃DivisibleSupported D where
  toFun J := ⟨supportedIdealProduct D J,dvd_mul_right _ _⟩
  invFun I := ⟨idealQuotient D.val I.val.val,gram_supported_quotient I.val.val D.val I.val.property I.property⟩
  left_inv J := by
    apply Subtype.ext
    exact mul_left_cancel₀ D.property.1 (idealQuotient_mul (dvd_mul_right D.val J.val))
  right_inv I := by
    apply Subtype.ext
    apply Subtype.ext
    exact idealQuotient_mul I.property


-- @@ L28-30 verbatim
lemma supported_dilation_generator (D J : SupportedIdeal) :
    primaryGenerator (supportedIdealProduct D J).val=primaryGenerator D.val*primaryGenerator J.val :=
  primaryGenerator_mul _ _


-- @@ L32-34 verbatim
lemma supported_dilation_norm (D J : SupportedIdeal) :
    Ideal.absNorm (supportedIdealProduct D J).val=Ideal.absNorm D.val*Ideal.absNorm J.val :=
  map_mul Ideal.absNorm _ _


-- @@ L36-41 verbatim
theorem supported_divisor_tsum (D : SupportedIdeal) (f : SupportedIdeal→ℂ) :
    (∑'I : SupportedIdeal,if D.val∣I.val then f I else 0)=
      ∑'J : SupportedIdeal,f (supportedIdealProduct D J) := by
  change (∑'I : SupportedIdeal,({I : SupportedIdeal | D.val∣I.val}.indicator f) I)=_
  rw [←tsum_subtype (s:={I : SupportedIdeal | D.val∣I.val}) (f:=f)]
  exact (supportedDilationEquiv D).tsum_eq (fun I : DivisibleSupported D=>f I.val) |>.symm


-- @@ L43-55 verbatim
theorem supported_divisor_pair_tsum (D : SupportedIdeal) (f : SupportedIdeal→SupportedIdeal→ℂ) :
    (∑'I : SupportedIdeal,∑'J : SupportedIdeal,
      if D.val∣I.val ∧ D.val∣J.val then f I J else 0)=
      ∑'I : SupportedIdeal,∑'J : SupportedIdeal,
        f (supportedIdealProduct D I) (supportedIdealProduct D J) := by
  have hinner (I : SupportedIdeal) : (∑'J : SupportedIdeal,if D.val∣I.val ∧ D.val∣J.val then f I J else 0)=
      if D.val∣I.val then ∑'J : SupportedIdeal,f I (supportedIdealProduct D J) else 0 := by
    by_cases hI : D.val∣I.val
    · simp only [hI,true_and,ite_true]
      exact supported_divisor_tsum D (f I)
    · simp [hI]
  simp_rw [hinner]
  exact supported_divisor_tsum D (fun I=>∑'J : SupportedIdeal,f I (supportedIdealProduct D J))


-- @@ L57-57 verbatim
end SevenEighths.ProbeGramCommon

-- @@ L58-58 verbatim
end


-- @@ L60-60 verbatim
end OAI
