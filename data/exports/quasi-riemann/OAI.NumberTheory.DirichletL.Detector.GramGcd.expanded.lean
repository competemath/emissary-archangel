import OAI.NumberTheory.DirichletL.Detector.GramJointSource


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

-- @@ L11-11 verbatim
abbrev SupportedIdeal := {I : Id // Supported I}


-- @@ L13-15 verbatim
lemma gram_supported_divisor (I D : Id) (hI : Supported I) (hd : D∣I) : Supported D := by
  obtain ⟨J,rfl⟩ := hd
  exact (supported_mul_iff D J).mp hI |>.1


-- @@ L17-18 verbatim
lemma gram_supported_quotient (I D : Id) (hI : Supported I) (hd : D∣I) :
    Supported (idealQuotient D I) := gram_supported_divisor I _ hI (idealQuotient_dvd hd)


-- @@ L20-21 verbatim
def gcdCommon (I J : SupportedIdeal) : SupportedIdeal :=
  ⟨gcd I.val J.val,gram_supported_divisor I.val _ I.property (gcd_dvd_left _ _)⟩


-- @@ L23-25 verbatim
def gcdLeft (I J : SupportedIdeal) : SupportedIdeal :=
  ⟨idealQuotient (gcdCommon I J).val I.val,
    gram_supported_quotient I.val _ I.property (gcd_dvd_left _ _)⟩


-- @@ L27-29 verbatim
def gcdRight (I J : SupportedIdeal) : SupportedIdeal :=
  ⟨idealQuotient (gcdCommon I J).val J.val,
    gram_supported_quotient J.val _ J.property (gcd_dvd_right _ _)⟩


-- @@ L31-33 verbatim
lemma gcd_residual_coprime (I J : SupportedIdeal) : IsCoprime (gcdLeft I J).val (gcdRight I J).val :=
  (gcd_eq_iff_quotient_coprime _ _ _ (gcdCommon I J).property.1
    (gcd_dvd_left _ _) (gcd_dvd_right _ _)).mp rfl


-- @@ L35-36 verbatim
lemma gcd_common_left (I J : SupportedIdeal) : (gcdCommon I J).val*(gcdLeft I J).val=I.val :=
  idealQuotient_mul (gcd_dvd_left _ _)


-- @@ L38-39 verbatim
lemma gcd_common_right (I J : SupportedIdeal) : (gcdCommon I J).val*(gcdRight I J).val=J.val :=
  idealQuotient_mul (gcd_dvd_right _ _)


-- @@ L41-41 verbatim
abbrev CoprimeTriple := {t : SupportedIdeal×SupportedIdeal×SupportedIdeal // IsCoprime t.2.1.val t.2.2.val}


-- @@ L43-44 verbatim
def gcdTriple (p : SupportedIdeal×SupportedIdeal) : CoprimeTriple :=
  ⟨(gcdCommon p.1 p.2,gcdLeft p.1 p.2,gcdRight p.1 p.2),gcd_residual_coprime p.1 p.2⟩


-- @@ L46-48 verbatim
def multiplyTriple (t : CoprimeTriple) : SupportedIdeal×SupportedIdeal :=
  (⟨t.val.1.val*t.val.2.1.val,(supported_mul_iff _ _).mpr ⟨t.val.1.property,t.val.2.1.property⟩⟩,
   ⟨t.val.1.val*t.val.2.2.val,(supported_mul_iff _ _).mpr ⟨t.val.1.property,t.val.2.2.property⟩⟩)


-- @@ L50-53 verbatim
lemma multiply_gcdTriple (p : SupportedIdeal×SupportedIdeal) : multiplyTriple (gcdTriple p)=p := by
  apply Prod.ext <;> apply Subtype.ext
  · exact gcd_common_left _ _
  · exact gcd_common_right _ _


-- @@ L55-69 verbatim
lemma gcdTriple_multiply (t : CoprimeTriple) : gcdTriple (multiplyTriple t)=t := by
  have he : gcd (t.val.1.val*t.val.2.1.val) (t.val.1.val*t.val.2.2.val)=t.val.1.val := by
    rw [_root_.gcd_mul_left,normalize_eq,Ideal.isCoprime_iff_gcd.mp t.property,mul_one]
  apply Subtype.ext
  apply Prod.ext
  · exact Subtype.ext he
  · apply Prod.ext <;> apply Subtype.ext
    · change idealQuotient (gcd _ _) (t.val.1.val*t.val.2.1.val)=t.val.2.1.val
      dsimp only [multiplyTriple]
      rw [he]
      exact mul_left_cancel₀ t.val.1.property.1 (idealQuotient_mul (dvd_mul_right _ _))
    · change idealQuotient (gcd _ _) (t.val.1.val*t.val.2.2.val)=t.val.2.2.val
      dsimp only [multiplyTriple]
      rw [he]
      exact mul_left_cancel₀ t.val.1.property.1 (idealQuotient_mul (dvd_mul_right _ _))


-- @@ L71-75 verbatim
def gcdPairEquiv : (SupportedIdeal×SupportedIdeal)≃CoprimeTriple where
  toFun := gcdTriple
  invFun := multiplyTriple
  left_inv := multiply_gcdTriple
  right_inv := gcdTriple_multiply


-- @@ L77-79 verbatim
lemma gcdPair_tsum (f : SupportedIdeal×SupportedIdeal→ℂ) :
    (∑'p,f p)=∑'t : CoprimeTriple,f (multiplyTriple t) := by
  exact (gcdPairEquiv.symm.tsum_eq f).symm


-- @@ L81-81 verbatim
end SevenEighths.ProbeGramCommon

-- @@ L82-82 verbatim
end


-- @@ L84-84 verbatim
end OAI
