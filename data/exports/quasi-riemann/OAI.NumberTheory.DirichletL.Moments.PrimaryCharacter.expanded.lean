import OAI.NumberTheory.DirichletL.Moments.FixedRay


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section

-- @@ L6-6 verbatim
open scoped Classical


-- @@ L8-8 verbatim
namespace SevenEighths.CenteredMomentPrimaryCharacter

-- @@ L9-9 verbatim
open HeckeFamily HeckeRowClosure CanonicalRowCompletion CanonicalQuadraticSieve

-- @@ L10-10 verbatim
open CenteredMomentPrimary CenteredMomentCommonSupport

-- @@ L11-11 verbatim
local notation "O" => ActualEisensteinCubic.O

-- @@ L12-12 verbatim
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda


-- @@ L14-17 verbatim
def rawPrimaryHom (r : O) (χ : MulChar (Residue r) ℂ) : O →* ℂ where
  toFun n := primaryIdealCharacter r χ (Ideal.span {n})
  map_one' := by simp [← Ideal.one_eq_top]
  map_mul' x y := by rw [← Ideal.span_singleton_mul_span_singleton,map_mul]


-- @@ L19-20 verbatim
def maskedPrimaryHom (r : O) (χ : MulChar (Residue r) ℂ) : O →* ℂ :=
  coprimalityMask (3:O)*rawPrimaryHom r χ


-- @@ L22-27 verbatim
theorem maskedPrimaryHom_unit_mul (r : O) (χ : MulChar (Residue r) ℂ) (u : Oˣ) (n : O) :
    maskedPrimaryHom r χ ((u:O)*n)=maskedPrimaryHom r χ n := by
  change (if IsCoprime (3:O) ((u:O)*n) then (1:ℂ) else 0)*
      primaryIdealCharacter r χ (Ideal.span {(u:O)*n}) =
    (if IsCoprime (3:O) n then (1:ℂ) else 0)*primaryIdealCharacter r χ (Ideal.span {n})
  rw [isCoprime_mul_unit_left_right u.isUnit,Ideal.span_singleton_mul_left_unit u.isUnit]


-- @@ L29-35 verbatim
theorem maskedPrimaryHom_ramified (r : O) (χ : MulChar (Residue r) ℂ) (n : O) (hn : λ₀∣n) :
    maskedPrimaryHom r χ n=0 := by
  have h3 : λ₀∣(3:O) := (dvd_pow_self λ₀ (by decide : 2≠0)).trans ActualEisensteinCubic.lambda_sq_dvd_three
  have hc : ¬IsCoprime (3:O) n := fun hc =>
    PrimaryIdealUnitReindex.lambda_prime_actual.not_isUnit (hc.isUnit_of_dvd' h3 hn)
  change (if IsCoprime (3:O) n then (1:ℂ) else 0)*_=0
  rw [ite_eq_right hc,zero_mul]


-- @@ L37-42 verbatim
theorem maskedPrimaryHom_primary (r : O) (χ : MulChar (Residue r) ℂ) (n : O)
    (hn : λ₀^2∣n-1) : maskedPrimaryHom r χ n=χ (Ideal.Quotient.mk _ n) := by
  change (if IsCoprime (3:O) n then (1:ℂ) else 0)*
    χ (Ideal.Quotient.mk _ (CompletedGauss.primaryGenerator (Ideal.span {n})))=_
  rw [ite_eq_left (CubicEisenstein.primary_coprime_three n hn).symm,one_mul,
    CompletedGauss.primaryGenerator_span n (CubicJacobiGlobal.primary_ne_zero n hn) hn]


-- @@ L44-54 verbatim
theorem maskedPrimaryHom_periodic (r : O) (χ : MulChar (Residue r) ℂ) :
    CanonicalCoefficientClass.FactorsModulo (Ideal.span {3*r}) (maskedPrimaryHom r χ) := by
  let F : O →* ℂ := χ.toMonoidHom.comp (Ideal.Quotient.mk (Ideal.span {r})).toMonoidHom
  apply periodic_of_primary _ _ _ F _ (maskedPrimaryHom_unit_mul r χ)
    (maskedPrimaryHom_ramified r χ) (maskedPrimaryHom_primary r χ)
  · apply Ideal.span_singleton_le_span_singleton.mpr
    exact ActualEisensteinCubic.lambda_sq_dvd_three.trans (dvd_mul_right _ _)
  · intro x y hxy
    apply congrArg χ
    apply Ideal.Quotient.eq.mpr
    exact Ideal.mem_span_singleton.mpr ((dvd_mul_left r 3).trans (Ideal.mem_span_singleton.mp hxy))


-- @@ L56-60 verbatim
def primaryCharacter (r : O) (hr : r≠0) (χ : MulChar (Residue r) ℂ) : Character :=
  rowCharacter (Ideal.span {3*r})
    (Ideal.span_singleton_eq_bot.not.mpr (mul_ne_zero (by norm_num) hr))
    (maskedPrimaryHom r χ) (maskedPrimaryHom_periodic r χ)
    (fun u => by simpa only [mul_one,map_one] using maskedPrimaryHom_unit_mul r χ u 1)


-- @@ L62-63 verbatim
@[simp] theorem primaryCharacter_modulus (r : O) (hr : r≠0) (χ : MulChar (Residue r) ℂ) :
    (primaryCharacter r hr χ).modulus=Ideal.span {3*r} := rfl


-- @@ L65-76 verbatim
theorem primaryCharacter_primary (r : O) (hr : r≠0) (χ : MulChar (Residue r) ℂ) (n : O)
    (hn : λ₀^2∣n-1) : elementCoeff (primaryCharacter r hr χ) n=χ (Ideal.Quotient.mk _ n) := by
  rw [primaryCharacter,elementCoeff_rowCharacter,maskedPrimaryHom_primary r χ n hn]
  split_ifs with hc
  · rfl
  · symm
    apply MulChar.map_nonunit
    intro hu
    apply hc
    apply isUnit_residue_of_coprime
    apply (CubicEisenstein.primary_coprime_three n hn).symm.mul_left
    exact (CubicEisenstein.isUnit_quotient_span_iff r n).mp hu


-- @@ L78-91 verbatim
theorem primaryCharacter_all (r : O) (hr : r≠0) (χ : MulChar (Residue r) ℂ) (n : O) :
    elementCoeff (primaryCharacter r hr χ) n=maskedPrimaryHom r χ n := by
  by_cases hn : λ₀∣n
  · rw [primaryCharacter,elementCoeff_rowCharacter,maskedPrimaryHom_ramified r χ n hn]
    split_ifs <;> rfl
  · have hg := (PrimaryIdealUnitReindex.primaryGenerator_span_ne_zero_iff n).mpr hn
    have hs := CompletedGauss.primaryGenerator_spec (Ideal.span {n}) hg
    obtain ⟨u,hu⟩ := Ideal.span_singleton_eq_span_singleton.mp hs.1.symm
    have hp : λ₀^2∣(u:O)*n-1 := by
      have hp' : λ₀^2∣CompletedGauss.primaryGenerator (Ideal.span {n})-1 := hs.2
      rwa [mul_comm,hu]
    rw [← elementCoeff_unit_mul (primaryCharacter r hr χ) u n,
      ← maskedPrimaryHom_unit_mul r χ u n,primaryCharacter_primary r hr χ _ hp,
      maskedPrimaryHom_primary r χ _ hp]


-- @@ L93-102 verbatim
theorem primaryCharacter_ideal (r : O) (hr : r≠0) (χ : MulChar (Residue r) ℂ)
    (I : Ideal O) (hI : Supported I) :
    idealCoeff (primaryCharacter r hr χ) I=
      χ (Ideal.Quotient.mk _ (CompletedGauss.primaryGenerator I)) := by
  have hn := supported_primaryGenerator_ne_zero I hI
  have hs := CompletedGauss.primaryGenerator_spec I hn
  calc
    _ = elementCoeff (primaryCharacter r hr χ) (CompletedGauss.primaryGenerator I) := by
      rw [← idealCoeff_span _ hn,hs.1]
    _ = _ := primaryCharacter_primary r hr χ _ hs.2


-- @@ L104-107 verbatim
theorem primaryCharacter_modulus_norm (r : O) (hr : r≠0) (χ : MulChar (Residue r) ℂ) :
    (primaryCharacter r hr χ).modulus.absNorm=
      (Ideal.span {(3:O)}).absNorm*(Ideal.span {r}).absNorm := by
  rw [primaryCharacter_modulus,← Ideal.span_singleton_mul_span_singleton,map_mul]


-- @@ L109-109 verbatim
end SevenEighths.CenteredMomentPrimaryCharacter


-- @@ L111-111 verbatim
end


-- @@ L113-113 verbatim
end OAI
