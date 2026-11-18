import OAI.NumberTheory.DirichletL.Moments.Active


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section

-- @@ L6-6 verbatim
open scoped BigOperators Classical

-- @@ L7-7 verbatim
local notation "O" => ActualEisensteinCubic.O

-- @@ L8-8 verbatim
namespace SevenEighths.CenteredMomentPrimitive

-- @@ L9-9 verbatim
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ConcreteTraceCRT

-- @@ L10-10 verbatim
open CenteredMomentCorrelation CenteredMomentCommonSupport CenteredMomentFourier


-- @@ L12-18 verbatim
def primitiveCharacter {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hg : ∀ i, goodLambda ∉ P i) (j : ι → ℕ) :
    MulChar (Residue (finitePrimeModulus P)) ℂ :=
  crtCharacter ((Ideal.quotEquivOfEq (span_finitePrimeModulus P)).trans
    (IdealGaussCRT.quotientProdEquivPi P hcop)) (fun i => actualSextic (P i) (hg i) ^ j i)


-- @@ L20-25 verbatim
theorem primitiveCharacter_apply {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hg : ∀ i, goodLambda ∉ P i) (j : ι → ℕ) (x : Residue (finitePrimeModulus P)) :
    primitiveCharacter P hcop hg j x =
      principalSexticRow P hcop hg j (finitePrimeModulus P) (span_finitePrimeModulus P) x := rfl


-- @@ L27-34 verbatim
@[simp] theorem primitiveCharacter_mk {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hg : ∀ i, goodLambda ∉ P i) (j : ι → ℕ) (x : O) :
    primitiveCharacter P hcop hg j (Ideal.Quotient.mk _ x) =
      finiteSexticRow P hg j x := by
  exact (primitiveCharacter_apply P hcop hg j _).trans
    (principalSexticRow_mk P hcop hg j (finitePrimeModulus P) (span_finitePrimeModulus P) x)


-- @@ L36-54 verbatim
theorem primitive_gauss_transform {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hg : ∀ i, goodLambda ∉ P i) (hchar : ∀ i, ringChar (O ⧸ P i) ≠ 2)
    (j : ι → ℕ) (hj0 : ∀ i, j i ≠ 0) (hj6 : ∀ i, j i < 6) (h : O) :
    residueGauss (finitePrimeModulus P) (finitePrimeModulus_ne_zero P)
      (primitiveCharacter P hcop hg j) (Ideal.Quotient.mk _ h) =
      star (finiteSexticRow P hg j h) * canonicalGaussSum P hcop hg j := by
  let r := finitePrimeModulus P
  let := finite_quotient_span (finitePrimeModulus_ne_zero P)
  let : Fintype (Residue r) := Fintype.ofFinite _
  let e := Ideal.quotEquivOfEq (span_finitePrimeModulus P)
  let : Fintype (O ⧸ ∏ i, P i) := Fintype.ofEquiv (Residue r) e.toEquiv
  let (i : ι) : Fintype (O ⧸ P i) := Fintype.ofFinite _
  simp only [residueGauss, tsum_fintype, primitiveCharacter_apply]
  rw [canonical_principal_gauss_transform P hcop hg hchar j hj0 hj6
    (finitePrimeModulus P) (span_finitePrimeModulus P)]
  exact congrArg (fun z : ℂ => star z * canonicalGaussSum P hcop hg j)
    (principalSexticRow_mk P hcop hg j (finitePrimeModulus P) (span_finitePrimeModulus P) h)


-- @@ L56-58 verbatim
lemma sqrt_absNorm (r : O) :
    Real.sqrt (Ideal.absNorm (Ideal.span {r}) : ℝ) = ‖eisEmbedding r‖ := by
  rw [← eisEmbedding_norm_sq_eq_absNorm_span, Real.sqrt_sq (norm_nonneg _)]


-- @@ L60-71 verbatim
theorem normalized_primitive_gauss_norm_le_one {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hg : ∀ i, goodLambda ∉ P i) (hchar : ∀ i, ringChar (O ⧸ P i) ≠ 2)
    (j : ι → ℕ) (hj0 : ∀ i, j i ≠ 0) (hj6 : ∀ i, j i < 6) (h : O) :
    ‖normalizedResidueGauss (finitePrimeModulus P) (finitePrimeModulus_ne_zero P)
      (primitiveCharacter P hcop hg j) (Ideal.Quotient.mk _ h)‖ ≤ 1 := by
  rw [normalizedResidueGauss, primitive_gauss_transform P hcop hg hchar j hj0 hj6,
    sqrt_absNorm, mul_div_assoc]
  change ‖star (finiteSexticRow P hg j h) * canonicalNormalizedGauss P hcop hg j‖ ≤ 1
  rw [norm_mul, norm_star, norm_canonicalNormalizedGauss P hcop hg hchar j hj0 hj6, mul_one]
  exact QuadraticInitialBound.finiteSexticRow_norm_le_one P hg j h


-- @@ L73-73 verbatim
end SevenEighths.CenteredMomentPrimitive

-- @@ L74-74 verbatim
end


-- @@ L76-76 verbatim
end OAI
