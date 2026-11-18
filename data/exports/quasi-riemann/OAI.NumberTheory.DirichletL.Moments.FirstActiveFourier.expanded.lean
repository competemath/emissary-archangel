import OAI.NumberTheory.DirichletL.Moments.FirstReduced


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section

-- @@ L6-6 verbatim
open scoped BigOperators Classical SchwartzMap


-- @@ L8-8 verbatim
namespace SevenEighths.CenteredMomentFirstActiveFourier

-- @@ L9-9 verbatim
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein EisensteinSchwartzPoisson

-- @@ L10-10 verbatim
open CenteredMomentCorrelation CenteredMomentCommonSupport CenteredMomentFourier

-- @@ L11-11 verbatim
open CenteredMomentFirstMixed CenteredMomentFirstReduced

-- @@ L12-12 verbatim
local notation "O" => ActualEisensteinCubic.O


-- @@ L14-38 verbatim
theorem shifted_active_fourier {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i,(P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ P i)
    (hchar : ∀ i,ringChar (O ⧸ P i)≠2)
    (j : ι → ℕ) (hj0 : ∀ i,j i≠0) (hj6 : ∀ i,j i<6) (v h : O) :
    let r := finitePrimeModulus P
    let G := principalSexticRow P hcop hg j r (span_finitePrimeModulus P)
    (∑' x : Residue r,G (Ideal.Quotient.mk _ v*x)*
      quotientTrace r (finitePrimeModulus_ne_zero P) (Ideal.Quotient.mk _ h*x)) =
      finiteSexticRow P hg j v*star (finiteSexticRow P hg j h)*canonicalGaussSum P hcop hg j := by
  dsimp only
  let := finite_quotient_span (finitePrimeModulus_ne_zero P)
  let : Fintype (Residue (finitePrimeModulus P)) := Fintype.ofFinite _
  let e := Ideal.quotEquivOfEq (span_finitePrimeModulus P)
  let : Fintype (O ⧸ ∏ i,P i) := Fintype.ofEquiv (Residue (finitePrimeModulus P)) e.toEquiv
  let (i : ι) : Fintype (O ⧸ P i) := Fintype.ofFinite _
  rw [tsum_fintype]
  simp_rw [CenteredMomentFirstReduced.principalSexticRow_mul P hcop hg j
    (finitePrimeModulus P) (span_finitePrimeModulus P),
    principalSexticRow_mk P hcop hg j (finitePrimeModulus P) (span_finitePrimeModulus P),mul_assoc]
  rw [← Finset.mul_sum,canonical_principal_gauss_transform P hcop hg hchar j hj0 hj6,
    principalSexticRow_mk P hcop hg j (finitePrimeModulus P) (span_finitePrimeModulus P)]
  change finiteSexticRow P hg j v*(star (finiteSexticRow P hg j h)*canonicalGaussSum P hcop hg j)=_
  ring


-- @@ L40-73 verbatim
theorem tripleFourier_active {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i,(P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ P i)
    (hchar : ∀ i,ringChar (O ⧸ P i)≠2)
    (j : ι → ℕ) (hj0 : ∀ i,j i≠0) (hj6 : ∀ i,j i<6)
    (a b : O) (ha : a≠0) (hb : b≠0)
    (har : IsCoprime a (b*finitePrimeModulus P)) (hbr : IsCoprime b (finitePrimeModulus P))
    (χa : MulChar (Residue a) ℂ) (χb : MulChar (Residue b) ℂ) (h : O) :
    let r := finitePrimeModulus P
    let G := principalSexticRow P hcop hg j r (span_finitePrimeModulus P)
    tripleFourier a b r ha hb (finitePrimeModulus_ne_zero P) χa χb G h =
      χa (Ideal.Quotient.mk _ (b*r))*χb (Ideal.Quotient.mk _ (a*r))*
        residueGauss a ha χa (Ideal.Quotient.mk _ h)*residueGauss b hb χb (Ideal.Quotient.mk _ h)*
        (finiteSexticRow P hg j (a*b)*star (finiteSexticRow P hg j h)*canonicalGaussSum P hcop hg j) := by
  dsimp only
  let := finite_quotient_span ha
  let := finite_quotient_span hb
  let := finite_quotient_span (finitePrimeModulus_ne_zero P)
  let := finite_quotient_span (mul_ne_zero hb (finitePrimeModulus_ne_zero P))
  let := finite_quotient_span (mul_ne_zero ha (mul_ne_zero hb (finitePrimeModulus_ne_zero P)))
  let : Fintype (Residue a) := Fintype.ofFinite _
  let : Fintype (Residue b) := Fintype.ofFinite _
  let : Fintype (Residue (finitePrimeModulus P)) := Fintype.ofFinite _
  let : Fintype (Residue (b*finitePrimeModulus P)) := Fintype.ofFinite _
  let : Fintype (Residue (a*(b*finitePrimeModulus P))) := Fintype.ofFinite _
  unfold tripleFourier tripleResidue
  rw [tsum_fintype,three_factor_mixed_fourier a b (finitePrimeModulus P) ha hb
    (finitePrimeModulus_ne_zero P) har hbr]
  simp only [frequencyReduction_mk]
  have hs := shifted_active_fourier P hcop hg hchar j hj0 hj6 (a*b) h
  dsimp only at hs
  rw [tsum_fintype] at hs
  rw [hs]


-- @@ L75-104 verbatim
theorem tripleFourier_active_norm_le {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i,(P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ P i)
    (hchar : ∀ i,ringChar (O ⧸ P i)≠2)
    (j : ι → ℕ) (hj0 : ∀ i,j i≠0) (hj6 : ∀ i,j i<6)
    (a b : O) (ha : a≠0) (hb : b≠0)
    (har : IsCoprime a (b*finitePrimeModulus P)) (hbr : IsCoprime b (finitePrimeModulus P))
    (χa : MulChar (Residue a) ℂ) (χb : MulChar (Residue b) ℂ) (h : O) :
    let r := finitePrimeModulus P
    let G := principalSexticRow P hcop hg j r (span_finitePrimeModulus P)
    ‖tripleFourier a b r ha hb (finitePrimeModulus_ne_zero P) χa χb G h‖ ≤
      ‖eisEmbedding r‖*‖residueGauss a ha χa (Ideal.Quotient.mk _ h)‖*
        ‖residueGauss b hb χb (Ideal.Quotient.mk _ h)‖ := by
  dsimp only
  let := finite_quotient_span ha
  let := finite_quotient_span hb
  let : Fintype (Residue a) := Fintype.ofFinite _
  let : Fintype (Residue b) := Fintype.ofFinite _
  rw [tripleFourier_active P hcop hg hchar j hj0 hj6 a b ha hb har hbr]
  simp only [norm_mul,norm_star,norm_canonicalGaussSum P hcop hg hchar j hj0 hj6]
  have hχa := QuadraticInitialBound.norm_finite_character_le_one χa (Ideal.Quotient.mk _ (b*finitePrimeModulus P))
  have hχb := QuadraticInitialBound.norm_finite_character_le_one χb (Ideal.Quotient.mk _ (a*finitePrimeModulus P))
  have hv := QuadraticInitialBound.finiteSexticRow_norm_le_one P hg j (a*b)
  have hh := QuadraticInitialBound.finiteSexticRow_norm_le_one P hg j h
  calc
    _ ≤ 1*1*‖residueGauss a ha χa (Ideal.Quotient.mk _ h)‖*
      ‖residueGauss b hb χb (Ideal.Quotient.mk _ h)‖*(1*1*‖eisEmbedding (finitePrimeModulus P)‖) := by
        gcongr
    _ = _ := by ring


-- @@ L106-106 verbatim
end SevenEighths.CenteredMomentFirstActiveFourier


-- @@ L108-108 verbatim
end


-- @@ L110-110 verbatim
end OAI
