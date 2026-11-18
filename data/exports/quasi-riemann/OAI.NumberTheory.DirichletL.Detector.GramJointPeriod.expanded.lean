import OAI.NumberTheory.DirichletL.Detector.GramJointMean


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
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

-- @@ L12-12 verbatim
variable {ι : Type*} [Fintype ι]


-- @@ L14-21 verbatim
lemma common_radical_norm_le (C : O) (hC : C≠0) (P : ι→Id) (c : ι→ℕ)
    (hc : ∀i,1≤c i) (he : Ideal.span {C}=∏i,P i^c i) :
    Ideal.absNorm (∏i,P i)≤Ideal.absNorm (Ideal.span {C}) := by
  apply Nat.le_of_dvd (Nat.pos_of_ne_zero
    (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr hC)))
  apply map_dvd Ideal.absNorm
  rw [he]
  exact Finset.prod_dvd_prod_of_dvd _ _ (fun i _=>dvd_pow_self _ (Nat.one_le_iff_ne_zero.mp (hc i)))


-- @@ L23-31 verbatim
lemma jointPeriod_norm_bound (S : Finset Id) (hS : ∀P∈S,P.IsMaximal)
    (C k : O) (hC : C≠0) (hk0 : k≠0) (u : Oˣ) (a b : ℕ) (r : O)
    (hk : k=u.val*λ₀^a*(2:O)^b*r) (P : ι→Id) (c : ι→ℕ)
    (hc : ∀i,1≤c i) (he : Ideal.span {C}=∏i,P i^c i) :
    Ideal.absNorm (jointPeriod S hS P r)≤
      Ideal.absNorm (jointFixedModulus S hS)*Ideal.absNorm (Ideal.span {C})*Ideal.absNorm (Ideal.span {k}) := by
  rw [jointPeriod,map_mul,map_mul]
  exact Nat.mul_le_mul (Nat.mul_le_mul_left _ (common_radical_norm_le C hC P c hc he))
    (numerator_good_norm_le u a b r k hk hk0)


-- @@ L33-45 verbatim
lemma jointPeriod_nonzero (S : Finset Id) (hS : ∀P∈S,P.IsMaximal)
    (C : O) (hC : C≠0) (P : ι→Id) (c : ι→ℕ)
    (hc : ∀i,1≤c i) (he : Ideal.span {C}=∏i,P i^c i) (r : O) (hr : r≠0) :
    jointPeriod S hS P r≠0 := by
  have hp : ∏i,P i≠(0:Id) := by
    intro hz
    have hd : (∏i,P i)∣Ideal.span {C} := by
      rw [he]
      exact Finset.prod_dvd_prod_of_dvd _ _ (fun i _=>dvd_pow_self _ (Nat.one_le_iff_ne_zero.mp (hc i)))
    rw [hz,zero_dvd_iff] at hd
    exact hC (Ideal.span_singleton_eq_bot.mp hd)
  exact mul_ne_zero (mul_ne_zero (jointFixedModulus_nonzero S hS) hp)
    (Ideal.span_singleton_eq_bot.not.mpr hr)


-- @@ L47-47 verbatim
end SevenEighths.ProbeGramCommon

-- @@ L48-48 verbatim
end


-- @@ L50-50 verbatim
end OAI
