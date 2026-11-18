import OAI.NumberTheory.DirichletL.Detector.LocalPhysical
import OAI.NumberTheory.DirichletL.Detector.Sextic
import OAI.NumberTheory.DirichletL.Detector.SixthFrequency
import OAI.NumberTheory.DirichletL.Moments.Unequal


-- @@ L6-6 verbatim
namespace OAI


-- @@ L8-8 verbatim
noncomputable section

-- @@ L9-9 verbatim
open scoped BigOperators Classical


-- @@ L11-11 verbatim
namespace SevenEighths.CenteredMomentAmplification

-- @@ L12-12 verbatim
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT CanonicalRowCompletion

-- @@ L13-13 verbatim
open CanonicalQuadraticSieve ConcretePrimeRowBridge ProbePrimePower ProbePhysical

-- @@ L14-14 verbatim
open CenteredMomentUnequal

-- @@ L15-15 verbatim
local notation "O" => ActualEisensteinCubic.O


-- @@ L17-31 verbatim
theorem gauss_prime_power_one (p : O) (hp : Prime p) [(Ideal.span {p}).IsMaximal]
    (hg : goodLambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2) (n : ℕ) :
    sexticGauss (p^(n+1)) (pow_ne_zero _ hp.ne_zero) 1 =
      if n = 0 then primeGauss p hp.ne_zero (actualSextic (Ideal.span {p}) hg) 1 else 0 := by
  rw [sexticGauss_prime_power p hp hg]
  have ht := actualSextic_primePowerGauss_at_pow p hp hg hc (n+1) n 0
  simp only [pow_zero] at ht
  rw [ht]
  by_cases hn : n = 0
  · subst n
    norm_num
  · have hn0 : ¬0 = n := Ne.symm hn
    have hpos : ¬n ≤ 0 := by omega
    simp only [ite_eq_right hn,ite_eq_right hn0,ite_eq_right hpos,show ¬n+1 ≤ 0 by omega,ite_false,sub_self]
    split_ifs <;> rfl


-- @@ L33-56 verbatim
theorem gauss_prime_power_six (p : O) (hp : Prime p) [(Ideal.span {p}).IsMaximal]
    (hg : goodLambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2) (n : ℕ) :
    sexticGauss (p^(n+1)) (pow_ne_zero _ hp.ne_zero) (p^6) =
      if n = 5 then (Ideal.absNorm (Ideal.span {p}) : ℂ)^5 *
        ((Ideal.absNorm (Ideal.span {p}) : ℂ)-1)
      else if n = 6 then (Ideal.absNorm (Ideal.span {p}) : ℂ)^6 *
        primeGauss p hp.ne_zero (actualSextic (Ideal.span {p}) hg) 1 else 0 := by
  rw [sexticGauss_prime_power p hp hg,actualSextic_primePowerGauss_at_pow p hp hg hc]
  have h6 : actualSextic (Ideal.span {p}) hg ^ 6 = 1 :=
    (actualSextic_pow_eq_one_iff _ hg hc 6).mpr dvd_rfl
  by_cases hn5 : n = 5
  · subst n
    norm_num
    ring
  · by_cases hn6 : n = 6
    · subst n
      simp only [hn5,show ¬6 ∣ 6+1 by decide,ite_false,ite_true,
        pow_succ (actualSextic (Ideal.span {p}) hg) 6,h6,one_mul]
    · rw [ite_eq_right hn5,ite_eq_right hn6]
      by_cases hd : 6 ∣ n+1
      · have hlarge : 6 < n := by omega
        simp only [hd,ite_true,show ¬n+1 ≤ 6 by omega,ite_false,
          show ¬n ≤ 6 by omega,sub_self]
      · simp only [hd,ite_false,show ¬6=n from Ne.symm hn6]


-- @@ L58-70 verbatim
theorem gauss_prime_power_unchanged (p : O) (hp : Prime p) [(Ideal.span {p}).IsMaximal]
    (hs : Supported (Ideal.span {p})) (hg : goodLambda ∉ Ideal.span {p})
    (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2) (n : ℕ)
    (hn0 : n ≠ 0) (hn5 : n ≠ 5) (hn6 : n ≠ 6) (h : O) (hph : ¬p ∣ h) :
    sexticGauss (p^(n+1)) (pow_ne_zero _ hp.ne_zero) (h*p^6) =
      sexticGauss (p^(n+1)) (pow_ne_zero _ hp.ne_zero) h := by
  have hcop : IsCoprime h (p^(n+1)) :=
    (hp.irreducible.coprime_iff_not_dvd.mpr hph).symm.pow_right
  have hsp := supported_power p hs (n+1)
  rw [sexticGauss_unit_scale _ hsp h (p^6) hcop,
    ← mul_one h, sexticGauss_unit_scale _ hsp h 1 hcop,
    gauss_prime_power_six p hp hg hc,gauss_prime_power_one p hp hg hc]
  simp only [hn0,hn5,hn6,ite_false,mul_zero]


-- @@ L72-77 verbatim
theorem gauss_sixth_frequency (a : O) (ha : Supported (Ideal.span {a}))
    (p h : O) (hcop : IsCoprime p a) :
    sexticGauss a (supportedElement_ne_zero a ha) (p^6*h) =
      sexticGauss a (supportedElement_ne_zero a ha) h := by
  rw [sexticGauss_unit_scale a ha (p^6) h hcop.pow_left,
    supported_sixth_value a p ha hcop.symm,inv_one,one_mul]


-- @@ L79-84 verbatim
theorem twelfth_power_mask (p : O) (hs : Supported (Ideal.span {p})) (u : O) :
    idealRowHom u (Ideal.span {p}) ^ 12 = coprimalityMask u p := by
  rw [show 12=6*2 by decide,pow_mul,← idealRowHom_argument_pow u 6 _ hs,
    idealRowHom_sixth_eq_mask u p hs]
  change (if IsCoprime u p then (1 : ℂ) else 0)^2 = if IsCoprime u p then 1 else 0
  split_ifs <;> norm_num


-- @@ L86-86 verbatim
end SevenEighths.CenteredMomentAmplification


-- @@ L88-88 verbatim
end


-- @@ L90-90 verbatim
end OAI
