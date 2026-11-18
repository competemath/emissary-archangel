import OAI.NumberTheory.DirichletL.Detector.GaussValuation
import OAI.NumberTheory.DirichletL.Moments.Canonical


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
noncomputable section

-- @@ L7-7 verbatim
namespace SevenEighths.ProbePrimePower

-- @@ L8-8 verbatim
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge CubicEisenstein

-- @@ L9-9 verbatim
local notation "O" => ActualEisensteinCubic.O


-- @@ L11-14 verbatim
theorem actualSextic_pow_eq_one_iff (P : Ideal O) [P.IsMaximal]
    (hg : goodLambda ∉ P) (hc : ringChar (O ⧸ P) ≠ 2) (n : ℕ) :
    actualSextic P hg ^ n = 1 ↔ 6 ∣ n := by
  rw [← orderOf_dvd_iff_pow_eq_one, CenteredMomentCanonical.actualSextic_order_six P hg hc]


-- @@ L16-34 verbatim
theorem actualSextic_primePowerGauss_at_pow (p : O) (hp : Prime p)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (hg : goodLambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    (r n j : ℕ) :
    primePowerGauss p hp.ne_zero (actualSextic (Ideal.span {p}) hg ^ r) n (p ^ j) =
      if 6 ∣ r then
        (if n + 1 ≤ j then (Ideal.absNorm (Ideal.span {p}) : ℂ) ^ (n + 1) else 0) -
        (if n ≤ j then (Ideal.absNorm (Ideal.span {p}) : ℂ) ^ n else 0)
      else if j = n then (Ideal.absNorm (Ideal.span {p}) : ℂ) ^ n *
        primeGauss p hp.ne_zero (actualSextic (Ideal.span {p}) hg ^ r) 1 else 0 := by
  by_cases hr : 6 ∣ r
  · rw [ite_eq_left hr, (actualSextic_pow_eq_one_iff _ hg hc r).mpr hr]
    apply primePowerGauss_at_pow_principal p hp
    have hprim : (quotientTrace p hp.ne_zero).IsPrimitive :=
      GeneralPrimitiveTrace.eisTraceModChar_breveE_primitive p hp.ne_zero
    simpa using hprim (a := 1) one_ne_zero
  · rw [ite_eq_right hr]
    exact primePowerGauss_at_pow_nonprincipal p hp _
      (fun h => hr ((actualSextic_pow_eq_one_iff _ hg hc r).mp h)) n j


-- @@ L36-36 verbatim
end SevenEighths.ProbePrimePower

-- @@ L37-37 verbatim
end


-- @@ L39-39 verbatim
end OAI
