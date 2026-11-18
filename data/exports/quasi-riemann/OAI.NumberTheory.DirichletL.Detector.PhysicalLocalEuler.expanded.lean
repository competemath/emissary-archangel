import OAI.NumberTheory.DirichletL.Detector.LocalPhysical
import OAI.NumberTheory.DirichletL.Detector.SourceLocal


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
noncomputable section

-- @@ L7-7 verbatim
open scoped Classical BigOperators

-- @@ L8-8 verbatim
namespace SevenEighths.ProbePhysical

-- @@ L9-9 verbatim
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge CanonicalRowCompletion

-- @@ L10-10 verbatim
open CubicEisenstein GaussianShiftedPartition ProbePrimePower ProbeEuler ProbeLocal

-- @@ L11-11 verbatim
local notation "O" => ActualEisensteinCubic.O


-- @@ L13-17 verbatim
lemma outerQuotient_mk (s H : O) :
    outerQuotient s (Ideal.Quotient.mk _ H)=idealRowHom H (Ideal.span {s}) := by
  unfold outerQuotient
  apply idealRowHom_congr_mod
  exact Ideal.Quotient.eq.mp (representative_spec _ _)


-- @@ L19-37 verbatim
theorem bareCongruenceCoefficient_all_prime_powers (p : O) (hp : Prime p)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hg : goodLambda∉Ideal.span {p}) (t k j : ℕ) :
    bareCongruenceCoefficient (p^t) (p^k) (pow_ne_zero _ hp.ne_zero) (p^j) =
      sourceScalar p hp hg t k j := by
  cases t with
  | zero =>
    simp only [pow_zero]
    rw [bareCongruenceCoefficient_inner_one _ (pow_ne_zero _ hp.ne_zero), outerQuotient_mk]
    unfold sourceScalar
    rw [ite_eq_left rfl]
    by_cases hk : k=0
    · subst k
      simp only [pow_zero, Ideal.span_singleton_one, ← Ideal.one_eq_top, map_one, ite_true]
    · rw [ite_eq_right hk, ← Ideal.span_singleton_pow, map_pow, idealRowHom_prime _ _ hg,
        MulChar.pow_apply' _ hk]
  | succ n =>
    rw [bareCongruenceCoefficient_prime_power p hp hg n k j]
    simp only [sourceScalar, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ite_false,
      Nat.add_sub_cancel]


-- @@ L39-47 verbatim
def physicalPrincipalSeries (p : O) (hp : Prime p)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hg : goodLambda∉Ideal.span {p})
    (eta a x w z : ℂ) : ℂ :=
  ∑ e : Fin 2, ∑' l, ∑' k, ∑' m,
    sourceWeightedScalar (Ideal.absNorm (Ideal.span {p})) eta a
      (localGamma p hp.ne_zero hg 1) (star (localGamma p hp.ne_zero hg 3))
      (actualSextic (Ideal.span {p}) hg (-1)) x w z
      (bareCongruenceCoefficient (p^(e.val+3*l)) (p^k) (pow_ne_zero _ hp.ne_zero) (p^(6*m)))
      e.val l k m


-- @@ L49-54 verbatim
theorem physicalPrincipalSeries_eq (p : O) (hp : Prime p)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hg : goodLambda∉Ideal.span {p})
    (eta a x w z : ℂ) :
    physicalPrincipalSeries p hp hg eta a x w z = sourcePrincipalSeries p hp hg eta a x w z := by
  simp only [physicalPrincipalSeries, sourcePrincipalSeries, sourcePrincipalTerm,
    bareCongruenceCoefficient_all_prime_powers p hp hg]


-- @@ L56-68 verbatim
theorem physicalPrincipalSeries_euler_identity (p : O) (hp : Prime p)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hg : goodLambda∉Ideal.span {p})
    (hc : ringChar (O ⧸ Ideal.span {p})≠2) (eta a x w z : ℂ)
    (hV : ‖coordV (Ideal.absNorm (Ideal.span {p})) z‖<1)
    (hR : ‖coordR (Ideal.absNorm (Ideal.span {p})) (a^2) x z‖<1)
    (hW : ‖coordW (Ideal.absNorm (Ideal.span {p})) 1 w‖<1)
    (hD : 1-coordD (Ideal.absNorm (Ideal.span {p})) eta 1 x≠0) :
    let Q : ℝ := Ideal.absNorm (Ideal.span {p})
    physicalPrincipalSeries p hp hg eta a x w z =
      (1-coordD Q eta 1 x) / ((1-coordV Q z)*(1-coordW Q 1 w)) *
        unramifiedClosed Q (a^2) eta 1 x w z := by
  rw [physicalPrincipalSeries_eq]
  exact sourcePrincipalSeries_euler_identity p hp hg hc eta a x w z hV hR hW hD


-- @@ L70-70 verbatim
end SevenEighths.ProbePhysical

-- @@ L71-71 verbatim
end


-- @@ L73-73 verbatim
end OAI
