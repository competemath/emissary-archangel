import OAI.NumberTheory.DirichletL.ParametersHighData
import OAI.NumberTheory.DirichletL.ParametersProbeWindows
import OAI.NumberTheory.DirichletL.PrimeRows.FirstTail


-- @@ L5-5 verbatim
namespace OAI


-- @@ L7-7 verbatim
noncomputable section

-- @@ L8-8 verbatim
open scoped Classical ContDiff

-- @@ L9-9 verbatim
namespace SevenEighths.Parameters

-- @@ L10-10 verbatim
open ProbePhysical ProbeHighRowFamily CanonicalQuadraticSieve

-- @@ L11-11 verbatim
local notation "O" => ActualEisensteinCubic.O


-- @@ L13-24 verbatim
lemma fixed_bad_primes_prime : ∀ P∈fixedBadPrimes,Prime P := by
  intro P hP
  rcases Finset.mem_insert.mp hP with hP|hP
  · subst P
    exact Ideal.prime_of_isPrime
      (Ideal.span_singleton_eq_bot.not.mpr PrimaryIdealUnitReindex.lambda_prime_actual.ne_zero)
      lambdaIdeal_maximal.isPrime
  · have he := Finset.mem_singleton.mp hP
    subst P
    exact Ideal.prime_of_isPrime
      (Ideal.span_singleton_eq_bot.not.mpr (by norm_num : (2:O)≠0))
      twoIdeal_maximal.isPrime


-- @@ L26-36 verbatim
theorem exists_fixed_source (e : ℝ) (he : 0<e)
    (S₀ : Finset (Ideal O)) (hS₀ : ∀P∈S₀,Prime P) :
    ∃ S : Finset (Ideal O), S₀⊆S ∧ SourceExclusions S ∧
      FirstTail (4*e) S ∧ (∀P∈S,P.IsMaximal) := by
  obtain ⟨S,hsub,hS,hfirst⟩ := exists_both_source_exclusions (4*e) (by positivity)
    (S₀∪fixedBadPrimes)
    (fun P hP => (Finset.mem_union.mp hP).elim (hS₀ P) (fixed_bad_primes_prime P))
    Finset.subset_union_right
  refine ⟨S,Finset.subset_union_left.trans hsub,hS,hfirst,?_⟩
  intro P hP
  exact (Ideal.isPrime_of_prime (hS.prime P hP)).isMaximal (hS.prime P hP).ne_zero


-- @@ L38-49 verbatim
theorem exists_fixed_probe_window : ∃ (w : ℝ→ℝ) (W : SchwartzMap ℝ ℂ),
    ContDiff ℝ ∞ w ∧ HasCompactSupport w ∧
    Function.support w⊆Set.Ioo 1 2 ∧ tsupport w⊆Set.Ioi 0 ∧
    (∀x,0≤w x ∧ w x≤1) ∧ w≠0 ∧ (∀x,W x=(w x:ℂ)) ∧ W≠0 ∧
    Function.support W⊆Set.Icc 1 2 ∧
    (∀x,(W x).im=0) ∧ (∀x,0≤(W x).re) := by
  obtain ⟨w,W,hw,hc,hs,hb,hv,hn,he,hWn,hWs,hr,hp⟩ := exists_probe_window
  refine ⟨w,W,hw,hc,hs,?_,hb,hn,he,hWn,hWs,hr,hp⟩
  have hcl : tsupport w⊆Set.Icc 1 2 :=
    closure_minimal (hs.trans Set.Ioo_subset_Icc_self) isClosed_Icc
  intro x hx
  exact lt_of_lt_of_le (by norm_num : (0:ℝ)<1) (hcl hx).1

-- @@ L50-50 verbatim
end SevenEighths.Parameters


-- @@ L52-52 verbatim
end


-- @@ L54-54 verbatim
end OAI
