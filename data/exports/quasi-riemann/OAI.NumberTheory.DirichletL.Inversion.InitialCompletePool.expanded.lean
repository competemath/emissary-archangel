import OAI.NumberTheory.DirichletL.Inversion.InitialLargeFourier
import OAI.NumberTheory.DirichletL.Descent.CompleteMarkedPool


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
noncomputable section


-- @@ L8-8 verbatim
open scoped BigOperators Classical

-- @@ L9-9 verbatim
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve ConcretePrimeRowBridge

-- @@ L10-10 verbatim
open UniqueFactorizationMonoid

-- @@ L11-11 verbatim
namespace SevenEighths.InverseInitialCompletePool

-- @@ L12-12 verbatim
open InverseInitialOverlap InverseInitialPoissonBridge InverseInitialLargePool

-- @@ L13-13 verbatim
open InverseInitialCommonTuples InverseInitialEnergyCallerWindow

-- @@ L14-14 verbatim
local notation "Eis"=>ActualEisensteinCubic.O


-- @@ L16-26 verbatim
private theorem bad_prime (P:Ideal Eis)(hP:P∈fixedBadPrimes) : Prime P := by
  rcases Finset.mem_insert.mp hP with hP|hP
  · subst P
    exact Ideal.prime_of_isPrime
      (Ideal.span_singleton_eq_bot.not.mpr PrimaryIdealUnitReindex.lambda_prime_actual.ne_zero)
      lambdaIdeal_maximal.isPrime
  · have he := Finset.mem_singleton.mp hP
    subst P
    exact Ideal.prime_of_isPrime
      (Ideal.span_singleton_eq_bot.not.mpr (by norm_num : (2:Eis)≠0))
      twoIdeal_maximal.isPrime


-- @@ L28-37 verbatim
theorem admissible_mem_complete {I:Ideal Eis}(hI:Admissible I)(D:ℕ)
    (hD:I.absNorm≤D) : I∈InitialMeanSquare.outsideSquarefreeIdeals fixedBadPrimes D := by
  apply Finset.mem_filter.mpr
  refine ⟨mem_outsideIdealsUpTo.mpr ⟨?_,hD,?_⟩,hI.2.1⟩
  · exact Nat.one_le_iff_ne_zero.mpr (fun h=>hI.1 (Ideal.absNorm_eq_zero_iff.mp h))
  · intro P hP hPI
    have hp := bad_prime P hP
    let : P.IsMaximal := (Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero
    have hfac := (mem_normalizedFactors_iff hI.1).mpr ⟨hp,hPI⟩
    exact (prime_good_iff_not_bad P).mp (hI.2.2 P hfac) hP


-- @@ L39-54 verbatim
theorem original_column_norm_bound (S:Finset (Ideal Eis)){P j c:Ideal Eis}
    (hP:Admissible P)(hj:j∣P)(hc:c∈columns S P j) :
    c.absNorm≤S.sup Ideal.absNorm*P.absNorm := by
  obtain ⟨hcs,hcj,hres,hnS⟩ := (mem_columns hP.2.1 hj).mp hc
  have hn := norm_reconstruct hres
  have hj0 := (admissible_of_dvd hP hj).1
  have hjpos : 1≤j.absNorm := Nat.one_le_iff_ne_zero.mpr
    (fun h=>hj0 (Ideal.absNorm_eq_zero_iff.mp h))
  have hnn : (reconstruct P j c).absNorm≤S.sup Ideal.absNorm := Finset.le_sup hnS
  have hPN : (residual P j).absNorm≤P.absNorm := Nat.le_of_dvd
    (Nat.pos_of_ne_zero (fun h=>hP.1 (Ideal.absNorm_eq_zero_iff.mp h)))
    (map_dvd Ideal.absNorm (idealQuotient_dvd hj))
  calc
    c.absNorm≤j.absNorm*c.absNorm := Nat.le_mul_of_pos_left _ hjpos
    _=(reconstruct P j c).absNorm*(residual P j).absNorm := hn.symm
    _≤_ := Nat.mul_le_mul hnn hPN


-- @@ L56-72 verbatim
theorem exists_complete_pool {κ:Type*}(S:Finset (Ideal Eis))(T:Finset κ)
    (P:κ→Ideal Eis)(j:Ideal Eis)(hP:∀k∈T,Admissible (P k))(hj:∀k∈T,j∣P k)
    (hS:∀n∈S,Squarefree n→Supported n)(bmax Xmax:ℝ)(hb:0≤bmax)(_hX:0≤Xmax) :
    ∃D:ℕ,tupleColumns S T P j⊆InitialMeanSquare.outsideSquarefreeIdeals fixedBadPrimes D ∧
      ∀b X:ℝ,0≤b→b≤bmax→0≤X→X≤Xmax→b*X≤(D:ℝ) := by
  let D := max (S.sup Ideal.absNorm*T.sup (fun k=>(P k).absNorm)) ⌈bmax*Xmax⌉₊
  refine ⟨D,?_,?_⟩
  · intro c hc
    obtain ⟨k,hk,hc⟩ := Finset.mem_biUnion.mp hc
    apply admissible_mem_complete (columns_admissible S (hP k hk) (hj k hk) hS hc)
    exact (original_column_norm_bound S (hP k hk) (hj k hk) hc).trans
      ((Nat.mul_le_mul_left (S.sup Ideal.absNorm)
        (Finset.le_sup (f:=fun k=>(P k).absNorm) hk)).trans (le_max_left _ _))
  · intro b X hb0 hbb hX0 hXX
    apply (mul_le_mul hbb hXX hX0 hb).trans
    exact (Nat.le_ceil (bmax*Xmax)).trans (by exact_mod_cast (le_max_right
      (S.sup Ideal.absNorm*T.sup (fun k=>(P k).absNorm)) ⌈bmax*Xmax⌉₊))


-- @@ L74-74 verbatim
end SevenEighths.InverseInitialCompletePool


-- @@ L76-76 verbatim
end


-- @@ L78-78 verbatim
end OAI
