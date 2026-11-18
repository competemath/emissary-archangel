import OAI.NumberTheory.DirichletL.Moments.DivisorAllocation


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section

-- @@ L6-6 verbatim
open scoped BigOperators Classical

-- @@ L7-7 verbatim
namespace SevenEighths.CenteredMomentDivisorExtraction

-- @@ L8-8 verbatim
open IdealMobiusDivisorSum CenteredMomentDivisorAllocation

-- @@ L9-9 verbatim
local notation "O" => ActualEisensteinCubic.O

-- @@ L10-10 verbatim
variable {ι : Type*} [DecidableEq ι]


-- @@ L12-13 verbatim
def selectedPrimes (D : Ideal O) (s : Finset ι) (a : Allocation D s) (i : ι) :
    Finset (primeSupport D) := Finset.univ.filter (fun P => i ∈ (a P).val)


-- @@ L15-16 verbatim
def selectedDivisor (D : Ideal O) (s : Finset ι) (a : Allocation D s) (i : ι) : Ideal O :=
  ∏ P ∈ selectedPrimes D s a i, (P:Ideal O)


-- @@ L18-25 verbatim
theorem selected_divides_factor (D : Ideal O) (s : Finset ι) (v : ι → Ideal O)
    (a : Allocation D s) (hn : allocationTerm D s v a ≠ 0)
    (P : primeSupport D) (i : ι) (hi : i ∈ (a P).val) : (P:Ideal O)∣v i := by
  have hP := (Finset.prod_ne_zero_iff.mp hn) P (Finset.mem_univ P)
  have hprod := (mul_ne_zero_iff.mp hP).2
  have hfactor := (Finset.prod_ne_zero_iff.mp hprod) i hi
  by_contra h
  exact hfactor (by simp only [ite_eq_right h])


-- @@ L27-29 verbatim
theorem selectedDivisor_ne_zero (D : Ideal O) (s : Finset ι) (a : Allocation D s) (i : ι) :
    selectedDivisor D s a i ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr (fun P _ => (support_prime P.property).ne_zero)


-- @@ L31-42 verbatim
theorem selectedDivisor_dvd (D : Ideal O) (s : Finset ι) (v : ι → Ideal O)
    (a : Allocation D s) (hn : allocationTerm D s v a ≠ 0) (i : ι) :
    selectedDivisor D s a i ∣ v i := by
  apply Finset.prod_dvd_of_coprime ?_ ?_
  · intro P hP Q hQ hne
    let : (P:Ideal O).IsMaximal := (Ideal.isPrime_of_prime (support_prime P.property)).isMaximal
      (support_prime P.property).ne_zero
    let : (Q:Ideal O).IsMaximal := (Ideal.isPrime_of_prime (support_prime Q.property)).isMaximal
      (support_prime Q.property).ne_zero
    exact Ideal.isCoprime_of_isMaximal (fun he => hne (Subtype.ext he))
  · intro P hP
    exact selected_divides_factor D s v a hn P i (Finset.mem_filter.mp hP).2


-- @@ L44-48 verbatim
theorem exists_factor_quotients (D : Ideal O) (s : Finset ι) (v : ι → Ideal O)
    (a : Allocation D s) (hn : allocationTerm D s v a ≠ 0) :
    ∃ q : ι → Ideal O, ∀ i, v i=selectedDivisor D s a i*q i := by
  choose q hq using (fun i => selectedDivisor_dvd D s v a hn i)
  exact ⟨q,hq⟩


-- @@ L50-55 verbatim
theorem selected_prime_slot (D : Ideal O) (s : Finset ι) (v : ι → Ideal O)
    (a : Allocation D s) (hn : allocationTerm D s v a ≠ 0)
    (P : primeSupport D) (i : ι) (hi : i ∈ (a P).val) (hv : Prime (v i)) :
    v i=(P:Ideal O) :=
  ((prime_dvd_prime_iff_eq (support_prime P.property) hv).mp
    (selected_divides_factor D s v a hn P i hi)).symm


-- @@ L57-65 verbatim
theorem double_selected_prime_slot_zero (D : Ideal O) (s : Finset ι) (v : ι → Ideal O)
    (a : Allocation D s) (P Q : primeSupport D) (hPQ : P ≠ Q)
    (i : ι) (hPi : i ∈ (a P).val) (hQi : i ∈ (a Q).val) (hv : Prime (v i)) :
    allocationTerm D s v a=0 := by
  by_contra hn
  apply hPQ
  apply Subtype.ext
  exact (selected_prime_slot D s v a hn P i hPi hv).symm.trans
    (selected_prime_slot D s v a hn Q i hQi hv)


-- @@ L67-67 verbatim
end SevenEighths.CenteredMomentDivisorExtraction


-- @@ L69-69 verbatim
end


-- @@ L71-71 verbatim
end OAI
