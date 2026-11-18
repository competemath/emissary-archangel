import OAI.NumberTheory.DirichletL.Moments.AmplificationAllocationCost
import OAI.NumberTheory.DirichletL.Moments.CommonRawScale


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
noncomputable section

-- @@ L7-7 verbatim
open scoped BigOperators Classical


-- @@ L9-9 verbatim
namespace SevenEighths.CenteredMomentAmplificationAllocationScale

-- @@ L10-10 verbatim
open CenteredMomentAmplificationAllocationCost CenteredMomentCommonAllocationSum

-- @@ L11-11 verbatim
open CenteredMomentCommonProfile CenteredMomentSourceLiveColumn CenteredMomentCommonRawScale

-- @@ L12-12 verbatim
open CenteredMomentAddedZeroUniform

-- @@ L13-13 verbatim
local notation "O" => ActualEisensteinCubic.O

-- @@ L14-14 verbatim
variable {ι : Type*} [Fintype ι]

 
-- @@ L16-22 verbatim
theorem all_slots_live (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (P : Ideal O) (hP : P≠0) (k : ℕ)
    (hslot : ∀ i,∀ I∈S (Sum.inl i),I≠0 ∧ IsCoprime P I)
    (B : actualAllocations S (P^k)) : liveIndices (B : Tuple ι)=Finset.univ := by
  apply Finset.filter_eq_self.mpr
  intro i hi
  exact allocation_slot_one S P hP k hslot B i

 
-- @@ L24-35 verbatim
theorem frozenCoefficient_exact (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (P : Ideal O) (hP : P≠0) (k : ℕ)
    (hslot : ∀ i,∀ I∈S (Sum.inl i),I≠0 ∧ IsCoprime P I)
    (B : actualAllocations S (P^k)) (R : Ideal O)
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (scale : ι → ℝ) :
    frozenCoefficient B (P^k) R ν Wslot scale=(if IsCoprime (P^k) R then 1 else 0) := by
  unfold frozenCoefficient
  have he : Finset.univ.filter (fun i => B.val (Sum.inl i)≠1)=∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro i hi
    exact not_not_intro (allocation_slot_one S P hP k hslot B i)
  rw [he,Finset.prod_empty,one_mul]

 
-- @@ L37-44 verbatim
theorem frozenCoefficient_norm_le (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (P : Ideal O) (hP : P≠0) (k : ℕ)
    (hslot : ∀ i,∀ I∈S (Sum.inl i),I≠0 ∧ IsCoprime P I)
    (B : actualAllocations S (P^k)) (R : Ideal O)
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (scale : ι → ℝ) :
    ‖frozenCoefficient B (P^k) R ν Wslot scale‖≤1 := by
  rw [frozenCoefficient_exact S P hP k hslot B R ν Wslot scale]
  split_ifs <;> simp

 
-- @@ L46-53 verbatim
theorem rawReduction_exact (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (P : Ideal O) (hP : P≠0) (k : ℕ)
    (hslot : ∀ i,∀ I∈S (Sum.inl i),I≠0 ∧ IsCoprime P I)
    (B : actualAllocations S (P^k)) (scale : ι → ℝ) :
    rawReduction B scale=(Ideal.absNorm P:ℝ)^k := by
  unfold rawReduction plainNorm frozenScale
  simp only [allocation_slot_one S P hP k hslot B,ite_true,Finset.prod_const_one,mul_one]
  rw [← Nat.cast_mul,← map_mul,allocation_plain_product S P hP k hslot B,map_pow,Nat.cast_pow]

 
-- @@ L55-59 verbatim
theorem live_slot_card (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (P : Ideal O) (hP : P≠0) (k : ℕ)
    (hslot : ∀ i,∀ I∈S (Sum.inl i),I≠0 ∧ IsCoprime P I)
    (B : actualAllocations S (P^k)) : Fintype.card (liveIndices (B : Tuple ι))=Fintype.card ι := by
  rw [Fintype.card_coe,all_slots_live S P hP k hslot B,Finset.card_univ]


-- @@ L61-71 verbatim
theorem remainingRaw_exact (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (P : Ideal O) (hP : P≠0) (k : ℕ)
    (hslot : ∀ i,∀ I∈S (Sum.inl i),I≠0 ∧ IsCoprime P I)
    (B : actualAllocations S (P^k)) (scale : ι → ℝ) (Traw : ℝ) :
    remainingRaw B Traw scale=(Traw*∏ i,scale i)/(Ideal.absNorm P:ℝ)^k := by
  have hb := (allocation_data S (P^k) B (Finset.mem_filter.mp B.property).1).1
  have he := raw_scale_identity B hb Traw scale
  rw [rawReduction_exact S P hP k hslot B scale] at he
  have hn : (Ideal.absNorm P:ℝ)≠0 := by
    exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr hP
  exact (eq_div_iff (pow_ne_zero k hn)).mpr he


-- @@ L73-73 verbatim
end SevenEighths.CenteredMomentAmplificationAllocationScale


-- @@ L75-75 verbatim
end


-- @@ L77-77 verbatim
end OAI
