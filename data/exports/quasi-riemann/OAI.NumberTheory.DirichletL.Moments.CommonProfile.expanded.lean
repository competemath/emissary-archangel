import OAI.NumberTheory.DirichletL.Moments.CommonPrimeSlots
import OAI.NumberTheory.DirichletL.Moments.SourceProfileMass


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
noncomputable section

-- @@ L7-7 verbatim
open scoped BigOperators Classical


-- @@ L9-9 verbatim
namespace SevenEighths.CenteredMomentCommonProfile

-- @@ L10-10 verbatim
open ActualEisensteinCubic CenteredMomentSourceProfileMass CenteredMomentAddedZeroUniform

-- @@ L11-11 verbatim
open CenteredMomentCommonPrimeSlots CenteredMomentCommonAllocationBox

-- @@ L12-12 verbatim
local notation "O" => ActualEisensteinCubic.O

-- @@ L13-13 verbatim
variable {ι : Type*} [Fintype ι]


-- @@ L15-15 verbatim
def liveIndices (B : Tuple ι) : Finset ι := Finset.univ.filter (fun i => B (Sum.inl i)=1)


-- @@ L17-18 verbatim
def remainingTuple (B u : Tuple ι) : Tuple (liveIndices B) :=
  Sum.elim (fun i => u (Sum.inl i.val)) (fun j => u (Sum.inr j))


-- @@ L20-21 verbatim
@[simp] theorem remainingTuple_slot (B u : Tuple ι) (i : liveIndices B) :
    remainingTuple B u (Sum.inl i)=u (Sum.inl i.val) := rfl


-- @@ L23-24 verbatim
@[simp] theorem remainingTuple_plain (B u : Tuple ι) (j : Fin 2) :
    remainingTuple B u (Sum.inr j)=u (Sum.inr j) := rfl


-- @@ L26-38 verbatim
theorem remaining_product (B u : Tuple ι)
    (hf : ∀ i,B (Sum.inl i)≠1 → u (Sum.inl i)=1) :
    finiteTupleProduct u=finiteTupleProduct (remainingTuple B u) := by
  simp only [finiteTupleProduct,Fintype.prod_sum_type,Fin.prod_univ_two,remainingTuple,
    Sum.elim_inl,Sum.elim_inr]
  rw [Finset.prod_coe_sort (liveIndices B) (fun i => u (Sum.inl i))]
  congr 1
  symm
  apply Finset.prod_subset (Finset.filter_subset _ _)
  intro i hi hnot
  apply hf i
  intro hBi
  exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hBi⟩)


-- @@ L40-55 verbatim
theorem slot_profiles_split (B u : Tuple ι)
    (hf : ∀ i,B (Sum.inl i)≠1 → u (Sum.inl i)=1)
    (β : ι → Ideal O → ℂ) :
    (∏ i,β i (B (Sum.inl i)*u (Sum.inl i)))=
      (∏ i∈Finset.univ.filter (fun i => B (Sum.inl i)≠1),β i (B (Sum.inl i)))*
        ∏ i : liveIndices B,β i.val (u (Sum.inl i.val)) := by
  rw [Finset.prod_coe_sort (liveIndices B) (fun i => β i (u (Sum.inl i)))]
  rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun i => B (Sum.inl i)=1)
    (fun i => β i (B (Sum.inl i)*u (Sum.inl i))),mul_comm]
  apply congrArg₂ (·*·)
  · apply Finset.prod_congr rfl
    intro i hi
    rw [hf i (Finset.mem_filter.mp hi).2,mul_one]
  · apply Finset.prod_congr rfl
    intro i hi
    rw [(Finset.mem_filter.mp hi).2,one_mul]


-- @@ L57-81 verbatim
theorem profile_common_allocation (B u : Tuple ι) (C R s : Ideal O)
    (hB : finiteTupleProduct B=C) (hsC : s∣C)
    (hf : ∀ i,B (Sum.inl i)≠1 → u (Sum.inl i)=1)
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O) :
    profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s (fun i => B i*u i)=
      ((∏ i∈Finset.univ.filter (fun i => B (Sum.inl i)≠1),
          ν i (B (Sum.inl i))*Wslot i ((Ideal.absNorm (B (Sum.inl i)):ℝ)/P i))*
        (if IsCoprime C R then 1 else 0))*
        profileCoefficient R (fun i : liveIndices B => ν i.val) (fun i => Wslot i.val) (fun i => P i.val)
          W₁ W₂ X₁ X₂ Y₁ Y₂ (B₁*B (Sum.inr 0)) (B₂*B (Sum.inr 1)) 1 (remainingTuple B u) := by
  have hprod : finiteTupleProduct (fun i => B i*u i)=C*finiteTupleProduct (remainingTuple B u) := by
    rw [finiteTupleProduct,Finset.prod_mul_distrib]
    change finiteTupleProduct B*finiteTupleProduct u=_
    rw [hB,remaining_product B u hf]
  have hdiv : s∣C*finiteTupleProduct (remainingTuple B u) := dvd_mul_of_dvd_left hsC _
  unfold profileCoefficient
  rw [slot_profiles_split B u hf (fun i I => ν i I*Wslot i ((Ideal.absNorm I:ℝ)/P i)),hprod]
  simp only [hdiv,ite_true,one_dvd,mul_one,remainingTuple_slot,remainingTuple_plain,
    IsCoprime.mul_left_iff]
  rw [mul_assoc B₁,mul_assoc B₂]
  by_cases hC : IsCoprime C R <;>
    by_cases hu : IsCoprime (finiteTupleProduct (remainingTuple B u)) R <;>
    simp_all only [true_and,false_and,ite_true,ite_false,mul_zero,zero_mul,mul_one]
  ring


-- @@ L83-93 verbatim
theorem actual_frozen_slots (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (hS : ∀ i,∀ I∈S i,I≠0) (C : Ideal O) (hC : C≠0)
    (B : Tuple ι) (hB : ∀ i,B i≠0)
    (hBs : ∀ i,IdealMobiusDivisorSum.primeSupport (B i)⊆IdealMobiusDivisorSum.primeSupport C)
    (u : Tuple ι) (hu : u∈residualBoxes S C B hB)
    (hp : ∀ i,∀ I∈S (Sum.inl i),Prime I) :
    ∀ i,B (Sum.inl i)≠1 → u (Sum.inl i)=1 := by
  intro i hi
  rcases prime_coordinate_cases S hS C hC B hB hBs u hu (Sum.inl i) (hp i) with h|h
  · exact False.elim (hi h.1)
  · exact h.1


-- @@ L95-95 verbatim
end SevenEighths.CenteredMomentCommonProfile


-- @@ L97-97 verbatim
end


-- @@ L99-99 verbatim
end OAI
