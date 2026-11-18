import OAI.NumberTheory.DirichletL.Moments.CommonAllocationSum


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section

-- @@ L6-6 verbatim
open scoped BigOperators Classical


-- @@ L8-8 verbatim
namespace SevenEighths.CenteredMomentCommonPrimeSlots

-- @@ L9-9 verbatim
open CenteredMomentCommonAllocationSum CenteredMomentCommonAllocationBox

-- @@ L10-10 verbatim
open CenteredMomentSupport IdealMobiusDivisorSum

-- @@ L11-11 verbatim
local notation "O" => ActualEisensteinCubic.O

-- @@ L12-12 verbatim
variable {ι : Type*} [Fintype ι]

 
-- @@ L14-18 verbatim
theorem residual_original_mem (S : ι → Finset (Ideal O)) (C : Ideal O)
    (B : ι → Ideal O) (hB : ∀ i,B i≠0) (u : ι → Ideal O)
    (hu : u∈residualBoxes S C B hB) (i : ι) : B i*u i∈S i :=
  (CenteredMomentFirstSectors.mem_residualPool _ _ _ _).mp
    (Finset.mem_filter.mp (Fintype.mem_piFinset.mp hu i)).1


-- @@ L20-42 verbatim
theorem prime_coordinate_cases (S : ι → Finset (Ideal O))
    (hS : ∀ i,∀ I∈S i,I≠0) (C : Ideal O) (hC : C≠0)
    (B : ι → Ideal O) (hB : ∀ i,B i≠0)
    (hBs : ∀ i,primeSupport (B i)⊆primeSupport C)
    (u : ι → Ideal O) (hu : u∈residualBoxes S C B hB)
    (i : ι) (hp : ∀ I∈S i,Prime I) :
    (B i=1 ∧ Prime (u i)) ∨ (u i=1 ∧ Prime (B i)) := by
  have hsrc := residual_original_mem S C B hB u hu i
  have hprime := hp _ hsrc
  by_cases hBi : B i=1
  · exact Or.inl ⟨hBi,by simpa only [hBi,one_mul] using hprime⟩
  · have hv : (fun j => B j*u j)∈sourceFiber S C B := by
      rw [← residualBoxes_image S hS C hC B hB hBs]
      exact Finset.mem_image.mpr ⟨u,hu,rfl⟩
    have he := (Finset.mem_filter.mp hv).2 i
    rw [supportExtract_prime _ hprime] at he
    have hmem : B i*u i∈primeSupport C := by
      by_contra hn
      rw [ite_eq_right hn] at he
      exact hBi he.symm
    rw [ite_eq_left hmem] at he
    have hu1 : u i=1 := mul_left_cancel₀ (hB i) (he.trans (mul_one (B i)).symm)
    exact Or.inr ⟨hu1,by simpa only [hu1,mul_one] using hprime⟩


-- @@ L44-44 verbatim
def liveSlots (T : Finset ι) (B : ι → Ideal O) : Finset ι := T.filter (fun i => B i=1)

-- @@ L45-45 verbatim
def frozenSlots (T : Finset ι) (B : ι → Ideal O) : Finset ι := T.filter (fun i => B i≠1)


-- @@ L47-68 verbatim
theorem slot_coefficient_product (S : ι → Finset (Ideal O))
    (hS : ∀ i,∀ I∈S i,I≠0) (C : Ideal O) (hC : C≠0)
    (B : ι → Ideal O) (hB : ∀ i,B i≠0)
    (hBs : ∀ i,primeSupport (B i)⊆primeSupport C)
    (u : ι → Ideal O) (hu : u∈residualBoxes S C B hB)
    (T : Finset ι) (hp : ∀ i∈T,∀ I∈S i,Prime I) (β : ι → Ideal O → ℂ) :
    (∏ i∈T,β i (B i*u i))=
      (∏ i∈frozenSlots T B,β i (B i))*(∏ i∈liveSlots T B,β i (u i)) := by
  rw [← Finset.prod_filter_mul_prod_filter_not T (fun i => B i=1) (fun i => β i (B i*u i)),mul_comm]
  apply congrArg₂ (·*·)
  · apply Finset.prod_congr rfl
    intro i hi
    have hTi := (Finset.mem_filter.mp hi).1
    have hBi := (Finset.mem_filter.mp hi).2
    have hu1 : u i=1 := by
      rcases prime_coordinate_cases S hS C hC B hB hBs u hu i (hp i hTi) with h|h
      · exact False.elim (hBi h.1)
      · exact h.1
    rw [hu1,mul_one]
  · apply Finset.prod_congr rfl
    intro i hi
    rw [(Finset.mem_filter.mp hi).2,one_mul]


-- @@ L70-85 verbatim
theorem slot_residual_product (S : ι → Finset (Ideal O))
    (hS : ∀ i,∀ I∈S i,I≠0) (C : Ideal O) (hC : C≠0)
    (B : ι → Ideal O) (hB : ∀ i,B i≠0)
    (hBs : ∀ i,primeSupport (B i)⊆primeSupport C)
    (u : ι → Ideal O) (hu : u∈residualBoxes S C B hB)
    (T : Finset ι) (hp : ∀ i∈T,∀ I∈S i,Prime I) :
    (∏ i∈T,u i)=∏ i∈liveSlots T B,u i := by
  symm
  apply Finset.prod_subset (Finset.filter_subset _ _)
  intro i hi hnot
  have hBi : B i≠1 := by
    intro he
    exact hnot (Finset.mem_filter.mpr ⟨hi,he⟩)
  rcases prime_coordinate_cases S hS C hC B hB hBs u hu i (hp i hi) with h|h
  · exact False.elim (hBi h.1)
  · exact h.1


-- @@ L87-87 verbatim
end SevenEighths.CenteredMomentCommonPrimeSlots


-- @@ L89-89 verbatim
end


-- @@ L91-91 verbatim
end OAI
