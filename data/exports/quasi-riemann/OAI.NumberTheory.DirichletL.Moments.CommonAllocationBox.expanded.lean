import OAI.NumberTheory.DirichletL.Moments.CommonAllocation
import OAI.NumberTheory.DirichletL.Moments.FirstSectors


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
noncomputable section

-- @@ L7-7 verbatim
open scoped BigOperators Classical


-- @@ L9-9 verbatim
namespace SevenEighths.CenteredMomentCommonAllocationBox

-- @@ L10-10 verbatim
open CenteredMomentCommonAllocation CenteredMomentSupport CenteredMomentCommonSectors

-- @@ L11-11 verbatim
open CenteredMomentFirstSectors IdealMobiusDivisorSum

-- @@ L12-12 verbatim
local notation "O" => ActualEisensteinCubic.O

-- @@ L13-13 verbatim
variable {ι : Type*} [Fintype ι]


-- @@ L15-17 verbatim
def sourceFiber (S : ι → Finset (Ideal O)) (C : Ideal O) (B : ι → Ideal O) :
    Finset (ι → Ideal O) :=
  (Fintype.piFinset S).filter (fun v => ∀ i,supportExtract (v i) (primeSupport C)=B i)


-- @@ L19-21 verbatim
def residualBoxes (S : ι → Finset (Ideal O)) (C : Ideal O) (B : ι → Ideal O)
    (hB : ∀ i,B i≠0) : Finset (ι → Ideal O) :=
  Fintype.piFinset (fun i => (residualPool (B i) (hB i) (S i)).filter (IsCoprime C))


-- @@ L23-59 verbatim
theorem residualBoxes_image (S : ι → Finset (Ideal O))
    (hS : ∀ i,∀ I∈S i,I≠0) (C : Ideal O) (hC : C≠0)
    (B : ι → Ideal O) (hB : ∀ i,B i≠0)
    (hBs : ∀ i,primeSupport (B i)⊆primeSupport C) :
    (residualBoxes S C B hB).image (fun v i => B i*v i)=sourceFiber S C B := by
  ext v
  constructor
  · intro hv
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hv
    have hui := Fintype.mem_piFinset.mp hu
    apply Finset.mem_filter.mpr
    constructor
    · apply Fintype.mem_piFinset.mpr
      intro i
      exact (mem_residualPool (B i) (hB i) (S i) _).mp (Finset.mem_filter.mp (hui i)).1
    · intro i
      have hp := Finset.mem_filter.mp (hui i)
      have hsrc := (mem_residualPool (B i) (hB i) (S i) _).mp hp.1
      have hu0 : u i≠0 := right_ne_zero_of_mul (hS i _ hsrc)
      rw [supportExtract_mul _ _ (hB i) hu0,supportExtract_of_subset _ (hB i) _ (hBs i),
        supportExtract_of_disjoint _ _ ((IdealCoprimeSieveOperator.primeSupport_disjoint_iff hC hu0).mpr hp.2).symm,mul_one]
  · intro hv
    obtain ⟨hv,hvB⟩ := Finset.mem_filter.mp hv
    have hvi := Fintype.mem_piFinset.mp hv
    let u := fun i => supportResidual (v i) (primeSupport C)
    have hi (i : ι) : B i*u i=v i := by
      rw [← hvB i]
      exact support_reconstruct _ (hS i _ (hvi i)) _
    refine Finset.mem_image.mpr ⟨u,?_,funext hi⟩
    apply Fintype.mem_piFinset.mpr
    intro i
    apply Finset.mem_filter.mpr
    constructor
    · apply (mem_residualPool (B i) (hB i) (S i) _).mpr
      rw [hi]
      exact hvi i
    · exact residual_factor_coprime C (v i) hC


-- @@ L61-70 verbatim
theorem sourceFiber_sum (S : ι → Finset (Ideal O))
    (hS : ∀ i,∀ I∈S i,I≠0) (C : Ideal O) (hC : C≠0)
    (B : ι → Ideal O) (hB : ∀ i,B i≠0)
    (hBs : ∀ i,primeSupport (B i)⊆primeSupport C) (F : (ι → Ideal O) → ℂ) :
    (∑ v∈sourceFiber S C B,F v)=
      ∑ u∈residualBoxes S C B hB,F (fun i => B i*u i) := by
  rw [← residualBoxes_image S hS C hC B hB hBs,Finset.sum_image]
  intro u hu v hv he
  funext i
  exact mul_left_cancel₀ (hB i) (congrFun he i)


-- @@ L72-82 verbatim
theorem sourceFiber_product_sum (S : ι → Finset (Ideal O))
    (hS : ∀ i,∀ I∈S i,I≠0) (C : Ideal O) (hC : C≠0)
    (B : ι → Ideal O) (hB : ∀ i,B i≠0)
    (hBs : ∀ i,primeSupport (B i)⊆primeSupport C) (hprod : ∏ i,B i=C)
    (a : Ideal O) (F : (ι → Ideal O) → ℂ) :
    (∑ v∈sourceFiber S C B,if (∏ i,v i)=C*a then F v else 0)=
      ∑ u∈residualBoxes S C B hB,if (∏ i,u i)=a then F (fun i => B i*u i) else 0 := by
  rw [sourceFiber_sum S hS C hC B hB hBs]
  apply Finset.sum_congr rfl
  intro u hu
  simp only [Finset.prod_mul_distrib,hprod,mul_right_inj' hC]


-- @@ L84-84 verbatim
end SevenEighths.CenteredMomentCommonAllocationBox


-- @@ L86-86 verbatim
end


-- @@ L88-88 verbatim
end OAI
