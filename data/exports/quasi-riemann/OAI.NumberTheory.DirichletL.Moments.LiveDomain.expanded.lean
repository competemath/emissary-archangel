import OAI.NumberTheory.DirichletL.Moments.LiveSupport
import OAI.NumberTheory.DirichletL.Moments.SourceRow
import OAI.NumberTheory.DirichletL.Moments.GaussEnergy


-- @@ L5-5 verbatim
namespace OAI


-- @@ L7-7 verbatim
noncomputable section

-- @@ L8-8 verbatim
open scoped BigOperators Classical SchwartzMap


-- @@ L10-10 verbatim
namespace SevenEighths.CenteredMomentLiveDomain

-- @@ L11-11 verbatim
open CenteredMomentSourceLiveColumn CenteredMomentLiveSupport CenteredMomentSourceMass

-- @@ L12-12 verbatim
open CenteredMomentAddedZeroUniform CenteredMomentCommonProfile CenteredMomentCommonAllocationSum

-- @@ L13-13 verbatim
open CenteredMomentFirstSectors CenteredMomentSourceRow CanonicalQuadraticSieve

-- @@ L14-14 verbatim
open CenteredMomentGaussEnergy

-- @@ L15-15 verbatim
local notation "O" => ActualEisensteinCubic.O

 
-- @@ L17-21 verbatim
theorem finite_column_mem {ι : Type*} [Fintype ι] (S : Finset (Tuple ι))
    (β : Tuple ι → ℂ) (a : Ideal O) (ha : finiteColumnCoefficient S β a≠0) : a∈finiteColumns S := by
  obtain ⟨v,hv,hvn⟩ := Finset.exists_ne_zero_of_sum_ne_zero ha
  obtain ⟨hv,he⟩ := Finset.mem_filter.mp hv
  exact Finset.mem_image.mpr ⟨v,hv,he⟩

 
-- @@ L23-40 verbatim
theorem sum_same_support (S T : Finset (Ideal O)) (c f : Ideal O → ℂ)
    (hST : ∀ I∈S,c I≠0 → I∈T) (hTS : ∀ I∈T,c I≠0 → I∈S) :
    (∑ I∈S,c I*f I)=∑ I∈T,c I*f I := by
  have hs : (∑ I∈S∩T,c I*f I)=∑ I∈S,c I*f I := by
    apply Finset.sum_subset Finset.inter_subset_left
    intro I hI hn
    have hc : c I=0 := by
      by_contra h
      exact hn (Finset.mem_inter.mpr ⟨hI,hST I hI h⟩)
    rw [hc,zero_mul]
  have ht : (∑ I∈S∩T,c I*f I)=∑ I∈T,c I*f I := by
    apply Finset.sum_subset Finset.inter_subset_right
    intro I hI hn
    have hc : c I=0 := by
      by_contra h
      exact hn (Finset.mem_inter.mpr ⟨hTS I hI h,hI⟩)
    rw [hc,zero_mul]
  exact hs.symm.trans ht

 
-- @@ L42-47 verbatim
theorem supported_residualPool (C : Ideal O) (hC : Supported C) (S : Finset (Ideal O)) :
    supportedColumns (residualPool C hC.1 S)=residualPool C hC.1 (supportedColumns S) := by
  ext I
  simp only [supportedColumns,Finset.mem_filter,mem_residualPool]
  rw [supported_mul_iff]
  tauto


-- @@ L49-52 verbatim
def primaryGaussRow (I : Ideal O) (z : O) : ℂ :=
  if hI : Supported I then
    gaussRow (CompletedGauss.primaryGenerator I)
      (by rw [primary_span_supported I hI];exact hI) z else 0


-- @@ L54-63 verbatim
theorem source_gaussPolynomial (S : Finset (Ideal O)) (c : Ideal O → ℂ) (z : O) :
    gaussPolynomial Finset.univ (sourceGenerator S) (sourceGenerator_supported S)
      (fun I : supportedColumns S => c I) z=
      ∑ I∈supportedColumns S,c I*primaryGaussRow I z := by
  unfold gaussPolynomial
  rw [← Finset.sum_coe_sort (supportedColumns S) (fun I => c I*primaryGaussRow I z)]
  apply Finset.sum_congr rfl
  intro I hI
  rw [primaryGaussRow,dite_eq_left (Finset.mem_filter.mp I.property).2]
  rfl


-- @@ L65-65 verbatim
variable {ι : Type*} [Fintype ι]

-- @@ L66-66 verbatim
local instance : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _


-- @@ L68-85 verbatim
theorem live_column_sum (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (hS : ∀ i,∀ I∈S i,I≠0) (hp : ∀ i,∀ I∈S (Sum.inl i),Prime I)
    (B : Tuple ι) (hB : ∀ i,B i≠0) (C R : Ideal O) (hC : Supported C)
    (hlabel : B∈allocationLabels S C) (hprod : finiteTupleProduct B=C)
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O) (f : Ideal O → ℂ) :
    let c := finiteColumnCoefficient (liveBox S B hB)
      (liveProfile B C R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂)
    (∑ I∈supportedColumns (residualPool C hC.1 (finiteColumns (Fintype.piFinset S))),c I*f I)=
      ∑ I∈supportedColumns (finiteColumns (liveBox S B hB)),c I*f I := by
  dsimp only
  apply sum_same_support
  · intro I hI hn
    exact Finset.mem_filter.mpr ⟨finite_column_mem _ _ I hn,(Finset.mem_filter.mp hI).2⟩
  · intro I hI hn
    have hh := live_column_original_support S hS hp B hB C R I hlabel hprod
      ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ hn
    exact Finset.mem_filter.mpr ⟨(mem_residualPool C hC.1 _ I).mpr hh.1,(Finset.mem_filter.mp hI).2⟩


-- @@ L87-110 verbatim
theorem live_gaussPolynomial (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (hS : ∀ i,∀ I∈S i,I≠0) (hp : ∀ i,∀ I∈S (Sum.inl i),Prime I)
    (B : Tuple ι) (hB : ∀ i,B i≠0) (C R : Ideal O) (hC : Supported C)
    (hlabel : B∈allocationLabels S C) (hprod : finiteTupleProduct B=C)
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O) (f : Ideal O → ℂ) (z : O) :
    let c := finiteColumnCoefficient (liveBox S B hB)
      (liveProfile B C R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂)
    let Q := residualPool C hC.1 (finiteColumns (Fintype.piFinset S))
    let T := finiteColumns (liveBox S B hB)
    gaussPolynomial Finset.univ (sourceGenerator Q) (sourceGenerator_supported Q)
      (fun I : supportedColumns Q => c I*f I) z=
      gaussPolynomial Finset.univ (sourceGenerator T) (sourceGenerator_supported T)
        (fun I : supportedColumns T => c I*f I) z := by
  let c := finiteColumnCoefficient (liveBox S B hB)
    (liveProfile B C R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂)
  let Q := residualPool C hC.1 (finiteColumns (Fintype.piFinset S))
  let T := finiteColumns (liveBox S B hB)
  change gaussPolynomial Finset.univ (sourceGenerator Q) (sourceGenerator_supported Q)
    (fun I : supportedColumns Q => c I*f I) z=_
  refine (source_gaussPolynomial Q (fun I => c I*f I) z).trans ?_
  refine Eq.trans ?_ (source_gaussPolynomial T (fun I => c I*f I) z).symm
  simpa only [mul_assoc] using live_column_sum S hS hp B hB C R hC hlabel hprod ν Wslot P W₁ W₂
    X₁ X₂ Y₁ Y₂ B₁ B₂ (fun I => f I*primaryGaussRow I z)


-- @@ L112-132 verbatim
theorem live_gaussEnergy (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (hS : ∀ i,∀ I∈S i,I≠0) (hp : ∀ i,∀ I∈S (Sum.inl i),Prime I)
    (B : Tuple ι) (hB : ∀ i,B i≠0) (C R : Ideal O) (hC : Supported C)
    (hlabel : B∈allocationLabels S C) (hprod : finiteTupleProduct B=C)
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O) (f : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    let c := finiteColumnCoefficient (liveBox S B hB)
      (liveProfile B C R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂)
    let Q := residualPool C hC.1 (finiteColumns (Fintype.piFinset S))
    let T := finiteColumns (liveBox S B hB)
    gaussEnergy Finset.univ (sourceGenerator Q) (sourceGenerator_supported Q)
      (fun I : supportedColumns Q => c I*f I) W K=
      gaussEnergy Finset.univ (sourceGenerator T) (sourceGenerator_supported T)
        (fun I : supportedColumns T => c I*f I) W K := by
  dsimp only
  unfold gaussEnergy
  apply tsum_congr
  intro z
  exact congrArg (fun x : ℂ => ((‖x‖^2:ℝ):ℂ)*W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K))
    (live_gaussPolynomial S hS hp B hB C R hC hlabel hprod ν Wslot P W₁ W₂
      X₁ X₂ Y₁ Y₂ B₁ B₂ f z)


-- @@ L134-134 verbatim
end SevenEighths.CenteredMomentLiveDomain


-- @@ L136-136 verbatim
end


-- @@ L138-138 verbatim
end OAI
