import OAI.NumberTheory.DirichletL.Moments.LiveDomain
import OAI.NumberTheory.DirichletL.Moments.RestrictedWindow


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
noncomputable section

-- @@ L7-7 verbatim
open scoped BigOperators Classical SchwartzMap


-- @@ L9-9 verbatim
namespace SevenEighths.CenteredMomentRestrictedDomain

-- @@ L10-10 verbatim
open CenteredMomentSourceLiveColumn CenteredMomentLiveSupport CenteredMomentSourceMass

-- @@ L11-11 verbatim
open CenteredMomentAddedZeroUniform CenteredMomentCommonProfile CenteredMomentCommonAllocationSum

-- @@ L12-12 verbatim
open CenteredMomentFirstSectors CenteredMomentSourceRow CanonicalQuadraticSieve

-- @@ L13-13 verbatim
open CenteredMomentRowNorm CenteredMomentRestrictedEnergy CenteredMomentLiveDomain

-- @@ L14-14 verbatim
local notation "O" => ActualEisensteinCubic.O


-- @@ L16-24 verbatim
theorem source_rowPolynomial (S : Finset (Ideal O)) (c : Ideal O → ℂ) (z : O) :
    rowPolynomial Finset.univ (sourceGenerator S)
      (fun I : supportedColumns S => c I) z=
      ∑ I∈supportedColumns S,c I*CanonicalRowCompletion.idealRowHom z I := by
  unfold rowPolynomial
  rw [← Finset.sum_coe_sort (supportedColumns S) (fun I => c I*CanonicalRowCompletion.idealRowHom z I)]
  apply Finset.sum_congr rfl
  intro I hI
  rw [sourceGenerator,primary_span_supported I (Finset.mem_filter.mp I.property).2]


-- @@ L26-26 verbatim
variable {ι : Type*} [Fintype ι]

-- @@ L27-27 verbatim
local instance : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _


-- @@ L29-52 verbatim
theorem live_rowPolynomial (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (hS : ∀ i,∀ I∈S i,I≠0) (hp : ∀ i,∀ I∈S (Sum.inl i),Prime I)
    (B : Tuple ι) (hB : ∀ i,B i≠0) (C R : Ideal O) (hC : Supported C)
    (hlabel : B∈allocationLabels S C) (hprod : finiteTupleProduct B=C)
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O) (f : Ideal O → ℂ) (z : O) :
    let c := finiteColumnCoefficient (liveBox S B hB)
      (liveProfile B C R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂)
    let Q := residualPool C hC.1 (finiteColumns (Fintype.piFinset S))
    let T := finiteColumns (liveBox S B hB)
    rowPolynomial Finset.univ (sourceGenerator Q)
      (fun I : supportedColumns Q => c I*f I) z=
      rowPolynomial Finset.univ (sourceGenerator T)
        (fun I : supportedColumns T => c I*f I) z := by
  let c := finiteColumnCoefficient (liveBox S B hB)
    (liveProfile B C R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂)
  let Q := residualPool C hC.1 (finiteColumns (Fintype.piFinset S))
  let T := finiteColumns (liveBox S B hB)
  change rowPolynomial Finset.univ (sourceGenerator Q)
    (fun I : supportedColumns Q => c I*f I) z=_
  refine (source_rowPolynomial Q (fun I => c I*f I) z).trans ?_
  refine Eq.trans ?_ (source_rowPolynomial T (fun I => c I*f I) z).symm
  simpa only [mul_assoc] using live_column_sum S hS hp B hB C R hC hlabel hprod ν Wslot P W₁ W₂
    X₁ X₂ Y₁ Y₂ B₁ B₂ (fun I => f I*CanonicalRowCompletion.idealRowHom z I)


-- @@ L54-74 verbatim
theorem live_restrictedEnergy (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (hS : ∀ i,∀ I∈S i,I≠0) (hp : ∀ i,∀ I∈S (Sum.inl i),Prime I)
    (B : Tuple ι) (hB : ∀ i,B i≠0) (C R : Ideal O) (hC : Supported C)
    (hlabel : B∈allocationLabels S C) (hprod : finiteTupleProduct B=C)
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O) (f : Ideal O → ℂ) (keep : O → Prop) (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    let c := finiteColumnCoefficient (liveBox S B hB)
      (liveProfile B C R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂)
    let Q := residualPool C hC.1 (finiteColumns (Fintype.piFinset S))
    let T := finiteColumns (liveBox S B hB)
    restrictedEnergy keep Finset.univ (sourceGenerator Q)
      (fun I : supportedColumns Q => c I*f I) W K=
      restrictedEnergy keep Finset.univ (sourceGenerator T)
        (fun I : supportedColumns T => c I*f I) W K := by
  dsimp only
  unfold restrictedEnergy
  apply tsum_congr
  intro z
  exact congrArg (fun x : ℂ => if keep z then ‖x‖^2*(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re else 0)
    (live_rowPolynomial S hS hp B hB C R hC hlabel hprod ν Wslot P W₁ W₂
      X₁ X₂ Y₁ Y₂ B₁ B₂ f z)


-- @@ L76-76 verbatim
end SevenEighths.CenteredMomentRestrictedDomain


-- @@ L78-78 verbatim
end


-- @@ L80-80 verbatim
end OAI
