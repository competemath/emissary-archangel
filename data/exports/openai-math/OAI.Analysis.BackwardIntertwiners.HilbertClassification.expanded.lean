import OAI.Analysis.BackwardIntertwiners.ModelProperties


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
namespace Hyperinvariant233

-- @@ L6-6 verbatim
open Filter

-- @@ L7-7 verbatim
open scoped Topology

-- @@ L8-8 verbatim
universe u

-- @@ L9-9 verbatim
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]



-- @@ L12-13 verbatim
def commutant (T : H →L[ℂ] H) : Subalgebra ℂ (H →L[ℂ] H) :=
  Subalgebra.centralizer ℂ ({T} : Set (H →L[ℂ] H))



-- @@ L16-19 verbatim
def TransitiveCommutant (T : H →L[ℂ] H) : Prop :=
  ∀ K : Submodule ℂ H, IsClosed (K : Set H) →
    (∀ A : H →L[ℂ] H, A * T = T * A → ∀ x ∈ K, A x ∈ K) →
    K = ⊥ ∨ K = ⊤



-- @@ L22-24 verbatim
@[instance_reducible]
def strongOperatorTopology : TopologicalSpace (H →L[ℂ] H) :=
  TopologicalSpace.induced (fun A : H →L[ℂ] H => (fun x : H => A x)) inferInstance



-- @@ L27-30 verbatim
def MainClaim : Prop :=
  ∃ T : H →L[ℂ] H, T ≠ 0 ∧
    Tendsto (fun n : ℕ => ‖T ^ n‖ ^ (1 / (n : ℝ))) atTop (𝓝 0) ∧
    TransitiveCommutant T



-- @@ L33-37 verbatim
def FullClaim : Prop :=
  ∃ T : H →L[ℂ] H, T ≠ 0 ∧
    Tendsto (fun n : ℕ => ‖T ^ n‖ ^ (1 / (n : ℝ))) atTop (𝓝 0) ∧
    TransitiveCommutant T ∧ commutant T ≠ ⊤ ∧
    @IsClosed (H →L[ℂ] H) strongOperatorTopology (commutant T : Set (H →L[ℂ] H))


-- @@ L39-39 verbatim
end Hyperinvariant233



-- @@ L42-42 verbatim
namespace Hyperinvariant233

-- @@ L43-43 verbatim
open Submodule TopologicalSpace

-- @@ L44-44 verbatim
universe u v

-- @@ L45-46 verbatim
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [SeparableSpace H]



-- @@ L49-61 verbatim
theorem orthonormal_subtype_countable (w : Set H)
    (hw : Orthonormal ℂ (Subtype.val : w → H)) : Countable w := by
  classical
  let : DiscreteTopology w := discreteTopology_iff_isOpen_singleton.mpr (by
    intro i
    have ho : IsOpen {j : w | (1 / 2 : ℝ) < ‖inner ℂ (i : H) (j : H)‖} :=
      isOpen_lt continuous_const (continuous_const.inner continuous_subtype_val).norm
    have he : {j : w | (1 / 2 : ℝ) < ‖inner ℂ (i : H) (j : H)‖} = {i} := by
      ext j
      rw [Set.mem_ofPred_eq, orthonormal_iff_ite.mp hw i j]
      by_cases hij : i = j <;> norm_num [hij, eq_comm]
    rwa [he] at ho)
  exact separableSpace_iff_countable.mp inferInstance




-- @@ L65-87 verbatim
theorem exists_nat_hilbertBasis (hInf : ¬FiniteDimensional ℂ H) :
    Nonempty (HilbertBasis ℕ ℂ H) := by
  classical
  obtain ⟨w, b, hb⟩ := exists_hilbertBasis ℂ H
  have hw : Orthonormal ℂ (Subtype.val : w → H) := by
    simpa only [hb] using b.orthonormal
  let : Countable w := orthonormal_subtype_countable w hw
  let : Infinite w := by
    refine not_finite_iff_infinite.mp ?_
    intro hfin
    let : Finite w := hfin
    let : Fintype w := Fintype.ofFinite w
    exact hInf (Module.Finite.of_basis b.toOrthonormalBasis.toBasis)
  let e : ℕ ≃ w := Classical.choice (inferInstance : Nonempty (ℕ ≃ w))
  have ho : Orthonormal ℂ (b ∘ e) := b.orthonormal.comp e e.injective
  have hr : Set.range (b ∘ e) = Set.range b := by
    ext x
    constructor
    · rintro ⟨n, rfl⟩
      exact ⟨e n, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨e.symm i, by simp⟩
  exact ⟨HilbertBasis.mk ho (by rw [hr, b.dense_span])⟩



-- @@ L90-97 verbatim
theorem nonempty_linearIsometryEquiv
    {K : Type v} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] [SeparableSpace K]
    (hH : ¬FiniteDimensional ℂ H) (hK : ¬FiniteDimensional ℂ K) :
    Nonempty (H ≃ₗᵢ[ℂ] K) := by
  obtain ⟨bH⟩ := exists_nat_hilbertBasis hH
  obtain ⟨bK⟩ := exists_nat_hilbertBasis hK
  exact ⟨bH.repr.trans bK.repr.symm⟩


-- @@ L99-99 verbatim
end Hyperinvariant233


-- @@ L101-101 verbatim
end OAI
