import OAI.Geometry.ProjectionBody.ConvexGeometry
import Mathlib.Algebra.BigOperators.Fin


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
noncomputable section

-- @@ L7-7 verbatim
open Set


-- @@ L9-9 verbatim
namespace ProjectionCounterexample


-- @@ L11-24 verbatim
/-- The coordinate isometry inserting a zero in slot `i`. -/
def insertZero {n : ℕ} (i : Fin (n + 1)) : E n →ₗᵢ[ℝ] E (n + 1) where
  toFun x := WithLp.toLp 2 (i.insertNth 0 x)
  map_add' x y := by
    ext j
    induction j using i.succAboveCases <;> simp
  map_smul' c x := by
    ext j
    induction j using i.succAboveCases <;> simp
  norm_map' x := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq,
      Fin.sum_univ_succAbove _ i]
    simp


-- @@ L26-27 verbatim
@[simp] theorem insertZero_same {n : ℕ} (i : Fin (n + 1)) (x : E n) :
    insertZero i x i = 0 := by simp [insertZero]


-- @@ L29-30 verbatim
@[simp] theorem insertZero_succAbove {n : ℕ} (i : Fin (n + 1)) (x : E n)
    (j : Fin n) : insertZero i x (i.succAbove j) = x j := by simp [insertZero]


-- @@ L32-35 verbatim
theorem sum_insertZero {n : ℕ} (i : Fin (n + 1)) (x : E n) :
    ∑ j, insertZero i x j = ∑ j, x j := by
  rw [Fin.sum_univ_succAbove _ i]
  simp


-- @@ L37-59 verbatim
/-- A coordinate facet is an actual isometric image of the lower-dimensional simplex. -/
theorem coordinate_facet_eq_image {n : ℕ} (i : Fin (n + 1)) :
    {x ∈ simplex (n + 1) | x i = 0} = insertZero i '' simplex n := by
  simp_rw [simplex_eq_coordinates]
  apply Subset.antisymm
  · rintro x ⟨⟨hx, hs⟩, hxi⟩
    let y : E n := WithLp.toLp 2 (fun j => x (i.succAbove j))
    have hy : (∀ j, 0 ≤ y j) ∧ ∑ j, y j ≤ 1 := by
      refine ⟨fun j => hx _, ?_⟩
      rw [Fin.sum_univ_succAbove _ i, hxi, zero_add] at hs
      exact hs
    refine ⟨y, hy, ?_⟩
    ext j
    induction j using i.succAboveCases
    · simpa using hxi.symm
    · simp [y]
  · rintro x ⟨y, ⟨hy, hs⟩, rfl⟩
    refine ⟨⟨?_, ?_⟩, by simp⟩
    · intro j
      induction j using i.succAboveCases
      · simp
      · simpa using hy _
    · simpa [sum_insertZero] using hs


-- @@ L61-63 verbatim
/-- The affine chart on the facet whose coordinate sum is one. -/
def sumFacetMap (n : ℕ) (x : E n) : E (n + 1) :=
  WithLp.toLp 2 (Fin.snoc (fun j => x j) (1 - ∑ j, x j))


-- @@ L65-66 verbatim
@[simp] theorem sumFacetMap_castSucc (n : ℕ) (x : E n) (i : Fin n) :
    sumFacetMap n x i.castSucc = x i := by simp [sumFacetMap]


-- @@ L68-69 verbatim
@[simp] theorem sumFacetMap_last (n : ℕ) (x : E n) :
    sumFacetMap n x (Fin.last n) = 1 - ∑ j, x j := by simp [sumFacetMap]


-- @@ L71-74 verbatim
@[simp] theorem sum_sumFacetMap (n : ℕ) (x : E n) :
    ∑ j, sumFacetMap n x j = 1 := by
  rw [Fin.sum_univ_castSucc]
  simp


-- @@ L76-102 verbatim
/-- The non-coordinate facet is an actual affine image of the lower-dimensional simplex. -/
theorem sum_facet_eq_image (n : ℕ) :
    {x ∈ simplex (n + 1) | ∑ j, x j = 1} = sumFacetMap n '' simplex n := by
  simp_rw [simplex_eq_coordinates]
  apply Subset.antisymm
  · rintro x ⟨⟨hx, _⟩, hs⟩
    let y : E n := WithLp.toLp 2 (fun j : Fin n => x j.castSucc)
    have hsum : ∑ j, y j = 1 - x (Fin.last n) := by
      rw [Fin.sum_univ_castSucc] at hs
      dsimp [y]
      linarith
    have hy : (∀ j, 0 ≤ y j) ∧ ∑ j, y j ≤ 1 := by
      refine ⟨fun j => hx _, ?_⟩
      rw [hsum]
      linarith [hx (Fin.last n)]
    refine ⟨y, hy, ?_⟩
    ext j
    induction j using Fin.lastCases
    · simp [hsum]
    · simp [y]
  · rintro x ⟨y, ⟨hy, hs⟩, rfl⟩
    refine ⟨⟨?_, by simp⟩, by simp⟩
    intro j
    induction j using Fin.lastCases
    · simp only [sumFacetMap_last]
      exact sub_nonneg.mpr hs
    · simpa using hy _


-- @@ L104-104 verbatim
end ProjectionCounterexample


-- @@ L106-106 verbatim
end


-- @@ L108-108 verbatim
end OAI
