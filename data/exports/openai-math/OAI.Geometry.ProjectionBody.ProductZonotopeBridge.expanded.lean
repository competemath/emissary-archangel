import OAI.Geometry.ProjectionBody.ZonotopeBridge
import OAI.Geometry.Zonotope.Product


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
noncomputable section

-- @@ L7-7 verbatim
open Set

-- @@ L8-8 verbatim
open scoped RealInnerProductSpace


-- @@ L10-10 verbatim
namespace ProjectionCounterexample


-- @@ L12-15 verbatim
/-- The sum of the two block support functions, with a common scale. -/
def blockSupport {n m : ℕ} (u : E (n + m)) : ℝ :=
  DiagonalZonotope.support (WithLp.ofLp (EuclideanSpace.finAddEquivProd u).1) +
  DiagonalZonotope.support (WithLp.ofLp (EuclideanSpace.finAddEquivProd u).2)


-- @@ L17-18 verbatim
lemma blockSupport_zero (n m : ℕ) : blockSupport (0 : E (n + m)) = 0 := by
  simp [blockSupport, DiagonalZonotope.support]


-- @@ L20-25 verbatim
lemma blockSupport_smul {n m : ℕ} (u : E (n + m)) (a : ℝ) :
    blockSupport (a • u) = |a| * blockSupport u := by
  simp only [blockSupport, map_smul, Prod.smul_fst, Prod.smul_snd]
  change DiagonalZonotope.support (a • WithLp.ofLp (EuclideanSpace.finAddEquivProd u).1) +
      DiagonalZonotope.support (a • WithLp.ofLp (EuclideanSpace.finAddEquivProd u).2) = _
  rw [DiagonalZonotope.support_smul, DiagonalZonotope.support_smul, mul_add]


-- @@ L27-50 verbatim
/-- A proved block brightness formula identifies the product projection zonotope. -/
theorem projectionBody_eq_productZonotope {n m : ℕ} (P : Set (E (n + m)))
    (c : ℝ) (hc : 0 < c)
    (hbrightness : ∀ u : E (n + m), ‖u‖ = 1 → projectionVolume P u = c * blockSupport u) :
    projectionBody P = DiagonalZonotope.euclideanProduct n m c := by
  calc
    projectionBody P = {x : E (n + m) | ∀ u : E (n + m), ‖u‖ = 1 →
        ⟪u, x⟫ ≤ c * blockSupport u} := by
      ext x
      constructor
      · intro hx u hu
        rw [← hbrightness u hu]
        exact hx u hu
      · intro hx u hu
        rw [hbrightness u hu]
        exact hx u hu
    _ = {x : E (n + m) | ∀ u : E (n + m), ⟪u, x⟫ ≤ c * blockSupport u} := by
      apply unit_support_halfspaces_eq
      · simp [blockSupport_zero]
      · intro a ha u
        rw [blockSupport_smul, abs_of_nonneg ha]
        ring
    _ = DiagonalZonotope.euclideanProduct n m c :=
      (DiagonalZonotope.euclideanProduct_eq_halfspaces n m c hc).symm


-- @@ L52-68 verbatim
/-- Body structure and attained orthogonal-projection support values for a block formula. -/
theorem projection_productZonotope_is_body_and_attains {n m : ℕ}
    (P : Set (E (n + m))) (c : ℝ) (hc : 0 < c)
    (hbrightness : ∀ u : E (n + m), ‖u‖ = 1 → projectionVolume P u = c * blockSupport u) :
    IsConvexBody (projectionBody P) ∧
      ∀ u : E (n + m), ‖u‖ = 1 → ∃ x ∈ projectionBody P, ⟪u, x⟫ = projectionVolume P u := by
  have hbody := projectionBody_eq_productZonotope P c hc hbrightness
  constructor
  · rw [hbody]
    exact ⟨DiagonalZonotope.isCompact_euclideanProduct n m c,
      DiagonalZonotope.convex_euclideanProduct n m c,
      DiagonalZonotope.euclideanProduct_interior_nonempty n m c hc.ne'⟩
  · intro u hu
    obtain ⟨x, hx, heq⟩ := DiagonalZonotope.euclideanProduct_support_attained n m c u
    refine ⟨x, hbody.symm ▸ hx, ?_⟩
    rw [hbrightness u hu]
    exact heq


-- @@ L70-70 verbatim
end ProjectionCounterexample


-- @@ L72-72 verbatim
end


-- @@ L74-74 verbatim
end OAI
