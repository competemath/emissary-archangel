import OAI.Geometry.Zonotope.Scaling
import OAI.Geometry.Zonotope.Body
import Mathlib.Analysis.InnerProductSpace.PiL2


-- @@ L5-5 verbatim
namespace OAI


-- @@ L7-7 verbatim
/-! Coordinate and Euclidean versions of the explicit centered zonotope. -/

-- @@ L8-8 verbatim
noncomputable section

-- @@ L9-9 verbatim
open Set

-- @@ L10-10 verbatim
open scoped BigOperators RealInnerProductSpace


-- @@ L12-12 verbatim
namespace DiagonalZonotope

-- @@ L13-13 verbatim
variable {ι : Type*} [Fintype ι]


-- @@ L15-17 verbatim
/-- The actual scalar image of the cube-plus-diagonal body in Euclidean space. -/
def euclidean (c : ℝ) : Set (EuclideanSpace ℝ ι) :=
  WithLp.toLp 2 '' ((fun y : ι → ℝ => c • y) '' centered)


-- @@ L19-20 verbatim
/-- The directional support value, before multiplication by the scale. -/
def support (u : ι → ℝ) : ℝ := ((∑ i, |u i|) + |∑ i, u i|) / 2


-- @@ L22-22 verbatim
lemma support_zero : support (0 : ι → ℝ) = 0 := by simp [support]


-- @@ L24-25 verbatim
lemma support_smul (u : ι → ℝ) (a : ℝ) : support (a • u) = |a| * support u :=
  support_value_smul u a


-- @@ L27-29 verbatim
lemma inner_eq_coordinates (u x : EuclideanSpace ℝ ι) :
    ⟪u, x⟫ = ∑ i, u i * x i := by
  simp only [PiLp.inner_apply, Real.inner_apply]


-- @@ L31-38 verbatim
omit [Fintype ι] in
lemma mem_euclidean_iff (c : ℝ) (x : EuclideanSpace ℝ ι) :
    x ∈ euclidean c ↔ WithLp.ofLp x ∈ (fun y : ι → ℝ => c • y) '' centered := by
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact hq
  · intro hx
    exact ⟨WithLp.ofLp x, hx, rfl⟩


-- @@ L40-50 verbatim
/-- All directional inequalities characterize this concrete Euclidean body. -/
theorem euclidean_eq_halfspaces [DecidableEq ι] (c : ℝ) (hc : 0 < c) :
    (euclidean c : Set (EuclideanSpace ℝ ι)) =
      {x | ∀ u : EuclideanSpace ℝ ι, ⟪u, x⟫ ≤ c * support (WithLp.ofLp u)} := by
  ext x
  rw [mem_euclidean_iff, scaled_centered_eq_support_halfspaces c hc]
  constructor
  · intro hx u
    simpa only [inner_eq_coordinates, support] using hx (WithLp.ofLp u)
  · intro hx u
    simpa only [inner_eq_coordinates, support] using hx (WithLp.toLp 2 u)


-- @@ L52-57 verbatim
/-- Every directional support inequality is attained by an explicit point. -/
theorem euclidean_support_attained (c : ℝ) (u : EuclideanSpace ℝ ι) :
    ∃ x ∈ euclidean c, ⟪u, x⟫ = c * support (WithLp.ofLp u) := by
  obtain ⟨x, hx, heq⟩ := scaled_centered_support_attained (WithLp.ofLp u) c
  refine ⟨WithLp.toLp 2 x, ⟨x, hx, rfl⟩, ?_⟩
  simpa only [inner_eq_coordinates, support] using heq


-- @@ L59-60 verbatim
lemma isCompact_euclidean (c : ℝ) : IsCompact (euclidean c : Set (EuclideanSpace ℝ ι)) :=
  (isCompact_scaled_centered c).image (PiLp.continuous_toLp 2 (fun _ : ι => ℝ))


-- @@ L62-64 verbatim
lemma convex_euclidean (c : ℝ) : Convex ℝ (euclidean c : Set (EuclideanSpace ℝ ι)) :=
  (convex_scaled_centered c).linear_image
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => ℝ)).symm.toLinearMap


-- @@ L66-72 verbatim
lemma euclidean_interior_nonempty (c : ℝ) (hc : c ≠ 0) :
    (interior (euclidean c : Set (EuclideanSpace ℝ ι))).Nonempty := by
  let e := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => ℝ)).symm.toHomeomorph
  have he : (euclidean c : Set (EuclideanSpace ℝ ι)) =
      e '' ((fun y : ι → ℝ => c • y) '' centered) := rfl
  rw [he, ← e.image_interior]
  exact (scaled_centered_interior_nonempty c hc).image _


-- @@ L74-74 verbatim
end DiagonalZonotope


-- @@ L76-76 verbatim
end


-- @@ L78-78 verbatim
end OAI
