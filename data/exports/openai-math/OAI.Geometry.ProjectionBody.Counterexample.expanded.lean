import OAI.Geometry.ProjectionBody.ProductBrightness
import OAI.Geometry.ProjectionBody.ProductZonotopeBridge
import OAI.Geometry.Zonotope.EuclideanVolume
import OAI.Geometry.ProjectionBody.Arithmetic


-- @@ L6-6 verbatim
namespace OAI


-- @@ L8-12 verbatim
/-!
The geometric projection formulas identify the two actual projection bodies.
Their proved Euclidean volumes are substituted into the normalized ratio before
the final exact arithmetic is performed.
-/


-- @@ L14-14 verbatim
noncomputable section

-- @@ L15-15 verbatim
open Set MeasureTheory

-- @@ L16-16 verbatim
open scoped RealInnerProductSpace


-- @@ L18-18 verbatim
namespace ProjectionCounterexample


-- @@ L20-25 verbatim
theorem simplex_twenty_brightness {u : E 20} (hu : ‖u‖ = 1) :
    projectionVolume (simplex 20) u =
      (1 / (Nat.factorial 19 : ℝ)) * DiagonalZonotope.support (WithLp.ofLp u) := by
  rw [simplex_projectionVolume (n := 19) (by decide) hu]
  unfold DiagonalZonotope.support
  ring


-- @@ L27-37 verbatim
theorem product_brightness {u : E 20} (hu : ‖u‖ = 1) :
    projectionVolume productBody u =
      (1 / ((Nat.factorial 9 : ℝ) * Nat.factorial 10)) * blockSupport (n := 10) (m := 10) u := by
  rw [product_projectionVolume hu]
  change (((∑ i, |firstBlock u i|) + |∑ i, firstBlock u i|) +
      ((∑ i, |secondBlock u i|) + |∑ i, secondBlock u i|)) /
      (2 * ((Nat.factorial 9 : ℝ) * Nat.factorial 10)) =
    (1 / ((Nat.factorial 9 : ℝ) * Nat.factorial 10)) *
      (((∑ i, |firstBlock u i|) + |∑ i, firstBlock u i|) / 2 +
        ((∑ i, |secondBlock u i|) + |∑ i, secondBlock u i|) / 2)
  ring


-- @@ L39-43 verbatim
theorem simplex_twenty_projectionBody :
    projectionBody (simplex 20) =
      DiagonalZonotope.euclidean (1 / (Nat.factorial 19 : ℝ)) :=
  projectionBody_eq_zonotope (simplex 20) (1 / (Nat.factorial 19 : ℝ))
    (by positivity) (fun _ => simplex_twenty_brightness)


-- @@ L45-50 verbatim
theorem product_projectionBody :
    projectionBody productBody = DiagonalZonotope.euclideanProduct 10 10
      (1 / ((Nat.factorial 9 : ℝ) * Nat.factorial 10)) :=
  projectionBody_eq_productZonotope (n := 10) (m := 10) productBody
    (1 / ((Nat.factorial 9 : ℝ) * Nat.factorial 10))
    (by positivity) (fun _ => product_brightness)


-- @@ L52-58 verbatim
theorem simplex_twenty_projection_support :
    IsConvexBody (projectionBody (simplex 20)) ∧
      ∀ u : E 20, ‖u‖ = 1 →
        ∃ x ∈ projectionBody (simplex 20), ⟪u, x⟫ = projectionVolume (simplex 20) u :=
  projection_zonotope_is_body_and_attains (simplex 20) (1 / (Nat.factorial 19 : ℝ))
    (by positivity)
    (fun _ => simplex_twenty_brightness)


-- @@ L60-66 verbatim
theorem product_projection_support :
    IsConvexBody (projectionBody productBody) ∧
      ∀ u : E 20, ‖u‖ = 1 →
        ∃ x ∈ projectionBody productBody, ⟪u, x⟫ = projectionVolume productBody u :=
  projection_productZonotope_is_body_and_attains (n := 10) (m := 10) productBody
    (1 / ((Nat.factorial 9 : ℝ) * Nat.factorial 10)) (by positivity)
    (fun _ => product_brightness)


-- @@ L68-73 verbatim
theorem simplex_twenty_ratio :
    ratio (simplex 20) = ((21 : ℝ) * 20 ^ 20) / (Nat.factorial 20 : ℝ) := by
  unfold ratio bodyVolume
  rw [simplex_twenty_projectionBody,
    DiagonalZonotope.volume_euclidean_toReal _ (by positivity), volume_simplex]
  norm_num [Nat.factorial]


-- @@ L75-80 verbatim
theorem product_ratio_value :
    ratio productBody = (((11 : ℝ) * 10 ^ 10) / (Nat.factorial 10 : ℝ)) ^ 2 := by
  unfold ratio bodyVolume
  rw [product_projectionBody,
    DiagonalZonotope.volume_euclideanProduct_toReal 10 10 _ (by positivity), volume_productBody]
  norm_num [Nat.factorial]


-- @@ L82-85 verbatim
theorem product_to_simplex_ratio :
    ratio productBody / ratio (simplex 20) = (22355476 : ℝ) / 22020096 := by
  rw [product_ratio_value, simplex_twenty_ratio]
  exact numerical_product_ratio


-- @@ L87-94 verbatim
theorem product_exceeds_simplex : ratio (simplex 20) < ratio productBody := by
  have hpos : 0 < ratio (simplex 20) := by
    rw [simplex_twenty_ratio]
    positivity
  have hratio : 1 < ratio productBody / ratio (simplex 20) := by
    rw [product_to_simplex_ratio]
    exact numerical_strict_excess
  simpa using (lt_div_iff₀ hpos).mp hratio


-- @@ L96-99 verbatim
theorem universal_simplex_upper_bound_false :
    ¬ (∀ P : Set (E 20), IsConvexBody P → ratio P ≤ ratio (simplex 20)) := by
  intro h
  exact (not_le_of_gt product_exceeds_simplex) (h productBody productBody_convexBody)


-- @@ L101-101 verbatim
end ProjectionCounterexample


-- @@ L103-103 verbatim
end


-- @@ L105-105 verbatim
end OAI
