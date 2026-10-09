import OAI.Geometry.ProjectionBody.GeometryDefinitions
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Geometry.Euclidean.Volume.Measure


-- @@ L5-5 verbatim
namespace OAI


-- @@ L7-11 verbatim
/-!
Geometric definitions for the product counterexample.
The projection measure is the canonically normalized Euclidean Hausdorff
measure of dimension `d - 1`, not ambient `d`-dimensional measure.
-/


-- @@ L13-13 verbatim
noncomputable section


-- @@ L15-15 verbatim
open Set MeasureTheory

-- @@ L16-16 verbatim
open scoped RealInnerProductSpace


-- @@ L18-18 verbatim
namespace ProjectionCounterexample


-- @@ L20-22 verbatim
/-- Orthogonal projection onto the hyperplane normal to `u`. -/
def project {d : ℕ} (u : E d) : E d →L[ℝ] E d :=
  (ℝ ∙ u)ᗮ.starProjection


-- @@ L24-26 verbatim
/-- Actual (d−1)-dimensional Euclidean volume of the orthogonal projection. -/
def projectionVolume {d : ℕ} (P : Set (E d)) (u : E d) : ℝ :=
  (Measure.euclideanHausdorffMeasure (d - 1) (project u '' P)).toReal


-- @@ L28-31 verbatim
/-- The projection body, defined entirely by its directional projection volumes.
The bounds are the normalized Hausdorff measures of orthogonal projections. -/
def projectionBody {d : ℕ} (P : Set (E d)) : Set (E d) :=
  {x | ∀ u : E d, ‖u‖ = 1 → ⟪u, x⟫ ≤ projectionVolume P u}


-- @@ L33-34 verbatim
/-- Lebesgue volume in the ambient Euclidean space. -/
def bodyVolume {d : ℕ} (P : Set (E d)) : ℝ := (volume P).toReal


-- @@ L36-38 verbatim
/-- The normalized projection-body volume. -/
def ratio {d : ℕ} (P : Set (E d)) : ℝ :=
  bodyVolume (projectionBody P) / bodyVolume P ^ (d - 1)


-- @@ L40-40 verbatim
end ProjectionCounterexample


-- @@ L42-42 verbatim
end


-- @@ L44-44 verbatim
end OAI
