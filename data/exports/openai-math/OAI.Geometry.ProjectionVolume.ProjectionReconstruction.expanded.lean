import OAI.Geometry.ProjectionVolume.Basic
import OAI.Geometry.ProjectionVolume.SupportGeometry


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
namespace Paper092


-- @@ L8-13 verbatim
theorem projectionBody_eq_of_brightness_eq_support {n : ℕ}
    {K C : Set (Euclidean n)} (hC : IsCompact C) (hne : C.Nonempty)
    (hconv : Convex ℝ C)
    (h : ∀ u, brightness K u = SupportGeometry.support C (innerSL ℝ u)) :
    projectionBody K = C :=
  SupportGeometry.halfSpaces_eq_of_eq_support hC hne hconv (brightness K) h


-- @@ L15-15 verbatim
end Paper092


-- @@ L17-17 verbatim
end OAI
