import OAI.Geometry.ProjectionBodies.AffineCovariance


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section

-- @@ L6-6 verbatim
open Set MeasureTheory

-- @@ L7-7 verbatim
namespace PettyProjection


-- @@ L9-16 verbatim
/-- The exact unrestricted inequality and its global equality characterization.
-/
theorem petty_projection_volume (n : ℕ) (hn : 4 ≤ n)
    (K : Set (Space n)) (hK : IsConvexBody K) :
    pettyConstant n ≤ projectionRatio K ∧
      (projectionRatio K = pettyConstant n ↔ IsEllipsoid K) := by
  obtain ⟨hbound,hrigid⟩ := projection_lower_bound hn hK
  exact ⟨hbound,hrigid,ellipsoid_projectionRatio (by omega)⟩


-- @@ L18-18 verbatim
theorem mainClaim_proved : MainClaim := petty_projection_volume


-- @@ L20-20 verbatim
theorem MainClaim_proved : MainClaim := mainClaim_proved


-- @@ L22-22 verbatim
end PettyProjection

-- @@ L23-23 verbatim
end


-- @@ L25-25 verbatim
end OAI
