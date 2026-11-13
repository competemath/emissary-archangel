import Mathlib
import Submission.RelativeNormalizationProduct
import Submission.AmbientAffineConjugation


-- @@ L5-13 verbatim
/-!
# Ball-supported relative normalization

This file connects the positioned local ambient move directly to the relative
normalization product theorem.  It is the componentwise induction interface:
choose a ball around the component being changed, keep every earlier component
outside the larger support ball, and the fully glued signed cobordism is
literally a product over all earlier components.
-/


-- @@ L15-15 verbatim
set_option autoImplicit false


-- @@ L17-17 verbatim
noncomputable section


-- @@ L19-19 verbatim
open Set Function

-- @@ L20-20 verbatim
open scoped Topology ContDiff RealInnerProductSpace


-- @@ L22-22 verbatim
namespace Submission

-- @@ L23-23 verbatim
namespace SmoothAmbientIsotopy


-- @@ L25-25 verbatim
variable {m : ℕ}


-- @@ L27-27 verbatim
local notation "E" => EuclideanSpace ℝ (Fin (m + 2))


-- @@ L29-53 verbatim
/-- A complete normalization whose ambient stage is supported near the ball
`(b,r)` preserves every set outside the larger support ball, provided the
defining-map and target-sign stages are stationary there too. -/
theorem ballLocalizedPlaneRotation_signedNormalization_productOn
    (θ r : ℝ) (hr : 0 < r) (b : E)
    {X Y : FramedLevelSet (m + 1)}
    (D : DefiningMapHomotopy
      ((ballLocalizedPlaneRotation (m := m) θ r hr b).pullback X) Y)
    (S : FiberSign X) (T : FiberSign Y)
    (hpos : ∀ x ∈ Y.fiber,
      (0 < ((ballLocalizedPlaneRotation (m := m) θ r hr b).pullbackSign S).restrict
          D.fiber_subset x ↔ 0 < T x))
    {K : Set E}
    (hK : K ⊆ {x | 2 * r ^ 2 ≤ localRadialSq (x - b)})
    (hD : D.FixedOn K X.g) (hT : ∀ x ∈ K, T x = S x) :
    (signedNormalizationCobordism
      (ballLocalizedPlaneRotation (m := m) θ r hr b)
      D S T hpos).ProductOn K X.g S := by
  apply signedNormalizationCobordism_productOn
    (A := ballLocalizedPlaneRotation (m := m) θ r hr b)
    (D := D) (S := S) (T := T) hpos
  · exact (ballLocalizedPlaneRotation_fixedOn
      (m := m) θ r hr b).mono hK
  · exact hD
  · exact hT


-- @@ L55-55 verbatim
end SmoothAmbientIsotopy

-- @@ L56-56 verbatim
end Submission
