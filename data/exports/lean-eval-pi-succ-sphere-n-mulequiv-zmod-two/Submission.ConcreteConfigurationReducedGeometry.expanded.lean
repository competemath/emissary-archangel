import Mathlib
import Submission.ConcreteConfigurationMorseReduction


-- @@ L4-16 verbatim
/-!
# Reduced configuration geometry with the identity frame gauge

The finite Morse reducer accepts an arbitrary smooth frame-gauge path after
the canonical component placement.  No nontrivial gauge is needed at that
interface: the relative endpoint normalizations in `ReductionData` already
match the placed presentation to the exact compact-event endpoints.

This file installs the constant identity gauge once and for all.  Hence the
complete configuration-reduction kit is reduced to the concrete finite
`ReductionData` family; placement and gauge fields no longer remain as
independent inputs.
-/


-- @@ L18-18 verbatim
set_option autoImplicit false


-- @@ L20-20 verbatim
noncomputable section


-- @@ L22-22 verbatim
open Set Function

-- @@ L23-23 verbatim
open scoped Topology ContDiff RealInnerProductSpace


-- @@ L25-25 verbatim
namespace Submission

-- @@ L26-26 verbatim
namespace ConcreteConfigurationReducedGeometry


-- @@ L28-28 verbatim
variable (m : ℕ)


-- @@ L30-30 verbatim
local notation "E" => EuclideanSpace ℝ (Fin (m + 3))

-- @@ L31-31 verbatim
local notation "F" => EuclideanSpace ℝ (Fin (m + 2))


-- @@ L33-44 verbatim
/-- The constant identity gauge is a valid frame-gauge path for every placed
configuration. -/
def identityFrameGaugeData {X : FramedLevelSet (m + 2)}
    (P : ConcreteConfigurationConfigure.ComponentPlacementData m X) :
    ConcreteConfigurationConfigure.FrameGaugeData m P where
  Q := fun _ _ => ContinuousLinearMap.id ℝ F
  smooth := contDiff_const
  zero := fun _ => rfl
  bijective := by
    intro _ _ _
    exact ContinuousLinearEquiv.bijective
      (ContinuousLinearEquiv.refl ℝ F)


-- @@ L46-55 verbatim
/-- In dimension at least three, canonical placement and the identity gauge
turn one finite-reduction witness into the complete narrowed geometry. -/
def geometryOfReduction {X : FramedLevelSet (m + 2)}
    (h3 : 3 ≤ m + 2) (S : FiberSign X)
    (D : ConcreteConfigurationMorseReduction.ReductionData m S
      (ConcreteConfigurationConfigure.componentPlacementData m h3)
      (identityFrameGaugeData m
        (ConcreteConfigurationConfigure.componentPlacementData m h3))) :
    ConcreteConfigurationConfigure.Geometry m S :=
  D.toGeometry


-- @@ L57-69 verbatim
/-- Direct production adapter: only the finite relative endpoint data and the
single zero-pair saddle model remain to be supplied. -/
def toConfigurationReductionKit
    (h3 : 3 ≤ m + 2)
    (supply : ∀ {X : FramedLevelSet (m + 2)} (S : FiberSign X),
      Nonempty
        (ConcreteConfigurationMorseReduction.ReductionData m S
          (ConcreteConfigurationConfigure.componentPlacementData m h3)
          (identityFrameGaugeData m
            (ConcreteConfigurationConfigure.componentPlacementData m h3)))) :
    ConfigurationReductionKit (m + 2) :=
  ConcreteConfigurationConfigure.toConfigurationReductionKitOfGeometry m
    (fun S => (supply S).map (geometryOfReduction m h3 S))


-- @@ L71-71 verbatim
end ConcreteConfigurationReducedGeometry

-- @@ L72-72 verbatim
end Submission

