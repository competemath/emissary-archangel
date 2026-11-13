import Mathlib
import Submission.ConcreteConfigurationMorseReduction


-- @@ L4-13 verbatim
/-!
# Exact-endpoint adapters for the concrete configuration reducer

The relative endpoint fields in `LocalHeadEventData` contain no work when the
current state is already definitionally the juxtaposed compact-model endpoint.
This file supplies the identity normalization and the resulting exact-event
constructor.  It isolates the genuine remaining task: arranging one coherent
family of states whose consecutive endpoints match, rather than repeatedly
rebuilding identity normalization records.
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
namespace ConcreteConfigurationMorseReduction


-- @@ L25-25 verbatim
variable {n : ℕ}


-- @@ L27-27 verbatim
local notation "E" => EuclideanSpace ℝ (Fin (n + 1))


-- @@ L29-42 verbatim
/-- The identity ambient pullback has a constant defining-map homotopy back
to the original presentation. -/
def identityPullbackHomotopy (X : FramedLevelSet n) :
    DefiningMapHomotopy ((SmoothAmbientIsotopy.refl n).pullback X) X where
  H := fun _ => X.g
  smooth := X.smooth.comp contDiff_snd
  H_zero := rfl
  H_one := rfl
  fiber_eq := by
    intro _ _ _
    rfl
  regular := by
    intro _ _ _ x hx
    exact X.regular x hx


-- @@ L44-44 verbatim
namespace NormalizationData


-- @@ L46-46 verbatim
variable {X : FramedLevelSet n}


-- @@ L48-54 verbatim
/-- Identity normalization of a signed presentation. -/
def refl (S : FiberSign X) : NormalizationData S S where
  ambient := SmoothAmbientIsotopy.refl n
  homotopy := identityPullbackHomotopy X
  signPattern := by
    intro _ _
    rfl


-- @@ L56-56 verbatim
end NormalizationData


-- @@ L58-58 verbatim
namespace RelativeNormalizationData


-- @@ L60-60 verbatim
variable {X : FramedLevelSet n}


-- @@ L62-72 verbatim
/-- Identity normalization is a literal product on every prescribed set. -/
def refl (S : FiberSign X) (K : Set E) :
    RelativeNormalizationData S S K where
  toNormalizationData := NormalizationData.refl S
  ambient_fixed := SmoothAmbientIsotopy.fixedOn_refl K
  homotopy_fixed := by
    intro _ _ _ _
    rfl
  target_fixed := by
    intro _ _
    rfl


-- @@ L74-74 verbatim
end RelativeNormalizationData


-- @@ L76-76 verbatim
namespace LocalHeadEventData


-- @@ L78-78 verbatim
variable {bkg : EuclideanSpace ℝ (Fin n)}


-- @@ L80-92 verbatim
/-- If the current endpoints are literally the compact head move with its
placed tail, the two relative endpoint normalizations are automatic. -/
def exact (M : SpatiallyFlatHeadMove n bkg)
    (tail : FlatSignedConfiguration n bkg) :
    LocalHeadEventData (M.sourceWithTailSign tail)
      (M.targetWithTailSign tail) M where
  tail := tail
  sourceNormalization :=
    RelativeNormalizationData.refl (M.sourceWithTailSign tail)
      (M.placedTail tail).X.fiber
  targetNormalization :=
    RelativeNormalizationData.refl (M.targetWithTailSign tail)
      (M.placedTail tail).X.fiber


-- @@ L94-94 verbatim
end LocalHeadEventData


-- @@ L96-96 verbatim
end ConcreteConfigurationMorseReduction

-- @@ L97-97 verbatim
end Submission

