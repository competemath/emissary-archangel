import Mathlib
import Submission.OrbitUnknottingFourierRelativeTrack
import Submission.OrbitUnknottingRelativeMoveAssembly


-- @@ L5-17 verbatim
/-!
# Finite assembly of local ambient moves along a circle track

The isotopy-extension analysis produces local moves between nearby slices of
an embedded-circle track.  This file records the exact finite induction which
turns those local moves into the one-orbit realization consumed by the global
relative-move assembly.

The chain is indexed by its literal initial and final track parameters.  Its
endpoint theorem therefore has no mesh arithmetic or list-alignment side
conditions: composing a head step `s -> t` with a tail chain `t -> r` gives a
chain `s -> r` by construction.
-/


-- @@ L19-19 verbatim
set_option autoImplicit false


-- @@ L21-21 verbatim
noncomputable section


-- @@ L23-23 verbatim
open Set Function

-- @@ L24-24 verbatim
open scoped Topology ContDiff RealInnerProductSpace


-- @@ L26-26 verbatim
namespace Submission

-- @@ L27-27 verbatim
namespace TamedField

-- @@ L28-28 verbatim
namespace FourierEmbeddingTrack


-- @@ L30-30 verbatim
variable {n : ℕ} {X : FramedLevelSet n} {V : TamedField X}


-- @@ L32-32 verbatim
local notation "E" => EuclideanSpace ℝ (Fin (n + 1))


-- @@ L34-34 verbatim
variable {h2 : 2 ≤ n} {O : V.OrbitIndex}


-- @@ L36-36 verbatim
namespace EmbeddedCircleTrack


-- @@ L38-38 verbatim
variable (T : EmbeddedCircleTrack (V := V) h2 O)


-- @@ L40-48 verbatim
/-- The real lift at time zero is the intrinsic orbit lift. -/
theorem lift_zero (u : ℝ) :
    T.lift 0 u = V.intrinsicOrbitLift O u := by
  calc
    T.lift 0 u = T.circle 0 (u : AddCircle (1 : ℝ)) :=
      (T.circle_coe 0 u).symm
    _ = V.intrinsicOrbitEmbedding O (u : AddCircle (1 : ℝ)) := by
      rw [T.start_circle]
    _ = V.intrinsicOrbitLift O u := V.intrinsicOrbitEmbedding_coe O u


-- @@ L50-60 verbatim
/-- The real lift at time one is the assigned canonical target lift. -/
theorem lift_one (u : ℝ) :
    T.lift 1 u = targetLift (V := V) h2 O u := by
  calc
    T.lift 1 u = T.circle 1 (u : AddCircle (1 : ℝ)) :=
      (T.circle_coe 1 u).symm
    _ = CanonicalRoundOrbit.circlePoint V h2 O
        (u : AddCircle (1 : ℝ)) := by
      rw [T.finish_circle]
    _ = targetLift (V := V) h2 O u :=
      (targetLift_eq_circlePoint (V := V) h2 O u).symm


-- @@ L62-62 verbatim
end EmbeddedCircleTrack


-- @@ L64-72 verbatim
/-- One ambient step between two literal slices of a fixed embedded-circle
track, stationary on the full relative obstacle configuration. -/
structure AmbientTrackStep
    (T : EmbeddedCircleTrack (V := V) h2 O) (s t : ℝ) where
  move : SmoothAmbientIsotopy n
  endpoint_lift : ∀ u : ℝ,
    move.forward 1 (T.lift s u) = T.lift t u
  fixed_obstacle : move.FixedOn
    (OrbitUnknottingSupport.obstacleSet V h2 O)


-- @@ L74-79 verbatim
/-- A type-indexed finite chain of compatible local ambient steps. -/
inductive AmbientTrackChain
    (T : EmbeddedCircleTrack (V := V) h2 O) : ℝ → ℝ → Type
  | refl (s : ℝ) : AmbientTrackChain T s s
  | cons {s t r : ℝ} (head : AmbientTrackStep T s t)
      (tail : AmbientTrackChain T t r) : AmbientTrackChain T s r


-- @@ L81-81 verbatim
namespace AmbientTrackChain


-- @@ L83-83 verbatim
variable {T : EmbeddedCircleTrack (V := V) h2 O}


-- @@ L85-88 verbatim
/-- Compose a finite track chain in chronological order. -/
def ambient : {s t : ℝ} → AmbientTrackChain T s t → SmoothAmbientIsotopy n
  | _, _, .refl _ => SmoothAmbientIsotopy.refl n
  | _, _, .cons head tail => head.move.followedBy tail.ambient


-- @@ L90-93 verbatim
@[simp] theorem ambient_refl (s : ℝ) :
    (AmbientTrackChain.refl s : AmbientTrackChain T s s).ambient =
      SmoothAmbientIsotopy.refl n :=
  rfl


-- @@ L95-99 verbatim
@[simp] theorem ambient_cons {s t r : ℝ}
    (head : AmbientTrackStep T s t) (tail : AmbientTrackChain T t r) :
    (AmbientTrackChain.cons head tail).ambient =
      head.move.followedBy tail.ambient :=
  rfl


-- @@ L101-110 verbatim
/-- The composed endpoint carries the initial parametrized slice exactly to
the final parametrized slice. -/
theorem ambient_forward_initial {s t : ℝ}
    (C : AmbientTrackChain T s t) (u : ℝ) :
    C.ambient.forward 1 (T.lift s u) = T.lift t u := by
  induction C with
  | refl r => rfl
  | @cons s r t head tail ih =>
      rw [ambient_cons, SmoothAmbientIsotopy.followedBy_forward,
        head.endpoint_lift, ih]


-- @@ L112-121 verbatim
/-- Relative fixedness is preserved by the whole finite chain. -/
theorem ambient_fixedObstacle {s t : ℝ}
    (C : AmbientTrackChain T s t) :
    C.ambient.FixedOn
      (OrbitUnknottingSupport.obstacleSet V h2 O) := by
  induction C with
  | refl r =>
      exact SmoothAmbientIsotopy.fixedOn_refl _
  | @cons s r t head tail ih =>
      exact head.fixed_obstacle.followedBy ih


-- @@ L123-123 verbatim
end AmbientTrackChain


-- @@ L125-125 verbatim
end FourierEmbeddingTrack


-- @@ L127-127 verbatim
namespace FourierRelativeTrack

-- @@ L128-128 verbatim
namespace RelativeEmbeddedCircleTrack


-- @@ L130-130 verbatim
variable {n : ℕ} {X : FramedLevelSet n} {V : TamedField X}

-- @@ L131-131 verbatim
variable {h2 : 2 ≤ n} {O : V.OrbitIndex}


-- @@ L133-133 verbatim
variable (R : RelativeEmbeddedCircleTrack (V := V) h2 O)


-- @@ L135-144 verbatim
/-- A finite ambient realization of the relative Fourier track is precisely
the one-orbit canonical move required by the global component assembly. -/
def relativeCanonicalOrbitMoveOfChain
    (C : FourierEmbeddingTrack.AmbientTrackChain R.track 0 1) :
    RelativeCanonicalOrbitMove V h2 O where
  move := C.ambient
  endpoint_lift u := by
    rw [← R.track.lift_zero u, C.ambient_forward_initial u,
      R.track.lift_one u]
  fixed_obstacle := C.ambient_fixedObstacle


-- @@ L146-146 verbatim
end RelativeEmbeddedCircleTrack

-- @@ L147-147 verbatim
end FourierRelativeTrack


-- @@ L149-149 verbatim
end TamedField

-- @@ L150-150 verbatim
end Submission
