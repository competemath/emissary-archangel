import Mathlib
import Submission.AmbientOrbitTargetConfiguration
import Submission.SOCartesianRadialExtension


-- @@ L5-18 verbatim
/-!
# Canonical round targets for all orbit components

For `2 ≤ n`, every finite orbit index receives a concrete round unit circle
in the first two coordinate directions.  The circles are separated by placing
their centers four units apart in the third coordinate direction, using the
canonical choice equivalence with `Fin`.

`SupportedCanonicalRoundUnknotting` is the sole local geometric contract: one
supported ambient unknotting move for each source orbit, stationary on every
other source and target.  Everything else—the finite schedule, its ambient
isotopy, the whole-fiber endpoint equation, and target disjointness—is derived
from that contract.
-/


-- @@ L20-20 verbatim
set_option autoImplicit false


-- @@ L22-22 verbatim
noncomputable section


-- @@ L24-24 verbatim
open Set Function

-- @@ L25-25 verbatim
open scoped Topology ContDiff RealInnerProductSpace


-- @@ L27-27 verbatim
namespace Submission


-- @@ L29-29 verbatim
variable {n : ℕ}


-- @@ L31-31 verbatim
local notation "E" => EuclideanSpace ℝ (Fin (n + 1))


-- @@ L33-33 verbatim
namespace FramedLevelSet


-- @@ L35-37 verbatim
/-- A nonnegative radius of a closed ball containing the compact fiber. -/
def fiberBoundingRadius (X : FramedLevelSet n) : ℝ :=
  max 0 (Classical.choose (X.fiber_bounded.subset_closedBall (0 : E)))


-- @@ L39-41 verbatim
theorem fiberBoundingRadius_nonneg (X : FramedLevelSet n) :
    0 ≤ X.fiberBoundingRadius :=
  le_max_left _ _


-- @@ L43-48 verbatim
theorem fiber_subset_closedBall_fiberBoundingRadius (X : FramedLevelSet n) :
    X.fiber ⊆ Metric.closedBall (0 : E) X.fiberBoundingRadius := by
  let R := Classical.choose (X.fiber_bounded.subset_closedBall (0 : E))
  have hR : X.fiber ⊆ Metric.closedBall (0 : E) R :=
    Classical.choose_spec (X.fiber_bounded.subset_closedBall (0 : E))
  exact hR.trans (Metric.closedBall_subset_closedBall (le_max_right 0 R))


-- @@ L50-50 verbatim
end FramedLevelSet


-- @@ L52-52 verbatim
namespace TamedField


-- @@ L54-54 verbatim
variable {X : FramedLevelSet n} (V : TamedField X)


-- @@ L56-58 verbatim
/-- The canonical finite slot assigned to an orbit component. -/
def orbitSlot (O : V.OrbitIndex) : Fin (Fintype.card V.OrbitIndex) :=
  Fintype.equivFin V.OrbitIndex O


-- @@ L60-61 verbatim
@[simp] theorem orbitSlot_injective : Function.Injective V.orbitSlot :=
  (Fintype.equivFin V.OrbitIndex).injective


-- @@ L63-63 verbatim
end TamedField


-- @@ L65-65 verbatim
namespace CanonicalRoundOrbit


-- @@ L67-67 verbatim
variable {X : FramedLevelSet n} (V : TamedField X) (h2 : 2 ≤ n)


-- @@ L69-70 verbatim
/-- Zeroth coordinate direction of the common circle plane. -/
def e₀ : E := EuclideanSpace.single (⟨0, by omega⟩ : Fin (n + 1)) 1


-- @@ L72-73 verbatim
/-- First coordinate direction of the common circle plane. -/
def e₁ : E := EuclideanSpace.single (⟨1, by omega⟩ : Fin (n + 1)) 1


-- @@ L75-76 verbatim
/-- Third coordinate direction used to separate component centers. -/
def e₂ : E := EuclideanSpace.single (⟨2, by omega⟩ : Fin (n + 1)) 1


-- @@ L78-80 verbatim
/-- Center of the canonical circle assigned to `O`. -/
def center (O : V.OrbitIndex) : E :=
  (X.fiberBoundingRadius + 3 + 4 * (V.orbitSlot O : ℕ) : ℝ) • e₂ h2


-- @@ L82-84 verbatim
/-- A concrete parametrization of the assigned round unit circle. -/
def point (O : V.OrbitIndex) (θ : ℝ) : E :=
  center V h2 O + Real.cos θ • e₀ h2 + Real.sin θ • e₁ h2


-- @@ L86-90 verbatim
/-- Quotient-circle parametrization of the assigned round unit circle.  This
is the compact parametrization used by the support-separation argument. -/
def circlePoint (O : V.OrbitIndex) (a : AddCircle (1 : ℝ)) : E :=
  center V h2 O + (addCircleCartesian a).1 • e₀ h2 +
    (addCircleCartesian a).2 • e₁ h2


-- @@ L92-93 verbatim
/-- The canonical round target set of one orbit component. -/
def target (O : V.OrbitIndex) : Set E := Set.range (circlePoint V h2 O)


-- @@ L95-96 verbatim
/-- The finite union which is the target of the global ambient schedule. -/
def targetUnion : Set E := ⋃ O : V.OrbitIndex, target V h2 O


-- @@ L98-101 verbatim
@[simp] theorem point_apply_two (O : V.OrbitIndex) (θ : ℝ) :
    point V h2 O θ (⟨2, by omega⟩ : Fin (n + 1)) =
      (X.fiberBoundingRadius + 3 + 4 * (V.orbitSlot O : ℕ) : ℝ) := by
  simp [point, center, e₀, e₁, e₂]


-- @@ L103-107 verbatim
@[simp] theorem circlePoint_apply_two (O : V.OrbitIndex)
    (a : AddCircle (1 : ℝ)) :
    circlePoint V h2 O a (⟨2, by omega⟩ : Fin (n + 1)) =
      (X.fiberBoundingRadius + 3 + 4 * (V.orbitSlot O : ℕ) : ℝ) := by
  simp [circlePoint, center, e₀, e₁, e₂]


-- @@ L109-113 verbatim
theorem continuous_circlePoint (O : V.OrbitIndex) :
    Continuous (circlePoint V h2 O) := by
  exact continuous_const.add
    (continuous_addCircleCartesian.fst.smul continuous_const) |>.add
      (continuous_addCircleCartesian.snd.smul continuous_const)


-- @@ L115-118 verbatim
/-- Every canonical target circle is compact. -/
theorem isCompact_target (O : V.OrbitIndex) :
    IsCompact (target V h2 O) :=
  isCompact_range (continuous_circlePoint V h2 O)


-- @@ L120-134 verbatim
/-- The canonical translated round circles occupy disjoint affine planes. -/
theorem target_disjoint {O P : V.OrbitIndex} (hOP : O ≠ P) :
    Disjoint (target V h2 O) (target V h2 P) := by
  rw [Set.disjoint_left]
  intro x hxO hxP
  obtain ⟨a, rfl⟩ := hxO
  obtain ⟨b, heq⟩ := hxP
  have hcoord := congrArg
    (fun x : E => x (⟨2, by omega⟩ : Fin (n + 1))) heq
  simp only [circlePoint_apply_two] at hcoord
  have hslotNat : (V.orbitSlot O : ℕ) = (V.orbitSlot P : ℕ) := by
    exact_mod_cast (by linarith :
      (V.orbitSlot O : ℝ) = (V.orbitSlot P : ℝ))
  have hslot : V.orbitSlot O = V.orbitSlot P := Fin.ext hslotNat
  exact hOP (V.orbitSlot_injective hslot)


-- @@ L136-155 verbatim
/-- All targets are placed strictly outside the ball containing the source
fiber, so no canonical target can meet any source component. -/
theorem target_disjoint_fiber (O : V.OrbitIndex) :
    Disjoint (target V h2 O) X.fiber := by
  rw [Set.disjoint_left]
  intro x hxTarget hxFiber
  obtain ⟨a, rfl⟩ := hxTarget
  have hball := X.fiber_subset_closedBall_fiberBoundingRadius hxFiber
  rw [Metric.mem_closedBall, dist_zero_right] at hball
  have hcoord := PiLp.norm_apply_le (circlePoint V h2 O a)
    (⟨2, by omega⟩ : Fin (n + 1))
  have hcenter_nonneg :
      0 ≤ (X.fiberBoundingRadius + 3 +
        4 * (V.orbitSlot O : ℕ) : ℝ) := by
    have hslot : (0 : ℝ) ≤ ((V.orbitSlot O : ℕ) : ℝ) :=
      Nat.cast_nonneg _
    nlinarith [X.fiberBoundingRadius_nonneg]
  rw [circlePoint_apply_two, Real.norm_eq_abs,
    abs_of_nonneg hcenter_nonneg] at hcoord
  nlinarith [X.fiberBoundingRadius_nonneg]


-- @@ L157-162 verbatim
theorem targetUnion_disjoint_fiber :
    Disjoint (targetUnion V h2) X.fiber := by
  rw [Set.disjoint_left]
  intro x hxTarget hxFiber
  obtain ⟨O, hxO⟩ := Set.mem_iUnion.mp hxTarget
  exact Set.disjoint_left.mp (target_disjoint_fiber V h2 O) hxO hxFiber


-- @@ L164-164 verbatim
end CanonicalRoundOrbit


-- @@ L166-166 verbatim
namespace SmoothAmbientIsotopy


-- @@ L168-168 verbatim
variable {X : FramedLevelSet n} {V : TamedField X}


-- @@ L170-183 verbatim
/-- The only local geometric input for placing every orbit on a canonical
round circle.  The relative support clause is stated solely on the finite
source/target configuration; a stronger neighborhood-supported unknotting
theorem can feed it by monotonicity. -/
structure SupportedCanonicalRoundUnknotting (h2 : 2 ≤ n) where
  move : V.OrbitIndex → SmoothAmbientIsotopy n
  endpoint_image : ∀ O : V.OrbitIndex,
    (move O).forward 1 '' (O : Set E) =
      CanonicalRoundOrbit.target V h2 O
  mutuallyRelative : ∀ O P : V.OrbitIndex, O ≠ P →
    (move O).FixedOn
        ((P : Set E) ∪ CanonicalRoundOrbit.target V h2 P) ∧
      (move P).FixedOn
        ((O : Set E) ∪ CanonicalRoundOrbit.target V h2 O)


-- @@ L185-185 verbatim
namespace SupportedCanonicalRoundUnknotting


-- @@ L187-187 verbatim
variable {h2 : 2 ≤ n}


-- @@ L189-195 verbatim
/-- Forget only the fact that the targets are the canonical round circles. -/
def toOrbitMoveFamily (U : SupportedCanonicalRoundUnknotting
    (X := X) (V := V) h2) : OrbitMoveFamily X V where
  target := CanonicalRoundOrbit.target V h2
  move := U.move
  endpoint_image := U.endpoint_image
  mutuallyRelative := U.mutuallyRelative


-- @@ L197-200 verbatim
/-- The globally accumulated ambient isotopy. -/
def ambient (U : SupportedCanonicalRoundUnknotting
    (X := X) (V := V) h2) : SmoothAmbientIsotopy n :=
  U.toOrbitMoveFamily.ambientSchedule


-- @@ L202-205 verbatim
/-- The endpoint framed presentation after the global round-circle move. -/
def endpointX (U : SupportedCanonicalRoundUnknotting
    (X := X) (V := V) h2) : FramedLevelSet n :=
  U.ambient.pullback X


-- @@ L207-210 verbatim
/-- Transport any source sign label to the round-circle endpoint. -/
def endpointSign (U : SupportedCanonicalRoundUnknotting
    (X := X) (V := V) h2) (S : FiberSign X) : FiberSign U.endpointX :=
  U.ambient.pullbackSign S


-- @@ L212-217 verbatim
/-- The local unknotting input already produces an actual signed framed
cobordism to the finite round-circle presentation. -/
def signedCobordism (U : SupportedCanonicalRoundUnknotting
    (X := X) (V := V) h2) (S : FiberSign X) :
    SignedFramedLevelCobordism S (U.endpointSign S) :=
  U.ambient.signedCobordism S


-- @@ L219-224 verbatim
/-- Each component reaches its assigned canonical round circle. -/
theorem ambient_endpoint_orbit (U : SupportedCanonicalRoundUnknotting
    (X := X) (V := V) h2) (O : V.OrbitIndex) :
    U.ambient.forward 1 '' (O : Set E) =
      CanonicalRoundOrbit.target V h2 O :=
  U.toOrbitMoveFamily.ambientSchedule_endpoint_image O


-- @@ L226-231 verbatim
/-- The whole transported fiber is exactly the canonical finite union of
round circles. -/
theorem ambient_pullback_fiber (U : SupportedCanonicalRoundUnknotting
    (X := X) (V := V) h2) :
    U.endpointX.fiber = CanonicalRoundOrbit.targetUnion V h2 := by
  exact U.toOrbitMoveFamily.ambientSchedule_pullback_fiber


-- @@ L233-237 verbatim
@[simp] theorem endpointSign_forward (U : SupportedCanonicalRoundUnknotting
    (X := X) (V := V) h2) (S : FiberSign X) (x : E) :
    U.endpointSign S (U.ambient.forward 1 x) = S x := by
  rw [endpointSign, SmoothAmbientIsotopy.pullbackSign_apply,
    U.ambient.left_inv 1 ⟨zero_le_one, le_rfl⟩]


-- @@ L239-268 verbatim
/-- A canonical target circle is positive exactly when its source orbit was
positive.  Thus the signed component ledger survives the global placement
without any additional compatibility choice. -/
theorem target_subset_positivePart_iff
    (U : SupportedCanonicalRoundUnknotting
      (X := X) (V := V) h2) (S : FiberSign X) (O : V.OrbitIndex) :
    CanonicalRoundOrbit.target V h2 O ⊆ (U.endpointSign S).positivePart ↔
      (O : Set E) ∈ S.positiveOrbitCollection V := by
  constructor
  · intro htarget
    rw [S.mem_positiveOrbitCollection_iff V O]
    have hxO : V.orbitPoint O ∈ (O : Set E) := by
      rw [V.orbitPoint_orbit]
      exact V.mem_orbit_self _
    have himage : U.ambient.forward 1 (V.orbitPoint O) ∈
        CanonicalRoundOrbit.target V h2 O := by
      rw [← U.ambient_endpoint_orbit O]
      exact ⟨V.orbitPoint O, hxO, rfl⟩
    exact (by simpa using (htarget himage).2)
  · intro hsource y hy
    rw [← U.ambient_endpoint_orbit O] at hy
    obtain ⟨x, hxO, rfl⟩ := hy
    have hpositive : 0 < S x := by
      have hsource' := hsource hxO
      exact hsource'.2
    exact ⟨by
      rw [U.ambient_pullback_fiber]
      exact Set.mem_iUnion.mpr ⟨O,
        (by rw [← U.ambient_endpoint_orbit O]; exact ⟨x, hxO, rfl⟩)⟩,
      by simpa using hpositive⟩


-- @@ L270-277 verbatim
/-- The target circles are pairwise disjoint, independently of the supplied
move implementation. -/
theorem target_pairwise_disjoint (_U : SupportedCanonicalRoundUnknotting
    (X := X) (V := V) h2) :
    Pairwise fun O P : V.OrbitIndex =>
      Disjoint (CanonicalRoundOrbit.target V h2 O)
        (CanonicalRoundOrbit.target V h2 P) := by
  exact fun O P hOP => CanonicalRoundOrbit.target_disjoint V h2 hOP


-- @@ L279-279 verbatim
end SupportedCanonicalRoundUnknotting

-- @@ L280-280 verbatim
end SmoothAmbientIsotopy

-- @@ L281-281 verbatim
end Submission
