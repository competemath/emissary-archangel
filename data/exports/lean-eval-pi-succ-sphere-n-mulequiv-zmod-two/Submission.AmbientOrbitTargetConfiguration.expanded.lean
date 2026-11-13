import Mathlib
import Submission.AmbientFiniteComponentSchedule


-- @@ L4-17 verbatim
/-!
# The target configuration of a finite ambient orbit schedule

`AmbientFiniteComponentSchedule` turns mutually relative local orbit moves
into one ambient isotopy and proves the endpoint image theorem one component
at a time.  This file upgrades that statement to the whole framed fiber.

The resulting endpoint presentation has fiber exactly the union of the
prescribed targets, and distinct orbit targets remain disjoint.  Consequently
the only geometric input needed to put an arbitrary tamed framed fiber into a
finite standard-circle configuration is the local supported move recorded by
`OrbitMoveFamily`; the global enumeration and compatibility argument is
formal.
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
namespace SmoothAmbientIsotopy

-- @@ L28-28 verbatim
namespace OrbitMoveFamily


-- @@ L30-30 verbatim
variable {n : ℕ}


-- @@ L32-32 verbatim
local notation "E" => EuclideanSpace ℝ (Fin (n + 1))


-- @@ L34-34 verbatim
variable {X : FramedLevelSet n} {V : TamedField X}


-- @@ L36-39 verbatim
/-- The finite target configuration, written canonically as a union indexed
by the actual orbit components. -/
def targetUnion (F : OrbitMoveFamily X V) : Set E :=
  ⋃ O : V.OrbitIndex, F.target O


-- @@ L41-45 verbatim
/-- Every orbit subset is contained in the framed fiber. -/
theorem orbit_subset_fiber (O : V.OrbitIndex) : (O : Set E) ⊆ X.fiber := by
  obtain ⟨p, hp, hO⟩ := V.mem_orbitFinset.mp O.property
  rw [hO]
  exact V.orbit_subset_fiber hp


-- @@ L47-65 verbatim
/-- The endpoint map of the accumulated finite schedule sends the entire
source fiber onto the union of the prescribed component targets. -/
theorem ambientSchedule_endpoint_fiber (F : OrbitMoveFamily X V) :
    F.ambientSchedule.forward 1 '' X.fiber = F.targetUnion := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    let O : V.OrbitIndex :=
      ⟨V.orbit x, V.mem_orbitFinset.mpr ⟨x, hx, rfl⟩⟩
    have hxO : x ∈ (O : Set E) := V.mem_orbit_self x
    have himage : F.ambientSchedule.forward 1 x ∈ F.target O := by
      rw [← F.ambientSchedule_endpoint_image O]
      exact ⟨x, hxO, rfl⟩
    exact Set.mem_iUnion.mpr ⟨O, himage⟩
  · intro hy
    obtain ⟨O, hyO⟩ := Set.mem_iUnion.mp hy
    rw [← F.ambientSchedule_endpoint_image O] at hyO
    obtain ⟨x, hxO, rfl⟩ := hyO
    exact ⟨x, orbit_subset_fiber O hxO, rfl⟩


-- @@ L67-72 verbatim
/-- The framed level set transported by the accumulated ambient isotopy has
exactly the prescribed finite target configuration as its zero fiber. -/
theorem ambientSchedule_pullback_fiber (F : OrbitMoveFamily X V) :
    (F.ambientSchedule.pullback X).fiber = F.targetUnion := by
  rw [F.ambientSchedule.pullback_fiber,
    F.ambientSchedule_endpoint_fiber]


-- @@ L74-89 verbatim
/-- Distinct target components stay disjoint.  No extra target-separation
hypothesis is required: it follows from disjointness of the original orbit
components and injectivity of the accumulated endpoint diffeomorphism. -/
theorem target_disjoint (F : OrbitMoveFamily X V)
    {O P : V.OrbitIndex} (hOP : O ≠ P) :
    Disjoint (F.target O) (F.target P) := by
  have hsets : (O : Set E) ≠ (P : Set E) := by
    intro h
    exact hOP (Subtype.ext h)
  have hsource : Disjoint (O : Set E) (P : Set E) :=
    V.orbitFinset_pairwise_disjoint O O.property P P.property hsets
  have hinj : Function.Injective (F.ambientSchedule.forward 1) :=
    (F.ambientSchedule.left_inv 1 ⟨zero_le_one, le_rfl⟩).injective
  rw [← F.ambientSchedule_endpoint_image O,
    ← F.ambientSchedule_endpoint_image P]
  exact hsource.image hinj.injOn (subset_univ _) (subset_univ _)


-- @@ L91-96 verbatim
/-- Pairwise form of target disjointness, convenient for downstream finite
configuration APIs. -/
theorem target_pairwise_disjoint (F : OrbitMoveFamily X V) :
    Pairwise fun O P : V.OrbitIndex => Disjoint (F.target O) (F.target P) := by
  intro O P hOP
  exact F.target_disjoint hOP


-- @@ L98-98 verbatim
end OrbitMoveFamily

-- @@ L99-99 verbatim
end SmoothAmbientIsotopy

-- @@ L100-100 verbatim
end Submission
