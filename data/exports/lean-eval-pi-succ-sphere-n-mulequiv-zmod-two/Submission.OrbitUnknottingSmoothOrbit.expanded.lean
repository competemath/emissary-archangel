import Mathlib
import Submission.OrbitUnknottingSmoothCutoff


-- @@ L4-19 verbatim
/-!
# Smooth embedded-circle data for an intrinsic orbit

The orbit machinery initially constructs its global flow through classical
Picard--Lindelöf solutions and records only a derivative in the time variable.
For ambient unknotting we need a genuinely smooth embedded circle.  This file
bootstraps the ODE identity

`d/dt flow(p,t) = v(flow(p,t))`

to prove that every flow line is `C∞`.  It then rescales one positive
fundamental period to period one and packages the resulting map from
`AddCircle 1` as a topological embedding with nonvanishing smooth lift.

No unknotting or isotopy-extension theorem is used here.
-/


-- @@ L21-21 verbatim
set_option autoImplicit false


-- @@ L23-23 verbatim
noncomputable section


-- @@ L25-25 verbatim
open Set Function

-- @@ L26-26 verbatim
open scoped Topology ContDiff RealInnerProductSpace


-- @@ L28-28 verbatim
namespace Submission

-- @@ L29-29 verbatim
namespace TamedField


-- @@ L31-31 verbatim
variable {n : ℕ} {X : FramedLevelSet n} (V : TamedField X)


-- @@ L33-33 verbatim
local notation "E" => EuclideanSpace ℝ (Fin (n + 1))


-- @@ L35-55 verbatim
/-- A flow line of the smooth tamed field is smooth to every finite order.

The proof bootstraps from continuity.  If the flow is `C^k`, then its
derivative `v ∘ flow` is `C^k`, so the flow is `C^(k+1)`. -/
theorem contDiff_flow (p : E) : ContDiff ℝ ∞ (V.flow p) := by
  rw [contDiff_infty]
  intro k
  induction k with
  | zero =>
      exact contDiff_zero.mpr (V.continuous_flow p)
  | succ k ih =>
      rw [show ((k + 1 : ℕ) : ℕ∞ω) = (k : ℕ∞ω) + 1 by norm_num,
        contDiff_succ_iff_deriv]
      refine ⟨fun t => (V.hasDerivAt_flow p t).differentiableAt, ?_, ?_⟩
      · simp
      · have hderiv : deriv (V.flow p) = V.v ∘ V.flow p := by
          funext t
          exact (V.hasDerivAt_flow p t).deriv
        rw [hderiv]
        exact (V.smooth.of_le
          (by exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤))).comp ih


-- @@ L57-59 verbatim
@[simp] theorem deriv_flow (p : E) (t : ℝ) :
    deriv (V.flow p) t = V.v (V.flow p t) :=
  (V.hasDerivAt_flow p t).deriv


-- @@ L61-65 verbatim
/-- On a fiber orbit the flow is a unit-speed immersion. -/
theorem norm_deriv_flow_of_mem_fiber {p : E} (hp : p ∈ X.fiber) (t : ℝ) :
    ‖deriv (V.flow p) t‖ = 1 := by
  rw [V.deriv_flow, V.v_eq_tau_of_mem_fiber (V.flow_mem_fiber hp t),
    norm_tauField (X.fiber_subset_regularSet (V.flow_mem_fiber hp t))]


-- @@ L67-69 verbatim
/-- The real lift of the selected orbit, rescaled so that its period is one. -/
def intrinsicOrbitLift (O : V.OrbitIndex) (u : ℝ) : E :=
  V.flow (V.orbitPoint O) (u * V.orbitPeriod O)


-- @@ L71-74 verbatim
theorem contDiff_intrinsicOrbitLift (O : V.OrbitIndex) :
    ContDiff ℝ ∞ (V.intrinsicOrbitLift O) := by
  exact (V.contDiff_flow (V.orbitPoint O)).comp
    (contDiff_id.mul contDiff_const)


-- @@ L76-86 verbatim
theorem hasDerivAt_intrinsicOrbitLift (O : V.OrbitIndex) (u : ℝ) :
    HasDerivAt (V.intrinsicOrbitLift O)
      (V.orbitPeriod O • V.v (V.intrinsicOrbitLift O u)) u := by
  have h :=
    (V.hasDerivAt_flow (V.orbitPoint O) (u * V.orbitPeriod O)).scomp u
      ((hasDerivAt_id u).mul_const (V.orbitPeriod O))
  change HasDerivAt
    (fun z : ℝ => V.flow (V.orbitPoint O) (z * V.orbitPeriod O))
    (V.orbitPeriod O •
      V.v (V.flow (V.orbitPoint O) (u * V.orbitPeriod O))) u
  simpa [Function.comp_def] using h


-- @@ L88-99 verbatim
/-- The rescaled lift has constant positive speed equal to the fundamental
period. -/
theorem norm_deriv_intrinsicOrbitLift (O : V.OrbitIndex) (u : ℝ) :
    ‖deriv (V.intrinsicOrbitLift O) u‖ = V.orbitPeriod O := by
  rw [(V.hasDerivAt_intrinsicOrbitLift O u).deriv, norm_smul,
    intrinsicOrbitLift,
    V.v_eq_tau_of_mem_fiber
      (V.flow_mem_fiber (V.orbitPoint_mem_fiber O) (u * V.orbitPeriod O)),
    norm_tauField (X.fiber_subset_regularSet
      (V.flow_mem_fiber (V.orbitPoint_mem_fiber O)
        (u * V.orbitPeriod O))),
    mul_one, Real.norm_eq_abs, abs_of_pos (V.orbitPeriod_pos O)]


-- @@ L101-106 verbatim
theorem deriv_intrinsicOrbitLift_ne_zero (O : V.OrbitIndex) (u : ℝ) :
    deriv (V.intrinsicOrbitLift O) u ≠ 0 := by
  intro hzero
  have hnorm := V.norm_deriv_intrinsicOrbitLift O u
  rw [hzero, norm_zero] at hnorm
  linarith [V.orbitPeriod_pos O]


-- @@ L108-114 verbatim
theorem periodic_intrinsicOrbitLift (O : V.OrbitIndex) :
    Function.Periodic (V.intrinsicOrbitLift O) 1 := by
  intro u
  change V.flow (V.orbitPoint O) ((u + 1) * V.orbitPeriod O) =
    V.flow (V.orbitPoint O) (u * V.orbitPeriod O)
  convert V.flow_periodic_orbitPeriod O (u * V.orbitPeriod O) using 1
  · ring


-- @@ L116-125 verbatim
/-- The intrinsic orbit as a concrete homeomorphic copy of the unit additive
circle.  It is the period-rescaling homeomorphism followed by the existing
flow-orbit homeomorphism. -/
def intrinsicOrbitHomeomorph (O : V.OrbitIndex) :
    AddCircle (1 : ℝ) ≃ₜ (O : Set E) :=
  (AddCircle.homeomorphAddCircle 1
      (V.fundamentalPeriod (V.orbitPoint_mem_fiber O)) one_ne_zero
      (ne_of_gt (V.fundamentalPeriod_pos (V.orbitPoint_mem_fiber O)))).trans
    ((V.orbitCircleHomeomorph (V.orbitPoint_mem_fiber O)).trans
      (Homeomorph.setCongr (V.orbitPoint_orbit O).symm))


-- @@ L127-129 verbatim
/-- The embedded-circle map into ambient Euclidean space. -/
def intrinsicOrbitEmbedding (O : V.OrbitIndex) : AddCircle (1 : ℝ) → E :=
  fun a => V.intrinsicOrbitHomeomorph O a


-- @@ L131-138 verbatim
@[simp] theorem intrinsicOrbitEmbedding_coe (O : V.OrbitIndex) (u : ℝ) :
    V.intrinsicOrbitEmbedding O (u : AddCircle (1 : ℝ)) =
      V.intrinsicOrbitLift O u := by
  simpa [intrinsicOrbitEmbedding, intrinsicOrbitHomeomorph,
      intrinsicOrbitLift, orbitPeriod, Homeomorph.setCongr,
      AddCircle.homeomorphAddCircle_apply_mk] using
    (V.orbitCircleHomeomorph_coe (V.orbitPoint_mem_fiber O)
      (u * V.fundamentalPeriod (V.orbitPoint_mem_fiber O)))


-- @@ L140-145 verbatim
theorem isEmbedding_intrinsicOrbitEmbedding (O : V.OrbitIndex) :
    Topology.IsEmbedding (V.intrinsicOrbitEmbedding O) := by
  change Topology.IsEmbedding
    ((fun x : (O : Set E) => (x : E)) ∘ V.intrinsicOrbitHomeomorph O)
  exact Topology.IsEmbedding.subtypeVal.comp
    (V.intrinsicOrbitHomeomorph O).isEmbedding


-- @@ L147-156 verbatim
theorem range_intrinsicOrbitEmbedding (O : V.OrbitIndex) :
    Set.range (V.intrinsicOrbitEmbedding O) = (O : Set E) := by
  apply Set.Subset.antisymm
  · rintro x ⟨a, rfl⟩
    exact (V.intrinsicOrbitHomeomorph O a).property
  · intro x hx
    let y : (O : Set E) := ⟨x, hx⟩
    refine ⟨(V.intrinsicOrbitHomeomorph O).symm y, ?_⟩
    exact congrArg Subtype.val
      ((V.intrinsicOrbitHomeomorph O).apply_symm_apply y)


-- @@ L158-169 verbatim
/-- The precise smooth-periodic-embedding input extracted from an orbit.
Smoothness and immersion are asserted on the real lift, while embeddedness is
asserted on the quotient circle. -/
structure SmoothPeriodicOrbitData (O : V.OrbitIndex) where
  lift : ℝ → E
  circle : AddCircle (1 : ℝ) → E
  smooth_lift : ContDiff ℝ ∞ lift
  periodic_lift : Function.Periodic lift 1
  circle_coe : ∀ u : ℝ, circle (u : AddCircle (1 : ℝ)) = lift u
  deriv_ne_zero : ∀ u : ℝ, deriv lift u ≠ 0
  isEmbedding_circle : Topology.IsEmbedding circle
  range_circle : Set.range circle = (O : Set E)


-- @@ L171-182 verbatim
/-- Every intrinsic orbit supplies the full smooth periodic embedded-circle
datum required by the codimension-at-least-three unknotting step. -/
def smoothPeriodicOrbitData (O : V.OrbitIndex) :
    SmoothPeriodicOrbitData V O where
  lift := V.intrinsicOrbitLift O
  circle := V.intrinsicOrbitEmbedding O
  smooth_lift := V.contDiff_intrinsicOrbitLift O
  periodic_lift := V.periodic_intrinsicOrbitLift O
  circle_coe := V.intrinsicOrbitEmbedding_coe O
  deriv_ne_zero := V.deriv_intrinsicOrbitLift_ne_zero O
  isEmbedding_circle := V.isEmbedding_intrinsicOrbitEmbedding O
  range_circle := V.range_intrinsicOrbitEmbedding O


-- @@ L184-184 verbatim
end TamedField

-- @@ L185-185 verbatim
end Submission
