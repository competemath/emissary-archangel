/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.SpaceAndTime.Space.SmoothFunctions
public import Physlib.Meta.Informal.Basic
public import Mathlib.Geometry.Manifold.Algebra.SmoothFunctions

-- @@ L11-31 verbatim
/-!

# Rigid bodies

A rigid body is one where the distance and relative orientation between particles does not change.
In other words, the body remains undeformed.

In this module we will define the basic properties of a rigid body, including
- mass
- center of mass
- inertia tensor
- inertia tensor about an arbitrary point

The moments of the last are taken about the given point rather than about the origin of the
reference frame. The parallel-axis theorem expresses it in terms of the inertia tensor about the
centre of mass.

## References

* Landau and Lifshitz, Mechanics, page 100, Section 32. [ref: landau_mechanics]
-/


-- @@ L33-33 verbatim
@[expose] public section


-- @@ L35-35 verbatim
open Manifold InnerProductSpace

-- @@ L36-36 verbatim
open Space (cmap cmap_apply)


-- @@ L38-40 verbatim
TODO "The definition of a rigid body is currently defined via linear maps
  from the space of smooth functions to ℝ. When possible, it should be change
  to *continuous* linear maps. "


-- @@ L42-45 verbatim
/-- A Rigid body defined by its mass distribution. -/
structure RigidBody (d : ℕ) where
  /-- The mass distribution of the rigid body. -/
  ρ : C^⊤⟮𝓘(ℝ, Space d), Space d; 𝓘(ℝ, ℝ), ℝ⟯ →ₗ[ℝ] ℝ


-- @@ L47-47 verbatim
namespace RigidBody


-- @@ L49-50 verbatim
/-- The total mass of the rigid body. -/
noncomputable def mass {d : ℕ} (R : RigidBody d) : ℝ := R.ρ ⟨fun _ => 1, contMDiff_const⟩


-- @@ L52-55 verbatim
/-- The mass distribution applied to the constant function `1` is the total mass. -/
@[simp]
lemma rho_one {d : ℕ} (R : RigidBody d) :
    R.ρ (1 : C^⊤⟮𝓘(ℝ, Space d), Space d; 𝓘(ℝ, ℝ), ℝ⟯) = R.mass := rfl


-- @@ L57-59 verbatim
/-- The center of mass of the rigid body. -/
noncomputable def centerOfMass {d : ℕ} (R : RigidBody d) : Space d := ⟨fun i =>
  (1 / R.mass) • R.ρ ⟨fun x => x i, ContDiff.contMDiff <| by fun_prop⟩⟩


-- @@ L61-65 verbatim
/-- The inertia tensor of the rigid body. -/
noncomputable def inertiaTensor {d : ℕ} (R : RigidBody d) :
    Matrix (Fin d) (Fin d) ℝ := fun i j =>
  R.ρ ⟨fun x => (if i = j then 1 else 0) * ∑ k : Fin d, (x k)^2 - x i * x j,
    ContDiff.contMDiff <| by fun_prop⟩


-- @@ L67-69 verbatim
lemma inertiaTensor_symmetric {d : ℕ} (R : RigidBody d) (i j : Fin d) :
    R.inertiaTensor i j = R.inertiaTensor j i := by
  simp only [inertiaTensor, eq_comm, mul_comm]


-- @@ L71-85 verbatim
/-- The first moment of the mass distribution about its own centre of mass vanishes:
for nonzero mass, `ρ` of the centred `j`-th coordinate function is zero. -/
lemma rho_coord_sub_centerOfMass {d : ℕ} (R : RigidBody d) (h : R.mass ≠ 0) (j : Fin d) :
    R.ρ (cmap (fun y => y j - R.centerOfMass j) (by fun_prop)) = 0 := by
  have hsplit : cmap (fun y => y j - R.centerOfMass j) (by fun_prop)
        = cmap (fun y => y j) (by fun_prop)
          - R.centerOfMass j • (1 : C^⊤⟮𝓘(ℝ, Space d), Space d; 𝓘(ℝ, ℝ), ℝ⟯) := by
    ext y
    simp only [cmap_apply, ContMDiffMap.coe_sub, ContMDiffMap.coe_smul,
      ContMDiffMap.coe_one, Pi.sub_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one]
  have hcoord : R.ρ (cmap (fun y => y j) (by fun_prop)) = R.mass * R.centerOfMass j := by
    have hc : R.centerOfMass j = (1 / R.mass) • R.ρ (cmap (fun y => y j) (by fun_prop)) := rfl
    rw [hc, smul_eq_mul, one_div, ← mul_assoc, mul_inv_cancel₀ h, one_mul]
  rw [hsplit, map_sub, map_smul, R.rho_one, hcoord, smul_eq_mul]
  ring


-- @@ L87-93 verbatim
/-- The inertia tensor of the rigid body about the point `p`, that is with the moments taken
about `p` rather than about the origin of the reference frame. Taking `p` to be the origin
recovers `RigidBody.inertiaTensor`, see `RigidBody.inertiaTensorAbout_zero`. -/
noncomputable def inertiaTensorAbout {d : ℕ} (R : RigidBody d) (p : Space d) :
    Matrix (Fin d) (Fin d) ℝ := fun i j =>
  R.ρ (cmap (fun y => (if i = j then 1 else 0) * ∑ k : Fin d, (y k - p k) ^ 2
    - (y i - p i) * (y j - p j)) (by fun_prop))


-- @@ L95-98 verbatim
/-- The `(i, j)` entry of the inertia tensor about `p` as a moment of the mass distribution. -/
lemma inertiaTensorAbout_apply {d : ℕ} (R : RigidBody d) (p : Space d) (i j : Fin d) :
    R.inertiaTensorAbout p i j = R.ρ (cmap (fun y => (if i = j then 1 else 0) *
      ∑ k : Fin d, (y k - p k) ^ 2 - (y i - p i) * (y j - p j)) (by fun_prop)) := rfl


-- @@ L100-105 verbatim
/-- The inertia tensor about the origin is the inertia tensor. -/
@[simp]
lemma inertiaTensorAbout_zero {d : ℕ} (R : RigidBody d) :
    R.inertiaTensorAbout 0 = R.inertiaTensor := by
  ext i j
  simp [inertiaTensorAbout, inertiaTensor, cmap]


-- @@ L107-110 verbatim
/-- The inertia tensor about any point is symmetric. -/
lemma inertiaTensorAbout_symmetric {d : ℕ} (R : RigidBody d) (p : Space d) (i j : Fin d) :
    R.inertiaTensorAbout p i j = R.inertiaTensorAbout p j i := by
  simp only [inertiaTensorAbout, eq_comm, mul_comm]


-- @@ L112-142 verbatim
/-- The integrand of the inertia tensor about `p` splits into the integrand about the centre of
mass, terms linear in the centred coordinates `y − c`, and a constant built from the
displacement `c − p`. -/
lemma inertiaTensorAbout_integrand_split {d : ℕ} (R : RigidBody d) (p : Space d) (i j : Fin d) :
    cmap (fun y => (if i = j then 1 else 0) * ∑ k : Fin d, (y k - p k) ^ 2
        - (y i - p i) * (y j - p j)) (by fun_prop)
      = cmap (fun y => (if i = j then 1 else 0) * ∑ k : Fin d, (y k - R.centerOfMass k) ^ 2
            - (y i - R.centerOfMass i) * (y j - R.centerOfMass j)) (by fun_prop)
        + ∑ k : Fin d, (2 * (if i = j then 1 else 0) * (R.centerOfMass k - p k)) •
            cmap (fun y => y k - R.centerOfMass k) (by fun_prop)
        - (R.centerOfMass j - p j) • cmap (fun y => y i - R.centerOfMass i) (by fun_prop)
        - (R.centerOfMass i - p i) • cmap (fun y => y j - R.centerOfMass j) (by fun_prop)
        + ((if i = j then 1 else 0) * ∑ k : Fin d, (R.centerOfMass k - p k) ^ 2
            - (R.centerOfMass i - p i) * (R.centerOfMass j - p j)) •
          (1 : C^⊤⟮𝓘(ℝ, Space d), Space d; 𝓘(ℝ, ℝ), ℝ⟯) := by
  ext y
  simp only [cmap_apply, ContMDiffMap.coe_add, ContMDiffMap.coe_sub, ContMDiffMap.coe_smul,
    ContMDiffMap.coe_one, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.one_apply]
  rw [← ContMDiffMap.coeFnAddMonoidHom_apply, map_sum, Finset.sum_apply]
  simp only [ContMDiffMap.coeFnAddMonoidHom_apply, ContMDiffMap.coe_smul, Pi.smul_apply,
    cmap_apply, smul_eq_mul]
  have hlin (a : ℝ) : ∑ k : Fin d, a * (R.centerOfMass k - p k) * (y k - R.centerOfMass k)
      = a * ∑ k : Fin d, (R.centerOfMass k - p k) * (y k - R.centerOfMass k) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hsum : ∑ k : Fin d, (y k - p k) ^ 2
      = ∑ k : Fin d, ((y k - R.centerOfMass k) ^ 2
        + 2 * (R.centerOfMass k - p k) * (y k - R.centerOfMass k)
        + (R.centerOfMass k - p k) ^ 2) := Finset.sum_congr rfl fun k _ => by ring
  rw [hsum, Finset.sum_add_distrib, Finset.sum_add_distrib, hlin, hlin]
  ring


-- @@ L144-158 verbatim
/-- **The parallel-axis theorem**: the inertia tensor about a point `p` is the inertia tensor
about the centre of mass `c` plus the inertia tensor about `p` of a point particle carrying the
total mass of the body and sitting at `c`, that is `M (|c − p|² 1 − (c − p) ⊗ (c − p))`. -/
theorem inertiaTensorAbout_eq_centerOfMass_add_pointMass {d : ℕ} (R : RigidBody d) (h : R.mass ≠ 0)
    (p : Space d) :
    R.inertiaTensorAbout p = R.inertiaTensorAbout R.centerOfMass
      + R.mass • (⟪R.centerOfMass - p, R.centerOfMass - p⟫_ℝ • (1 : Matrix (Fin d) (Fin d) ℝ)
        - Matrix.vecMulVec ⇑(R.centerOfMass - p) ⇑(R.centerOfMass - p)) := by
  ext i j
  rw [inertiaTensorAbout_apply, inertiaTensorAbout_integrand_split R p i j, map_add, map_sub,
    map_sub, map_add, map_sum, ← inertiaTensorAbout_apply]
  simp only [map_smul, R.rho_coord_sub_centerOfMass h, smul_eq_mul, mul_zero,
    Finset.sum_const_zero, R.rho_one, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply,
    Matrix.one_apply, Matrix.vecMulVec_apply, Space.inner_eq_sum, Space.sub_apply, pow_two]
  ring


-- @@ L160-166 verbatim
/-- The inertia tensor about the origin is the inertia tensor about the centre of mass `c` plus
`M (|c|² 1 − c ⊗ c)`. -/
lemma inertiaTensor_eq_centerOfMass_add_pointMass {d : ℕ} (R : RigidBody d) (h : R.mass ≠ 0) :
    R.inertiaTensor = R.inertiaTensorAbout R.centerOfMass
      + R.mass • (⟪R.centerOfMass, R.centerOfMass⟫_ℝ • (1 : Matrix (Fin d) (Fin d) ℝ)
        - Matrix.vecMulVec ⇑R.centerOfMass ⇑R.centerOfMass) := by
  simpa using R.inertiaTensorAbout_eq_centerOfMass_add_pointMass h 0


-- @@ L168-172 expanded
/-- One can describe the motion of rigid body with a fixed (inertial) coordinate system (X,Y,Z)
    and a moving system (x₁,x₂,x₃) rigidly attached to the body. -/
def coordinate_system : InformalDefinition
    where
  tag := "LL31.3"
  deps := [``RigidBody]


-- @@ L174-179 expanded
/-- A rigid body in three-dimensional space has six degrees of freedom:
    three translational (for the position of its centre of mass) and three
    rotational (for its orientation). -/
def rigid_body_dof : InformalLemma where
  tag := "LL32-6DF"
  deps := [``RigidBody]


-- @@ L181-186 expanded
/-- The velocity v of any point in a rigid body is
    v = V + Ω × r,
    where V is the velocity of the origin of the moving system and Ω is the angular velocity. -/
def velocity_decomposition : InformalLemma
    where
  tag := "LL31.L3"
  deps := [``RigidBody]


-- @@ L188-192 expanded
/-- The angular velocity of rotation of a rigid body from a system of coordinates fixed in the
    body is independent of the system chosen. -/
def angular_velocity_is_well_defined : InformalLemma
    where
  tag := "LL32-AM"
  deps := [``RigidBody]


-- @@ L194-199 expanded
/-- The motion of a rigid body can be decomposed into a translation of some reference point plus a
    rotation about that point. There exists a time-dependent vector V(t) and angular velocity ω(t)
    such that v(r) = V + ω × r, where r is measured from the reference point. -/
def decomposition_of_motion : InformalLemma
    where
  tag := "LL32-DM"
  deps := [``RigidBody]


-- @@ L201-205 expanded
/-- The centre of mass of a rigid body moves as if all mass were concentrated at that
    point and acted upon by the resultant external force: M a_CM = ∑ F_ext. -/
def center_of_mass_point_moves_as_particle : InformalLemma
    where
  tag := "LL32-CM"
  deps := [``RigidBody]


-- @@ L207-211 expanded
/-- The total angular momentum about a point O is L = ∫ r × v dm. With v = V + ω × r about the
    centre of mass, L = R × (M V) + I_CM ω, where R is the centre of mass position. -/
def angular_momentum_about_point : InformalLemma
    where
  tag := "LL32-L"
  deps := [``RigidBody]


-- @@ L213-218 expanded
/-- In the inertial frame, the translational equation of motion of a rigid body is given by
    dP/dt = F, where `P` is the total linear momentum and `F` is the total external force acting
    on the body. -/
def translational_equation_inertial : InformalLemma
    where
  tag := "LL32-TR"
  deps := [``RigidBody]


-- @@ L220-225 expanded
/-- In the inertial frame, the rotational equation of motion of a rigid body about the center of
    mass is given by dM/dt = K, where `M` is the total angular momentum and `K` is the total
    external torque. -/
def rotational_equation_inertial : InformalLemma
    where
  tag := "LL32-ROT"
  deps := [``RigidBody]


-- @@ L227-232 expanded
/-- The kinetic energy decomposes into translational and rotational parts:
    T = (1/2) M |V|² + (1/2) ω ⋅ I_CM ω.
    Here V is the velocity of the centre of mass and I_CM is the inertia tensor about that point. -/
def kinetic_energy_decomposition : InformalLemma
    where
  tag := "LL32-TK"
  deps := [``RigidBody]


-- @@ L234-238 expanded
/-- Because the inertia tensor is real symmetric, there exists an orthonormal basis of principal
    axes in which it is diagonal. The corresponding directions are the principal axes of inertia. -/
def principal_axes_of_inertia : InformalDefinition
    where
  tag := "LL32-PAE"
  deps := [``RigidBody]


-- @@ L240-243 expanded
/-- None of the principal moments of inertia can exceed the sum of other two. -/
def principal_axes_of_inertia_bound : InformalLemma
    where
  tag := "LL32-PAEB"
  deps := [``RigidBody]


-- @@ L245-248 expanded
/-- An asymmetrical top is when none of the principal moments of inertia are equal. -/
def asymmetrical_top : InformalDefinition
    where
  tag := "LL32-AST"
  deps := [``RigidBody]


-- @@ L250-253 expanded
/-- A symmetrical top is when only two of the principal moments of inertia are equal. -/
def symmetrical_top : InformalDefinition
    where
  tag := "LL32-ST"
  deps := [``RigidBody]


-- @@ L255-258 expanded
/-- A spherical top is when all three of the principal moments of inertia are equal. -/
def spherical_top : InformalDefinition
    where
  tag := "LL32-SPT"
  deps := [``RigidBody]


-- @@ L260-265 expanded
/-- A rotating body-fixed frame is a coordinate system attached to the body
    that rotates with the body relative to an inertial (fixed) frame. The frame
    is characterised by its angular velocity vector Ω(t). -/
def RotatingFrame : InformalDefinition
    where
  tag := "LL32-RF"
  deps := [``RigidBody]


-- @@ L267-272 expanded
/-- The time derivative in the rotating frame, d'/dt, is the derivative
    of the components of a vector with respect to time when expressed in the
    rotating (body-fixed) frame. -/
def rotating_frame_derivative : InformalDefinition
    where
  tag := "LL32-dprime"
  deps := [``RigidBody]


-- @@ L274-280 expanded
/-- For any vector field A(t), its inertial-frame time derivative equals the rotating-frame
    derivative plus the contribution from the frame rotation:
      (dA/dt)_inertial = (dA/dt)_rotating + Ω × A.
    Here Ω is the angular velocity of the rotating frame. -/
def transport_law_inertial_rotating : InformalLemma
    where
  tag := "LL36-Ltransport"
  deps := [``RigidBody]


-- @@ L282-287 expanded
/-- For linear momentum, the relation between inertial and rotating derivatives is
      (dP/dt)_inertial = d'P/dt + Ω × P.
    So, d'P/dt + Ω × P = F which is the linear-momentum equation in the rotating frame. -/
def transport_law_for_momentum : InformalLemma
    where
  tag := "LL32-transportP"
  deps := [``RigidBody]


-- @@ L289-296 expanded
/-- For angular momentum, the relation between inertial and rotating derivatives is
      (dM/dt)_inertial = d'M/dt + Ω × M,
    and with the rotational form of Newton's law M_tot = (dM/dt)_inertial this yields
      d'M/dt + Ω × M = K,
    the angular-momentum equation in the rotating frame. -/
def transport_law_for_angular_momentum : InformalLemma
    where
  tag := "LL32-transportM"
  deps := [``RigidBody]


-- @@ L298-304 expanded
/-- When motion is described in body-fixed principal axes (I₁, I₂, I₃ diagonal), the equations of
    rotational motion (Euler’s equations) are:
    I₁ dω₁/dt + (I₃ − I₂) ω₂ ω₃ = M₁, with cyclic permutations.
    M is the external torque about the centre of mass. -/
def euler_equations : InformalLemma where
  tag := "LL32-EQ"
  deps := [``RigidBody]


-- @@ L306-310 expanded
/-- A rigid body can perform steady (uniform) rotation about any principal axis if the torque about
    that axis vanishes. Stability depends on the ordering of principal moments. -/
def steady_rotation_conditions : InformalLemma
    where
  tag := "LL32-SR"
  deps := [``RigidBody]


-- @@ L312-316 expanded
/-- Rotations about the largest and smallest principal axes are stable under small perturbations;
    rotation about the intermediate axis is unstable (tennis-racket effect). -/
def intermediate_axis_instability : InformalLemma
    where
  tag := "LL32-IAI"
  deps := [``RigidBody]


-- @@ L318-323 expanded
/-- If a rigid body is confined to planar motion, its dynamics reduce to a two-dimensional problem:
    the inertia reduces to a scalar moment and rotation is described
    by a single angular velocity. -/
def reduction_to_two_body : InformalLemma
    where
  tag := "LL32-RTB"
  deps := [``RigidBody]


-- @@ L325-330 expanded
/-- The power delivered to a rigid body by forces is P = ∑ Fᵢ ⋅ vᵢ = F_tot ⋅ V + M ⋅ ω, where F_tot
    is total force, V the reference point velocity, and M the torque. Translational and rotational
    contributions separate. -/
def rigid_body_work_and_power : InformalLemma
    where
  tag := "LL32-WP"
  deps := [``RigidBody]


-- @@ L332-337 expanded
/-- Small oscillations about a stable equilibrium orientation are governed by linearised equations
    obtained by expanding energy to second order in angular displacements. Normal modes and
    frequencies depend on inertia and restoring torques. -/
def small_oscillations_about_equilibrium : InformalLemma
    where
  tag := "LL32-SO"
  deps := [``RigidBody]


-- @@ L339-339 verbatim
end RigidBody
