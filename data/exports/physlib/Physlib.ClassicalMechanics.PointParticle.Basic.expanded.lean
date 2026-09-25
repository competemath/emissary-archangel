/-
Copyright (c) 2026 Raunak Chhatwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raunak Chhatwal
-/
module

public import Physlib.SpaceAndTime.ReferenceFrame

-- @@ L9-33 verbatim
/-!
# Point particles

This module defines point particles together with their motion relative to a
reference frame. A `Particle` has a constant positive mass and a position over
time. Velocity and acceleration are derived from that position rather than stored
as independent data.

The trajectory is part of the particle's description, but need not be given by an
explicit solution formula. Particle values can be considered subject to conditions
on their positions and on the forces acting on them. A particular mechanical model
can therefore be specified by constraints on particles, with the existence of
particles satisfying those constraints established separately.

A particle by itself carries no equation of motion or assumption about which
forces act on it. It is a constituent from which systems can be assembled, rather
than a specification of an isolated or unconstrained one-particle system. Newton's
laws are imposed when particles and forces are assembled in
`ClassicalMechanics.PointParticle.NewtonianSystem`.

Position and its first time derivative are required to be differentiable when the
frame is inertial. This ensures that the velocity and acceleration used in
Newtonian systems are genuine derivatives. The trajectories in this definition
are defined for all real-valued time coordinates relative to the frame's time origin.
-/


-- @@ L35-35 verbatim
@[expose] public noncomputable section


-- @@ L37-37 verbatim
open scoped BigOperators Classical


-- @@ L39-39 verbatim
namespace ClassicalMechanics.ReferenceFrame


-- @@ L41-41 verbatim
variable {d : ℕ} {frame : ReferenceFrame d}


-- @@ L43-44 verbatim
/-- Positive real numbers. -/
notation "ℝ+" => {x : ℝ // 0 < x}


-- @@ L46-53 expanded
/-- A point particle in `frame`. -/
structure Particle (frame : ReferenceFrame d) where
  /-- The particle's mass. -/
  mass : { x : ℝ // 0 < x }
  /-- The particle's position in frame coordinates. -/
  pos : ℝ → frame.Vector
  pos_twice_differentiable : frame.IsInertial → Differentiable ℝ pos ∧ Differentiable ℝ (deriv pos)


-- @@ L55-55 verbatim
namespace Particle


-- @@ L57-57 verbatim
variable (particle : frame.Particle)


-- @@ L59-61 verbatim
/-- Position is differentiable in an inertial frame. -/
instance [h : Fact frame.IsInertial] : Fact (Differentiable ℝ particle.pos) :=
  ⟨particle.pos_twice_differentiable h.out |>.left⟩


-- @@ L63-65 verbatim
/-- The particle's velocity. -/
def velocity [_h : Fact (Differentiable ℝ particle.pos)] : ℝ → frame.Vector :=
  deriv particle.pos


-- @@ L67-69 verbatim
/-- Velocity is differentiable in an inertial frame. -/
instance [h : Fact frame.IsInertial] : Fact (Differentiable ℝ particle.velocity) :=
  ⟨particle.pos_twice_differentiable h.out |>.right⟩


-- @@ L71-74 verbatim
/-- The particle's acceleration. -/
def acceleration [Fact (Differentiable ℝ particle.pos)]
    [_h : Fact (Differentiable ℝ particle.velocity)] : ℝ → frame.Vector :=
  deriv particle.velocity


-- @@ L76-78 verbatim
/-- The particle's position in affine space at frame time coordinate `t`. -/
def pointInSpace (t : ℝ) : Space d :=
  Vector.dispEquiv t (particle.pos t) +ᵥ frame.origin (frame.timeEquiv t)


-- @@ L80-80 verbatim
end ClassicalMechanics.ReferenceFrame.Particle
