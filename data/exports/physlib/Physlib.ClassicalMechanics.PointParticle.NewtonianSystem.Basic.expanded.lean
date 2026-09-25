/-
Copyright (c) 2026 Raunak Chhatwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raunak Chhatwal
-/
module

public import Physlib.ClassicalMechanics.Force
public import Physlib.ClassicalMechanics.PointParticle.Basic

-- @@ L10-36 verbatim
/-!
# Newtonian point-particle systems

This module defines `NewtonianSystem`, consisting of an inertial reference frame, a finite
collection of point particles, and the internal and external forces acting on
them. Particles carry masses and positions over time; forces carry vector values
over time and identify the particles they act on.

Newton's second law requires the net force on each particle to equal its mass
times its acceleration. Newton's third law requires the multiset of internal
forces to be invariant under equal-and-opposite reversal.

Particles and forces are stored in multisets. For example, if two identical springs
connect the same pair of particles, the net force on either particle must count
both spring forces, even though they are equal.

Many classical systems are specified by constraints rather than explicit position
and force functions. Such models can be formalized as conditions on `NewtonianSystem`
values: which particles and forces are present, geometric constraints such as
fixed distances, and restrictions on the forces such as centrality.

Results can be proved for arbitrary systems satisfying these conditions. An
existence proof establishes that a satisfying system exists for given parameters
and initial conditions; choice can then be used to select one. Explicit formulas
for the positions and forces are not required to state the conditions or to
reason about systems satisfying them.
-/


-- @@ L38-38 verbatim
@[expose] public noncomputable section


-- @@ L40-40 verbatim
open scoped BigOperators Classical


-- @@ L42-42 verbatim
namespace ClassicalMechanics.PointParticle


-- @@ L44-44 verbatim
open ReferenceFrame


-- @@ L46-46 verbatim
variable {d : ℕ}


-- @@ L48-50 verbatim
/-!
## A. Systems
-/


-- @@ L52-67 verbatim
/-- A finite system of point particles satisfying Newton's laws. -/
structure NewtonianSystem (d : ℕ) where
  /-- The system's reference frame. -/
  frame : ReferenceFrame d
  [isInertial : Fact frame.IsInertial]
  /-- The particles in the system. -/
  particles : Multiset frame.Particle
  /-- Forces between particles in the system. -/
  internalForces : Multiset (frame.InternalForce particles)
  /-- Forces on the system from external sources. -/
  externalForces : Multiset (frame.Force particles)
  /-- Newton's second law: the net force on each particle equals its mass times its acceleration. -/
  newton_second_law : ∀ particle : particles,
    netForce particle internalForces externalForces = particle.1.mass • particle.1.acceleration
  /-- Newton's third law: internal forces and their reverses occur with equal multiplicities. -/
  newton_third_law : internalForces.map .reverse = internalForces


-- @@ L69-69 verbatim
namespace NewtonianSystem


-- @@ L71-71 verbatim
variable (system : NewtonianSystem d)


-- @@ L73-74 verbatim
instance : Fact system.frame.IsInertial :=
  system.isInertial


-- @@ L76-78 verbatim
/-!
## B. System particles
-/


-- @@ L80-81 verbatim
/-- Vectors in the system's frame. -/
abbrev Vector := system.frame.Vector


-- @@ L83-84 verbatim
/-- A particle in `system`. -/
abbrev Particle : Type := system.particles


-- @@ L86-86 verbatim
namespace Particle


-- @@ L88-88 verbatim
variable {system : NewtonianSystem d} (particle : system.Particle) (t : ℝ)


-- @@ L90-91 expanded
/-- The particle's mass. -/
def mass : { x : ℝ // 0 < x } :=
  particle.1.mass


-- @@ L93-94 verbatim
/-- The particle's position at `t`. -/
def pos : system.Vector := particle.1.pos t


-- @@ L96-97 verbatim
/-- The particle's velocity at `t`. -/
def velocity : system.Vector := particle.1.velocity t


-- @@ L99-100 verbatim
/-- The particle's acceleration at `t`. -/
def acceleration : system.Vector := particle.1.acceleration t


-- @@ L102-103 verbatim
/-- The particle's momentum at `t`. -/
def momentum : system.Vector := particle.mass • particle.velocity t


-- @@ L105-106 verbatim
/-- The particle's kinetic energy at `t`. -/
def kineticEnergy : ℝ := particle.mass * ‖particle.velocity t‖ ^ 2 / 2


-- @@ L108-108 verbatim
end Particle


-- @@ L110-112 verbatim
/-!
## C. System forces
-/


-- @@ L114-116 verbatim
/-- A force in `system`. -/
abbrev Force : Type :=
  system.internalForces ⊕ system.externalForces


-- @@ L118-118 verbatim
namespace Force


-- @@ L120-120 verbatim
variable {system : NewtonianSystem d} (force : system.Force)


-- @@ L122-124 verbatim
/-- The underlying force. -/
@[coe] def inner : system.frame.Force system.Particle :=
  match force with | .inl force => force | .inr force => force


-- @@ L126-126 verbatim
instance : Coe system.Force (system.frame.Force system.Particle) := Coe.mk inner


-- @@ L128-129 verbatim
/-- The force at `t`. -/
def value (t : ℝ) : system.Vector := force.inner.value t


-- @@ L131-132 verbatim
instance : CoeFun system.Force (fun _ => ℝ → system.Vector) where
  coe := value


-- @@ L134-135 verbatim
/-- The force's target. -/
def target : system.Particle := force.inner.target


-- @@ L137-138 verbatim
/-- Whether `force` is internal. -/
def Internal : Prop := force.isLeft


-- @@ L140-141 verbatim
/-- Whether `force` is external. -/
def External : Prop := force.isRight


-- @@ L143-143 verbatim
end Force


-- @@ L145-146 verbatim
/-- An internal force in `system`. -/
abbrev InternalForce : Type := system.internalForces


-- @@ L148-148 verbatim
namespace InternalForce


-- @@ L150-150 verbatim
variable {system : NewtonianSystem d} (force : system.InternalForce)


-- @@ L152-153 verbatim
/-- View an internal force as a system force. -/
instance : Coe system.InternalForce system.Force := Coe.mk .inl


-- @@ L155-156 verbatim
/-- The force at `t`. -/
def value (t : ℝ) : system.Vector := force.1.value t


-- @@ L158-159 verbatim
/-- The force's target. -/
def target : system.Particle := force.1.target


-- @@ L161-162 verbatim
/-- The force's source. -/
def source : system.Particle := force.1.source


-- @@ L164-171 verbatim
/-- A force and its reverse have the same multiplicity. -/
lemma reverse_count_eq :
    system.internalForces.count force.1.reverse = system.internalForces.count force.1 := by
  rw [← congrArg (Multiset.count force.1.reverse) system.newton_third_law]
  refine Multiset.count_map_eq_count' _ _ (Function.Involutive.injective ?_) _
  intro internalForce
  rcases internalForce with ⟨⟨value, target⟩, source, source_ne_target⟩
  simp [ReferenceFrame.InternalForce.reverse]


-- @@ L173-175 verbatim
/-- The reverse force. -/
def reverse : system.InternalForce :=
  ⟨force.1.reverse, (finCongr force.reverse_count_eq).symm force.2⟩


-- @@ L177-179 verbatim
/-- Whether the force lies along the line joining its source and target. -/
def Central : Prop :=
  ∀ t, ∃ c : ℝ, force.value t = c • (force.target.pos t - force.source.pos t)


-- @@ L181-181 verbatim
end InternalForce


-- @@ L183-185 verbatim
/-!
## D. Aggregate quantities
-/


-- @@ L187-187 verbatim
variable (t : ℝ)


-- @@ L189-191 verbatim
/-- Total mass. -/
def mass : ℝ :=
  ∑ particle : system.Particle, particle.mass


-- @@ L193-195 verbatim
/-- Total momentum at `t`. -/
def momentum : system.Vector :=
  ∑ particle : system.Particle, particle.momentum t


-- @@ L197-199 verbatim
/-- Net external force at `t`. -/
def netExternalForce : system.Vector :=
  ∑ force : system.Force with force.External, force t


-- @@ L201-203 verbatim
/-- Total kinetic energy at `t`. -/
def kineticEnergy : ℝ :=
  ∑ particle : system.Particle, particle.kineticEnergy t


-- @@ L205-205 verbatim
end ClassicalMechanics.PointParticle.NewtonianSystem
