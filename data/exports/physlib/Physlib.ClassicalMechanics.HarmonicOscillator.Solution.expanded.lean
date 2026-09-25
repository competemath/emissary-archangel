/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaneal Sajan, Joseph Tooby-Smith, Lode Vermeulen
-/
module

public import Physlib.ClassicalMechanics.HarmonicOscillator.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg

-- @@ L10-69 verbatim
/-!

# Solutions to the classical harmonic oscillator

## i. Overview

In this module we define the solutions to the classical harmonic oscillator,
prove that they satisfy the equation of motion, and prove some properties of the solutions.

## ii. Key results

- `InitialConditions` is a structure for the initial conditions for the harmonic oscillator.
- `trajectories` is the trajectories to the harmonic oscillator for given initial conditions.
- `trajectories_equationOfMotion` proves that the solution satisfies the equation of motion.

## iii. Table of contents

- A. The initial conditions
  - A.1. Definition of the initial conditions
  - A.2. Relation to other types of initial conditions
    - A.2.1. Initial conditions at arbitrary time
    - A.2.2. Initial conditions from two positions at different times
    - A.2.3. Initial conditions from two velocities at different times
  - A.3. The zero initial conditions
    - A.3.1. Simple results for the zero initial conditions
- B. Trajectories associated with the initial conditions
  - B.1. The trajectory associated with the initial conditions
    - B.1.1. Definitional equality for the trajectory
  - B.2. The trajectory for zero initial conditions
  - B.3. Smoothness of the trajectories
  - B.4. Velocity of the trajectories
  - B.5. Acceleration of the trajectories
  - B.6. The initial conditions of the trajectories
- C. Trajectories and Equation of motion
  - C.1. Uniqueness of the solutions
- D. The energy of the trajectories
  - D.1. Correctness of InitialConditionsAtTime conversion
  - D.2. Correctness of InitialConditionsFromTwoPositions conversion
  - D.3. Correctness of InitialConditionsFromTwoVelocities conversion
- E. Amplitude–phase parametrization
  - E.1. The amplitude–phase initial conditions
  - E.2. Conversion to standard initial conditions
  - E.3. The trajectory in normal form
  - E.4. Recovering the amplitude and phase
- F. Special conditions of the trajectory
  - F.1. Normal form for standard initial conditions
  - F.2. Times at which the velocity is zero
  - F.3. The position when the velocity is zero
  - F.4. Times at which the trajectory passes through zero
- G. Periodicity and recurrence
  - G.1. The period
  - G.2. Periodicity of the trajectory
  - G.3. Return to the initial state

## iv. References

References for the classical harmonic oscillator include:

* Landau & Lifshitz, Mechanics, page 58, section 21. [ref: landau_mechanics]
-/


-- @@ L71-78 verbatim
TODO "Split this file into smaller modules, keeping `Solution.lean` as an umbrella import.
The intended organization is:
- `Solution.Basic` for trajectory construction and equation-of-motion facts;
- `Solution.Energy` for energy-related lemmas;
- `Solution.InitialData` for alternative initial-condition parametrizations;
- `Solution.AmplitudePhase` for the amplitude-phase normal form;
- `Solution.SpecialTimes` for velocity-zero times, turning points, and zero crossings;
- `Solution.Periodicity` for period and recurrence facts."


-- @@ L80-80 verbatim
@[expose] public section


-- @@ L82-82 verbatim
namespace ClassicalMechanics

-- @@ L83-83 verbatim
open Real Time ContDiff


-- @@ L85-85 verbatim
namespace HarmonicOscillator


-- @@ L87-87 verbatim
variable (S : HarmonicOscillator)


-- @@ L89-97 verbatim
/-!

## A. The initial conditions

We define the type of initial conditions for the harmonic oscillator.
The initial conditions are currently defined as an initial position and an initial velocity,
that is the values of the solution and its time derivative at time `0`.

-/

-- @@ L98-104 verbatim
/-!

### A.1. Definition of the initial conditions

We start by defining the type of initial conditions for the harmonic oscillator.

-/


-- @@ L106-116 verbatim
/-- The initial conditions for the harmonic oscillator specified by an initial position,
  and an initial velocity.

The `@[ext]` attribute provides an extensionality lemma for `InitialConditions`.
That is, a lemma which states that two initial conditions are equal if their
initial positions and initial velocities are equal. -/
@[ext] structure InitialConditions where
  /-- The initial position of the harmonic oscillator. -/
  x₀ : EuclideanSpace ℝ (Fin 1)
  /-- The initial velocity of the harmonic oscillator. -/
  v₀ : EuclideanSpace ℝ (Fin 1)


-- @@ L118-144 verbatim
/-!

### A.2. Relation to other types of initial conditions

We relate the initial condition given by an initial position and an initial velocity
to other specifications of initial conditions.

In this section, we implement alternative ways to specify initial conditions for the harmonic
oscillator. The standard `InitialConditions` type specifies position and velocity at time `t=0`,
but in practice it is often useful to specify initial conditions at other times or in other forms.

Currently implemented:
- **Initial conditions at arbitrary time**: Specify position and velocity at any time `t₀`,
  not necessarily at `t=0`.
  This is useful for problems where the natural reference time is not zero.
- **Initial conditions from two positions at different times**: Specify the position at two
  distinct times `t₁` and `t₂` that satisfy the non-degeneracy condition.
- **Initial conditions from two velocities at different times**: Specify the velocity at two
  distinct times `t₁` and `t₂` that satisfy the non-degeneracy condition.
- **Amplitude–phase parametrization**: Specify the solution as a single shifted cosine
  `x(t) = A cos (ω t - φ)` with amplitude `A` and phase `φ`.

All alternative forms can be converted to the standard `InitialConditions` type via conversion
functions, and we prove that the converted initial conditions produce trajectories that satisfy
the original specifications.

-/


-- @@ L146-163 verbatim
/-!

#### A.2.1. Initial conditions at arbitrary time

We define a type for initial conditions specified at an arbitrary time `t₀`, rather than at `t=0`.
This is useful when the natural reference point for a problem is not at time zero.

The conversion to the standard `InitialConditions` works by "running the trajectory backward in
time" from `t₀` to `0`. Given that we know `x(t₀)` and `v(t₀)`, we use the harmonic oscillator
solution formula with time-reversal to determine what `x(0)` and `v(0)` must have been.

Mathematically, if `x(t) = cos(ωt)·x₀ + (sin(ωt)/ω)·v₀`, then setting `t = t₀`:
  `x(t₀) = cos(ωt₀)·x₀ + (sin(ωt₀)/ω)·v₀`
  `v(t₀) = -ω·sin(ωt₀)·x₀ + cos(ωt₀)·v₀`

Solving this linear system for `x₀` and `v₀` gives the formulas in `toInitialConditions` below.

-/


-- @@ L165-178 verbatim
/-- Initial conditions for the harmonic oscillator specified at an arbitrary time `t₀`.

  This structure allows specifying the position and velocity at any time `t₀`, not necessarily
  at `t=0`. This is useful for problems where the natural reference time is not zero.

  The conditions can be converted to the standard `InitialConditions` format (at `t=0`)
  using the `toInitialConditions` function. -/
@[ext] structure InitialConditionsAtTime where
  /-- The time at which the initial conditions are specified. -/
  t₀ : Time
  /-- The position at time t₀. -/
  xT₀ : EuclideanSpace ℝ (Fin 1)
  /-- The velocity at time t₀. -/
  vT₀ : EuclideanSpace ℝ (Fin 1)


-- @@ L180-180 verbatim
namespace InitialConditionsAtTime


-- @@ L182-193 verbatim
/-- Convert initial conditions at time `t₀` to standard initial conditions at `t=0`.

  This conversion uses the harmonic oscillator solution formula with time-reversal.
  The resulting `InitialConditions` will produce a trajectory that passes through
  `xT₀` with velocity `vT₀` at time `t₀`.

  See `toInitialConditions_trajectory_at_t₀` and `toInitialConditions_velocity_at_t₀` for
  the correctness proofs. -/
noncomputable def toInitialConditions (S : HarmonicOscillator)
    (IC : InitialConditionsAtTime) : InitialConditions where
  x₀ := cos (S.ω * IC.t₀) • IC.xT₀ - (sin (S.ω * IC.t₀) / S.ω) • IC.vT₀
  v₀ := S.ω • sin (S.ω * IC.t₀) • IC.xT₀ + cos (S.ω * IC.t₀) • IC.vT₀


-- @@ L195-198 verbatim
/-!
The correctness proofs showing that the conversion produces the expected trajectory
are given later in section D.1, after the trajectory machinery has been defined.
-/


-- @@ L200-200 verbatim
end InitialConditionsAtTime



-- @@ L203-224 verbatim
/-!

#### A.2.2. Initial conditions from two positions at different times

We define a type for initial conditions specified by two measured positions `xT₁` and `xT₂`
at two distinct times `t₁` and `t₂`.

The conversion to the standard `InitialConditions` is obtained by solving for `x₀` and `v₀` the
two equations given by evaluating the trajectory at `t₁` and `t₂`:
  `xT₁ = cos(ωt₁)·x₀ + (sin(ωt₁)/ω)·v₀`
  `xT₂ = cos(ωt₂)·x₀ + (sin(ωt₂)/ω)·v₀`

This linear system has determinant `(cos(ωt₁)·sin(ωt₂) - cos(ωt₂)·sin(ωt₁))/ω = sin(ω(t₂-t₁))/ω`.
Writing `Δ = sin(ω(t₂-t₁))`, solving the system gives the formulas used below:
  `x₀ = (sin(ωt₂)·xT₁ - sin(ωt₁)·xT₂)/Δ`
  `v₀ = ω·(cos(ωt₁)·xT₂ - cos(ωt₂)·xT₁)/Δ`

The conversion is defined as a total function, but it recovers the initial conditions only when
`Δ = sin(ω(t₂-t₁)) ≠ 0`, i.e. when `t₂ - t₁` is not an integer multiple of half a period. The
correctness proofs, under this nondegeneracy condition, are given later in section D.2.

-/


-- @@ L226-239 verbatim
/-- Initial conditions for the harmonic oscillator specified by two positions
  `xT₁` and `xT₂` measured at two times `t₁` and `t₂` respectively.

  The conditions can be converted to the standard `InitialConditions` format
  using the `toInitialConditions` function. -/
@[ext] structure InitialConditionsFromTwoPositions where
  /-- The first measurement time. -/
  t₁ : Time
  /-- The position at time `t₁`. -/
  xT₁ : EuclideanSpace ℝ (Fin 1)
  /-- The second measurement time. -/
  t₂ : Time
  /-- The position at time `t₂`. -/
  xT₂ : EuclideanSpace ℝ (Fin 1)



-- @@ L242-242 verbatim
namespace InitialConditionsFromTwoPositions


-- @@ L244-254 verbatim
/-- Convert two-position initial conditions to standard initial conditions at `t = 0`.

  Obtained by solving the 2×2 linear system from the trajectory formula at `t₁` and `t₂`.
  See `toInitialConditions_trajectory_at_t₁` and `toInitialConditions_trajectory_at_t₂` in
  section D.2 for the correctness proofs (valid under `sin (S.ω * (t₂ - t₁)) ≠ 0`). -/
noncomputable def toInitialConditions (S : HarmonicOscillator)
    (IC : InitialConditionsFromTwoPositions) : InitialConditions where
  x₀ := (sin (S.ω * IC.t₂) / sin (S.ω * (IC.t₂ - IC.t₁))) • IC.xT₁
      - (sin (S.ω * IC.t₁) / sin (S.ω * (IC.t₂ - IC.t₁))) • IC.xT₂
  v₀ := (S.ω * cos (S.ω * IC.t₁) / sin (S.ω * (IC.t₂ - IC.t₁))) • IC.xT₂
      - (S.ω * cos (S.ω * IC.t₂) / sin (S.ω * (IC.t₂ - IC.t₁))) • IC.xT₁


-- @@ L256-256 verbatim
end InitialConditionsFromTwoPositions


-- @@ L258-279 verbatim
/-!

#### A.2.3. Initial conditions from two velocities at different times

We define a type for initial conditions specified by two measured velocities `vT₁` and `vT₂`
at two distinct times `t₁` and `t₂`.

The conversion to the standard `InitialConditions` is obtained by solving for `x₀` and `v₀` the
two equations given by evaluating the velocity of the trajectory at `t₁` and `t₂`:
  `vT₁ = -ω·sin(ωt₁)·x₀ + cos(ωt₁)·v₀`
  `vT₂ = -ω·sin(ωt₂)·x₀ + cos(ωt₂)·v₀`

This linear system has determinant `ω·(cos(ωt₁)·sin(ωt₂) - cos(ωt₂)·sin(ωt₁)) = ω·sin(ω(t₂-t₁))`.
Writing `Δ = sin(ω(t₂-t₁))`, solving the system gives the formulas used below:
  `x₀ = (cos(ωt₂)·vT₁ - cos(ωt₁)·vT₂)/(ω·Δ)`
  `v₀ = (sin(ωt₂)·vT₁ - sin(ωt₁)·vT₂)/Δ`

The conversion is defined as a total function, but it recovers the initial conditions only when
`Δ = sin(ω(t₂-t₁)) ≠ 0`, i.e. when `t₂ - t₁` is not an integer multiple of half a period. The
correctness proofs, under this nondegeneracy condition, are given later in section D.3.

-/


-- @@ L281-294 verbatim
/-- Initial conditions for the harmonic oscillator specified by two velocities
  `vT₁` and `vT₂` measured at two times `t₁` and `t₂` respectively.

  The conditions can be converted to the standard `InitialConditions` format
  using the `toInitialConditions` function. -/
@[ext] structure InitialConditionsFromTwoVelocities where
  /-- The first measurement time. -/
  t₁ : Time
  /-- The velocity at time `t₁`. -/
  vT₁ : EuclideanSpace ℝ (Fin 1)
  /-- The second measurement time. -/
  t₂ : Time
  /-- The velocity at time `t₂`. -/
  vT₂ : EuclideanSpace ℝ (Fin 1)


-- @@ L296-296 verbatim
namespace InitialConditionsFromTwoVelocities


-- @@ L298-308 verbatim
/-- Convert two-velocity initial conditions to standard initial conditions at `t = 0`.

  Obtained by solving the 2×2 linear system from the velocity formula at `t₁` and `t₂`.
  See `toInitialConditions_velocity_at_t₁` and `toInitialConditions_velocity_at_t₂` in
  section D.3 for the correctness proofs (valid under `sin (S.ω * (t₂ - t₁)) ≠ 0`). -/
noncomputable def toInitialConditions (S : HarmonicOscillator)
    (IC : InitialConditionsFromTwoVelocities) : InitialConditions where
  x₀ := (cos (S.ω * IC.t₂) / (S.ω * sin (S.ω * (IC.t₂ - IC.t₁)))) • IC.vT₁
      - (cos (S.ω * IC.t₁) / (S.ω * sin (S.ω * (IC.t₂ - IC.t₁)))) • IC.vT₂
  v₀ := (sin (S.ω * IC.t₂) / sin (S.ω * (IC.t₂ - IC.t₁))) • IC.vT₁
      - (sin (S.ω * IC.t₁) / sin (S.ω * (IC.t₂ - IC.t₁))) • IC.vT₂


-- @@ L310-310 verbatim
end InitialConditionsFromTwoVelocities


-- @@ L312-322 verbatim
/-!

### A.3. The zero initial conditions

The zero initial conditions are the initial conditions with zero initial position
and zero initial velocity.

In the end, we will see that this corresponds to the solution which is identically zero,
i.e. the particle remains at rest at the origin.

-/


-- @@ L324-324 verbatim
namespace InitialConditions


-- @@ L326-327 verbatim
/-- The zero initial condition. -/
instance : Zero InitialConditions := ⟨0, 0⟩


-- @@ L329-335 verbatim
/-!

#### A.3.1. Simple results for the zero initial conditions

Some simple results about the zero initial conditions.

-/

-- @@ L336-338 verbatim
/-- The zero initial condition has zero starting point. -/
@[simp]
lemma x₀_zero : x₀ 0 = 0 := rfl


-- @@ L340-342 verbatim
/-- The zero initial condition has zero starting velocity. -/
@[simp]
lemma v₀_zero : v₀ 0 = 0 := rfl


-- @@ L344-344 verbatim
end InitialConditions

-- @@ L345-355 verbatim
/-!

## B. Trajectories associated with the initial conditions

To each initial condition we association a trajectory. We will prove some basic properties
of these trajectories.

Eventually we will show that these trajectories satisfy the equation of motion, for
now we can think of them as some choice of trajectory associated with the initial conditions.

-/


-- @@ L357-357 verbatim
namespace InitialConditions


-- @@ L359-363 verbatim
/-!

### B.1. The trajectory associated with the initial conditions

-/


-- @@ L365-367 verbatim
/-- Given initial conditions, the solution to the classical harmonic oscillator. -/
noncomputable def trajectory (IC : InitialConditions) : Time → EuclideanSpace ℝ (Fin 1) := fun t =>
  cos (S.ω * t) • IC.x₀ + (sin (S.ω * t)/S.ω) • IC.v₀


-- @@ L369-375 verbatim
/-!

#### B.1.1. Definitional equality for the trajectory

We show a basic definitional equality for the trajectory.

-/

-- @@ L376-377 verbatim
lemma trajectory_eq (IC : InitialConditions) :
    IC.trajectory S = fun t : Time => cos (S.ω * t) • IC.x₀ + (sin (S.ω * t)/S.ω) • IC.v₀ := rfl


-- @@ L379-385 verbatim
/-!

### B.2. The trajectory for zero initial conditions

The trajectory for zero initial conditions is the zero function.

-/


-- @@ L387-390 verbatim
/-- For zero initial conditions, the trajectory is zero. -/
@[simp]
lemma trajectory_zero : trajectory S 0 = fun _ => 0 := by
  simp [trajectory_eq]


-- @@ L392-398 verbatim
/-!

### B.3. Smoothness of the trajectories

The trajectories for any initial conditions are smooth functions of time.

-/


-- @@ L400-405 verbatim
@[fun_prop]
lemma trajectory_contDiff (S : HarmonicOscillator) (IC : InitialConditions) {n : WithTop ℕ∞} :
    ContDiff ℝ n (IC.trajectory S) := by
  rw [trajectory_eq]
  have h : ContDiff ℝ n (Time.val : Time → ℝ) := Time.toRealCLM.contDiff
  fun_prop


-- @@ L407-413 verbatim
/-!

### B.4. Velocity of the trajectories

We give a simplification of the velocity of the trajectory.

-/


-- @@ L415-434 verbatim
lemma trajectory_velocity (IC : InitialConditions) : ∂ₜ (IC.trajectory S) =
    fun t : Time => - S.ω • sin (S.ω * t.val) • IC.x₀ + cos (S.ω * t.val) • IC.v₀ := by
  funext t
  rw [trajectory_eq, Time.deriv, fderiv_fun_add (by fun_prop) (by fun_prop)]
  rw [fderiv_smul_const (by fun_prop), fderiv_smul_const (by fun_prop)]
  have h1 : (fderiv ℝ (fun t => sin (S.ω * t.val) / S.ω) t) =
    (1/ S.ω) • (fderiv ℝ (fun t => sin (S.ω * t.val)) t) := by
    rw [← fderiv_mul_const]
    congr
    funext t
    field_simp
    fun_prop
  simp [h1]
  rw [fderiv_cos (by fun_prop), fderiv_sin (by fun_prop),
    fderiv_fun_mul (by fun_prop) (by fun_prop)]
  simp only [fderiv_fun_const, Pi.zero_apply, smul_zero, add_zero, neg_smul,
    _root_.neg_apply, FunLike.coe_smul, Pi.smul_apply, fderiv_val,
    smul_eq_mul, mul_one]
  field_simp [S.ω_ne_zero]
  module


-- @@ L436-442 verbatim
/-!

### B.5. Acceleration of the trajectories

We give a simplification of the acceleration of the trajectory.

-/


-- @@ L444-457 verbatim
lemma trajectory_acceleration (IC : InitialConditions) : ∂ₜ (∂ₜ (IC.trajectory S)) =
    fun t : Time => - S.ω^2 • cos (S.ω * t.val) • IC.x₀ - S.ω • sin (S.ω * t.val) • IC.v₀ := by
  funext t
  rw [trajectory_velocity, Time.deriv, fderiv_fun_add (by fun_prop) (by fun_prop)]
  rw [fderiv_smul_const (by fun_prop), fderiv_fun_const_smul (by fun_prop),
    fderiv_smul_const (by fun_prop)]
  simp only [neg_smul, add_apply, ContinuousLinearMap.smulRight_apply]
  rw [fderiv_cos (by fun_prop), fderiv_sin (by fun_prop),
    fderiv_fun_mul (by fun_prop) (by fun_prop)]
  field_simp [smul_smul]
  simp only [fderiv_fun_const, Pi.ofNat_apply, smul_zero, add_zero, _root_.neg_apply,
    FunLike.coe_smul, Pi.smul_apply, ContinuousLinearMap.smulRight_apply, fderiv_val,
    smul_eq_mul, mul_one, neg_smul]
  module


-- @@ L459-466 verbatim
/-!

### B.6. The initial conditions of the trajectories

We show that, unsurprisingly, the trajectories have the initial conditions
used to define them.

-/


-- @@ L468-472 verbatim
/-- For a set of initial conditions `IC` the position of the solution at time `0` is
  `IC.x₀`. -/
@[simp]
lemma trajectory_position_at_zero (IC : InitialConditions) : IC.trajectory S 0 = IC.x₀ := by
  simp [trajectory]


-- @@ L474-476 verbatim
@[simp]
lemma trajectory_velocity_at_zero (IC : InitialConditions) : ∂ₜ (IC.trajectory S) 0 = IC.v₀ := by
  simp [trajectory_velocity]


-- @@ L478-484 verbatim
/-!

## C. Trajectories and Equation of motion

The trajectories satisfy the equation of motion for the harmonic oscillator.

-/


-- @@ L486-500 verbatim
lemma trajectory_equationOfMotion (IC : InitialConditions) :
    EquationOfMotion S (IC.trajectory S) := by
  rw [EquationOfMotion, gradLagrangian_eq_force (S := S) (xₜ := IC.trajectory S)
    (trajectory_contDiff S IC)]
  funext t
  simp only [Pi.zero_apply]
  rw [trajectory_acceleration, force_eq_linear]
  ext
  have hωm : S.ω ^ 2 * S.m = S.k := by
    rw [ω_sq]
    field_simp [m_ne_zero S]
  simp [trajectory_eq, smul_add, smul_smul, mul_comm]
  rw [← hωm]
  field_simp [ω_ne_zero S]
  ring


-- @@ L502-509 verbatim
/-!

### C.1. Uniqueness of the solutions

We show that the trajectories are the unique solutions to the equation of motion
for the given initial conditions.

-/

-- @@ L510-568 verbatim
/-- The trajectories to the equation of motion for a given set of initial conditions
  are unique.

  Given any smooth `x` satisfying the equation of motion with the same initial
  position and velocity, the difference `y = x - IC.trajectory S` also solves the
  equation of motion with zero initial conditions; energy conservation then forces
  its energy, and hence `y`, to vanish identically, so `x = IC.trajectory S`. -/
lemma trajectories_unique (IC : InitialConditions) (x : Time → EuclideanSpace ℝ (Fin 1))
    (hx : ContDiff ℝ ∞ x) :
    S.EquationOfMotion x ∧ x 0 = IC.x₀ ∧ ∂ₜ x 0 = IC.v₀ →
    x = IC.trajectory S := by
  rintro ⟨hEOM, hx0, hv0⟩
  have hTraj : ContDiff ℝ ∞ (IC.trajectory S) := by fun_prop
  -- Time-derivative of a difference of differentiable functions, used below on `x - traj`.
  have dsub : ∀ f g : Time → EuclideanSpace ℝ (Fin 1),
      Differentiable ℝ f → Differentiable ℝ g →
      ∂ₜ (fun t => f t - g t) = fun t => ∂ₜ f t - ∂ₜ g t := by
    intro f g hf hg
    funext t
    simp only [Time.deriv_eq, fderiv_fun_sub (hf t) (hg t), sub_apply]
  -- The difference `y := x - traj` is smooth, again solves the equation of motion (the force is
  -- linear), and has vanishing initial data; energy conservation then forces `y = 0`.
  set y : Time → EuclideanSpace ℝ (Fin 1) := fun t => x t - IC.trajectory S t with hydef
  have hyContDiff : ContDiff ℝ ∞ y := hx.sub hTraj
  have hy_deriv : ∂ₜ y = fun t => ∂ₜ x t - ∂ₜ (IC.trajectory S) t :=
    dsub x _ (hx.differentiable (by simp)) (hTraj.differentiable (by simp))
  have hy_deriv2 : ∂ₜ (∂ₜ y) = fun t => ∂ₜ (∂ₜ x) t - ∂ₜ (∂ₜ (IC.trajectory S)) t := by
    rw [hy_deriv]
    exact dsub _ _ (deriv_differentiable_of_contDiff _ hx)
      (deriv_differentiable_of_contDiff _ hTraj)
  have hNewt_x := (S.equationOfMotion_iff_newtons_2nd_law x hx).1 hEOM
  have hNewt_traj := (S.equationOfMotion_iff_newtons_2nd_law (IC.trajectory S) hTraj).1
    (trajectory_equationOfMotion S IC)
  have hEOM_y : S.EquationOfMotion y :=
    (S.equationOfMotion_iff_newtons_2nd_law y hyContDiff).2 fun t => by
      rw [hy_deriv2]
      simp [smul_sub, hNewt_x, hNewt_traj, hydef, force_eq_linear]
  have hE : ∀ t, S.energy y t = 0 := fun t =>
    (S.energy_conservation_of_equationOfMotion' y hyContDiff hEOM_y t).trans <| by
      have hy0 : y 0 = 0 := by simp [hydef, hx0]
      have hyv0 : ∂ₜ y 0 = 0 := by
        rw [congrFun hy_deriv 0, hv0, trajectory_velocity_at_zero S IC]; simp
      simp [HarmonicOscillator.energy, HarmonicOscillator.kineticEnergy,
        HarmonicOscillator.potentialEnergy, hy0, hyv0, one_div, smul_eq_mul]
  -- Both energies are nonnegative, so a vanishing total energy forces `y t = 0`.
  funext t
  have hk : 0 ≤ S.kineticEnergy y t := by
    simp only [HarmonicOscillator.kineticEnergy]
    exact mul_nonneg (mul_nonneg (by norm_num) S.m_pos.le) real_inner_self_nonneg
  have hp : 0 ≤ S.potentialEnergy (y t) := by
    simp only [HarmonicOscillator.potentialEnergy, smul_eq_mul]
    exact mul_nonneg (by norm_num) (mul_nonneg S.k_pos.le real_inner_self_nonneg)
  have hpe : S.potentialEnergy (y t) = 0 := ((add_eq_zero_iff_of_nonneg hk hp).mp (hE t)).2
  simp only [HarmonicOscillator.potentialEnergy, smul_eq_mul] at hpe
  rcases mul_eq_zero.mp hpe with h | h
  · norm_num at h
  · have hyt : x t - IC.trajectory S t = 0 :=
      inner_self_eq_zero.mp ((mul_eq_zero.mp h).resolve_left S.k_ne_zero)
    exact sub_eq_zero.mp hyt


-- @@ L570-577 verbatim
/-!

## D. The energy of the trajectories

For a given set of initial conditions, the energy of the trajectory is constant,
due to the conservation of energy. Here we show it's value.

-/


-- @@ L579-584 verbatim
lemma trajectory_energy (IC : InitialConditions) : S.energy (IC.trajectory S) =
    fun _ => 1/2 * (S.m * ‖IC.v₀‖ ^2 + S.k * ‖IC.x₀‖ ^ 2) := by
  funext t
  rw [energy_conservation_of_equationOfMotion' _ _ (by fun_prop) (trajectory_equationOfMotion S IC)]
  simp [energy, kineticEnergy, potentialEnergy]
  ring


-- @@ L586-586 verbatim
end InitialConditions


-- @@ L588-596 verbatim
/-!

### D.1. Correctness of InitialConditionsAtTime conversion

We now prove the correctness lemmas for the `InitialConditionsAtTime.toInitialConditions`
conversion function. These show that the conversion produces a trajectory that passes through
the specified position and velocity at the specified time.

-/


-- @@ L598-598 verbatim
namespace InitialConditionsAtTime


-- @@ L600-610 verbatim
/-- The trajectory resulting from `toInitialConditions` passes through the specified
  position `xT₀` at time `t₀`. -/
@[simp]
lemma toInitialConditions_trajectory_at_t₀ (S : HarmonicOscillator)
    (IC : InitialConditionsAtTime) :
    (IC.toInitialConditions S).trajectory S IC.t₀ = IC.xT₀ := by
  rw [InitialConditions.trajectory_eq, toInitialConditions]
  ext i
  simp only [smul_add, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
  field_simp [S.ω_ne_zero]
  linear_combination (S.ω * IC.xT₀.ofLp i) * cos_sq_add_sin_sq (S.ω * IC.t₀.val)


-- @@ L612-623 verbatim
/-- The trajectory resulting from `toInitialConditions` has the specified
  velocity `vT₀` at time `t₀`. -/
@[simp]
lemma toInitialConditions_velocity_at_t₀ (S : HarmonicOscillator)
    (IC : InitialConditionsAtTime) :
    ∂ₜ ((IC.toInitialConditions S).trajectory S) IC.t₀ = IC.vT₀ := by
  rw [InitialConditions.trajectory_velocity, toInitialConditions]
  ext i
  simp only [neg_smul, smul_add, PiLp.add_apply, PiLp.neg_apply, PiLp.smul_apply, PiLp.sub_apply,
    smul_eq_mul]
  field_simp [S.ω_ne_zero]
  linear_combination (IC.vT₀.ofLp i) * cos_sq_add_sin_sq (S.ω * IC.t₀.val)


-- @@ L625-634 verbatim
/-- The energy of the trajectory at time `t₀` equals the energy computed from the
  initial conditions at `t₀`. -/
lemma toInitialConditions_energy_at_t₀ (S : HarmonicOscillator)
    (IC : InitialConditionsAtTime) :
    S.energy ((IC.toInitialConditions S).trajectory S) IC.t₀ =
    1/2 * (S.m * ‖IC.vT₀‖^2 + S.k * ‖IC.xT₀‖^2) := by
  unfold energy kineticEnergy potentialEnergy
  simp only [toInitialConditions_trajectory_at_t₀, toInitialConditions_velocity_at_t₀]
  simp only [real_inner_self_eq_norm_sq, smul_eq_mul]
  ring


-- @@ L636-636 verbatim
end InitialConditionsAtTime


-- @@ L638-650 verbatim
/-!

### D.2. Correctness of InitialConditionsFromTwoPositions conversion

The conversion recovers the initial conditions only when `sin (S.ω * (t₂ - t₁)) ≠ 0`. This
condition fails exactly when `ω·(t₂ - t₁) = n·π` for some integer `n`, i.e. when `t₂ - t₁` is an
integer multiple of half a period; in that case `x(t₂) = (-1)^n · x(t₁)` for every trajectory,
independent of `v₀`, so the two positions do not determine the initial conditions.

Under this nondegeneracy condition, we prove that the resulting trajectory passes through `xT₁`
at `t₁` and `xT₂` at `t₂`.

-/


-- @@ L652-652 verbatim
namespace InitialConditionsFromTwoPositions


-- @@ L654-664 verbatim
/-- The trajectory from `toInitialConditions` passes through `xT₁` at time `t₁`,
  provided `sin (S.ω * (t₂ - t₁)) ≠ 0`. -/
lemma toInitialConditions_trajectory_at_t₁ (S : HarmonicOscillator)
    (IC : InitialConditionsFromTwoPositions)
    (hΔ : sin (S.ω * (IC.t₂ - IC.t₁)) ≠ 0) :
    (IC.toInitialConditions S).trajectory S IC.t₁ = IC.xT₁ := by
  rw [InitialConditions.trajectory_eq, toInitialConditions]
  ext i
  simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
  field_simp [S.ω_ne_zero]
  grind [mul_sub, Real.sin_sub]


-- @@ L666-676 verbatim
/-- The trajectory from `toInitialConditions` passes through `xT₂` at time `t₂`,
  provided `sin (S.ω * (t₂ - t₁)) ≠ 0`. -/
lemma toInitialConditions_trajectory_at_t₂ (S : HarmonicOscillator)
    (IC : InitialConditionsFromTwoPositions)
    (hΔ : sin (S.ω * (IC.t₂ - IC.t₁)) ≠ 0) :
    (IC.toInitialConditions S).trajectory S IC.t₂ = IC.xT₂ := by
  rw [InitialConditions.trajectory_eq, toInitialConditions]
  ext i
  simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
  field_simp [S.ω_ne_zero]
  grind [mul_sub, Real.sin_sub]


-- @@ L678-678 verbatim
end InitialConditionsFromTwoPositions


-- @@ L680-688 verbatim
/-!

### D.3. Correctness of InitialConditionsFromTwoVelocities conversion

The conversion recovers the initial conditions only when `sin (S.ω * (t₂ - t₁)) ≠ 0`. Under this
nondegeneracy condition, we prove that the resulting trajectory has velocity `vT₁` at `t₁` and
`vT₂` at `t₂`.

-/


-- @@ L690-690 verbatim
namespace InitialConditionsFromTwoVelocities


-- @@ L692-703 verbatim
/-- The trajectory from `toInitialConditions` has velocity `vT₁` at time `t₁`,
  provided `sin (S.ω * (t₂ - t₁)) ≠ 0`. -/
lemma toInitialConditions_velocity_at_t₁ (S : HarmonicOscillator)
    (IC : InitialConditionsFromTwoVelocities)
    (hΔ : sin (S.ω * (IC.t₂ - IC.t₁)) ≠ 0) :
    ∂ₜ ((IC.toInitialConditions S).trajectory S) IC.t₁ = IC.vT₁ := by
  rw [InitialConditions.trajectory_velocity, toInitialConditions]
  ext i
  simp only [neg_smul, PiLp.add_apply, PiLp.neg_apply, PiLp.smul_apply, PiLp.sub_apply,
    smul_eq_mul]
  field_simp [S.ω_ne_zero]
  grind [mul_sub, Real.sin_sub]


-- @@ L705-716 verbatim
/-- The trajectory from `toInitialConditions` has velocity `vT₂` at time `t₂`,
  provided `sin (S.ω * (t₂ - t₁)) ≠ 0`. -/
lemma toInitialConditions_velocity_at_t₂ (S : HarmonicOscillator)
    (IC : InitialConditionsFromTwoVelocities)
    (hΔ : sin (S.ω * (IC.t₂ - IC.t₁)) ≠ 0) :
    ∂ₜ ((IC.toInitialConditions S).trajectory S) IC.t₂ = IC.vT₂ := by
  rw [InitialConditions.trajectory_velocity, toInitialConditions]
  ext i
  simp only [neg_smul, PiLp.add_apply, PiLp.neg_apply, PiLp.smul_apply, PiLp.sub_apply,
    smul_eq_mul]
  field_simp [S.ω_ne_zero]
  grind [mul_sub, Real.sin_sub]


-- @@ L718-718 verbatim
end InitialConditionsFromTwoVelocities


-- @@ L720-741 verbatim
/-!

## E. Amplitude–phase parametrization

The state of the harmonic oscillator at `t = 0` is captured by `InitialConditions` as a position
`x₀` and a velocity `v₀`. An equivalent and often more physical description writes the solution as
a single shifted cosine of amplitude `A` and phase `φ`:
  `x(t) = A cos (ω t - φ)`.

Expanding with the angle-subtraction identity,
  `A cos (ω t - φ) = (A cos φ) cos (ω t) + (A sin φ) sin (ω t)`,
and matching coefficients against the standard solution
  `x(t) = cos (ω t) x₀ + (sin (ω t) / ω) v₀`
gives the change of coordinates
  `x₀ = A cos φ`,   `v₀ = A ω sin φ`.

We implement the forward map `(A, φ) ↦ (x₀, v₀)` as `toInitialConditions`, prove the resulting
trajectory is the cosine normal form above (with velocity `-A ω sin (ω t - φ)`), and implement the
inverse map `(x₀, v₀) ↦ (A, φ)` as `fromInitialConditions`, recovering `A` and `φ` as the polar
coordinates of the phase vector `(x₀, v₀ / ω)`.

-/


-- @@ L743-751 verbatim
/-!

### E.1. The amplitude–phase initial conditions

We define a type for initial conditions specified by an amplitude `A` and a phase angle `φ`. Being
an amplitude and an angle, these are stored as scalars, rather than as vectors as for the other
initial-condition types.

-/


-- @@ L753-762 verbatim
/-- Initial conditions for the harmonic oscillator specified by an amplitude `A` and a phase
  offset `φ`, describing the solution `x(t) = A cos (ω t - φ)`.

  The conditions can be converted to the standard `InitialConditions` format using the
  `toInitialConditions` function. -/
@[ext] structure AmplitudePhase where
  /-- The amplitude of the oscillation. -/
  A : ℝ
  /-- The phase offset of the oscillation. -/
  φ : ℝ


-- @@ L764-764 verbatim
namespace AmplitudePhase


-- @@ L766-773 verbatim
/-!

### E.2. Conversion to standard initial conditions

Using `x₀ = A cos φ` and `v₀ = A ω sin φ`, we convert amplitude–phase data to the standard initial
position and velocity at `t = 0`.

-/


-- @@ L775-783 verbatim
/-- Convert amplitude–phase initial conditions to standard initial conditions at `t = 0`, via
  `x₀ = A cos φ` and `v₀ = A ω sin φ`.

  See `toInitialConditions_trajectory_eq_cos` and `toInitialConditions_velocity_eq_sin` in
  section E.3 for the correctness proofs. -/
noncomputable def toInitialConditions (S : HarmonicOscillator) (IC : AmplitudePhase) :
    InitialConditions where
  x₀ := EuclideanSpace.single 0 (IC.A * cos IC.φ)
  v₀ := EuclideanSpace.single 0 (IC.A * S.ω * sin IC.φ)


-- @@ L785-793 verbatim
/-!

### E.3. The trajectory in normal form

The trajectory built from amplitude–phase data is exactly the single cosine
`x(t) = A cos (ω t - φ)`, with velocity `v(t) = -A ω sin (ω t - φ)`. In the position identity the
factor `1 / ω` of the standard solution cancels the `ω` in `v₀ = A ω sin φ`, which uses `ω ≠ 0`.

-/


-- @@ L795-805 verbatim
/-- The trajectory of amplitude–phase initial conditions is the cosine normal form
  `x(t) = A cos (ω t - φ)`. -/
lemma toInitialConditions_trajectory_eq_cos (S : HarmonicOscillator) (IC : AmplitudePhase)
    (t : Time) :
    (IC.toInitialConditions S).trajectory S t
      = EuclideanSpace.single 0 (IC.A * cos (S.ω * t - IC.φ)) := by
  rw [InitialConditions.trajectory_eq, toInitialConditions]
  ext i
  fin_cases i
  simp [Real.cos_sub]
  field_simp [S.ω_ne_zero]


-- @@ L807-816 verbatim
/-- The velocity of the amplitude–phase trajectory is `v(t) = -A ω sin (ω t - φ)`. -/
lemma toInitialConditions_velocity_eq_sin (S : HarmonicOscillator) (IC : AmplitudePhase)
    (t : Time) :
    ∂ₜ ((IC.toInitialConditions S).trajectory S) t
      = EuclideanSpace.single 0 (-(IC.A * S.ω * sin (S.ω * t.val - IC.φ))) := by
  rw [InitialConditions.trajectory_velocity, toInitialConditions]
  ext i
  fin_cases i
  simp [Real.sin_sub]
  ring


-- @@ L818-831 verbatim
/-!

### E.4. Recovering the amplitude and phase

The inverse map `(x₀, v₀) ↦ (A, φ)` must solve `x₀ = A cos φ` and `v₀ / ω = A sin φ`. Recovering
the angle with the real `arctan` covers only `(-π/2, π/2)` and forces a case split at `x₀ = 0`; we
instead embed the phase vector as the complex number `z = x₀ + (v₀ / ω) i` and read off `A = ‖z‖`
and `φ = Complex.arg z`, with `arg` in the canonical range `(-π, π]`. The degenerate state
`x₀ = v₀ = 0` is covered by the convention `arg 0 = 0`, so no case split is needed.

We prove that converting initial conditions to amplitude–phase form and back returns the original
initial conditions.

-/


-- @@ L833-841 verbatim
/-- Recover amplitude–phase data from standard initial conditions, as the polar coordinates of the
  phase vector `(x₀, v₀ / ω)` embedded as `z = x₀ + (v₀ / ω) i`: the amplitude is `‖z‖` and the
  phase is `Complex.arg z`.

  See `toInitialConditions_fromInitialConditions` for the right-inverse identity. -/
noncomputable def fromInitialConditions (S : HarmonicOscillator) (IC : InitialConditions) :
    AmplitudePhase where
  A := ‖(⟨IC.x₀ 0, IC.v₀ 0 / S.ω⟩ : ℂ)‖
  φ := Complex.arg (⟨IC.x₀ 0, IC.v₀ 0 / S.ω⟩ : ℂ)


-- @@ L843-866 verbatim
/-- `fromInitialConditions` is a right inverse of `toInitialConditions`: converting initial
  conditions to amplitude–phase form and back recovers them exactly. -/
lemma toInitialConditions_fromInitialConditions (S : HarmonicOscillator)
    (IC : InitialConditions) :
    (fromInitialConditions S IC).toInitialConditions S = IC := by
  have hω : S.ω ≠ 0 := S.ω_ne_zero
  set z : ℂ := (⟨IC.x₀ 0, IC.v₀ 0 / S.ω⟩ : ℂ)
  -- polar identities
  have hcos : ‖z‖ * cos (Complex.arg z) = z.re := Complex.norm_mul_cos_arg z
  have hsin : ‖z‖ * sin (Complex.arg z) = z.im := Complex.norm_mul_sin_arg z
  -- By construction the parts of `z` are exactly the original data.
  have hre : z.re = IC.x₀ 0 := rfl
  have him : z.im = IC.v₀ 0 / S.ω := rfl
  apply InitialConditions.ext
  · -- Position: `‖z‖ cos (arg z) = Re z = IC.x₀ 0`, and `single 0 (IC.x₀ 0) = IC.x₀`.
    show EuclideanSpace.single 0 (‖z‖ * cos (Complex.arg z)) = IC.x₀
    rw [hcos, hre]
    ext i; fin_cases i; simp
  · -- Velocity: `‖z‖ ω sin (arg z) = ω · Im z = ω · (v₀ / ω) = IC.v₀ 0`, then reassemble.
    show EuclideanSpace.single 0 (‖z‖ * S.ω * sin (Complex.arg z)) = IC.v₀
    have hv : ‖z‖ * S.ω * sin (Complex.arg z) = IC.v₀ 0 := by
      rw [mul_right_comm, hsin, him]; field_simp
    rw [hv]
    ext i; fin_cases i; simp


-- @@ L868-868 verbatim
end AmplitudePhase



-- @@ L871-871 verbatim
namespace InitialConditions


-- @@ L873-885 verbatim
/-!

## F. Special conditions of the trajectory

We use the amplitude-phase parametrization from section E to describe the special times of a
trajectory. After converting arbitrary initial conditions to amplitude and phase, every trajectory
has the form `x(t) = A cos (ω t - φ)` and its velocity has the form `v(t) = -Aω sin (ω t - φ)`.

Thus the turning points of the motion are controlled by the zeros of `sin (ω t - φ)`, while the
times at which the trajectory passes through the origin are controlled by the zeros of
`cos (ω t - φ)`.

-/


-- @@ L887-895 verbatim
/-!

### F.1. Normal form for standard initial conditions

The amplitude-phase normal form was first proved for data already expressed as an
`AmplitudePhase`. We now transport those identities back to ordinary `InitialConditions` using
`AmplitudePhase.fromInitialConditions`.

-/


-- @@ L897-906 verbatim
/-- Every trajectory of the harmonic oscillator is a single shifted cosine after converting its
  initial conditions to amplitude-phase form. -/
lemma trajectory_eq_cos (IC : InitialConditions) (t : Time) :
    IC.trajectory S t =
      EuclideanSpace.single 0 ((AmplitudePhase.fromInitialConditions S IC).A *
        cos (S.ω * t - (AmplitudePhase.fromInitialConditions S IC).φ)) := by
  conv_lhs =>
    rw [← AmplitudePhase.toInitialConditions_fromInitialConditions S IC]
  exact AmplitudePhase.toInitialConditions_trajectory_eq_cos S
    (AmplitudePhase.fromInitialConditions S IC) t


-- @@ L908-916 verbatim
/-- The velocity of every trajectory is the corresponding shifted sine in amplitude-phase form. -/
lemma trajectory_velocity_eq_sin (IC : InitialConditions) (t : Time) :
    ∂ₜ (IC.trajectory S) t =
      EuclideanSpace.single 0 (-((AmplitudePhase.fromInitialConditions S IC).A * S.ω *
        sin (S.ω * t.val - (AmplitudePhase.fromInitialConditions S IC).φ))) := by
  conv_lhs =>
    rw [← AmplitudePhase.toInitialConditions_fromInitialConditions S IC]
  exact AmplitudePhase.toInitialConditions_velocity_eq_sin S
    (AmplitudePhase.fromInitialConditions S IC) t


-- @@ L918-926 verbatim
/-!

### F.2. Times at which the velocity is zero

In amplitude-phase form the velocity is `v(t) = -Aω sin (ω t - φ)`. For nonzero amplitude this
vanishes exactly when `sin (ω t - φ) = 0`, equivalently when `ω t - φ` is an
integer multiple of `π`.

-/


-- @@ L928-935 verbatim
/-- For nonzero amplitude, the velocity vanishes exactly when the sine factor in
  amplitude-phase form vanishes. -/
lemma trajectory_velocity_eq_zero_iff_sin_eq_zero (IC : InitialConditions)
    (hA : (AmplitudePhase.fromInitialConditions S IC).A ≠ 0) (t : Time) :
    ∂ₜ (IC.trajectory S) t = 0 ↔
      sin (S.ω * t.val - (AmplitudePhase.fromInitialConditions S IC).φ) = 0 := by
  rw [trajectory_velocity_eq_sin]
  simp [hA, S.ω_ne_zero]


-- @@ L937-955 verbatim
/-- For nonzero amplitude, the velocity is zero exactly at phase times `φ + nπ`. -/
lemma trajectory_velocity_eq_zero_iff_exists_int (IC : InitialConditions)
    (hA : (AmplitudePhase.fromInitialConditions S IC).A ≠ 0) (t : Time) :
    ∂ₜ (IC.trajectory S) t = 0 ↔
      ∃ n : ℤ,
        (t : ℝ) =
          ((AmplitudePhase.fromInitialConditions S IC).φ + n * π) / S.ω := by
  rw [trajectory_velocity_eq_zero_iff_sin_eq_zero S IC hA t]
  constructor
  · intro h
    obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.mp h
    refine ⟨n, ?_⟩
    rw [eq_div_iff S.ω_ne_zero, mul_comm]
    linarith
  · rintro ⟨n, hn⟩
    rw [Real.sin_eq_zero_iff, hn]
    refine ⟨n, ?_⟩
    field_simp [S.ω_ne_zero]
    ring


-- @@ L957-968 verbatim
/-!

### F.3. The position when the velocity is zero

The zeros of the velocity are the turning points of the oscillator. In amplitude-phase form,
these are the times when `sin (ω t - φ) = 0`; equivalently, `cos (ω t - φ)` is `1` or `-1`.
At exactly those times the trajectory has maximal norm, equal to the amplitude `A`.

The statement also covers the degenerate case `A = 0`: then the trajectory and its velocity are
identically zero, so both sides of the equivalence hold at every time.

-/


-- @@ L970-996 verbatim
/-- The velocity vanishes exactly when the trajectory has norm equal to the amplitude. -/
lemma trajectory_velocity_eq_zero_iff_norm_eq_amplitude (IC : InitialConditions)
    (t : Time) :
    ∂ₜ (IC.trajectory S) t = 0 ↔
      ‖IC.trajectory S t‖ = (AmplitudePhase.fromInitialConditions S IC).A := by
  by_cases hA : (AmplitudePhase.fromInitialConditions S IC).A = 0
  · rw [trajectory_velocity_eq_sin, trajectory_eq_cos]
    simp [hA]
  rw [trajectory_velocity_eq_zero_iff_sin_eq_zero S IC hA t, trajectory_eq_cos]
  set A := (AmplitudePhase.fromInitialConditions S IC).A
  set θ := S.ω * t.val - (AmplitudePhase.fromInitialConditions S IC).φ
  show sin θ = 0 ↔ ‖EuclideanSpace.single 0 (A * cos θ)‖ = A
  have hA' : A ≠ 0 := by simpa [A] using hA
  have hA_nonneg : 0 ≤ A := norm_nonneg (⟨IC.x₀ 0, IC.v₀ 0 / S.ω⟩ : ℂ)
  have hA_pos : 0 < A := lt_of_le_of_ne hA_nonneg (Ne.symm hA')
  constructor
  · intro hsin
    rcases Real.sin_eq_zero_iff_cos_eq.mp hsin with hcos | hcos <;>
      simp [hcos, abs_of_pos hA_pos]
  · intro hnorm
    have hnorm' : |A * cos θ| = A := by
      simpa using hnorm
    have hcos_abs : |cos θ| = 1 := by
      rw [abs_mul, abs_of_pos hA_pos] at hnorm'
      exact mul_left_cancel₀ hA' (hnorm'.trans (mul_one A).symm)
    obtain ⟨n, hn⟩ := Real.abs_cos_eq_one_iff.mp hcos_abs
    exact Real.sin_eq_zero_iff.mpr ⟨n, hn⟩


-- @@ L998-1006 verbatim
/-!

### F.4. Times at which the trajectory passes through zero

In amplitude-phase form the trajectory is `x(t) = A cos (ω t - φ).` For nonzero amplitude this
vanishes exactly when `cos (ω t - φ) = 0`, equivalently when the phase is an odd multiple
of `π / 2`.

-/


-- @@ L1008-1015 verbatim
/-- For nonzero amplitude, the trajectory passes through zero exactly when the cosine factor in
  amplitude-phase form vanishes. -/
lemma trajectory_eq_zero_iff_cos_eq_zero (IC : InitialConditions)
    (hA : (AmplitudePhase.fromInitialConditions S IC).A ≠ 0) (t : Time) :
    IC.trajectory S t = 0 ↔
      cos (S.ω * t.val - (AmplitudePhase.fromInitialConditions S IC).φ) = 0 := by
  rw [trajectory_eq_cos]
  simp [hA]


-- @@ L1017-1036 verbatim
/-- For nonzero amplitude, the trajectory passes through zero exactly at phase times
  `φ + (2n + 1)π / 2`. -/
lemma trajectory_eq_zero_iff_exists_int (IC : InitialConditions)
    (hA : (AmplitudePhase.fromInitialConditions S IC).A ≠ 0) (t : Time) :
    IC.trajectory S t = 0 ↔
      ∃ n : ℤ,
        (t : ℝ) =
          ((AmplitudePhase.fromInitialConditions S IC).φ + (2 * n + 1) * π / 2) / S.ω := by
  rw [trajectory_eq_zero_iff_cos_eq_zero S IC hA t]
  constructor
  · intro h
    obtain ⟨n, hn⟩ := Real.cos_eq_zero_iff.mp h
    refine ⟨n, ?_⟩
    rw [eq_div_iff S.ω_ne_zero, mul_comm]
    linarith
  · rintro ⟨n, hn⟩
    rw [Real.cos_eq_zero_iff, hn]
    refine ⟨n, ?_⟩
    field_simp [S.ω_ne_zero]
    ring


-- @@ L1038-1038 verbatim
end InitialConditions


-- @@ L1040-1049 verbatim
/-!

## G. Periodicity and recurrence

Every trajectory is a shifted cosine of angular frequency `ω`, so it repeats after a fixed period
`T = 2π / ω`. We record the period, show the trajectory is periodic, and prove that — for
non-trivial initial data — the trajectory returns to its initial position and velocity exactly at
integer multiples of the period.

-/


-- @@ L1051-1057 verbatim
/-!

### G.1. The period

The period `T = 2π / ω` is the time for one complete oscillation; it is positive since `ω > 0`.

-/


-- @@ L1059-1062 verbatim
/--
The period of a harmonic oscillator is `2 * π / ω`.
-/
noncomputable def period (S : HarmonicOscillator) : ℝ := 2 * π / S.ω


-- @@ L1064-1065 verbatim
@[inherit_doc period]
scoped notation "T" => HarmonicOscillator.period


-- @@ L1067-1067 verbatim
lemma period_eq : T S = 2 * π / S.ω := rfl


-- @@ L1069-1069 verbatim
lemma period_pos : 0 < T S := div_pos (by positivity) S.ω_pos


-- @@ L1071-1078 verbatim
/-!

### G.2. Periodicity of the trajectory

The trajectory satisfies `x(t + T) = x(t)`: advancing time by one period shifts the phase `ω t`
by `2π`, leaving `cos` and `sin` unchanged.

-/


-- @@ L1080-1089 verbatim
/--
The trajectory of the harmonic oscillator is periodic with period of `2 * π / ω`.
-/
lemma trajectory_periodic (IC : InitialConditions) :
    Function.Periodic (IC.trajectory S) (T S) := fun t ↦ by
  have h : S.ω * (t.val + 2 * π / S.ω) = S.ω * t.val + 2 * π := by
    have := S.ω_ne_zero
    ring_nf; field_simp
  rw [InitialConditions.trajectory, add_val, period_eq, h, cos_add_two_pi, sin_add_two_pi]
  rfl


-- @@ L1091-1098 verbatim
/-!

### G.3. Return to the initial state

For non-trivial initial data, the trajectory returns to its initial position and velocity only at
integer multiples of the period.

-/


-- @@ L1100-1152 verbatim
/--
Assuming that the initial coordinate and velocity are not simultaneously zero,
the time stamps when the harmonic oscillator returns to its initial coordinate and velocity is
a multiple of its period
-/
lemma return_time (IC : InitialConditions) (non_trivial : IC.x₀ ≠ 0 ∨ IC.v₀ ≠ 0)
    (t : Time) (ht : IC.trajectory S t = IC.x₀ ∧ ∂ₜ (IC.trajectory S) t = IC.v₀) :
    ∃ n : ℤ,  (n : ℝ) * (T S) = t := by
  have htx := ht.left
  have htv := ht.right
  rw [InitialConditions.trajectory_eq] at htx
  rw [InitialConditions.trajectory_velocity] at htv
  simp at htx
  simp at htv
  set c := cos (S.ω * t)
  set s :=  sin (S.ω * t)
  set xx := inner ℝ IC.x₀ IC.x₀
  set vv := inner ℝ IC.v₀ IC.v₀
  set xv := inner ℝ IC.x₀ IC.v₀
  set det := vv + xx *  S.ω^2
  have hxx0 : 0 ≤ xx := real_inner_self_nonneg
  have hvv0 : 0 ≤ vv := real_inner_self_nonneg
  have hω2 : 0 < S.ω ^ 2 := pow_pos S.ω_pos 2
  have zero_lt_det : 0 < det := by
    show 0 < vv + xx * S.ω ^ 2
    rcases non_trivial with hx | hv
    · nlinarith [real_inner_self_pos.mpr hx]
    · nlinarith [real_inner_self_pos.mpr hv]
  have det_ne_zero : det ≠ 0 := zero_lt_det.ne'
  have hxx : c * xx + (s / S.ω) * xv = xx := by
    have h := congrArg (inner ℝ IC.x₀) htx
    simpa only [inner_add_right, real_inner_smul_right] using h
  have hvv : - S.ω * s * xv + c * vv = vv := by
    have h := congrArg (fun w => inner ℝ w IC.v₀) htv
    simpa only [inner_add_left, inner_neg_left, real_inner_smul_left, neg_mul, mul_assoc] using h
  have hcos : 1 = cos (S.ω * t) := by
    calc
    1 =  det / det := by simp only [ne_eq, det_ne_zero, not_false_eq_true, div_self]
    _ = (vv + xx * S.ω^2 ) / det := by rfl
    _ = c * ((vv + xx * S.ω^2) / det) + s * xv *S.ω* (S.ω/S.ω-1 ) / det := by
      nth_rewrite 1 [← hvv, ← hxx]
      ring_nf
    _ = c * ((vv + xx * S.ω^2) / det ) := by
      simp only [ne_eq, S.ω_ne_zero, not_false_eq_true,
        div_self, sub_self, mul_zero, zero_div, add_zero]
    _ = c * (det / det) := by rfl
    _ = c := by simp only [ne_eq, det_ne_zero, not_false_eq_true, div_self, mul_one]
    _ = _ := by rfl
  obtain ⟨n, hn⟩ := (Real.cos_eq_one_iff (S.ω * t)).mp hcos.symm
  refine ⟨n, ?_⟩
  rw [period_eq]
  field_simp [S.ω_ne_zero]
  linear_combination hn

-- @@ L1153-1153 verbatim
end HarmonicOscillator


-- @@ L1155-1155 verbatim
end ClassicalMechanics
