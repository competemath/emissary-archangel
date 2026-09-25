/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory J. Loges
-/
module

public import Physlib.Meta.Informal.Basic
public import Physlib.QuantumMechanics.Operators.Momentum
public import Physlib.QuantumMechanics.Operators.Multiplication
public import Physlib.QuantumMechanics.QuantumSystem.Basic

-- @@ L12-53 verbatim
/-!

# The quantum harmonic oscillator

## i. Overview

The harmonic oscillator is one of the most important examples in non-relativistic quantum mechanics.
It describes a particle of mass `m` subject to a positive-definite quadratic potential
in `d` dimensions.

- `Basic.lean` : Properties of the potential, definition of isotropic oscillators,
    kinetic, potential and Hamiltonian operators.
- `LadderOperators.lean` : Definitions of the raising/lowering/number operators
    and their algebraic properties.

## ii. Key results

- `potentialFunction_apply` : the potential function, expanded to `½m · ∑ᵢ ωᵢ²xᵢ²`.
- `potentialOperator_isSelfAdjoint` : the potential operator is self-adjoint.

## iii. Table of contents

- A. Basic properties
  - A.1. Positive mass
  - A.2. Positive natural frequencies
- B. Characteristic lengths
- C. The quadratic potential function
  - C.1. Positive-definite matrix
  - C.2. Quadratic form
  - C.3. Potential function
- D. Isotropic oscillators
- E. Hilbert space
- F. Operators
  - E.1. Kinetic energy
  - E.2. Potential energy
  - E.3. Hamiltonian
- G. As a quantum system

## iv. References

* None.
-/


-- @@ L55-55 verbatim
@[expose] public section


-- @@ L57-58 verbatim
TODO "Determine the spectrum of the quantum harmonic oscillator in terms of
  the natural frequencies and integer quantum numbers."


-- @@ L60-61 verbatim
TODO "Determine the energy eigenstates of the quantum harmonic oscillator
  in the 'Cartesian basis' in terms of Hermite polynomials."


-- @@ L63-64 verbatim
TODO "Determine the energy eigenstates of the isotropic quantum harmonic oscillator
  in the 'spherical basis' in terms of spherical harmonics."


-- @@ L66-66 verbatim
noncomputable section

-- @@ L67-67 verbatim
namespace QuantumMechanics


-- @@ L69-76 verbatim
/-- The `d`-dimensional quantum harmonic oscillator. -/
structure HarmonicOscillator (d : ℕ) where
  /-- The mass (positive). -/
  m : ℝ
  hm : 0 < m
  /-- The natural frequencies (positive). -/
  ω : Fin d → ℝ
  hω : ∀ i, 0 < ω i


-- @@ L78-78 verbatim
variable {d : ℕ} (Q : HarmonicOscillator d) (i : Fin d)


-- @@ L80-80 verbatim
namespace HarmonicOscillator


-- @@ L82-82 verbatim
open Constants SpaceDHilbertSpace MeasureTheory


-- @@ L84-86 verbatim
/-!
## A. Basic properties
-/


-- @@ L88-90 verbatim
/-!
### A.1. Positive mass
-/


-- @@ L92-93 verbatim
@[simp]
lemma m_pos : 0 < Q.m := Q.hm


-- @@ L95-96 verbatim
@[simp]
lemma m_nonneg : 0 ≤ Q.m := Q.hm.le


-- @@ L98-99 verbatim
@[simp]
lemma m_ne_zero : Q.m ≠ 0 := Q.hm.ne'


-- @@ L101-103 verbatim
/-!
### A.2. Positive natural frequencies
-/


-- @@ L105-106 verbatim
@[simp]
lemma ω_pos : 0 < Q.ω i := Q.hω i


-- @@ L108-109 verbatim
@[simp]
lemma ω_nonneg : 0 ≤ Q.ω i := (Q.hω i).le


-- @@ L111-112 verbatim
@[simp]
lemma ω_ne_zero : Q.ω i ≠ 0 := (Q.hω i).ne'


-- @@ L114-116 verbatim
/-!
## B. Characteristic lengths
-/


-- @@ L118-119 verbatim
/-- The characteristic length `ξ i ≔ √ℏ / (√Q.m * √(Q.ω i))`. -/
def ξ : ℝ := √ℏ / (√Q.m * √(Q.ω i))


-- @@ L121-121 verbatim
lemma ξ_eq : Q.ξ i = √ℏ / (√Q.m * √(Q.ω i)) := rfl


-- @@ L123-124 verbatim
@[simp]
lemma ξ_pos : 0 < Q.ξ i := by simp [ξ_eq]


-- @@ L126-127 verbatim
@[simp]
lemma ξ_nonneg : 0 ≤ Q.ξ i := (Q.ξ_pos i).le


-- @@ L129-130 verbatim
@[simp]
lemma ξ_ne_zero : Q.ξ i ≠ 0 := (Q.ξ_pos i).ne'


-- @@ L132-132 verbatim
lemma ξ_sq : (Q.ξ i) ^ 2 = ℏ / (Q.m * Q.ω i) := by rw [Q.ξ_eq]; field_simp; simp [← mul_rotate]


-- @@ L134-134 verbatim
lemma ξ_inv : (Q.ξ i)⁻¹ = √Q.m * √(Q.ω i) / √ℏ := by simp [ξ_eq]


-- @@ L136-136 verbatim
lemma ξ_inv' : (Q.ξ i)⁻¹ = Q.m * Q.ω i * Q.ξ i / ℏ := by field_simp; simp [ξ_sq, mul_assoc]


-- @@ L138-140 verbatim
/-!
## C. The quadratic potential function
-/


-- @@ L142-142 verbatim
section


-- @@ L144-144 verbatim
open Matrix


-- @@ L146-148 verbatim
/-!
### C.1. Positive-definite matrix
-/


-- @@ L150-151 verbatim
/-- The positive-definite matrix defining the quadratic potential function. -/
def potentialMatrix : Matrix (Fin d) (Fin d) ℝ := diagonal ((2⁻¹ * Q.m) • Q.ω ^ 2)


-- @@ L153-153 verbatim
lemma potentialMatrix_eq : Q.potentialMatrix = diagonal ((2⁻¹ * Q.m) • Q.ω ^ 2) := rfl


-- @@ L155-155 verbatim
lemma potentialMatrix_isHermitian : Q.potentialMatrix.IsHermitian := by simp [potentialMatrix_eq]


-- @@ L157-161 verbatim
@[simp]
lemma potentialMatrix_mulVec (v : Fin d → ℝ) :
    Q.potentialMatrix *ᵥ v = (2⁻¹ * Q.m) • (Q.ω ^ 2 * v) := by
  ext
  simp [potentialMatrix_eq, smul_mulVec, mulVec_diagonal]


-- @@ L163-165 verbatim
/-!
### C.2. Quadratic form
-/


-- @@ L167-168 verbatim
/-- The positive-definite quadratic form associated to the potential matrix. -/
def potentialQuadraticForm : QuadraticForm ℝ (Fin d → ℝ) := Q.potentialMatrix.toQuadraticForm'


-- @@ L170-172 verbatim
/-!
### C.3. Potential function
-/


-- @@ L174-175 verbatim
/-- The quadratic potential function, `½m · ∑ i, ωᵢ²·xᵢ²`. -/
def potentialFunction : Space d → ℝ := Q.potentialQuadraticForm ∘ Space.val


-- @@ L177-177 verbatim
lemma potentialFunction_eq : Q.potentialFunction = Q.potentialQuadraticForm ∘ Space.val := rfl


-- @@ L179-187 verbatim
/-- The potential function, expanded: `½m · ∑ᵢ ωᵢ²xᵢ²`. -/
lemma potentialFunction_apply (x : Space d) :
    Q.potentialFunction x = (2⁻¹ * Q.m) * ∑ i, (Q.ω i) ^ 2 * (x i) ^ 2 := by
  show Q.potentialQuadraticForm (Space.val x) = _
  rw [potentialQuadraticForm, Matrix.toQuadraticForm', LinearMap.BilinMap.toQuadraticMap_apply,
    Matrix.toLinearMap₂'_apply', potentialMatrix_mulVec, dotProduct, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.smul_apply, Pi.mul_apply, Pi.pow_apply, smul_eq_mul]
  ring


-- @@ L189-195 verbatim
/-- The potential function for the harmonic oscillator is continuous, hence a.e. strongly
measurable. -/
lemma potentialFunction_continuous : Continuous Q.potentialFunction := by
  have heq : Q.potentialFunction = fun x => (2⁻¹ * Q.m) * ∑ i, (Q.ω i) ^ 2 * (x i) ^ 2 :=
    funext Q.potentialFunction_apply
  rw [heq]
  fun_prop


-- @@ L197-200 verbatim
/-- The potential function for the harmonic oscillator is a.e. strongly measurable. -/
lemma potentialFunction_aestronglyMeasurable :
    MeasureTheory.AEStronglyMeasurable Q.potentialFunction volume :=
  Q.potentialFunction_continuous.aestronglyMeasurable


-- @@ L202-202 verbatim
end


-- @@ L204-206 verbatim
/-!
## D. Isotropic oscillators
-/


-- @@ L208-209 verbatim
/-- A Harmonic oscillator is isotropic if all natural frequencies are equal. -/
def IsIsotropic : Prop := ∀ i j, Q.ω i = Q.ω j


-- @@ L211-211 verbatim
lemma isIsotropic_def : Q.IsIsotropic ↔ ∀ i j, Q.ω i = Q.ω j := Iff.rfl


-- @@ L213-213 verbatim
lemma isIsotropic_of_one (Q : HarmonicOscillator 1) : Q.IsIsotropic := by simp [isIsotropic_def]


-- @@ L215-217 verbatim
/-!
## E. Hilbert space
-/


-- @@ L219-221 verbatim
/-- The Hilbert space for the quantum harmonic oscillator. -/
@[nolint unusedArguments]
abbrev HS (_ : HarmonicOscillator d) : Type _ := SpaceDHilbertSpace d


-- @@ L223-225 verbatim
/-!
## F. Operators
-/


-- @@ L227-229 verbatim
/-!
### F.1. Kinetic energy
-/


-- @@ L231-232 verbatim
/-- The kinetic energy operator, `p²/2m`. -/
def kineticOperator : Q.HS →ₗ.[ℂ] Q.HS := (2 * Q.m)⁻¹ • momentumSqOperator


-- @@ L234-236 verbatim
/-!
### F.2. Potential energy
-/


-- @@ L238-238 verbatim
section


-- @@ L240-240 verbatim
open MeasureTheory Complex


-- @@ L242-243 expanded
/-- The potential operator which maps `ψ` to `Q.potentialFunction • ψ`. -/
def potentialOperator : Q.HS →ₗ.[ℂ] Q.HS :=
  mulOperator volume (ofReal ∘ Q.potentialFunction)


-- @@ L245-249 verbatim
/-- The potential operator for the harmonic oscillator is self-adjoint. -/
lemma potentialOperator_isSelfAdjoint : IsSelfAdjoint Q.potentialOperator :=
  mulOperator_isSelfAdjoint_ofReal
    (Complex.continuous_ofReal.comp Q.potentialFunction_continuous).aestronglyMeasurable
    (by ext; simp)


-- @@ L251-251 verbatim
end


-- @@ L253-255 verbatim
/-!
### F.3. Hamiltonian
-/


-- @@ L257-258 verbatim
/-- The Hamiltonian for the harmonic oscillator. -/
def hamiltonian : Q.HS →ₗ.[ℂ] Q.HS := Q.kineticOperator + Q.potentialOperator


-- @@ L260-260 verbatim
lemma hamiltonain_eq : Q.hamiltonian = Q.kineticOperator + Q.potentialOperator := rfl


-- @@ L262-265 expanded
/-- The Hamiltonian for the harmonic oscillator is essentially self-adjoint. -/
def hamiltonian_essentially_self_adjoint : InformalLemma
    where
  deps := [``HarmonicOscillator.hamiltonian]
  tag := "QM-HO-hamESA"


-- @@ L267-269 verbatim
/-!
## G. As a quantum system
-/


-- @@ L271-275 expanded
/-- The `d`-dimensional harmonic oscillator as a quantum system
  (self-adjoint Hamiltonian acting on a Hilbert space). -/
def toQuantumSystem : InformalDefinition
    where
  deps := [``HarmonicOscillator.hamiltonian_essentially_self_adjoint]
  tag := "QM-HO-sys"


-- @@ L277-277 verbatim
end HarmonicOscillator

-- @@ L278-278 verbatim
end QuantumMechanics

-- @@ L279-279 verbatim
end
