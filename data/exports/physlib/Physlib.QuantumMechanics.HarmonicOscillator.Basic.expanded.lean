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

-- @@ L12-51 verbatim
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

## iii. Table of contents

- A. Basic properties
  - A.1. Positive mass
  - A.2. Positive natural frequencies
- B. Characteristic lengths
  - B.1. Coordinate rescaling
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


-- @@ L53-53 verbatim
@[expose] public section


-- @@ L55-55 verbatim
noncomputable section

-- @@ L56-56 verbatim
namespace QuantumMechanics


-- @@ L58-65 verbatim
/-- The `d`-dimensional quantum harmonic oscillator. -/
structure HarmonicOscillator (d : ℕ) where
  /-- The mass (positive). -/
  m : ℝ
  hm : 0 < m
  /-- The natural frequencies (positive). -/
  ω : Fin d → ℝ
  hω : ∀ i, 0 < ω i


-- @@ L67-67 verbatim
variable {d : ℕ} (Q : HarmonicOscillator d) (i : Fin d)


-- @@ L69-69 verbatim
namespace HarmonicOscillator


-- @@ L71-71 verbatim
open Constants SpaceDHilbertSpace MeasureTheory


-- @@ L73-75 verbatim
/-!
## A. Basic properties
-/


-- @@ L77-79 verbatim
/-!
### A.1. Positive mass
-/


-- @@ L81-82 verbatim
@[simp]
lemma m_pos : 0 < Q.m := Q.hm


-- @@ L84-85 verbatim
@[simp]
lemma m_nonneg : 0 ≤ Q.m := Q.hm.le


-- @@ L87-88 verbatim
@[simp]
lemma m_ne_zero : Q.m ≠ 0 := Q.hm.ne'


-- @@ L90-92 verbatim
/-!
### A.2. Positive natural frequencies
-/


-- @@ L94-95 verbatim
@[simp]
lemma ω_pos : 0 < Q.ω i := Q.hω i


-- @@ L97-98 verbatim
@[simp]
lemma ω_nonneg : 0 ≤ Q.ω i := (Q.hω i).le


-- @@ L100-101 verbatim
@[simp]
lemma ω_ne_zero : Q.ω i ≠ 0 := (Q.hω i).ne'


-- @@ L103-105 verbatim
/-!
## B. Characteristic lengths
-/


-- @@ L107-108 verbatim
/-- The characteristic length `ξ i ≔ √ℏ / (√Q.m * √(Q.ω i))`. -/
def ξ : ℝ := √ℏ / (√Q.m * √(Q.ω i))


-- @@ L110-110 verbatim
lemma ξ_eq : Q.ξ i = √ℏ / (√Q.m * √(Q.ω i)) := rfl


-- @@ L112-113 verbatim
@[simp]
lemma ξ_pos : 0 < Q.ξ i := by simp [ξ_eq]


-- @@ L115-116 verbatim
@[simp]
lemma ξ_nonneg : 0 ≤ Q.ξ i := (Q.ξ_pos i).le


-- @@ L118-119 verbatim
@[simp]
lemma ξ_ne_zero : Q.ξ i ≠ 0 := (Q.ξ_pos i).ne'


-- @@ L121-121 verbatim
lemma ξ_sq : (Q.ξ i) ^ 2 = ℏ / (Q.m * Q.ω i) := by rw [Q.ξ_eq]; field_simp; simp [← mul_rotate]


-- @@ L123-123 verbatim
lemma ξ_inv : (Q.ξ i)⁻¹ = √Q.m * √(Q.ω i) / √ℏ := by simp [ξ_eq]


-- @@ L125-125 verbatim
lemma ξ_inv' : (Q.ξ i)⁻¹ = Q.m * Q.ω i * Q.ξ i / ℏ := by field_simp; simp [ξ_sq, mul_assoc]


-- @@ L127-129 verbatim
/-!
### B.1. Coordinate rescaling
-/


-- @@ L131-138 verbatim
/-- The continuous linear equivalence which rescales `xᵢ` to `ξᵢxᵢ`. -/
def ξEquiv : Space d ≃L[ℝ] Space d where
  toFun x := ⟨fun i ↦ Q.ξ i * x i⟩
  invFun x := ⟨fun i ↦ (Q.ξ i)⁻¹ * x i⟩
  map_add' _ _ := by ext; simp [mul_add]
  map_smul' _ _ := by ext; simp [mul_left_comm]
  left_inv _ := by simp
  right_inv _ := by simp


-- @@ L140-141 verbatim
@[simp]
lemma ξEquiv_apply (x : Space d) (i : Fin d) : Q.ξEquiv x i = Q.ξ i * x i := rfl


-- @@ L143-144 verbatim
@[simp]
lemma ξEquiv_symm_apply (x : Space d) (i : Fin d) : Q.ξEquiv.symm x i = (Q.ξ i)⁻¹ * x i := rfl


-- @@ L146-148 verbatim
/-!
## C. The quadratic potential function
-/


-- @@ L150-150 verbatim
section


-- @@ L152-152 verbatim
open Matrix


-- @@ L154-156 verbatim
/-!
### C.1. Positive-definite matrix
-/


-- @@ L158-159 verbatim
/-- The positive-definite matrix defining the quadratic potential function. -/
def potentialMatrix : Matrix (Fin d) (Fin d) ℝ := diagonal ((2⁻¹ * Q.m) • Q.ω ^ 2)


-- @@ L161-161 verbatim
lemma potentialMatrix_eq : Q.potentialMatrix = diagonal ((2⁻¹ * Q.m) • Q.ω ^ 2) := rfl


-- @@ L163-163 verbatim
lemma potentialMatrix_isHermitian : Q.potentialMatrix.IsHermitian := by simp [potentialMatrix_eq]


-- @@ L165-169 verbatim
@[simp]
lemma potentialMatrix_mulVec (v : Fin d → ℝ) :
    Q.potentialMatrix *ᵥ v = (2⁻¹ * Q.m) • (Q.ω ^ 2 * v) := by
  ext
  simp [potentialMatrix_eq, smul_mulVec, mulVec_diagonal]


-- @@ L171-173 verbatim
/-!
### C.2. Quadratic form
-/


-- @@ L175-176 verbatim
/-- The positive-definite quadratic form associated to the potential matrix. -/
def potentialQuadraticForm : QuadraticForm ℝ (Fin d → ℝ) := Q.potentialMatrix.toQuadraticForm'


-- @@ L178-180 verbatim
/-!
### C.3. Potential function
-/


-- @@ L182-183 verbatim
/-- The quadratic potential function, `½m · ∑ i, ωᵢ²·xᵢ²`. -/
def potentialFunction : Space d → ℝ := Q.potentialQuadraticForm ∘ Space.val


-- @@ L185-185 verbatim
lemma potentialFunction_eq : Q.potentialFunction = Q.potentialQuadraticForm ∘ Space.val := rfl


-- @@ L187-190 expanded
/-- The potential function for the harmonic oscillator is a.e. strongly measurable. -/
def potentialFunction_aestronglyMeasurable : InformalLemma
    where
  deps := [``HarmonicOscillator]
  tag := "QM-HO-potAESM"


-- @@ L192-192 verbatim
end


-- @@ L194-196 verbatim
/-!
## D. Isotropic oscillators
-/


-- @@ L198-199 verbatim
/-- A Harmonic oscillator is isotropic if all natural frequencies are equal. -/
def IsIsotropic : Prop := ∀ i j, Q.ω i = Q.ω j


-- @@ L201-201 verbatim
lemma isIsotropic_def : Q.IsIsotropic ↔ ∀ i j, Q.ω i = Q.ω j := Iff.rfl


-- @@ L203-203 verbatim
lemma isIsotropic_of_one (Q : HarmonicOscillator 1) : Q.IsIsotropic := by simp [isIsotropic_def]


-- @@ L205-207 verbatim
/-!
## E. Hilbert space
-/


-- @@ L209-211 verbatim
/-- The Hilbert space for the quantum harmonic oscillator. -/
@[nolint unusedArguments]
abbrev HS (_ : HarmonicOscillator d) : Type _ := SpaceDHilbertSpace d


-- @@ L213-215 verbatim
/-!
## F. Operators
-/


-- @@ L217-219 verbatim
/-!
### F.1. Kinetic energy
-/


-- @@ L221-222 verbatim
/-- The kinetic energy operator, `p²/2m`. -/
def kineticOperator : Q.HS →ₗ.[ℂ] Q.HS := (2 * Q.m)⁻¹ • momentumSqOperator


-- @@ L224-226 verbatim
/-!
### F.2. Potential energy
-/


-- @@ L228-228 verbatim
section


-- @@ L230-230 verbatim
open MeasureTheory Complex


-- @@ L232-233 expanded
/-- The potential operator which maps `ψ` to `Q.potentialFunction • ψ`. -/
def potentialOperator : Q.HS →ₗ.[ℂ] Q.HS :=
  mulOperator volume (ofReal ∘ Q.potentialFunction)


-- @@ L235-238 expanded
/-- The potential operators for the harmonic oscillator is self-adjoint. -/
def potentialOperator_isSelfAdjoint : InformalLemma
    where
  deps := [``HarmonicOscillator.potentialFunction_aestronglyMeasurable]
  tag := "QM-HO-potSA"


-- @@ L240-240 verbatim
end


-- @@ L242-244 verbatim
/-!
### F.3. Hamiltonian
-/


-- @@ L246-247 verbatim
/-- The Hamiltonian for the harmonic oscillator. -/
def hamiltonian : Q.HS →ₗ.[ℂ] Q.HS := Q.kineticOperator + Q.potentialOperator


-- @@ L249-249 verbatim
lemma hamiltonain_eq : Q.hamiltonian = Q.kineticOperator + Q.potentialOperator := rfl


-- @@ L251-254 expanded
/-- The Hamiltonian for the harmonic oscillator is essentially self-adjoint. -/
def hamiltonian_essentially_self_adjoint : InformalLemma
    where
  deps := [``HarmonicOscillator.hamiltonian]
  tag := "QM-HO-hamESA"


-- @@ L256-258 verbatim
/-!
## G. As a quantum system
-/


-- @@ L260-264 expanded
/-- The `d`-dimensional harmonic oscillator as a quantum system
  (self-adjoint Hamiltonian acting on a Hilbert space). -/
def toQuantumSystem : InformalDefinition
    where
  deps := [``HarmonicOscillator.hamiltonian_essentially_self_adjoint]
  tag := "QM-HO-sys"


-- @@ L266-266 verbatim
end HarmonicOscillator

-- @@ L267-267 verbatim
end QuantumMechanics

-- @@ L268-268 verbatim
end
