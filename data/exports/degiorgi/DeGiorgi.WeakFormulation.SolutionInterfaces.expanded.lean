import DeGiorgi.WeakFormulation.BilinearForm


-- @@ L3-8 verbatim
/-!
# Weak Formulation: Solution Interfaces

This module packages weak problems together with the weak-solution,
subsolution, and supersolution interfaces built from the bilinear form.
-/


-- @@ L10-10 verbatim
noncomputable section


-- @@ L12-12 verbatim
open MeasureTheory Filter

-- @@ L13-13 verbatim
open scoped InnerProductSpace


-- @@ L15-15 verbatim
namespace DeGiorgi


-- @@ L17-17 verbatim
variable {d : ℕ} [NeZero d]


-- @@ L19-19 verbatim
local notation "E" => AmbientSpace d


-- @@ L21-27 verbatim
/-- A weak elliptic Dirichlet problem on an open bounded domain. -/
structure WeakProblem where
  Ω : Set E
  hΩ : IsOpen Ω
  hΩ_bdd : Bornology.IsBounded Ω
  coeff : EllipticCoeff d Ω
  rhs : (E → ℝ) → ℝ


-- @@ L29-35 verbatim
/-- `u` is a weak solution of the variational problem `P` if it lies in
`H₀¹(P.Ω)` and satisfies the weak identity against every `H₀¹` test function. -/
def IsWeakSolution (P : WeakProblem (d := d)) (u : E → ℝ) : Prop :=
  MemH01 u P.Ω ∧
  ∀ (hwu : MemW1pWitness 2 u P.Ω) (v : E → ℝ), MemH01 v P.Ω →
    ∀ (hwv : MemW1pWitness 2 v P.Ω),
      bilinFormOfCoeff P.coeff hwu hwv = P.rhs v


-- @@ L37-43 verbatim
/-- `u` is a weak subsolution of `-div(A∇u) ≤ 0` on `Ω`. -/
def IsSubsolution {Ω : Set E} (A : EllipticCoeff d Ω) (u : E → ℝ) : Prop :=
  MemW1p 2 u Ω ∧
  ∀ (hu : MemW1pWitness 2 u Ω)
    (φ : E → ℝ), MemH01 φ Ω →
    ∀ (hφ : MemW1pWitness 2 φ Ω),
      (∀ x, 0 ≤ φ x) → bilinFormOfCoeff A hu hφ ≤ 0


-- @@ L45-51 verbatim
/-- `u` is a weak supersolution of `-div(A∇u) ≥ 0` on `Ω`. -/
def IsSupersolution {Ω : Set E} (A : EllipticCoeff d Ω) (u : E → ℝ) : Prop :=
  MemW1p 2 u Ω ∧
  ∀ (hu : MemW1pWitness 2 u Ω)
    (φ : E → ℝ), MemH01 φ Ω →
    ∀ (hφ : MemW1pWitness 2 φ Ω),
      (∀ x, 0 ≤ φ x) → 0 ≤ bilinFormOfCoeff A hu hφ


-- @@ L53-56 verbatim
/-- `u` is a weak solution of the homogeneous equation iff it is both a weak
subsolution and a weak supersolution. -/
def IsSolution {Ω : Set E} (A : EllipticCoeff d Ω) (u : E → ℝ) : Prop :=
  IsSubsolution A u ∧ IsSupersolution A u


-- @@ L58-68 verbatim
/-- `u` is a local weak solution of the homogeneous equation on `Ω` if it lies
in `W^{1,2}(Ω)` and the bilinear form vanishes against every `H₀¹(Ω)` test
function. This is the equality-form local weak-solution interface used by the
Harnack and Holder statements. -/
def IsHomogeneousWeakSolution {Ω : Set E}
    (A : EllipticCoeff d Ω) (u : E → ℝ) : Prop :=
  MemW1p 2 u Ω ∧
  ∀ (hu : MemW1pWitness 2 u Ω)
    (φ : E → ℝ), MemH01 φ Ω →
    ∀ (hφ : MemW1pWitness 2 φ Ω),
      bilinFormOfCoeff A hu hφ = 0


-- @@ L70-73 verbatim
/-- Extract Sobolev membership from a subsolution. -/
theorem isSubsolution_memW1p {Ω : Set E} {A : EllipticCoeff d Ω} {u : E → ℝ}
    (h : IsSubsolution A u) : MemW1p 2 u Ω :=
  h.left


-- @@ L75-78 verbatim
/-- Extract Sobolev membership from a supersolution. -/
theorem isSupersolution_memW1p {Ω : Set E} {A : EllipticCoeff d Ω} {u : E → ℝ}
    (h : IsSupersolution A u) : MemW1p 2 u Ω :=
  h.left


-- @@ L80-88 verbatim
/-- A homogeneous weak solution is a subsolution. -/
theorem isHomogeneousWeakSolution_isSubsolution
    {Ω : Set E} {A : EllipticCoeff d Ω} {u : E → ℝ}
    (h : IsHomogeneousWeakSolution A u) :
    IsSubsolution A u := by
  refine ⟨h.1, ?_⟩
  intro hu φ hφ hφw hφ_nonneg
  have hEq : bilinFormOfCoeff A hu hφw = 0 := h.2 hu φ hφ hφw
  simp [hEq]


-- @@ L90-98 verbatim
/-- A homogeneous weak solution is a supersolution. -/
theorem isHomogeneousWeakSolution_isSupersolution
    {Ω : Set E} {A : EllipticCoeff d Ω} {u : E → ℝ}
    (h : IsHomogeneousWeakSolution A u) :
    IsSupersolution A u := by
  refine ⟨h.1, ?_⟩
  intro hu φ hφ hφw hφ_nonneg
  have hEq : bilinFormOfCoeff A hu hφw = 0 := h.2 hu φ hφ hφw
  simp [hEq]


-- @@ L100-106 verbatim
/-- A homogeneous weak solution is both a subsolution and a supersolution. -/
theorem isHomogeneousWeakSolution_isSolution
    {Ω : Set E} {A : EllipticCoeff d Ω} {u : E → ℝ}
    (h : IsHomogeneousWeakSolution A u) :
    IsSolution A u :=
  ⟨isHomogeneousWeakSolution_isSubsolution h,
    isHomogeneousWeakSolution_isSupersolution h⟩


-- @@ L108-108 verbatim
end DeGiorgi
