/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev
-/
module

public import LeanPool.HopfProblem.Prelude
public import LeanPool.HopfProblem.HomologyTheory.FirstHurewicz3
import all LeanPool.HopfProblem.Foundations.Core1
import all LeanPool.HopfProblem.Lattice.Core1
import all LeanPool.HopfProblem.Foundations.Core2
import all LeanPool.HopfProblem.HomologyTheory.FirstHurewicz3


-- @@ L15-19 verbatim
/-!
# Hopf problem: lattice · core 2

Supporting definitions and proofs for this stage of the six-sphere construction.
-/



-- @@ L22-22 verbatim
open Set Function Filter Manifold Topology


-- @@ L24-27 verbatim
open scoped BigOperators CategoryTheory Complex.UnitDisc ComplexConjugate ContDiff ContinuousMap
  Convolution ENNReal EuclideanSpace Fin.NatCast InnerProductSpace Interval Matrix MatrixGroups
  Modular NNReal Pointwise RealInnerProductSpace TensorProduct UniformConvergence Uniformity
  UpperHalfPlane


-- @@ L29-29 verbatim
universe u v


-- @@ L31-31 verbatim
noncomputable section


-- @@ L33-33 verbatim
namespace Mathoverflow1973


-- @@ L35-35 verbatim
local infixr:80 " ≫ₚ " => Path.trans


-- @@ L37-37 verbatim
local notation:100 f " ∣[" k "] " a:100 => SlashAction.map k a f


-- @@ L39-39 verbatim
private theorem A₁_fixes_ε : A₁ *ᵥ ε = ε := by decide


-- @@ L41-41 verbatim
private theorem A₂_fixes_ε' : A₂ *ᵥ ε' = ε' := by decide


-- @@ L43-45 verbatim
private theorem M₀_sub_one_mulVec (v : Lattice) : (M₀ - 1) *ᵥ v = ![0, 0, v 1, -v 0] := by
  ext i
  fin_cases i <;> simp [M₀, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Matrix.one_apply]


-- @@ L47-57 verbatim
private theorem M₀_sub_one_kernel (v : Lattice) : (M₀ - 1) *ᵥ v = 0 ↔ v 0 = 0 ∧ v 1 = 0 := by
  rw [M₀_sub_one_mulVec]
  constructor
  · intro h
    have h₂ := congrFun h 2
    have h₃ := congrFun h 3
    change v 1 = 0 at h₂
    change -v 0 = 0 at h₃
    exact ⟨neg_eq_zero.mp h₃, h₂⟩
  · rintro ⟨h₀, h₁⟩
    simp [h₀, h₁]


-- @@ L59-69 verbatim
private theorem
    M₀_sub_one_range (v : Lattice) : (∃ w : Lattice, (M₀ - 1) *ᵥ w = v) ↔ v 0 = 0 ∧ v 1 = 0 :=
  by
  constructor
  · rintro ⟨w, rfl⟩
    simp [M₀_sub_one_mulVec]
  · rintro ⟨h₀, h₁⟩
    refine ⟨![-v 3, v 2, 0, 0], ?_⟩
    rw [M₀_sub_one_mulVec]
    ext i
    fin_cases i <;> simp [h₀, h₁]


-- @@ L71-81 verbatim
private theorem A₁_fixed_iff (v : Lattice) : A₁ *ᵥ v = v ↔ v 1 = 2 * v 0 ∧ v 2 = -4 * v 0 := by
  constructor
  · intro h
    have h₁ := congrFun h 1
    have h₂ := congrFun h 2
    have h₃ := congrFun h 3
    simp [A₁, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at h₁ h₂ h₃
    omega
  · rintro ⟨h₁, h₂⟩
    ext i
    fin_cases i <;> simp [A₁, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, h₁, h₂] <;> ring


-- @@ L83-94 verbatim
private theorem A₂_fixed_iff (v : Lattice) : A₂ *ᵥ v = v ↔ v 1 = 3 * v 0 ∧ v 2 = -3 * v 0 := by
  constructor
  · intro h
    have h₁ := congrFun h 1
    have h₂ := congrFun h 2
    have h₃ := congrFun h 3
    simp [A₂, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at h₁ h₂ h₃
    omega
  · rintro ⟨h₁, h₂⟩
    ext i
    fin_cases i <;> simp [A₂, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, h₁, h₂]
    ring


-- @@ L96-99 verbatim
/-- An integer coordinate vector of length `n`. -/
public
abbrev LocalSystemMatrices.Vec (n : ℕ) :=
  Fin n → ℤ


-- @@ L101-104 verbatim
/-- The linear functional selecting the last coordinate of a rank-four vector. -/
public
def LocalSystemMatrices.lastCoordinate : Vec 4 →ₗ[ℤ] ℤ :=
  LinearMap.proj 3


-- @@ L106-109 verbatim
/-- The two coordinate indices represented by an exterior-square basis element. -/
public
def LocalSystemMatrices.pairIndices : Fin 6 → Fin 2 → Fin 4 :=
  ![![0, 1], ![0, 2], ![0, 3], ![1, 2], ![1, 3], ![2, 3] ]


-- @@ L111-112 verbatim
private def LocalSystemMatrices.exteriorSquare (T : LatticeMatrix) : Matrix (Fin 6) (Fin 6) ℤ :=
  fun i j => (T.submatrix (pairIndices i) (pairIndices j)).det


-- @@ L114-115 verbatim
private def LocalSystemMatrices.tripleIndices : Fin 4 → Fin 3 → Fin 4 :=
  ![![0, 1, 2], ![0, 1, 3], ![0, 2, 3], ![1, 2, 3] ]


-- @@ L117-118 verbatim
private def LocalSystemMatrices.exteriorCube (T : LatticeMatrix) : LatticeMatrix := fun i j =>
  (T.submatrix (tripleIndices i) (tripleIndices j)).det


-- @@ L120-120 verbatim
end Mathoverflow1973


-- @@ L122-122 verbatim
end
