/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev
-/
module

public import LeanPool.HopfProblem.Prelude
public import LeanPool.HopfProblem.Foundations.LineBundleTransport
import all LeanPool.HopfProblem.Foundations.Core1
import all LeanPool.HopfProblem.Foundations.LineBundleTransport


-- @@ L13-17 verbatim
/-!
# Hopf problem: lattice · core 1

Supporting definitions and proofs for this stage of the six-sphere construction.
-/



-- @@ L20-20 verbatim
open Set Function Filter Manifold Topology


-- @@ L22-25 verbatim
open scoped BigOperators CategoryTheory Complex.UnitDisc ComplexConjugate ContDiff ContinuousMap
  Convolution ENNReal EuclideanSpace Fin.NatCast InnerProductSpace Interval Matrix MatrixGroups
  Modular NNReal Pointwise RealInnerProductSpace TensorProduct UniformConvergence Uniformity
  UpperHalfPlane


-- @@ L27-27 verbatim
universe u v


-- @@ L29-29 verbatim
noncomputable section


-- @@ L31-31 verbatim
namespace Mathoverflow1973


-- @@ L33-33 verbatim
local infixr:80 " ≫ₚ " => Path.trans


-- @@ L35-35 verbatim
local notation:100 f " ∣[" k "] " a:100 => SlashAction.map k a f


-- @@ L37-40 verbatim
/-- The rank-four integer lattice in coordinate form. -/
public
abbrev Lattice :=
  Fin 4 → ℤ


-- @@ L42-43 verbatim
private def T₁ : LatticeMatrix :=
  !![1, 0, -6, 2; 0, -1, 1, 1; 0, -1, 0, 1; 0, 0, 0, 1]


-- @@ L45-46 verbatim
private def T₂ : LatticeMatrix :=
  !![1, 6, 0, -3; 0, 0, -1, 1; 0, 1, 0, 0; 0, 0, 0, 1]


-- @@ L48-49 verbatim
private def T₀ : LatticeMatrix :=
  !![1, 0, 0, 1; 0, 1, -1, 0; 0, 0, 1, 0; 0, 0, 0, 1]


-- @@ L51-52 verbatim
private def A₁ : LatticeMatrix :=
  !![1, 0, 0, 0; 6, 0, 1, 0; -6, -1, -1, 0; -2, 1, 0, 1]


-- @@ L54-55 verbatim
private def A₂ : LatticeMatrix :=
  !![1, 0, 0, 0; 0, 0, -1, 0; -6, 1, 0, 0; 3, 0, 1, 1]


-- @@ L57-58 verbatim
private def M₀ : LatticeMatrix :=
  !![1, 0, 0, 0; 0, 1, 0, 0; 0, 1, 1, 0; -1, 0, 0, 1]


-- @@ L60-61 verbatim
private def B₀ : Matrix (Fin 2) (Fin 2) ℤ :=
  !![0, 1; -1, 0]


-- @@ L63-63 verbatim
private theorem T₁_cube : T₁ ^ 3 = 1 := by decide


-- @@ L65-65 verbatim
private theorem T₂_fourth : T₂ ^ 4 = 1 := by decide


-- @@ L67-67 verbatim
private theorem A₁_eq_transpose_sq : A₁ = (T₁ ^ 2).transpose := by decide


-- @@ L69-69 verbatim
private theorem A₂_eq_transpose_cube : A₂ = (T₂ ^ 3).transpose := by decide


-- @@ L71-71 verbatim
end Mathoverflow1973


-- @@ L73-73 verbatim
end
