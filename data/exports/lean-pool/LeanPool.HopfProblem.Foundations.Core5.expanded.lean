/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev
-/
module

public import LeanPool.HopfProblem.Prelude
public import LeanPool.HopfProblem.Foundations.TrianglePeriodFamilyHomologySplitting
import all LeanPool.HopfProblem.Foundations.TrianglePeriodFamilyHomologySplitting


-- @@ L12-16 verbatim
/-!
# Hopf problem: foundations · core 5

Supporting definitions and proofs for this stage of the six-sphere construction.
-/



-- @@ L19-19 verbatim
open Set Function Filter Manifold Topology


-- @@ L21-24 verbatim
open scoped BigOperators CategoryTheory Complex.UnitDisc ComplexConjugate ContDiff ContinuousMap
  Convolution ENNReal EuclideanSpace Fin.NatCast InnerProductSpace Interval Matrix MatrixGroups
  Modular NNReal Pointwise RealInnerProductSpace TensorProduct UniformConvergence Uniformity
  UpperHalfPlane


-- @@ L26-26 verbatim
universe u v


-- @@ L28-28 verbatim
noncomputable section


-- @@ L30-30 verbatim
namespace Mathoverflow1973


-- @@ L32-32 verbatim
local infixr:80 " ≫ₚ " => Path.trans


-- @@ L34-34 verbatim
local notation:100 f " ∣[" k "] " a:100 => SlashAction.map k a f


-- @@ L36-39 verbatim
/-- The linear combination of local twisting numbers used by the gluing construction. -/
public
def twistOrder (ℓ₀ ℓ₁ ℓ₂ : ℤ) : ℤ :=
  12 * ℓ₀ - 4 * ℓ₁ - 3 * ℓ₂


-- @@ L41-42 verbatim
public
theorem main_twist_value : twistOrder 0 1 (-1) = -1 := by decide


-- @@ L44-48 verbatim
private def twistRelators (a b d : ℤ) : Fin 5 → FreeGroup (Fin 3) :=
  let c := FreeGroup.of (0 : Fin 3)
  let x := FreeGroup.of (1 : Fin 3)
  let y := FreeGroup.of (2 : Fin 3)
  ![c * x * (x * c)⁻¹, c * y * (y * c)⁻¹, x * y * (c ^ a)⁻¹, x ^ 3 * (c ^ b)⁻¹, y ^ 4 * (c ^ d)⁻¹]


-- @@ L50-50 verbatim
end Mathoverflow1973


-- @@ L52-52 verbatim
end
