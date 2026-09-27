/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev
-/
module

public import LeanPool.HopfProblem.Prelude
public import LeanPool.HopfProblem.HomologyOfX.ThreefoldHomology4
import all LeanPool.HopfProblem.HomologyOfX.ThreefoldHomology4


-- @@ L12-16 verbatim
/-!
# Hopf problem: main theorem · core 2

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
/-- The unit `n`-sphere in Euclidean `(n+1)`-space. -/
public
abbrev unitSphere (n : ℕ) :=
  Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1


-- @@ L41-41 verbatim
end Mathoverflow1973


-- @@ L43-43 verbatim
end
