/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev
-/
module

public import LeanPool.HopfProblem.Prelude
public import LeanPool.HopfProblem.Threefold.SixSphereComplexAtlas
import all LeanPool.HopfProblem.MainTheorem.Core2
import all LeanPool.HopfProblem.Threefold.SixSphereComplexAtlas


-- @@ L13-17 verbatim
/-!
# Hopf problem: main theorem · core 3

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


-- @@ L37-42 verbatim
public
theorem mathoverflow_1973 :
    ∃ atlas : ChartedSpace (EuclideanSpace ℂ (Fin 3)) (unitSphere 6),
      letI := atlas
      IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin 3)) 1 (unitSphere 6) := by
  exact SixSphereComplexAtlas.exists_complex_atlas


-- @@ L44-44 verbatim
end Mathoverflow1973


-- @@ L46-46 verbatim
end
