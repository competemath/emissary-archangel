/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev
-/
module

public import LeanPool.HopfProblem.Prelude
public import LeanPool.HopfProblem.Hurewicz.HigherHurewicz2
import all LeanPool.HopfProblem.HomologyTheory.SphereHomology1
import all LeanPool.HopfProblem.Hurewicz.HigherHurewicz2


-- @@ L13-17 verbatim
/-!
# Hopf problem: main theorem · six sphere cube 2

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
/-- The standard unit six-sphere. -/
public
abbrev SixSphereCube.StandardSphere :=
  SphereHomology.UnitSphere 6


-- @@ L42-44 verbatim
private def SixSphereCube.euclideanOnePointSphereHomeomorph :
    OnePoint (EuclideanSpace ℝ (Fin 6)) ≃ₜ StandardSphere :=
  onePointEquivSphereOfFinrankEq (V := EuclideanSpace ℝ (Fin 6)) (ι := Fin 7) (by simp)


-- @@ L46-47 verbatim
private def SixSphereCube.sphereBasePoint : StandardSphere :=
  euclideanOnePointSphereHomeomorph (OnePoint.infty)


-- @@ L49-49 verbatim
end Mathoverflow1973


-- @@ L51-51 verbatim
end
