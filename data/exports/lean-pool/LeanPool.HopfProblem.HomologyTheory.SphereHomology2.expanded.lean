/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev
-/
module

public import LeanPool.HopfProblem.Prelude
public import LeanPool.HopfProblem.HomologyTheory.FirstHurewicz1
import all LeanPool.HopfProblem.HomologyTheory.SingularMayerVietoris
import all LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology1
import all LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology2
import all LeanPool.HopfProblem.HomologyTheory.SphereHomology1
import all LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology3
import all LeanPool.HopfProblem.HomologyTheory.FirstHurewicz1


-- @@ L17-21 verbatim
/-!
# Hopf problem: homology theory · sphere homology 2

Supporting definitions and proofs for this stage of the six-sphere construction.
-/



-- @@ L24-24 verbatim
open Set Function Filter Manifold Topology


-- @@ L26-29 verbatim
open scoped BigOperators CategoryTheory Complex.UnitDisc ComplexConjugate ContDiff ContinuousMap
  Convolution ENNReal EuclideanSpace Fin.NatCast InnerProductSpace Interval Matrix MatrixGroups
  Modular NNReal Pointwise RealInnerProductSpace TensorProduct UniformConvergence Uniformity
  UpperHalfPlane


-- @@ L31-31 verbatim
universe u v


-- @@ L33-33 verbatim
noncomputable section


-- @@ L35-35 verbatim
namespace Mathoverflow1973


-- @@ L37-37 verbatim
local infixr:80 " ≫ₚ " => Path.trans


-- @@ L39-39 verbatim
local notation:100 f " ∣[" k "] " a:100 => SlashAction.map k a f


-- @@ L41-43 verbatim
private def SphereHomology.unitCircleHomologyOneEquiv :
    SingularMayerVietoris.SingularHomology _root_.Circle 1 ≃ₗ[ℤ] ℤ :=
  (unitCircleHomologyEquiv 1).trans PeriodTorusHigherHomology.circleHomologyOneEquiv


-- @@ L45-48 verbatim
private theorem SphereHomology.unitCircle_homology_subsingleton (n : ℕ) :
    Subsingleton (SingularMayerVietoris.SingularHomology _root_.Circle (n + 2)) := by
  let := PeriodTorusHigherHomology.circle_homology_subsingleton n
  exact (unitCircleHomologyEquiv (n + 2)).injective.subsingleton



-- @@ L51-55 verbatim
private def SphereHomology.sphereCircleHomologyOneEquiv :
    SingularMayerVietoris.SingularHomology (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1)
        1 ≃ₗ[ℤ]
      ℤ :=
  (sphereCircleHomologyEquiv 1).trans unitCircleHomologyOneEquiv


-- @@ L57-63 verbatim
public
theorem SphereHomology.sphereCircle_homology_subsingleton (n : ℕ) :
    Subsingleton
      (SingularMayerVietoris.SingularHomology (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1)
        (n + 2)) := by
  let := unitCircle_homology_subsingleton n
  exact (sphereCircleHomologyEquiv (n + 2)).injective.subsingleton


-- @@ L65-67 verbatim
private def SphereHomology.unitSphereHomologyZeroEquiv (n : ℕ) :
    SingularMayerVietoris.SingularHomology (UnitSphere (n + 1)) 0 ≃ₗ[ℤ] ℤ :=
  PeriodTorusHigherHomology.connectedHomologyZeroEquiv (UnitSphere (n + 1))


-- @@ L69-72 verbatim
private def SphereHomology.unitSphereHomologyTopEquiv :
    (n : ℕ) → SingularMayerVietoris.SingularHomology (UnitSphere (n + 1)) (n + 1) ≃ₗ[ℤ] ℤ
  | 0 => sphereCircleHomologyOneEquiv
  | n + 1 => (unitSphereHomologySuspensionEquiv (n + 1) n).trans (unitSphereHomologyTopEquiv n)


-- @@ L74-76 verbatim
private def SphereHomology.unitSphereTopClass (n : ℕ) :
    SingularMayerVietoris.SingularHomology (UnitSphere (n + 1)) (n + 1) :=
  (unitSphereHomologyTopEquiv n).symm 1


-- @@ L78-78 verbatim
end Mathoverflow1973


-- @@ L80-80 verbatim
end
