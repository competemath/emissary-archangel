/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev
-/
module

public import LeanPool.HopfProblem.Prelude
public import LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology4
import all LeanPool.HopfProblem.HomologyTheory.SingularMayerVietoris
import all LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology1
import all LeanPool.HopfProblem.CuspFibre.CuspCentralHomology2
import all LeanPool.HopfProblem.HomologyTheory.SphereHomology1
import all LeanPool.HopfProblem.HomologyTheory.FirstHurewicz1
import all LeanPool.HopfProblem.HomologyTheory.SphereHomology2
import all LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology4


-- @@ L18-22 verbatim
/-!
# Hopf problem: homology theory · sphere homology 3

Supporting definitions and proofs for this stage of the six-sphere construction.
-/



-- @@ L25-25 verbatim
open Set Function Filter Manifold Topology


-- @@ L27-30 verbatim
open scoped BigOperators CategoryTheory Complex.UnitDisc ComplexConjugate ContDiff ContinuousMap
  Convolution ENNReal EuclideanSpace Fin.NatCast InnerProductSpace Interval Matrix MatrixGroups
  Modular NNReal Pointwise RealInnerProductSpace TensorProduct UniformConvergence Uniformity
  UpperHalfPlane


-- @@ L32-32 verbatim
universe u v


-- @@ L34-34 verbatim
noncomputable section


-- @@ L36-36 verbatim
namespace Mathoverflow1973


-- @@ L38-38 verbatim
local infixr:80 " ≫ₚ " => Path.trans


-- @@ L40-40 verbatim
local notation:100 f " ∣[" k "] " a:100 => SlashAction.map k a f


-- @@ L42-47 verbatim
private instance
    SphereHomology.suspension_middleBand_pathConnectedSpace (X : Type) [TopologicalSpace X]
    [PathConnectedSpace X] : PathConnectedSpace (CuspCentralHomology.Suspension.middleBand X) :=
  (CuspCentralHomology.Suspension.middleBandHomeomorph (X :=
        X)).symm.surjective.pathConnectedSpace
    (CuspCentralHomology.Suspension.middleBandHomeomorph (X := X)).symm.continuous


-- @@ L49-61 verbatim
private def
    SphereHomology.suspensionHomologyOneEquivKernel (X : Type) [TopologicalSpace X] [Nonempty X] :
    SingularMayerVietoris.SingularHomology (CuspCentralHomology.Suspension X) 1 ≃ₗ[ℤ]
      LinearMap.ker
        (SingularMayerVietoris.leftHomologyMap
          ((CuspCentralHomology.Suspension.northOpen : Set (CuspCentralHomology.Suspension X)))
          ((CuspCentralHomology.Suspension.southOpen : Set (CuspCentralHomology.Suspension X)))
          0) :=
  CuspCentralHomology.contractibleCoverHomologyOneEquivKernel
    ((CuspCentralHomology.Suspension.northOpen : Set (CuspCentralHomology.Suspension X)))
    ((CuspCentralHomology.Suspension.southOpen : Set (CuspCentralHomology.Suspension X)))
    CuspCentralHomology.Suspension.northOpen_isOpen
    CuspCentralHomology.Suspension.southOpen_isOpen CuspCentralHomology.Suspension.open_cover


-- @@ L63-73 verbatim
private theorem SphereHomology.suspensionLeftHomologyMap_zero_ker (X : Type) [TopologicalSpace X]
    [PathConnectedSpace X] :
    LinearMap.ker
        (SingularMayerVietoris.leftHomologyMap
          ((CuspCentralHomology.Suspension.northOpen : Set (CuspCentralHomology.Suspension X)))
          ((CuspCentralHomology.Suspension.southOpen : Set (CuspCentralHomology.Suspension X)))
          0) =
      ⊥ :=
  leftHomologyMap_zero_ker
    ((CuspCentralHomology.Suspension.northOpen : Set (CuspCentralHomology.Suspension X)))
    ((CuspCentralHomology.Suspension.southOpen : Set (CuspCentralHomology.Suspension X)))


-- @@ L75-87 verbatim
private theorem SphereHomology.suspension_homology_one_subsingleton (X : Type) [TopologicalSpace X]
    [PathConnectedSpace X] :
    Subsingleton (SingularMayerVietoris.SingularHomology (CuspCentralHomology.Suspension X) 1) := by
  let :
    Subsingleton
      (LinearMap.ker
        (SingularMayerVietoris.leftHomologyMap
          ((CuspCentralHomology.Suspension.northOpen : Set (CuspCentralHomology.Suspension X)))
          ((CuspCentralHomology.Suspension.southOpen : Set (CuspCentralHomology.Suspension X)))
          0)) := by
    rw [suspensionLeftHomologyMap_zero_ker X]
    infer_instance
  exact (suspensionHomologyOneEquivKernel X).injective.subsingleton


-- @@ L89-94 verbatim
private theorem SphereHomology.unitSphere_homology_one_subsingleton (n : ℕ) :
    Subsingleton (SingularMayerVietoris.SingularHomology (UnitSphere (n + 2)) 1) := by
  let := suspension_homology_one_subsingleton (UnitSphere (n + 1))
  exact
    (PeriodTorusHigherHomology.homeomorphHomologyEquiv (suspensionSphereHomeomorph (n + 1)).symm
        1).injective.subsingleton


-- @@ L96-115 verbatim
public
theorem SphereHomology.unitSphere_homology_subsingleton (n k : ℕ) (hk : k ≠ 0) (hkn : k ≠ n + 1) :
    Subsingleton (SingularMayerVietoris.SingularHomology (UnitSphere (n + 1)) k) := by
  induction n generalizing k with
  | zero =>
    cases k with
    | zero => exact (hk rfl).elim
    | succ k =>
      cases k with
      | zero => exact (hkn rfl).elim
      | succ k => exact sphereCircle_homology_subsingleton k
  | succ n ih =>
    cases k with
    | zero => exact (hk rfl).elim
    | succ k =>
      cases k with
      | zero => exact unitSphere_homology_one_subsingleton n
      | succ k =>
        let := ih (k + 1) (Nat.succ_ne_zero _) (by omega)
        exact (unitSphereHomologySuspensionEquiv (n + 1) k).injective.subsingleton


-- @@ L117-117 verbatim
end Mathoverflow1973


-- @@ L119-119 verbatim
end
