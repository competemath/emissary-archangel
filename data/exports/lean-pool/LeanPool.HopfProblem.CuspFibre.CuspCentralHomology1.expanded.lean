/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev
-/
module

public import LeanPool.HopfProblem.Prelude
public import LeanPool.HopfProblem.Recognition.Smale5
import all LeanPool.HopfProblem.HomologyTheory.SingularMayerVietoris
import all LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology1
import all LeanPool.HopfProblem.Recognition.Smale5


-- @@ L14-18 verbatim
/-!
# Hopf problem: cusp fibre · cusp central homology 1

Supporting definitions and proofs for this stage of the six-sphere construction.
-/



-- @@ L21-21 verbatim
open Set Function Filter Manifold Topology


-- @@ L23-26 verbatim
open scoped BigOperators CategoryTheory Complex.UnitDisc ComplexConjugate ContDiff ContinuousMap
  Convolution ENNReal EuclideanSpace Fin.NatCast InnerProductSpace Interval Matrix MatrixGroups
  Modular NNReal Pointwise RealInnerProductSpace TensorProduct UniformConvergence Uniformity
  UpperHalfPlane


-- @@ L28-28 verbatim
universe u v


-- @@ L30-30 verbatim
noncomputable section


-- @@ L32-32 verbatim
namespace Mathoverflow1973


-- @@ L34-34 verbatim
local infixr:80 " ≫ₚ " => Path.trans


-- @@ L36-36 verbatim
local notation:100 f " ∣[" k "] " a:100 => SlashAction.map k a f


-- @@ L38-55 verbatim
private theorem
    CuspCentralHomology.singularHomologyMap_const_eq_zero {Y : Type} [TopologicalSpace Y]
    (X : Type) [TopologicalSpace X] (y : Y) (n : ℕ) (hn : n ≠ 0) :
    SingularMayerVietoris.singularHomologyMap (ContinuousMap.const X y) n = 0 := by
  let := PeriodTorusHigherHomology.point_homology_subsingleton n hn
  change
    SingularMayerVietoris.singularHomologyMap
        ((ContinuousMap.const Unit y).comp (ContinuousMap.const X ())) n =
      0
  rw [PeriodTorusHigherHomology.singularHomologyMap_comp]
  ext a
  change
    SingularMayerVietoris.singularHomologyMap (ContinuousMap.const Unit y) n
        (SingularMayerVietoris.singularHomologyMap (ContinuousMap.const X ()) n a) =
      0
  rw [Subsingleton.elim (SingularMayerVietoris.singularHomologyMap (ContinuousMap.const X ()) n a)
      (0 : SingularMayerVietoris.SingularHomology Unit n),
    map_zero]


-- @@ L57-63 verbatim
public
theorem CuspCentralHomology.singularHomologyMap_eq_zero_of_nullhomotopic {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) (hf : f.Nullhomotopic) (n : ℕ)
    (hn : n ≠ 0) : SingularMayerVietoris.singularHomologyMap f n = 0 := by
  obtain ⟨y, hy⟩ := hf
  rw [PeriodTorusHigherHomology.homotopic_homologyMap hy n]
  exact singularHomologyMap_const_eq_zero X y n hn


-- @@ L65-65 verbatim
end Mathoverflow1973


-- @@ L67-67 verbatim
end
