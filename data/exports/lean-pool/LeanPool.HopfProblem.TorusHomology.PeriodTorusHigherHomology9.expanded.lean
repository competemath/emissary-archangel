/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev
-/
module

public import LeanPool.HopfProblem.Prelude
public import LeanPool.HopfProblem.HomologyOfX.TrianglePeriodFamilyHomologyAlgebra
import all LeanPool.HopfProblem.HomologyTheory.SingularMayerVietoris
import all LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology1
import all LeanPool.HopfProblem.HomologyOfX.TrianglePeriodFamilyHomologyAlgebra


-- @@ L14-18 verbatim
/-!
# Hopf problem: torus homology · period torus higher homology 9

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


-- @@ L38-43 verbatim
/-- Right translation by a fixed element as a continuous map. -/
@[expose]
public
def PeriodTorusHigherHomology.rightTranslation {G : Type*} [TopologicalSpace G] [AddGroup G]
    [IsTopologicalAddGroup G] (a : G) : C(G, G) :=
  ⟨fun x => x + a, continuous_id.add continuous_const⟩


-- @@ L45-49 verbatim
@[simp]
public
theorem PeriodTorusHigherHomology.rightTranslation_apply {G : Type*} [TopologicalSpace G]
    [AddGroup G] [IsTopologicalAddGroup G] (a x : G) : rightTranslation a x = x + a :=
  rfl


-- @@ L51-58 verbatim
private def PeriodTorusHigherHomology.rightTranslationHomotopyAlong {G : Type*} [TopologicalSpace G]
    [AddGroup G] [IsTopologicalAddGroup G] {a : G} (p : Path (0 : G) a) :
    (ContinuousMap.id G).Homotopy (rightTranslation a)
    where
  toFun z := z.2 + p z.1
  continuous_toFun := continuous_snd.add (p.continuous.comp continuous_fst)
  map_zero_left x := by simp
  map_one_left x := by simp


-- @@ L60-63 verbatim
private theorem PeriodTorusHigherHomology.rightTranslation_singularHomologyMap_of_path {G : Type}
    [TopologicalSpace G] [AddGroup G] [IsTopologicalAddGroup G] {a : G} (p : Path (0 : G) a)
    (n : ℕ) : SingularMayerVietoris.singularHomologyMap (rightTranslation a) n = LinearMap.id := by
  rw [← homotopy_homologyMap (rightTranslationHomotopyAlong p) n, singularHomologyMap_id]


-- @@ L65-69 verbatim
@[simp]
private theorem PeriodTorusHigherHomology.rightTranslation_singularHomologyMap {G : Type}
    [TopologicalSpace G] [AddGroup G] [IsTopologicalAddGroup G] [PathConnectedSpace G] (a : G)
    (n : ℕ) : SingularMayerVietoris.singularHomologyMap (rightTranslation a) n = LinearMap.id :=
  rightTranslation_singularHomologyMap_of_path (PathConnectedSpace.somePath 0 a) n


-- @@ L71-71 verbatim
end Mathoverflow1973


-- @@ L73-73 verbatim
end
