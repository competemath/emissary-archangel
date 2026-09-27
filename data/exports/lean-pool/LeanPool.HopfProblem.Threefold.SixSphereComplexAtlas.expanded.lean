/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev
-/
module

public import LeanPool.HopfProblem.Prelude
public import LeanPool.HopfProblem.MainTheorem.Core2
public import LeanPool.HopfProblem.Recognition.Smale13
import all LeanPool.HopfProblem.Foundations.Core2
import all LeanPool.HopfProblem.Toric.ToricSpace1
import all LeanPool.HopfProblem.Threefold.SpecialPeriods7
import all LeanPool.HopfProblem.Threefold.SpecialPeriods8
import all LeanPool.HopfProblem.Recognition.Smale7
import all LeanPool.HopfProblem.Threefold.SpecialPeriods11
import all LeanPool.HopfProblem.Threefold.SpecialPeriods12
import all LeanPool.HopfProblem.MainTheorem.Core2
import all LeanPool.HopfProblem.Recognition.Degree3
import all LeanPool.HopfProblem.Recognition.Smale13


-- @@ L22-26 verbatim
/-!
# Hopf problem: threefold · six sphere complex atlas

Supporting definitions and proofs for this stage of the six-sphere construction.
-/



-- @@ L29-29 verbatim
open Set Function Filter Manifold Topology


-- @@ L31-34 verbatim
open scoped BigOperators CategoryTheory Complex.UnitDisc ComplexConjugate ContDiff ContinuousMap
  Convolution ENNReal EuclideanSpace Fin.NatCast InnerProductSpace Interval Matrix MatrixGroups
  Modular NNReal Pointwise RealInnerProductSpace TensorProduct UniformConvergence Uniformity
  UpperHalfPlane


-- @@ L36-36 verbatim
universe u v


-- @@ L38-38 verbatim
noncomputable section


-- @@ L40-40 verbatim
namespace Mathoverflow1973


-- @@ L42-42 verbatim
local infixr:80 " ≫ₚ " => Path.trans


-- @@ L44-44 verbatim
local notation:100 f " ∣[" k "] " a:100 => SlashAction.map k a f


-- @@ L46-55 verbatim
attribute [local instance] SpecialPeriods.Threefold.chartedSpace
    SpecialPeriods.Threefold.space_isManifold SpecialPeriods.Threefold.space_isSmoothRealManifold
    SpecialPeriods.Threefold.space_compact SpecialPeriods.Threefold.space_t2Space
    SpecialPeriods.Threefold.space_secondCountable in
private def
    SixSphereComplexAtlas.threefoldHomeomorph : SpecialPeriods.Threefold.Space ≃ₜ unitSphere 6 :=
  Classical.choice
    (Smale.homeomorphic_sixSphere_of_homotopySixSphere (ℂ × ComplexPlane₂)
      SpecialPeriods.Threefold.Space SpecialPeriods.Threefold.real_dimension
      Degree.threefoldHomotopyEquiv)


-- @@ L57-62 verbatim
attribute [local instance] SpecialPeriods.Threefold.chartedSpace
    SpecialPeriods.Threefold.space_isManifold SpecialPeriods.Threefold.space_isSmoothRealManifold
    SpecialPeriods.Threefold.space_compact SpecialPeriods.Threefold.space_t2Space
    SpecialPeriods.Threefold.space_secondCountable in
private def SixSphereComplexAtlas.modelEquiv : (ℂ × ComplexPlane₂) ≃L[ℂ] EuclideanSpace ℂ (Fin 3) :=
  SpecialPeriods.Threefold.cuspModelEquiv.symm.trans (EuclideanSpace.equiv (Fin 3) ℂ).symm


-- @@ L64-77 verbatim
attribute [local instance] SpecialPeriods.Threefold.chartedSpace
    SpecialPeriods.Threefold.space_isManifold SpecialPeriods.Threefold.space_isSmoothRealManifold
    SpecialPeriods.Threefold.space_compact SpecialPeriods.Threefold.space_t2Space
    SpecialPeriods.Threefold.space_secondCountable in
public
theorem SixSphereComplexAtlas.exists_complex_analytic_atlas :
    ∃ atlas : ChartedSpace (EuclideanSpace ℂ (Fin 3)) (unitSphere 6),
      letI := atlas
      IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin 3)) ω (unitSphere 6) := by
  let := ManifoldAtlasTransport.chartedSpace (H := ℂ × ComplexPlane₂) threefoldHomeomorph
  let := ManifoldAtlasTransport.isManifold 𝓘(ℂ, ℂ × ComplexPlane₂) ω threefoldHomeomorph
  exact
    ⟨SpecialPeriods.Threefold.ModelChange.chartedSpace modelEquiv (unitSphere 6),
      SpecialPeriods.Threefold.ModelChange.isManifold modelEquiv (unitSphere 6) ω⟩


-- @@ L79-92 verbatim
attribute [local instance] SpecialPeriods.Threefold.chartedSpace
    SpecialPeriods.Threefold.space_isManifold SpecialPeriods.Threefold.space_isSmoothRealManifold
    SpecialPeriods.Threefold.space_compact SpecialPeriods.Threefold.space_t2Space
    SpecialPeriods.Threefold.space_secondCountable in
public
theorem SixSphereComplexAtlas.exists_complex_atlas :
    ∃ atlas : ChartedSpace (EuclideanSpace ℂ (Fin 3)) (unitSphere 6),
      letI := atlas
      IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin 3)) 1 (unitSphere 6) := by
  obtain ⟨atlas, h⟩ := exists_complex_analytic_atlas
  refine ⟨atlas, ?_⟩
  let := atlas
  let := h
  infer_instance


-- @@ L94-94 verbatim
end Mathoverflow1973


-- @@ L96-96 verbatim
end
