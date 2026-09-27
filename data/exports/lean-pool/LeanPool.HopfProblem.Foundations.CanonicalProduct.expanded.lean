/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev
-/
module

public import LeanPool.HopfProblem.Prelude
public import LeanPool.HopfProblem.Hurewicz.ThirdHurewicz
import all LeanPool.HopfProblem.Hurewicz.ThirdHurewicz


-- @@ L12-16 verbatim
/-!
# Hopf problem: foundations · canonical product

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


-- @@ L36-56 verbatim
private def CanonicalProduct.prodLine {E F M N : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [TopologicalSpace M] [ChartedSpace E M]
    [TopologicalSpace N] [ChartedSpace F N]
    (e : PartialDiffeomorph (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ F) M N ω) :
    PartialDiffeomorph (((modelWithCornersSelf ℂ E)).prod (modelWithCornersSelf ℂ ℂ))
      (((modelWithCornersSelf ℂ F)).prod (modelWithCornersSelf ℂ ℂ)) (M × ℂ) (N × ℂ) ω
    where
  toFun p := (e p.1, p.2)
  invFun p := (e.symm p.1, p.2)
  source := e.source ×ˢ Set.univ
  target := e.target ×ˢ Set.univ
  map_source' _ h := ⟨e.map_source h.1, Set.mem_univ _⟩
  map_target' _ h := ⟨e.map_target h.1, Set.mem_univ _⟩
  left_inv' _ h := Prod.ext (e.left_inv h.1) rfl
  right_inv' _ h := Prod.ext (e.right_inv h.1) rfl
  open_source := e.open_source.prod isOpen_univ
  open_target := e.open_target.prod isOpen_univ
  contMDiffOn_toFun :=
    (e.contMDiffOn_toFun.comp contMDiffOn_fst (fun _ h => h.1)).prodMk contMDiffOn_snd
  contMDiffOn_invFun :=
    (e.contMDiffOn_invFun.comp contMDiffOn_fst (fun _ h => h.1)).prodMk contMDiffOn_snd


-- @@ L58-69 verbatim
private theorem
    CanonicalProduct.isLocalDiffeomorphAt_prodLine {E F M N : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F] [TopologicalSpace M]
    [ChartedSpace E M] [TopologicalSpace N] [ChartedSpace F N] {f : M → N} {p : M × ℂ}
    (hf : IsLocalDiffeomorphAt (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ F) ω f p.1) :
    IsLocalDiffeomorphAt (((modelWithCornersSelf ℂ E)).prod (modelWithCornersSelf ℂ ℂ))
      (((modelWithCornersSelf ℂ F)).prod (modelWithCornersSelf ℂ ℂ)) ω
      (fun q : M × ℂ => (f q.1, q.2)) p := by
  obtain ⟨e, he, hfe⟩ := hf
  refine ⟨prodLine e, ⟨he, Set.mem_univ _⟩, ?_⟩
  intro q hq
  exact Prod.ext (hfe hq.1) rfl


-- @@ L71-79 verbatim
public
theorem CanonicalProduct.isLocalDiffeomorph_prodLine {E F M N : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F] [TopologicalSpace M]
    [ChartedSpace E M] [TopologicalSpace N] [ChartedSpace F N] {f : M → N}
    (hf : IsLocalDiffeomorph (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ F) ω f) :
    IsLocalDiffeomorph (((modelWithCornersSelf ℂ E)).prod (modelWithCornersSelf ℂ ℂ))
      (((modelWithCornersSelf ℂ F)).prod (modelWithCornersSelf ℂ ℂ)) ω
      (fun q : M × ℂ => (f q.1, q.2)) :=
  fun p => isLocalDiffeomorphAt_prodLine (hf p.1)


-- @@ L81-81 verbatim
end Mathoverflow1973


-- @@ L83-83 verbatim
end
