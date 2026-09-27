/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev
-/
module

public import LeanPool.HopfProblem.Prelude
public import LeanPool.HopfProblem.Pi1.TwistGroup
import all LeanPool.HopfProblem.Toric.DiagonalQuotient1
import all LeanPool.HopfProblem.Toric.DiagonalQuotient2
import all LeanPool.HopfProblem.Foundations.SplitGroupExtension
import all LeanPool.HopfProblem.Pi1.TwistGroup


-- @@ L15-19 verbatim
/-!
# Hopf problem: toric · diagonal quotient 4

Supporting definitions and proofs for this stage of the six-sphere construction.
-/



-- @@ L22-22 verbatim
open Set Function Filter Manifold Topology


-- @@ L24-27 verbatim
open scoped BigOperators CategoryTheory Complex.UnitDisc ComplexConjugate ContDiff ContinuousMap
  Convolution ENNReal EuclideanSpace Fin.NatCast InnerProductSpace Interval Matrix MatrixGroups
  Modular NNReal Pointwise RealInnerProductSpace TensorProduct UniformConvergence Uniformity
  UpperHalfPlane


-- @@ L29-29 verbatim
universe u v


-- @@ L31-31 verbatim
noncomputable section


-- @@ L33-33 verbatim
namespace Mathoverflow1973


-- @@ L35-35 verbatim
local infixr:80 " ≫ₚ " => Path.trans


-- @@ L37-37 verbatim
local notation:100 f " ∣[" k "] " a:100 => SlashAction.map k a f


-- @@ L39-60 verbatim
public
theorem DiagonalQuotient.fundamentalGroup_basepointChange_of_homotopy {F E : Type*}
    [TopologicalSpace F] [TopologicalSpace E] (f₀ f₁ : C(F, E)) (H : f₀.Homotopy f₁) (c : F)
    (v : FundamentalGroup F c) :
    FundamentalGroup.fundamentalGroupMulEquivOfPath (H.evalAt c) (FundamentalGroup.map f₀ c v) =
      FundamentalGroup.map f₁ c v := by
  obtain ⟨p, rfl⟩ := Path.Homotopic.Quotient.mk_surjective v
  rw [fundamentalGroup_basepoint_change_apply]
  change
    (Path.Homotopic.Quotient.mk (H.evalAt c)).symm.trans
        ((Path.Homotopic.Quotient.mk (p.map f₀.continuous)).trans
          (Path.Homotopic.Quotient.mk (H.evalAt c))) =
      Path.Homotopic.Quotient.mk (p.map f₁.continuous)
  have hsquare :
    (Path.Homotopic.Quotient.mk (p.map f₀.continuous)).trans
        (Path.Homotopic.Quotient.mk (H.evalAt c)) =
      (Path.Homotopic.Quotient.mk (H.evalAt c)).trans
        (Path.Homotopic.Quotient.mk (p.map f₁.continuous)) := by
    rw [← Path.Homotopic.Quotient.mk_trans, ← Path.Homotopic.Quotient.mk_trans]
    exact Path.Homotopic.Quotient.eq.mpr (Path.Homotopic.map_trans_evalAt H p)
  rw [hsquare, ← Path.Homotopic.Quotient.trans_assoc, Path.Homotopic.Quotient.symm_trans,
    Path.Homotopic.Quotient.refl_trans]


-- @@ L62-78 verbatim
private def DiagonalQuotient.fibreBasepointHomotopy {G B F : Type*} [Group G] [MulAction G B]
    [MulAction G F] [TopologicalSpace B] [TopologicalSpace F] {b₀ b₁ : B} (p : Path b₀ b₁) :
    ContinuousMap.Homotopy
      (⟨fibreInclusion G B F b₀, fibreInclusion_continuous G B F b₀⟩ : C(F, Space G B F))
      ⟨fibreInclusion G B F b₁, fibreInclusion_continuous G B F b₁⟩
    where
  toFun x := quotient G B F (p x.1, x.2)
  continuous_toFun :=
    (quotient_continuous G B F).comp ((p.continuous.comp continuous_fst).prodMk continuous_snd)
  map_zero_left
    f := by
    change quotient G B F (p 0, f) = quotient G B F (b₀, f)
    rw [p.source]
  map_one_left
    f := by
    change quotient G B F (p 1, f) = quotient G B F (b₁, f)
    rw [p.target]


-- @@ L80-84 verbatim
private def
    DiagonalQuotient.fibreBasepointPath {G B F : Type*} [Group G] [MulAction G B] [MulAction G F]
    [TopologicalSpace B] [TopologicalSpace F] (c : F) {b₀ b₁ : B} (p : Path b₀ b₁) :
    Path (fibreInclusion G B F b₀ c) (fibreInclusion G B F b₁ c) :=
  (fibreBasepointHomotopy (G := G) (F := F) p).evalAt c


-- @@ L86-93 verbatim
private theorem DiagonalQuotient.fibreFundamentalGroupHom_baseChange {G B F : Type*} [Group G]
    [MulAction G B] [MulAction G F] [TopologicalSpace B] [TopologicalSpace F] (c : F) {b₀ b₁ : B}
    (p : Path b₀ b₁) (v : FundamentalGroup F c) :
    FundamentalGroup.fundamentalGroupMulEquivOfPath (fibreBasepointPath (G := G) c p)
        (fibreFundamentalGroupHom (G := G) b₀ c v) =
      fibreFundamentalGroupHom (G := G) b₁ c v :=
  fundamentalGroup_basepointChange_of_homotopy _ _ (fibreBasepointHomotopy (G := G) (F := F) p) c
    v


-- @@ L95-95 verbatim
end Mathoverflow1973


-- @@ L97-97 verbatim
end
