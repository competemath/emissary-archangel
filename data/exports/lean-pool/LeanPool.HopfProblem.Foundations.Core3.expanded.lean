/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev
-/
module

public import LeanPool.HopfProblem.Prelude
public import LeanPool.HopfProblem.Hurewicz.SecondHurewicz
import all LeanPool.HopfProblem.Foundations.Core2
import all LeanPool.HopfProblem.Hurewicz.SecondHurewicz


-- @@ L13-17 verbatim
/-!
# Hopf problem: foundations · core 3

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
/-- The standard integral lattice spanned by the coordinate basis of `RealPlane₄`. -/
public
def standardLattice : Submodule ℤ RealPlane₄ :=
  Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin 4)))


-- @@ L42-43 verbatim
private instance standardLattice_discrete : DiscreteTopology standardLattice :=
  inferInstanceAs (DiscreteTopology (Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin 4)))))


-- @@ L45-46 verbatim
private instance standardLattice_isZLattice : IsZLattice ℝ standardLattice :=
  inferInstanceAs (IsZLattice ℝ (Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin 4)))))


-- @@ L48-51 verbatim
private instance standardLattice_closed : IsClosed (standardLattice : Set RealPlane₄) := by
  have : DiscreteTopology standardLattice.toAddSubgroup :=
    inferInstanceAs (DiscreteTopology standardLattice)
  exact AddSubgroup.isClosed_of_discreteTopology (U := standardLattice.toAddSubgroup)


-- @@ L53-56 verbatim
/-- The four-dimensional real torus obtained from the standard lattice quotient. -/
public
abbrev RealTorus₄ :=
  RealPlane₄ ⧸ standardLattice


-- @@ L58-60 verbatim
private instance realTorus_secondCountable : SecondCountableTopology RealTorus₄ :=
  (IsOpenQuotientMap.of_isOpenMap_isQuotientMap standardLattice.isOpenMap_mkQ
    standardLattice.isQuotientMap_mkQ).secondCountableTopology


-- @@ L62-63 verbatim
private instance realTorus_pathConnected : PathConnectedSpace RealTorus₄ :=
  standardLattice.mkQ_surjective.pathConnectedSpace standardLattice.continuous_mkQ


-- @@ L65-73 verbatim
private instance realTorus_compact : CompactSpace RealTorus₄ := by
  have hper : ∀ z w, w ∈ standardLattice → standardLattice.mkQ (z + w) = standardLattice.mkQ z := by
    intro z w hw
    have hw' : standardLattice.mkQ w = 0 := (Submodule.Quotient.mk_eq_zero standardLattice).mpr hw
    rw [map_add, hw', add_zero]
  have h :=
    IsZLattice.isCompact_range_of_periodic standardLattice standardLattice.mkQ
      standardLattice.continuous_mkQ hper
  exact ⟨by simpa only [Set.range_eq_univ.mpr standardLattice.mkQ_surjective] using h⟩


-- @@ L75-90 verbatim
private theorem
    contMDiff_of_comp_localDiffeomorph {E F F' H K K' M N P : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedAddCommGroup F']
    [NormedSpace ℂ F'] [TopologicalSpace H] [TopologicalSpace K] [TopologicalSpace K']
    [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace K N]
    [TopologicalSpace P] [ChartedSpace K' P] (I : ModelWithCorners ℂ E H)
    (J : ModelWithCorners ℂ F K) (L : ModelWithCorners ℂ F' K') {f : M → N}
    (hf : IsLocalDiffeomorph I J ω f) (hsurj : Function.Surjective f) {g : N → P}
    (hgf : ContMDiff I L ω (g ∘ f)) : ContMDiff J L ω g := by
  intro y
  obtain ⟨x, rfl⟩ := hsurj y
  have h := hgf.contMDiffAt.comp (f x) (hf x).localInverse_contMDiffAt
  apply h.congr_of_eventuallyEq
  filter_upwards [(hf x).localInverse_eventuallyEq_right] with z hz
  change g z = g (f ((hf x).localInverse z))
  rw [show f ((hf x).localInverse z) = z from hz]


-- @@ L92-92 verbatim
end Mathoverflow1973


-- @@ L94-94 verbatim
end
