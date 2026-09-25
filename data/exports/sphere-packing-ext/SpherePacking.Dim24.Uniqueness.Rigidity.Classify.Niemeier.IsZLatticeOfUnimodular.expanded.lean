module
public import SpherePacking.Dim24.Uniqueness.LatticeInvariants
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.Topology.Bases


-- @@ L8-23 verbatim
/-!
# Unimodular implies full rank

In this repo, `Unimodular L` is defined as `ZLattice.covolume L volume = 1`.
Since `ZLattice.covolume` is defined using `MeasureTheory.addCovolume`, and `ENNReal.toReal ⊤ = 0`,
any lattice whose action admits *only* infinite-volume fundamental domains has covolume `0`.

We use this to show: if `L` is discrete and unimodular in `ℝ²⁴`, then it spans `ℝ²⁴` over `ℝ`.

## Main definitions
* `IsZLatticeOfUnimodular.spanR`

## Main statements
* `IsZLatticeOfUnimodular.countable_of_discrete`
* `IsZLatticeOfUnimodular.volume_univ_orthogonal_eq_top`
-/



-- @@ L26-26 verbatim
namespace SpherePacking.Dim24.Uniqueness.RigidityClassify


-- @@ L28-28 verbatim
noncomputable section


-- @@ L30-30 verbatim
open scoped RealInnerProductSpace Topology

-- @@ L31-31 verbatim
open MeasureTheory


-- @@ L33-33 verbatim
local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)


-- @@ L35-35 verbatim
namespace IsZLatticeOfUnimodular


-- @@ L37-37 verbatim
variable (L : Submodule ℤ ℝ²⁴)


-- @@ L39-42 verbatim
/-- The real span of `L`, as an `ℝ`-subspace of `ℝ²⁴`. -/
@[expose]
public abbrev spanR : Submodule ℝ ℝ²⁴ :=
  Submodule.span ℝ (L : Set ℝ²⁴)


-- @@ L44-47 verbatim
/-- The underlying set of `L` is contained in its real span `spanR L`. -/
public lemma subset_spanR : (L : Set ℝ²⁴) ⊆ (spanR (L := L)) := by
  intro x hx
  exact Submodule.subset_span hx


-- @@ L49-49 verbatim
/-! ### Countability -/


-- @@ L51-55 verbatim
/-- A discrete `ℤ`-submodule of `ℝ²⁴` is countable. -/
public lemma countable_of_discrete [DiscreteTopology L] : Countable L := by
  -- A discrete separable space is countable; `L` is separable as a subspace of `ℝ²⁴`.
  haveI : TopologicalSpace.SeparableSpace L := by infer_instance
  exact (TopologicalSpace.separableSpace_iff_countable (α := L)).1 (by infer_instance)


-- @@ L57-57 verbatim
/-! ### Orthogonal complement nontriviality -/


-- @@ L59-63 verbatim
/-- If `spanR L` is not all of `ℝ²⁴`, then its orthogonal complement is nontrivial. -/
public lemma orthogonal_ne_bot_of_spanR_ne_top (h : spanR (L := L) ≠ ⊤) :
    (spanR (L := L))ᗮ ≠ ⊥ := by
  intro hbot
  exact h (by simpa [Submodule.orthogonal_eq_bot_iff] using hbot)


-- @@ L65-71 verbatim
/-- If `spanR L` is not all of `ℝ²⁴`, then the orthogonal complement has infinite volume. -/
public lemma volume_univ_orthogonal_eq_top (h : spanR (L := L) ≠ ⊤) :
    volume (Set.univ : Set (↥((spanR (L := L))ᗮ))) = ⊤ := by
  have hne : (spanR (L := L))ᗮ ≠ ⊥ := orthogonal_ne_bot_of_spanR_ne_top (L := L) h
  haveI : Nontrivial ((spanR (L := L))ᗮ) :=
    Submodule.nontrivial_iff_ne_bot.mpr hne
  simp_all


-- @@ L73-73 verbatim
end IsZLatticeOfUnimodular


-- @@ L75-75 verbatim
end


-- @@ L77-77 verbatim
end SpherePacking.Dim24.Uniqueness.RigidityClassify
