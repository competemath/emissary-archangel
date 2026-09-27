/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module

public import LeanPool.RellichKondrachov.Geometry.Manifold.Sobolev.ChartMeasureLp
public import LeanPool.RellichKondrachov.Geometry.Manifold.Sobolev.H1
public import LeanPool.RellichKondrachov.Geometry.Manifold.Sobolev.H2
public import LeanPool.RellichKondrachov.MeasureTheory.Function.LpSpace.Restrict


-- @@ L13-28 verbatim
/-!
# `RellichKondrachov.Geometry.Manifold.Sobolev.EmbeddingL2`

Define the canonical continuous linear maps `H¹ → L²` and `H² → L²` on a compact manifold, relative
to finite chart data.

The construction is by summing, over the finite chart index type, the chartwise `L²` components
(coming from `h1ToChartL2` / `h2ToChartL2`) pulled back to `M` via a
measure-preserving chart map and then extended by zero from the chart source.

## Main definitions

- `RellichKondrachov.Geometry.Manifold.Sobolev.FiniteChartData.chartToGlobalL2`
- `RellichKondrachov.Geometry.Manifold.Sobolev.FiniteChartData.h1ToL2`
- `RellichKondrachov.Geometry.Manifold.Sobolev.FiniteChartData.h2ToL2`
-/


-- @@ L30-30 verbatim
@[expose] public section


-- @@ L32-32 verbatim
namespace RellichKondrachov

-- @@ L33-33 verbatim
namespace Geometry

-- @@ L34-34 verbatim
namespace Manifold

-- @@ L35-35 verbatim
namespace Sobolev


-- @@ L37-37 verbatim
open Set Topology

-- @@ L38-38 verbatim
open scoped BigOperators ENNReal MeasureTheory

-- @@ L39-39 verbatim
open MeasureTheory

-- @@ L40-40 verbatim
open scoped _root_.Manifold


-- @@ L42-42 verbatim
local notation "n∞" => (⊤ : WithTop ℕ∞)


-- @@ L44-44 verbatim
noncomputable section


-- @@ L46-46 verbatim
section


-- @@ L48-48 verbatim
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

-- @@ L49-49 verbatim
variable {H : Type*} [TopologicalSpace H]

-- @@ L50-50 verbatim
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

-- @@ L51-51 verbatim
variable {I : ModelWithCorners ℝ E H}

-- @@ L52-52 verbatim
variable [IsManifold I n∞ M] [IsManifold I (1 : WithTop ℕ∞) M]

-- @@ L53-53 verbatim
variable [I.Boundaryless]

-- @@ L54-54 verbatim
variable [T2Space M] [CompactSpace M]


-- @@ L56-57 verbatim
/-- Borel σ-algebra on the manifold `M`. -/
local instance instMeasurableSpaceMEmbeddingL2 : MeasurableSpace M := borel M

-- @@ L58-58 verbatim
local instance instBorelSpaceMEmbeddingL2 : BorelSpace M := ⟨rfl⟩


-- @@ L60-61 verbatim
/-- Borel σ-algebra on the model space `E`. -/
local instance instMeasurableSpaceEEmbeddingL2 : MeasurableSpace E := borel E

-- @@ L62-62 verbatim
local instance instBorelSpaceEEmbeddingL2 : BorelSpace E := ⟨rfl⟩

-- @@ L63-64 verbatim
local instance instOpensMeasurableSpaceEEmbeddingL2 : OpensMeasurableSpace E := by
  infer_instance


-- @@ L66-66 verbatim
namespace FiniteChartData


-- @@ L68-68 verbatim
variable (d : FiniteChartData (H := H) (M := M) I)


-- @@ L70-83 verbatim
/-- The chartwise-to-global `L²` map on the manifold: pull back along a measure-preserving chart map
and extend by zero from the chart source. -/
noncomputable def chartToGlobalL2 {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (μ : Measure M) (i : d.ι) :
    (E →₂[chartMeasure (d := d) (I := I) μ i] F) →L[ℝ] (M →₂[μ] F) := by
  classical
  let s : Set M := (extChartAt I (d.center i)).source
  have hs : MeasurableSet s :=
    (isOpen_extChartAt_source (I := I) (x := d.center i)).measurableSet
  exact
    (MeasureTheory.Lp.extendByZeroₗᵢ
      (μ := μ) (p := (2 : ENNReal)) (s := s) hs).toContinuousLinearMap.comp
      ((chartPullbackL2
        (d := d) (I := I) (μ := μ) (i := i) (F := F)).toContinuousLinearMap)


-- @@ L85-91 verbatim
/-- The continuous linear inclusion `H¹(d,μ) → L²(M,μ)` defined by summing the chartwise `L²`
components after pulling them back to `M` and extending by zero. -/
noncomputable def h1ToL2 (μ : Measure M) [IsFiniteMeasure μ] :
    (↥(h1 (d := d) (I := I) (μ := μ))) →L[ℝ] (M →₂[μ] ℝ) := by
  classical
  exact ∑ i : d.ι, (chartToGlobalL2 (d := d) (I := I) (μ := μ) (F := ℝ) i).comp
    (h1ToChartL2 (d := d) (I := I) (μ := μ) i)


-- @@ L93-99 verbatim
/-- The continuous linear inclusion `H²(d,μ) → L²(M,μ)` defined by summing the chartwise `L²`
components after pulling them back to `M` and extending by zero. -/
noncomputable def h2ToL2 (μ : Measure M) [IsFiniteMeasure μ] :
    (↥(h2 (d := d) (I := I) (μ := μ))) →L[ℝ] (M →₂[μ] ℝ) := by
  classical
  exact ∑ i : d.ι, (chartToGlobalL2 (d := d) (I := I) (μ := μ) (F := ℝ) i).comp
    (h2ToChartL2 (d := d) (I := I) (μ := μ) i)


-- @@ L101-111 verbatim
/-- The canonical linear map `C¹(M) →ₗ H¹(d,μ)` landing in the dense range used to define `H¹`. -/
noncomputable def c1ToH1 (μ : Measure M) [IsFiniteMeasure μ] :
    ↥(C1 (E := E) (H := H) (M := M) (I := I)) →ₗ[ℝ] ↥(h1 (d := d) (I := I) (μ := μ)) := by
  classical
  refine
    LinearMap.codRestrict (h1 (d := d) (I := I) (μ := μ)) (h1Graph (d := d) (I := I) (μ := μ)) ?_
  intro f
  -- `h1` is the closure of the range of `h1Graph`, so the range is contained in `h1`.
  change h1Graph (d := d) (I := I) (μ := μ) f ∈
      (LinearMap.range (h1Graph (d := d) (I := I) (μ := μ))).topologicalClosure
  exact (Submodule.le_topologicalClosure _ ) ⟨f, rfl⟩


-- @@ L113-120 verbatim
/-- The linear map `C¹(M) →ₗ L²(M,μ)` obtained by summing the per-chart
`L²` localizations pulled back to `M` and extended by zero. -/
noncomputable def c1ToL2 (μ : Measure M) [IsFiniteMeasure μ] :
    ↥(C1 (E := E) (H := H) (M := M) (I := I)) →ₗ[ℝ] (M →₂[μ] ℝ) := by
  classical
  exact ∑ i : d.ι,
    (chartToGlobalL2 (d := d) (I := I) (μ := μ) (F := ℝ) i).toLinearMap.comp
      ((LinearMap.fst ℝ _ _).comp (h1GraphChart (d := d) (I := I) (μ := μ) i))


-- @@ L122-129 verbatim
omit [T2Space M] in
lemma h1ToL2_c1ToH1 (μ : Measure M) [IsFiniteMeasure μ]
    (f : ↥(C1 (E := E) (H := H) (M := M) (I := I))) :
    h1ToL2 (d := d) (I := I) (μ := μ) (c1ToH1 (d := d) (I := I) (μ := μ) f) =
      c1ToL2 (d := d) (I := I) (μ := μ) f := by
  classical
  -- Expand everything to chartwise definitions; `simp` reduces the claim to pointwise equality.
  simp [h1ToL2, c1ToH1, c1ToL2, h1ToChartL2, h1ToChart, h1Graph, Finset.sum_apply]


-- @@ L131-140 verbatim
/-- The canonical linear map `C²(M) →ₗ H²(d,μ)` landing in the dense range used to define `H²`. -/
noncomputable def c2ToH2 (μ : Measure M) [IsFiniteMeasure μ] :
    ↥(C2 (E := E) (H := H) (M := M) (I := I)) →ₗ[ℝ] ↥(h2 (d := d) (I := I) (μ := μ)) := by
  classical
  refine
    LinearMap.codRestrict (h2 (d := d) (I := I) (μ := μ)) (h2Graph (d := d) (I := I) (μ := μ)) ?_
  intro f
  change h2Graph (d := d) (I := I) (μ := μ) f ∈
      (LinearMap.range (h2Graph (d := d) (I := I) (μ := μ))).topologicalClosure
  exact (Submodule.le_topologicalClosure _ ) ⟨f, rfl⟩


-- @@ L142-149 verbatim
/-- The linear map `C²(M) →ₗ L²(M,μ)` obtained by summing the per-chart
`L²` localizations pulled back to `M` and extended by zero. -/
noncomputable def c2ToL2 (μ : Measure M) [IsFiniteMeasure μ] :
    ↥(C2 (E := E) (H := H) (M := M) (I := I)) →ₗ[ℝ] (M →₂[μ] ℝ) := by
  classical
  exact ∑ i : d.ι,
    (chartToGlobalL2 (d := d) (I := I) (μ := μ) (F := ℝ) i).toLinearMap.comp
      ((LinearMap.fst ℝ _ _).comp (h2GraphChart (d := d) (I := I) (μ := μ) i))


-- @@ L151-157 verbatim
omit [IsManifold I (1 : WithTop ℕ∞) M] [T2Space M] in
lemma h2ToL2_c2ToH2 (μ : Measure M) [IsFiniteMeasure μ]
    (f : ↥(C2 (E := E) (H := H) (M := M) (I := I))) :
    h2ToL2 (d := d) (I := I) (μ := μ) (c2ToH2 (d := d) (I := I) (μ := μ) f) =
      c2ToL2 (d := d) (I := I) (μ := μ) f := by
  classical
  simp [h2ToL2, c2ToH2, c2ToL2, h2ToChartL2, h2ToChart, h2Graph, Finset.sum_apply]


-- @@ L159-159 verbatim
end FiniteChartData


-- @@ L161-161 verbatim
end


-- @@ L163-163 verbatim
end


-- @@ L165-165 verbatim
end Sobolev

-- @@ L166-166 verbatim
end Manifold

-- @@ L167-167 verbatim
end Geometry

-- @@ L168-168 verbatim
end RellichKondrachov
