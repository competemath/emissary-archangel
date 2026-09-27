/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module

public import LeanPool.RellichKondrachov.Geometry.Manifold.Sobolev.ChartMeasure


-- @@ L10-31 verbatim
/-!
# `RellichKondrachov.Geometry.Manifold.Sobolev.ChartMeasureLp`

`L²`-level utilities for chart pushforward measures.

Given `d : FiniteChartData` and a measure `μ` on `M`, `ChartMeasure` defines the pushforward
measure `chartMeasure μ i` on the model space `E` along the extended chart
`extChartAt I (d.center i)`.

This file provides:

- a measurable modification of `extChartAt` (relative to the restricted
  measure on the chart source);
- a `MeasurePreserving` witness for that modification;
- the induced `L²` pullback map as a linear isometry (`MeasureTheory.Lp.compMeasurePreservingₗᵢ`).

## Main definitions

- `RellichKondrachov.Geometry.Manifold.Sobolev.FiniteChartData.extChartAtMk`
- `RellichKondrachov.Geometry.Manifold.Sobolev.FiniteChartData.measurePreserving_extChartAtMk`
- `RellichKondrachov.Geometry.Manifold.Sobolev.FiniteChartData.chartPullbackL2`
-/


-- @@ L33-33 verbatim
@[expose] public section


-- @@ L35-35 verbatim
namespace RellichKondrachov

-- @@ L36-36 verbatim
namespace Geometry

-- @@ L37-37 verbatim
namespace Manifold

-- @@ L38-38 verbatim
namespace Sobolev


-- @@ L40-40 verbatim
open scoped _root_.Manifold MeasureTheory Topology

-- @@ L41-41 verbatim
open MeasureTheory


-- @@ L43-43 verbatim
section


-- @@ L45-45 verbatim
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

-- @@ L46-46 verbatim
variable {H : Type*} [TopologicalSpace H]

-- @@ L47-47 verbatim
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

-- @@ L48-48 verbatim
variable {I : ModelWithCorners ℝ E H} [IsManifold I (⊤ : WithTop ℕ∞) M]


-- @@ L50-51 verbatim
/-- Borel σ-algebra on the manifold `M`. -/
local instance instMeasurableSpaceMChartMeasureLp : MeasurableSpace M := borel M

-- @@ L52-52 verbatim
local instance instBorelSpaceMChartMeasureLp : BorelSpace M := ⟨rfl⟩


-- @@ L54-55 verbatim
/-- Borel σ-algebra on the model space `E`. -/
local instance instMeasurableSpaceEChartMeasureLp : MeasurableSpace E := borel E

-- @@ L56-56 verbatim
local instance instBorelSpaceEChartMeasureLp : BorelSpace E := ⟨rfl⟩

-- @@ L57-59 verbatim
local instance instOpensMeasurableSpaceChartMeasureLp :
    OpensMeasurableSpace E := by
  infer_instance


-- @@ L61-61 verbatim
namespace FiniteChartData


-- @@ L63-63 verbatim
variable (d : FiniteChartData (H := H) (M := M) I)


-- @@ L65-68 verbatim
/-- A measurable modification of the extended chart `extChartAt`, relative to the restricted measure
on the chart source. -/
noncomputable def extChartAtMk (μ : Measure M) (i : d.ι) : M → E :=
  (aemeasurable_extChartAt (d := d) (I := I) (μ := μ) i).mk


-- @@ L70-73 verbatim
lemma extChartAt_ae_eq_extChartAtMk (μ : Measure M) (i : d.ι) :
    extChartAt I (d.center i) =ᵐ[μ.restrict (extChartAt I (d.center i)).source]
      extChartAtMk (d := d) (I := I) μ i :=
  (aemeasurable_extChartAt (d := d) (I := I) (μ := μ) i).ae_eq_mk


-- @@ L75-90 verbatim
/-- The measurable modification `extChartAtMk` is measure-preserving from the restricted measure on
the chart source to `chartMeasure`. -/
lemma measurePreserving_extChartAtMk (μ : Measure M) (i : d.ι) :
    MeasurePreserving (extChartAtMk (d := d) (I := I) μ i)
      (μ.restrict (extChartAt I (d.center i)).source) (chartMeasure (d := d) (I := I) μ i) := by
  classical
  refine ⟨?_, ?_⟩
  · exact (aemeasurable_extChartAt (d := d) (I := I) (μ := μ) i).measurable_mk
  · -- `chartMeasure` is the pushforward by `extChartAt`; replace it by the measurable modification.
    have hmap :
        Measure.map (extChartAtMk (d := d) (I := I) μ i)
            (μ.restrict (extChartAt I (d.center i)).source) =
          Measure.map (extChartAt I (d.center i))
            (μ.restrict (extChartAt I (d.center i)).source) := by
      exact Measure.map_congr (extChartAt_ae_eq_extChartAtMk (d := d) (I := I) (μ := μ) i).symm
    simpa [FiniteChartData.chartMeasure] using hmap


-- @@ L92-104 verbatim
/-- Pull back `L²` functions on the chart model space `E` to `L²` functions on `M`, using the
measure-preserving measurable modification `extChartAtMk`. -/
noncomputable def chartPullbackL2 {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (μ : Measure M) (i : d.ι) :
    (E →₂[chartMeasure (d := d) (I := I) μ i] F) →ₗᵢ[ℝ]
      (M →₂[μ.restrict (extChartAt I (d.center i)).source] F) := by
  classical
  simpa using
    (MeasureTheory.Lp.compMeasurePreservingₗᵢ (𝕜 := ℝ) (E := F) (p := (2 : ENNReal))
          (μ := μ.restrict (extChartAt I (d.center i)).source)
          (μb := chartMeasure (d := d) (I := I) μ i)
          (f := extChartAtMk (d := d) (I := I) μ i)
          (measurePreserving_extChartAtMk (d := d) (I := I) (μ := μ) i))


-- @@ L106-106 verbatim
end FiniteChartData


-- @@ L108-108 verbatim
end


-- @@ L110-110 verbatim
end Sobolev

-- @@ L111-111 verbatim
end Manifold

-- @@ L112-112 verbatim
end Geometry

-- @@ L113-113 verbatim
end RellichKondrachov
