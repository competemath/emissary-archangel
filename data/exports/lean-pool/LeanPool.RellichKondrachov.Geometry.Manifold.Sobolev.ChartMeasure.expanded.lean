/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module

public import LeanPool.RellichKondrachov.Geometry.Manifold.Sobolev.ChartData


-- @@ L10-18 verbatim
/-!
# `RellichKondrachov.Geometry.Manifold.Sobolev.ChartMeasure`

Pushforward measures on the model space arising from charts.

For chart-based Sobolev spaces on a manifold `M`, it is convenient to transport the ambient measure
on `M` to a measure on the model space `E` using `extChartAt`. This file defines the resulting
measures and records basic finiteness instances needed by the Euclidean Sobolev baseline.
-/


-- @@ L20-20 verbatim
@[expose] public section


-- @@ L22-22 verbatim
namespace RellichKondrachov

-- @@ L23-23 verbatim
namespace Geometry

-- @@ L24-24 verbatim
namespace Manifold

-- @@ L25-25 verbatim
namespace Sobolev


-- @@ L27-27 verbatim
open scoped _root_.Manifold MeasureTheory Topology

-- @@ L28-28 verbatim
open MeasureTheory


-- @@ L30-30 verbatim
section


-- @@ L32-32 verbatim
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

-- @@ L33-33 verbatim
variable {H : Type*} [TopologicalSpace H]

-- @@ L34-34 verbatim
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

-- @@ L35-35 verbatim
variable {I : ModelWithCorners ℝ E H} [IsManifold I (⊤ : WithTop ℕ∞) M]


-- @@ L37-38 verbatim
/-- Borel σ-algebra on the model space `E`. -/
local instance instMeasurableSpaceChartMeasure : MeasurableSpace M := borel M

-- @@ L39-39 verbatim
local instance instBorelSpaceChartMeasure : BorelSpace M := ⟨rfl⟩


-- @@ L41-42 verbatim
/-- Borel σ-algebra on the model space `E`. -/
local instance instMeasurableSpaceChartMeasure1 : MeasurableSpace E := borel E

-- @@ L43-43 verbatim
local instance instBorelSpaceChartMeasure1 : BorelSpace E := ⟨rfl⟩

-- @@ L44-44 verbatim
local instance instOpensMeasurableSpaceChartMeasure : OpensMeasurableSpace E := by infer_instance


-- @@ L46-51 verbatim
/-- Any finite measure is finite on compact sets. -/
lemma isFiniteMeasureOnCompacts_of_isFiniteMeasure {α : Type*} [TopologicalSpace α]
    [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ] :
    IsFiniteMeasureOnCompacts μ :=
  ⟨fun K _hK =>
    (measure_mono (Set.subset_univ K)).trans_lt (measure_lt_top μ Set.univ)⟩


-- @@ L53-53 verbatim
namespace FiniteChartData


-- @@ L55-55 verbatim
variable (d : FiniteChartData (H := H) (M := M) I)


-- @@ L57-66 verbatim
/-!
## Chart measures

Given a measure `μ` on `M`, each chart center `d.center i` yields a pushforward measure on `E`
along the extended chart `extChartAt I (d.center i)`.

We define this as a pushforward of the **restricted** measure
`μ.restrict (extChartAt I (d.center i)).source`
so that the value of `extChartAt` outside its source is irrelevant.
-/


-- @@ L68-70 verbatim
/-- The pushforward of a measure `μ` on `M` along the extended chart `extChartAt`. -/
noncomputable def chartMeasure (μ : Measure M) (i : d.ι) : Measure E :=
  (μ.restrict (extChartAt I (d.center i)).source).map (extChartAt I (d.center i))


-- @@ L72-72 verbatim
section


-- @@ L74-74 verbatim
omit [FiniteDimensional ℝ E]


-- @@ L76-87 verbatim
/-- The extended chart is a.e.-measurable with respect to the restricted measure on its source. -/
lemma aemeasurable_extChartAt (μ : Measure M) (i : d.ι) :
    AEMeasurable (extChartAt I (d.center i))
      (μ.restrict (extChartAt I (d.center i)).source) := by
  classical
  have hs :
      MeasurableSet (extChartAt I (d.center i)).source :=
    (isOpen_extChartAt_source (I := I) (x := d.center i)).measurableSet
  have hcont :
      Continuous ((extChartAt I (d.center i)).source.domRestrict (extChartAt I (d.center i))) :=
    (continuousOn_iff_continuous_domRestrict).1 (continuousOn_extChartAt (I := I) (x := d.center i))
  exact aemeasurable_restrict_of_measurable_subtype (μ := μ) hs hcont.measurable


-- @@ L89-89 verbatim
end


-- @@ L91-95 verbatim
instance instIsFiniteMeasurechartMeasure (μ : Measure M) (i : d.ι) [IsFiniteMeasure μ] :
    IsFiniteMeasure (chartMeasure (d := d) (I := I) μ i) := by
  classical
  delta chartMeasure
  infer_instance


-- @@ L97-100 verbatim
instance instIsFiniteMeasureOnCompactschartMeasure (μ : Measure M) (i : d.ι) [IsFiniteMeasure μ] :
    IsFiniteMeasureOnCompacts (chartMeasure (d := d) (I := I) μ i) := by
  classical
  exact isFiniteMeasureOnCompacts_of_isFiniteMeasure (μ := chartMeasure (d := d) (I := I) μ i)


-- @@ L102-102 verbatim
end FiniteChartData


-- @@ L104-104 verbatim
end


-- @@ L106-106 verbatim
end Sobolev

-- @@ L107-107 verbatim
end Manifold

-- @@ L108-108 verbatim
end Geometry

-- @@ L109-109 verbatim
end RellichKondrachov
