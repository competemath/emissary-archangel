/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module

public import LeanPool.RellichKondrachov.Geometry.Manifold.Riemannian.VolumeMeasure
public import LeanPool.RellichKondrachov.Geometry.Manifold.Sobolev.ChartDataRiemannian
public import LeanPool.RellichKondrachov.Geometry.Manifold.Sobolev.EmbeddingL2
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
import LeanPool.RellichKondrachov.Geometry.Manifold.Riemannian.VolumeMeasure.Finiteness
import LeanPool.RellichKondrachov.Geometry.Manifold.Sobolev.RellichKondrachov
import LeanPool.RellichKondrachov.Geometry.Manifold.Sobolev.RellichKondrachovRiemannian.Chartwise


-- @@ L16-21 verbatim
/-!
# `RellichKondrachov.Geometry.Manifold.Sobolev.RellichKondrachovRiemannian.Global`

Finite-atlas assembly: turn the per-chart compactness result into compactness of the global
`H¹ → L²` map for the Riemannian volume measure.
-/


-- @@ L23-23 verbatim
@[expose] public section


-- @@ L25-25 verbatim
namespace RellichKondrachov

-- @@ L26-26 verbatim
namespace Geometry

-- @@ L27-27 verbatim
namespace Manifold

-- @@ L28-28 verbatim
namespace Sobolev


-- @@ L30-30 verbatim
open Set Filter Topology

-- @@ L31-31 verbatim
open scoped BigOperators ENNReal MeasureTheory _root_.Manifold NNReal

-- @@ L32-32 verbatim
open MeasureTheory

-- @@ L33-33 verbatim
open _root_.Manifold _root_.Bundle


-- @@ L35-35 verbatim
local notation "n∞" => (⊤ : WithTop ℕ∞)


-- @@ L37-37 verbatim
noncomputable section


-- @@ L39-49 verbatim
variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  (I : ModelWithCorners ℝ E H)
  [IsManifold I n∞ M] [IsManifold I (1 : WithTop ℕ∞) M]
  [Bundle.RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
  [I.Boundaryless]
  [T3Space M]
  [T2Space M] [CompactSpace M]


-- @@ L51-53 verbatim
/-- Borel σ-algebra on the manifold `M`. -/
local instance instMeasurableSpaceMGlobal :
    MeasurableSpace M := borel M

-- @@ L54-54 verbatim
local instance instBorelSpaceMGlobal : BorelSpace M := ⟨rfl⟩


-- @@ L56-58 verbatim
/-- Borel σ-algebra on the model space `E`. -/
local instance instMeasurableSpaceEGlobal :
    MeasurableSpace E := borel E

-- @@ L59-59 verbatim
local instance instBorelSpaceEGlobal : BorelSpace E := ⟨rfl⟩

-- @@ L60-64 verbatim
local instance instOpensMeasurableSpaceGlobal :
    OpensMeasurableSpace E := by
  infer_instance

-- On compact manifolds, the Riemannian volume measure is finite.

-- @@ L65-70 verbatim
local instance instIsFiniteMeasureriemannianVolumeMeasureGlobal :
    IsFiniteMeasure
        (RellichKondrachov.Geometry.Manifold.Riemannian.riemannianVolumeMeasure
          (I := I) (M := M)) :=
  Riemannian.riemannianVolumeMeasure_isFiniteMeasure
    (I := I) (M := M)


-- @@ L72-72 verbatim
namespace RiemannianFiniteChartData


-- @@ L74-74 verbatim
variable (dR : RiemannianFiniteChartData (H := H) (M := M) I)


-- @@ L76-110 verbatim
omit [T2Space M] in
private lemma isCompactOperator_chartToGlobalL2_h1ToChartL2 (i : dR.d.ι) :
    let μM :=
      RellichKondrachov.Geometry.Manifold.Riemannian.riemannianVolumeMeasure (I := I) (M := M)
    IsCompactOperator fun x : ↥(FiniteChartData.h1 (d := dR.d) (I := I) (μ := μM)) =>
      (FiniteChartData.chartToGlobalL2 (d := dR.d) (I := I) (μ := μM) (F := ℝ) i)
        ((FiniteChartData.h1ToChartL2 (d := dR.d) (I := I) (μ := μM) i) x) := by
  classical
  intro μM
  let μchart := FiniteChartData.chartMeasure (d := dR.d) (I := I) μM i
  let K : Set E := FiniteChartData.rhoSupportImage (d := dR.d) (I := I) i
  have hKm : MeasurableSet K := rhoSupportImage_measurable (dR := dR) (I := I) i
  have hcomp : IsCompactOperator (h1ToChartL2Range (dR := dR) (I := I) (i := i) : _ → _) := by
    simpa [μchart, K] using (isCompactOperator_h1ToChartL2Range (dR := dR) (I := I) (E := E) i)
  -- Postcompose by the inclusion into `L²(μchart)` and then by `chartToGlobalL2`.
  have hcomp' :
      IsCompactOperator fun x : ↥(FiniteChartData.h1 (d := dR.d) (I := I) (μ := μM)) =>
        ((LinearMap.range
              ((MeasureTheory.Lp.extendByZeroₗᵢ
                    (μ := μchart) (E := ℝ) (p := (2 : ℝ≥0∞)) (s := K) hKm).toLinearMap)).subtypeL)
          ((h1ToChartL2Range (dR := dR) (I := I) (i := i)) x) :=
    hcomp.clm_comp
      ((LinearMap.range
            ((MeasureTheory.Lp.extendByZeroₗᵢ
                  (μ := μchart) (E := ℝ) (p := (2 : ℝ≥0∞)) (s := K) hKm).toLinearMap)).subtypeL)
  have hcomp'' :
      IsCompactOperator fun x : ↥(FiniteChartData.h1 (d := dR.d) (I := I) (μ := μM)) =>
        (FiniteChartData.chartToGlobalL2 (d := dR.d) (I := I) (μ := μM) (F := ℝ) i)
          (((LinearMap.range
                ((MeasureTheory.Lp.extendByZeroₗᵢ
                      (μ := μchart) (E := ℝ) (p := (2 : ℝ≥0∞)) (s := K) hKm).toLinearMap)).subtypeL)
            ((h1ToChartL2Range (dR := dR) (I := I) (i := i)) x)) :=
    hcomp'.clm_comp (FiniteChartData.chartToGlobalL2 (d := dR.d) (I := I) (μ := μM) (F := ℝ) i)
  -- Identify the composite through the range with the original summand.
  simpa [h1ToChartL2Range, μchart, K] using hcomp''


-- @@ L112-130 verbatim
omit [T2Space M] in
theorem isCompactOperator_h1ToL2_riemannianVolume :
    IsCompactOperator fun x :
        ↥(FiniteChartData.h1 (d := dR.d) (I := I)
              (μ :=
                RellichKondrachov.Geometry.Manifold.Riemannian.riemannianVolumeMeasure (I := I)
                  (M := M))) =>
      FiniteChartData.h1ToL2 (d := dR.d) (I := I)
        (μ :=
          RellichKondrachov.Geometry.Manifold.Riemannian.riemannianVolumeMeasure
            (I := I) (M := M)) x := by
  classical
  let μM :=
    RellichKondrachov.Geometry.Manifold.Riemannian.riemannianVolumeMeasure (I := I) (M := M)
  -- Apply the finite-sum glue lemma once each chart contribution is compact.
  refine
    (FiniteChartData.isCompactOperator_h1ToL2_of_summands (d := dR.d) (I := I) (μ := μM) ?_)
  intro i
  simpa [μM] using (isCompactOperator_chartToGlobalL2_h1ToChartL2 (dR := dR) (I := I) (E := E) i)


-- @@ L132-132 verbatim
end RiemannianFiniteChartData


-- @@ L134-134 verbatim
end


-- @@ L136-136 verbatim
end Sobolev

-- @@ L137-137 verbatim
end Manifold

-- @@ L138-138 verbatim
end Geometry

-- @@ L139-139 verbatim
end RellichKondrachov
