import RellichKondrachov.Geometry.Manifold.Sobolev.RellichKondrachov
import RellichKondrachov.Geometry.Manifold.Sobolev.RellichKondrachovRiemannian.Chartwise

/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/


-- @@ L10-15 verbatim
/-!
# `RellichKondrachov.Geometry.Manifold.Sobolev.RellichKondrachovRiemannian.Global`

Finite-atlas assembly: turn the per-chart compactness result into compactness of the global
`H¹ → L²` map for the Riemannian volume measure.
-/


-- @@ L17-17 verbatim
namespace RellichKondrachov

-- @@ L18-18 verbatim
namespace Geometry

-- @@ L19-19 verbatim
namespace Manifold

-- @@ L20-20 verbatim
namespace Sobolev


-- @@ L22-22 verbatim
open Set Filter Topology

-- @@ L23-23 verbatim
open scoped BigOperators ENNReal MeasureTheory Manifold NNReal

-- @@ L24-24 verbatim
open MeasureTheory

-- @@ L25-25 verbatim
open _root_.Manifold _root_.Bundle


-- @@ L27-27 verbatim
local notation "n∞" => (⊤ : WithTop ℕ∞)


-- @@ L29-29 verbatim
noncomputable section


-- @@ L31-31 verbatim
set_option linter.unnecessarySimpa false


-- @@ L33-43 verbatim
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


-- @@ L45-46 verbatim
local instance instMeasurableSpaceM_SobolevRellichKondrachovRiemannian_Global :
    MeasurableSpace M := borel M

-- @@ L47-47 verbatim
local instance instBorelSpaceM_SobolevRellichKondrachovRiemannian_Global : BorelSpace M := ⟨rfl⟩


-- @@ L49-50 verbatim
local instance instMeasurableSpaceE_SobolevRellichKondrachovRiemannian_Global :
    MeasurableSpace E := borel E

-- @@ L51-51 verbatim
local instance instBorelSpaceE_SobolevRellichKondrachovRiemannian_Global : BorelSpace E := ⟨rfl⟩

-- @@ L52-56 verbatim
local instance instOpensMeasurableSpaceE_SobolevRellichKondrachovRiemannian_Global :
    OpensMeasurableSpace E := by
  infer_instance

-- On compact manifolds, the Riemannian volume measure is finite.

-- @@ L57-62 verbatim
local instance instIsFiniteMeasure_riemannianVolumeMeasure_Global :
    IsFiniteMeasure
        (RellichKondrachov.Geometry.Manifold.Riemannian.riemannianVolumeMeasure
          (I := I) (M := M)) :=
  Riemannian.riemannianVolumeMeasure_isFiniteMeasure
    (I := I) (M := M)


-- @@ L64-64 verbatim
namespace RiemannianFiniteChartData


-- @@ L66-66 verbatim
variable (dR : RiemannianFiniteChartData (H := H) (M := M) I)


-- @@ L68-102 verbatim
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


-- @@ L104-122 verbatim
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


-- @@ L124-124 verbatim
end RiemannianFiniteChartData


-- @@ L126-126 verbatim
end


-- @@ L128-128 verbatim
end Sobolev

-- @@ L129-129 verbatim
end Manifold

-- @@ L130-130 verbatim
end Geometry

-- @@ L131-131 verbatim
end RellichKondrachov
