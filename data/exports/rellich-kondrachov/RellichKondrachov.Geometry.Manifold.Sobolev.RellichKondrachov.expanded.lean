import Mathlib.Analysis.Normed.Operator.Compact
import RellichKondrachov.Geometry.Manifold.Sobolev.EmbeddingL2

/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/


-- @@ L10-25 verbatim
/-!
# `RellichKondrachov.Geometry.Manifold.Sobolev.RellichKondrachov`

Infrastructure for proving Rellich–Kondrachov compact embeddings on compact manifolds.

This file is intentionally small: it packages the *operator-theoretic glue* showing that the
manifold embedding `H¹ → L²` (defined as a finite sum of chart contributions in
`Sobolev.EmbeddingL2`) is compact once each chart contribution is compact.

The analytic heart of Rellich (compactness on Euclidean chart domains) is tracked separately.

## Main results

- `RellichKondrachov.Geometry.Manifold.Sobolev.FiniteChartData.isCompactOperator_h1ToL2_of_summands`
- `RellichKondrachov.Geometry.Manifold.Sobolev.FiniteChartData.isCompactOperator_h2ToL2_of_summands`
-/


-- @@ L27-27 verbatim
namespace RellichKondrachov

-- @@ L28-28 verbatim
namespace Geometry

-- @@ L29-29 verbatim
namespace Manifold

-- @@ L30-30 verbatim
namespace Sobolev


-- @@ L32-32 verbatim
open Set Topology

-- @@ L33-33 verbatim
open scoped BigOperators ENNReal MeasureTheory

-- @@ L34-34 verbatim
open MeasureTheory

-- @@ L35-35 verbatim
open scoped _root_.Manifold


-- @@ L37-37 verbatim
local notation "n∞" => (⊤ : WithTop ℕ∞)


-- @@ L39-39 verbatim
noncomputable section


-- @@ L41-41 verbatim
section


-- @@ L43-43 verbatim
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

-- @@ L44-44 verbatim
variable {H : Type*} [TopologicalSpace H]

-- @@ L45-45 verbatim
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

-- @@ L46-46 verbatim
variable {I : ModelWithCorners ℝ E H}

-- @@ L47-47 verbatim
variable [IsManifold I n∞ M] [IsManifold I (1 : WithTop ℕ∞) M]

-- @@ L48-48 verbatim
variable [I.Boundaryless]

-- @@ L49-49 verbatim
variable [T2Space M] [CompactSpace M]


-- @@ L51-51 verbatim
local instance instMeasurableSpaceM_SobolevRellichKondrachov : MeasurableSpace M := borel M

-- @@ L52-52 verbatim
local instance instBorelSpaceM_SobolevRellichKondrachov : BorelSpace M := ⟨rfl⟩


-- @@ L54-54 verbatim
local instance instMeasurableSpaceE_SobolevRellichKondrachov : MeasurableSpace E := borel E

-- @@ L55-55 verbatim
local instance instBorelSpaceE_SobolevRellichKondrachov : BorelSpace E := ⟨rfl⟩

-- @@ L56-57 verbatim
local instance instOpensMeasurableSpaceE_SobolevRellichKondrachov : OpensMeasurableSpace E := by
  infer_instance


-- @@ L59-59 verbatim
namespace FiniteChartData


-- @@ L61-61 verbatim
variable (d : FiniteChartData (H := H) (M := M) I)


-- @@ L63-75 verbatim
private lemma isCompactOperator_fintype_sum {X Y : Type*} [TopologicalSpace X] [AddCommMonoid X]
    [TopologicalSpace Y] [AddCommMonoid Y] [ContinuousAdd Y]
    {ι : Type*} [Fintype ι] (f : ι → X → Y) (hf : ∀ i, IsCompactOperator (f i)) :
    IsCompactOperator fun x : X => ∑ i : ι, f i x := by
  classical
  -- Work with the `Finset.univ` sum and use `IsCompactOperator.add`.
  have huniv : IsCompactOperator (fun x : X => (Finset.univ : Finset ι).sum fun i => f i x) := by
    refine Finset.induction_on (s := (Finset.univ : Finset ι)) ?_ ?_
    · simpa using (isCompactOperator_zero : IsCompactOperator (fun _ : X => (0 : Y)))
    · intro a s ha hs
      have hfa : IsCompactOperator (f a) := hf a
      simpa [Finset.sum_insert ha, add_comm, add_left_comm, add_assoc] using hfa.add hs
  simpa using huniv


-- @@ L77-97 verbatim
omit [T2Space M] in
/-- If each chart contribution in the definition of `h1ToL2` is a compact operator, then the
manifold inclusion `H¹ → L²` is a compact operator. -/
theorem isCompactOperator_h1ToL2_of_summands (μ : Measure M) [IsFiniteMeasure μ]
    (h :
      ∀ i : d.ι,
        IsCompactOperator
          (fun x => (chartToGlobalL2 (d := d) (I := I) (μ := μ) (F := ℝ) i)
              (h1ToChartL2 (d := d) (I := I) (μ := μ) i x))) :
    IsCompactOperator fun x => h1ToL2 (d := d) (I := I) (μ := μ) x := by
  classical
  -- `h1ToL2` is a finite sum over the chart index type.
  simpa [h1ToL2] using
    (isCompactOperator_fintype_sum
      (X := ↥(h1 (d := d) (I := I) (μ := μ)))
      (Y := (M →₂[μ] ℝ))
      (ι := d.ι)
      (f := fun i x =>
        (chartToGlobalL2 (d := d) (I := I) (μ := μ) (F := ℝ) i)
          ((h1ToChartL2 (d := d) (I := I) (μ := μ) i) x))
      h)


-- @@ L99-118 verbatim
omit [IsManifold I (1 : WithTop ℕ∞) M] [T2Space M] in
/-- If each chart contribution in the definition of `h2ToL2` is a compact operator, then the
manifold inclusion `H² → L²` is a compact operator. -/
theorem isCompactOperator_h2ToL2_of_summands (μ : Measure M) [IsFiniteMeasure μ]
    (h :
      ∀ i : d.ι,
        IsCompactOperator
          (fun x => (chartToGlobalL2 (d := d) (I := I) (μ := μ) (F := ℝ) i)
              (h2ToChartL2 (d := d) (I := I) (μ := μ) i x))) :
    IsCompactOperator fun x => h2ToL2 (d := d) (I := I) (μ := μ) x := by
  classical
  simpa [h2ToL2] using
    (isCompactOperator_fintype_sum
      (X := ↥(h2 (d := d) (I := I) (μ := μ)))
      (Y := (M →₂[μ] ℝ))
      (ι := d.ι)
      (f := fun i x =>
        (chartToGlobalL2 (d := d) (I := I) (μ := μ) (F := ℝ) i)
          ((h2ToChartL2 (d := d) (I := I) (μ := μ) i) x))
      h)


-- @@ L120-120 verbatim
end FiniteChartData


-- @@ L122-122 verbatim
end


-- @@ L124-124 verbatim
end


-- @@ L126-126 verbatim
end Sobolev

-- @@ L127-127 verbatim
end Manifold

-- @@ L128-128 verbatim
end Geometry

-- @@ L129-129 verbatim
end RellichKondrachov
