/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module

public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import LeanPool.RellichKondrachov.Geometry.Manifold.Sobolev.EmbeddingL2


-- @@ L11-26 verbatim
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


-- @@ L28-28 verbatim
@[expose] public section


-- @@ L30-30 verbatim
namespace RellichKondrachov

-- @@ L31-31 verbatim
namespace Geometry

-- @@ L32-32 verbatim
namespace Manifold

-- @@ L33-33 verbatim
namespace Sobolev


-- @@ L35-35 verbatim
open Set Topology

-- @@ L36-36 verbatim
open scoped BigOperators ENNReal MeasureTheory

-- @@ L37-37 verbatim
open MeasureTheory

-- @@ L38-38 verbatim
open scoped _root_.Manifold


-- @@ L40-40 verbatim
local notation "n∞" => (⊤ : WithTop ℕ∞)


-- @@ L42-42 verbatim
noncomputable section


-- @@ L44-44 verbatim
section


-- @@ L46-46 verbatim
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

-- @@ L47-47 verbatim
variable {H : Type*} [TopologicalSpace H]

-- @@ L48-48 verbatim
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

-- @@ L49-49 verbatim
variable {I : ModelWithCorners ℝ E H}

-- @@ L50-50 verbatim
variable [IsManifold I n∞ M] [IsManifold I (1 : WithTop ℕ∞) M]

-- @@ L51-51 verbatim
variable [I.Boundaryless]

-- @@ L52-52 verbatim
variable [T2Space M] [CompactSpace M]


-- @@ L54-55 verbatim
/-- Borel σ-algebra on the manifold `M`. -/
local instance instMeasurableSpaceMRellichKondrachov : MeasurableSpace M := borel M

-- @@ L56-56 verbatim
local instance instBorelSpaceMRellichKondrachov : BorelSpace M := ⟨rfl⟩


-- @@ L58-59 verbatim
/-- Borel σ-algebra on the model space `E`. -/
local instance instMeasurableSpaceERellichKondrachov : MeasurableSpace E := borel E

-- @@ L60-60 verbatim
local instance instBorelSpaceERellichKondrachov : BorelSpace E := ⟨rfl⟩

-- @@ L61-62 verbatim
local instance instOpensMeasurableSpaceERellichKondrachov : OpensMeasurableSpace E := by
  infer_instance


-- @@ L64-64 verbatim
namespace FiniteChartData


-- @@ L66-66 verbatim
variable (d : FiniteChartData (H := H) (M := M) I)


-- @@ L68-81 verbatim
private lemma isCompactOperator_fintype_sum {X Y : Type*} [TopologicalSpace X] [AddCommMonoid X]
    [TopologicalSpace Y] [AddCommMonoid Y] [ContinuousAdd Y]
    {ι : Type*} [Fintype ι] (f : ι → X → Y) (hf : ∀ i, IsCompactOperator (f i)) :
    IsCompactOperator fun x : X => ∑ i : ι, f i x := by
  classical
  -- Work with the `Finset.univ` sum and use `IsCompactOperator.add`.
  have huniv : IsCompactOperator (fun x : X => (Finset.univ : Finset ι).sum fun i => f i x) := by
    refine Finset.induction_on (s := (Finset.univ : Finset ι)) ?_ ?_
    · exact (isCompactOperator_zero : IsCompactOperator (fun _ : X => (0 : Y)))
    · intro a s ha hs
      have hfa : IsCompactOperator (f a) := hf a
      simp only [Finset.sum_insert ha]
      exact hfa.add hs
  simpa using huniv


-- @@ L83-103 verbatim
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


-- @@ L105-124 verbatim
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


-- @@ L126-126 verbatim
end FiniteChartData


-- @@ L128-128 verbatim
end


-- @@ L130-130 verbatim
end


-- @@ L132-132 verbatim
end Sobolev

-- @@ L133-133 verbatim
end Manifold

-- @@ L134-134 verbatim
end Geometry

-- @@ L135-135 verbatim
end RellichKondrachov
