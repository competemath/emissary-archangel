/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module

public import LeanPool.RellichKondrachov.Geometry.Manifold.Sobolev.ChartMeasure
public import LeanPool.RellichKondrachov.Geometry.Manifold.Sobolev.LocalizationH2


-- @@ L11-31 verbatim
/-!
# `RellichKondrachov.Geometry.Manifold.Sobolev.H2`

Define a scalar `H²` space on a compact manifold relative to finite chart data.

Given `d : FiniteChartData` and a finite measure `μ` on `M`, we define a manifold `H²` space as the
topological closure of the range of a chartwise graph map into

`L²(E, μᵢ) × (L²(E, μᵢ;E) × L²(E, μᵢ; E →L E))`

where `μᵢ` is the pushforward chart measure (`chartMeasure`) and the graph map is obtained by:

1. localizing a `C²` function `f : M → ℝ` to a chart (extend-by-zero outside the chart target);
2. viewing it as an element of Euclidean `C²_c`;
3. applying the Euclidean `H²` graph map.

## Main definitions

- `RellichKondrachov.Geometry.Manifold.Sobolev.FiniteChartData.C2`
- `RellichKondrachov.Geometry.Manifold.Sobolev.FiniteChartData.h2`
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
open Set Topology

-- @@ L41-41 verbatim
open scoped ENNReal MeasureTheory

-- @@ L42-42 verbatim
open MeasureTheory

-- @@ L43-43 verbatim
open scoped _root_.Manifold


-- @@ L45-45 verbatim
local notation "n∞" => (⊤ : WithTop ℕ∞)


-- @@ L47-47 verbatim
noncomputable section


-- @@ L49-49 verbatim
section


-- @@ L51-51 verbatim
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

-- @@ L52-52 verbatim
variable {H : Type*} [TopologicalSpace H]

-- @@ L53-53 verbatim
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

-- @@ L54-54 verbatim
variable {I : ModelWithCorners ℝ E H}

-- @@ L55-55 verbatim
variable [IsManifold I n∞ M] [IsManifold I (1 : WithTop ℕ∞) M]

-- @@ L56-56 verbatim
variable [I.Boundaryless]

-- @@ L57-57 verbatim
variable [T2Space M] [CompactSpace M]


-- @@ L59-60 verbatim
/-- Borel σ-algebra on the model space `E`. -/
local instance instMeasurableSpaceEH2 : MeasurableSpace E := borel E

-- @@ L61-61 verbatim
local instance instBorelSpaceEH2 : BorelSpace E := ⟨rfl⟩

-- @@ L62-62 verbatim
local instance instOpensMeasurableSpaceEH2 : OpensMeasurableSpace E := by infer_instance


-- @@ L64-65 verbatim
/-- Borel σ-algebra on the manifold `M`. -/
local instance instMeasurableSpaceMH2 : MeasurableSpace M := borel M

-- @@ L66-66 verbatim
local instance instBorelSpaceMH2 : BorelSpace M := ⟨rfl⟩


-- @@ L68-68 verbatim
namespace FiniteChartData


-- @@ L70-85 verbatim
/-- `C²` scalar functions `M → ℝ` (in the manifold sense), as a submodule of `M → ℝ`. -/
def C2 : Submodule ℝ (M → ℝ) where
  carrier := {f | ContMDiff I (𝓘(ℝ, ℝ)) 2 f}
  zero_mem' := by
    exact (contMDiff_const (I := I) (I' := (𝓘(ℝ, ℝ))) (n := (2 : WithTop ℕ∞)) (c := (0 : ℝ)))
  add_mem' := by
    intro f g hf hg
    simpa using (hf.add hg)
  smul_mem' := by
    intro c f hf
    have hc :
        ContMDiff I (𝓘(ℝ, ℝ)) 2 (fun _ : M => c) := by
      simpa using
        (contMDiff_const (I := I) (I' := (𝓘(ℝ, ℝ))) (n := (2 : WithTop ℕ∞)) (c := c))
    -- Scalar multiplication on `ℝ` is multiplication.
    simpa [Pi.mul_def, Pi.smul_def, smul_eq_mul] using (hc.mul hf)


-- @@ L87-87 verbatim
variable (d : FiniteChartData (H := H) (M := M) I)

-- @@ L88-88 verbatim
variable (μ : Measure M) [IsFiniteMeasure μ]


-- @@ L90-90 verbatim
/-! ### Target types -/


-- @@ L92-96 verbatim
/-- The chartwise target type `L² × (L²(E) × L²(E →L E))` used to define manifold `H²`. -/
abbrev h2TargetE (μ : Measure M) (i : d.ι) : Type _ :=
  ↥(E →₂[chartMeasure (d := d) (I := I) μ i] ℝ) ×
    (↥(E →₂[chartMeasure (d := d) (I := I) μ i] E) ×
      ↥(E →₂[chartMeasure (d := d) (I := I) μ i] (E →L[ℝ] E)))


-- @@ L98-99 verbatim
/-- The product-of-charts target type used to define manifold `H²`. -/
abbrev h2Target (μ : Measure M) : Type _ := ∀ i : d.ι, h2TargetE (d := d) (I := I) μ i


-- @@ L101-103 verbatim
/-- The chart measure viewed on the model vector space. -/
abbrev chartMeasureE (i : d.ι) : Measure E :=
  chartMeasure (d := d) (I := I) μ i


-- @@ L105-105 verbatim
private abbrev L2ℝ (i : d.ι) : Type _ := ↥(E →₂[chartMeasureE (d := d) (I := I) (μ := μ) i] ℝ)

-- @@ L106-106 verbatim
private abbrev L2E (i : d.ι) : Type _ := ↥(E →₂[chartMeasureE (d := d) (I := I) (μ := μ) i] E)

-- @@ L107-108 verbatim
private abbrev L2EE (i : d.ι) : Type _ :=
  ↥(E →₂[chartMeasureE (d := d) (I := I) (μ := μ) i] (E →L[ℝ] E))


-- @@ L110-113 verbatim
private abbrev H2TargetE (i : d.ι) : Type _ :=
  L2ℝ (d := d) (I := I) (μ := μ) i ×
    (L2E (d := d) (I := I) (μ := μ) i ×
      L2EE (d := d) (I := I) (μ := μ) i)


-- @@ L115-115 verbatim
private abbrev H2Target : Type _ := ∀ i : d.ι, H2TargetE (d := d) (I := I) (μ := μ) i


-- @@ L117-239 verbatim
/-- Localize a twice continuously differentiable manifold function to a compactly supported chart
function. -/
noncomputable def localizeToC2c (i : d.ι) :
    ↥(C2 (E := E) (H := H) (M := M) (I := I)) →ₗ[ℝ]
      ↥(RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.C2c (E := E)) where
  toFun f :=
    ⟨localize (d := d) f.1 i, localize_mem_C2c (d := d) (I := I) (f := f.1) f.2 i⟩
  map_add' f g := by
    ext y
    by_cases hy : y ∈ (extChartAt I (d.center i)).target
    · have hfg :
          localize (d := d) (f.1 + g.1) i y =
            d.ρ i ((extChartAt I (d.center i)).symm y) *
              (f.1 + g.1) ((extChartAt I (d.center i)).symm y) := by
        simpa [FiniteChartData.localize] using
          (Set.indicator_of_mem (s := (extChartAt I (d.center i)).target) (a := y)
            (f := fun y =>
              d.ρ i ((extChartAt I (d.center i)).symm y) *
                (f.1 + g.1) ((extChartAt I (d.center i)).symm y)) hy)
      have hf :
          localize (d := d) f.1 i y =
            d.ρ i ((extChartAt I (d.center i)).symm y) *
              f.1 ((extChartAt I (d.center i)).symm y) := by
        simpa [FiniteChartData.localize] using
          (Set.indicator_of_mem
            (s := (extChartAt I (d.center i)).target) (a := y)
            (f := fun y =>
              d.ρ i ((extChartAt I (d.center i)).symm y) *
                f.1 ((extChartAt I (d.center i)).symm y))
            hy)
      have hg :
          localize (d := d) g.1 i y =
            d.ρ i ((extChartAt I (d.center i)).symm y) *
              g.1 ((extChartAt I (d.center i)).symm y) := by
        simpa [FiniteChartData.localize] using
          (Set.indicator_of_mem
            (s := (extChartAt I (d.center i)).target) (a := y)
            (f := fun y =>
              d.ρ i ((extChartAt I (d.center i)).symm y) *
                g.1 ((extChartAt I (d.center i)).symm y))
            hy)
      simp [hfg, hf, hg, mul_add]
    · have hfg : localize (d := d) (f.1 + g.1) i y = 0 := by
        simpa [FiniteChartData.localize] using
          (Set.indicator_of_notMem
            (s := (extChartAt I (d.center i)).target) (a := y)
            (f := fun y =>
              d.ρ i ((extChartAt I (d.center i)).symm y) *
                (f.1 + g.1)
                  ((extChartAt I (d.center i)).symm y))
            hy)
      have hf : localize (d := d) f.1 i y = 0 := by
        simpa [FiniteChartData.localize] using
          (Set.indicator_of_notMem
            (s := (extChartAt I (d.center i)).target) (a := y)
            (f := fun y =>
              d.ρ i ((extChartAt I (d.center i)).symm y) *
                f.1 ((extChartAt I (d.center i)).symm y))
            hy)
      have hg : localize (d := d) g.1 i y = 0 := by
        simpa [FiniteChartData.localize] using
          (Set.indicator_of_notMem
            (s := (extChartAt I (d.center i)).target) (a := y)
            (f := fun y =>
              d.ρ i ((extChartAt I (d.center i)).symm y) *
                g.1 ((extChartAt I (d.center i)).symm y))
            hy)
      simp [hfg, hf, hg]
  map_smul' c f := by
    ext y
    by_cases hy : y ∈ (extChartAt I (d.center i)).target
    · have hcf :
          localize (d := d) (c • f.1) i y =
            d.ρ i ((extChartAt I (d.center i)).symm y) *
              (c • f.1)
                ((extChartAt I (d.center i)).symm y) := by
        simpa [FiniteChartData.localize] using
          (Set.indicator_of_mem
            (s := (extChartAt I (d.center i)).target) (a := y)
            (f := fun y =>
              d.ρ i ((extChartAt I (d.center i)).symm y) *
                (c • f.1)
                  ((extChartAt I (d.center i)).symm y))
            hy)
      have hf :
          localize (d := d) f.1 i y =
            d.ρ i ((extChartAt I (d.center i)).symm y) *
              f.1 ((extChartAt I (d.center i)).symm y) := by
        simpa [FiniteChartData.localize] using
          (Set.indicator_of_mem
            (s := (extChartAt I (d.center i)).target) (a := y)
            (f := fun y =>
              d.ρ i ((extChartAt I (d.center i)).symm y) *
                f.1 ((extChartAt I (d.center i)).symm y))
            hy)
      have key :
          d.ρ i ((extChartAt I (d.center i)).symm y) *
              (c • f.1) ((extChartAt I (d.center i)).symm y) =
            c * (d.ρ i ((extChartAt I (d.center i)).symm y) *
              f.1 ((extChartAt I (d.center i)).symm y)) := by
        simp only [Pi.smul_apply, smul_eq_mul]
        ring
      simp only [SetLike.val_smul, RingHom.id_apply,
        Pi.smul_apply, smul_eq_mul, hcf, hf]
      simpa only [smul_eq_mul, Pi.smul_apply] using key
    · have hcf : localize (d := d) (c • f.1) i y = 0 := by
        simpa [FiniteChartData.localize] using
          (Set.indicator_of_notMem
            (s := (extChartAt I (d.center i)).target) (a := y)
            (f := fun y =>
              d.ρ i ((extChartAt I (d.center i)).symm y) *
                (c • f.1)
                  ((extChartAt I (d.center i)).symm y))
            hy)
      have hf : localize (d := d) f.1 i y = 0 := by
        simpa [FiniteChartData.localize] using
          (Set.indicator_of_notMem
            (s := (extChartAt I (d.center i)).target) (a := y)
            (f := fun y =>
              d.ρ i ((extChartAt I (d.center i)).symm y) *
                f.1 ((extChartAt I (d.center i)).symm y))
            hy)
      simp [hcf, hf]


-- @@ L241-247 verbatim
/-- The per-chart graph map `C²(M) →ₗ h2TargetE` obtained by localization to chart `i` and the
Euclidean `H²` graph construction. -/
noncomputable def h2GraphChart (i : d.ι) :
    ↥(C2 (E := E) (H := H) (M := M) (I := I)) →ₗ[ℝ] h2TargetE (d := d) (I := I) μ i :=
  (RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.graph2
      (μ := chartMeasureE (d := d) (I := I) (μ := μ) i) (E := E)).comp
    (localizeToC2c (d := d) (I := I) i)


-- @@ L249-253 verbatim
/-- The product-of-charts graph map `C²(M) →ₗ ∀ i, h2TargetE i` used to define manifold `H²`. -/
noncomputable def h2Graph :
    ↥(C2 (E := E) (H := H) (M := M) (I := I)) →ₗ[ℝ] h2Target (d := d) (I := I) μ := by
  classical
  refine LinearMap.pi fun i => h2GraphChart (d := d) (I := I) (μ := μ) i


-- @@ L255-261 verbatim
private instance instContinuousConstSMulH2TargetE (i : d.ι) :
    ContinuousConstSMul ℝ (h2TargetE (d := d) (I := I) μ i) :=
  inferInstanceAs
    (ContinuousConstSMul ℝ
      (↥(E →₂[chartMeasure (d := d) (I := I) μ i] ℝ) ×
        (↥(E →₂[chartMeasure (d := d) (I := I) μ i] E) ×
          ↥(E →₂[chartMeasure (d := d) (I := I) μ i] (E →L[ℝ] E)))))


-- @@ L263-266 verbatim
private instance instContinuousConstSMulH2Target :
    ContinuousConstSMul ℝ (h2Target (d := d) (I := I) μ) :=
  inferInstanceAs
    (ContinuousConstSMul ℝ (∀ i : d.ι, h2TargetE (d := d) (I := I) μ i))


-- @@ L268-270 verbatim
/-- The `H²` submodule defined by chart localizations and the Euclidean `H²` graph construction. -/
noncomputable def h2 : Submodule ℝ (h2Target (d := d) (I := I) μ) :=
  (LinearMap.range (h2Graph (d := d) (I := I) (μ := μ))).topologicalClosure


-- @@ L272-275 verbatim
omit [IsManifold I (1 : WithTop ℕ∞) M] [T2Space M] in
theorem isClosed_h2 :
    IsClosed (h2 (d := d) (I := I) (μ := μ) : Set (h2Target (d := d) (I := I) μ)) := by
  simp [h2]


-- @@ L277-280 verbatim
/-- `H²` is complete (a Hilbert space once the ambient `L²` spaces are). -/
instance instCompleteSpaceh2 : CompleteSpace (↥(h2 (d := d) (I := I) (μ := μ))) := by
  classical
  exact (isClosed_h2 (d := d) (I := I) (μ := μ)).isComplete.completeSpace_coe


-- @@ L282-286 verbatim
/-- The continuous projection `H² →` chartwise
`L² × (L²(E) × L²(E →L E))` for a fixed chart index. -/
noncomputable def h2ToChart (i : d.ι) :
    (↥(h2 (d := d) (I := I) (μ := μ))) →L[ℝ] h2TargetE (d := d) (I := I) μ i :=
  (ContinuousLinearMap.proj (R := ℝ) i).comp (Submodule.subtypeL (h2 (d := d) (I := I) (μ := μ)))


-- @@ L288-291 verbatim
/-- The continuous chartwise `L²` map extracted from `H²`. -/
noncomputable def h2ToChartL2 (i : d.ι) :
    (↥(h2 (d := d) (I := I) (μ := μ))) →L[ℝ] ↥(E →₂[chartMeasure (d := d) (I := I) μ i] ℝ) :=
  (ContinuousLinearMap.fst ℝ _ _).comp (h2ToChart (d := d) (I := I) (μ := μ) i)


-- @@ L293-297 verbatim
/-- The continuous chartwise gradient map `H² → L²(E)` extracted from `H²`. -/
noncomputable def h2ToChartL2Grad (i : d.ι) :
    (↥(h2 (d := d) (I := I) (μ := μ))) →L[ℝ] ↥(E →₂[chartMeasure (d := d) (I := I) μ i] E) :=
  (ContinuousLinearMap.fst ℝ _ _).comp
    ((ContinuousLinearMap.snd ℝ _ _).comp (h2ToChart (d := d) (I := I) (μ := μ) i))


-- @@ L299-304 verbatim
/-- The continuous chartwise Hessian map `H² → L²(E →L E)` extracted from `H²`. -/
noncomputable def h2ToChartL2Hess (i : d.ι) :
    (↥(h2 (d := d) (I := I) (μ := μ))) →L[ℝ]
      ↥(E →₂[chartMeasure (d := d) (I := I) μ i] (E →L[ℝ] E)) :=
  (ContinuousLinearMap.snd ℝ _ _).comp
    ((ContinuousLinearMap.snd ℝ _ _).comp (h2ToChart (d := d) (I := I) (μ := μ) i))


-- @@ L306-306 verbatim
end FiniteChartData


-- @@ L308-308 verbatim
end


-- @@ L310-310 verbatim
end


-- @@ L312-312 verbatim
end Sobolev

-- @@ L313-313 verbatim
end Manifold

-- @@ L314-314 verbatim
end Geometry

-- @@ L315-315 verbatim
end RellichKondrachov
