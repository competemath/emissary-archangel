import RellichKondrachov.Geometry.Manifold.Sobolev.ChartMeasure
import RellichKondrachov.Geometry.Manifold.Sobolev.LocalizationH2

/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/


-- @@ L10-30 verbatim
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
open scoped ENNReal MeasureTheory

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


-- @@ L56-56 verbatim
local instance instMeasurableSpaceE_SobolevH2 : MeasurableSpace E := borel E

-- @@ L57-57 verbatim
local instance instBorelSpaceE_SobolevH2 : BorelSpace E := ⟨rfl⟩

-- @@ L58-58 verbatim
local instance instOpensMeasurableSpaceE_SobolevH2 : OpensMeasurableSpace E := by infer_instance


-- @@ L60-60 verbatim
local instance instMeasurableSpaceM_SobolevH2 : MeasurableSpace M := borel M

-- @@ L61-61 verbatim
local instance instBorelSpaceM_SobolevH2 : BorelSpace M := ⟨rfl⟩


-- @@ L63-63 verbatim
namespace FiniteChartData


-- @@ L65-80 verbatim
/-- `C²` scalar functions `M → ℝ` (in the manifold sense), as a submodule of `M → ℝ`. -/
def C2 : Submodule ℝ (M → ℝ) where
  carrier := {f | ContMDiff I (𝓘(ℝ, ℝ)) 2 f}
  zero_mem' := by
    simpa using (contMDiff_const (I := I) (I' := (𝓘(ℝ, ℝ))) (n := (2 : WithTop ℕ∞)) (c := (0 : ℝ)))
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


-- @@ L82-82 verbatim
variable (d : FiniteChartData (H := H) (M := M) I)

-- @@ L83-83 verbatim
variable (μ : Measure M) [IsFiniteMeasure μ]


-- @@ L85-85 verbatim
/-! ### Target types -/


-- @@ L87-91 verbatim
/-- The chartwise target type `L² × (L²(E) × L²(E →L E))` used to define manifold `H²`. -/
abbrev h2TargetE (μ : Measure M) (i : d.ι) : Type _ :=
  ↥(E →₂[chartMeasure (d := d) (I := I) μ i] ℝ) ×
    (↥(E →₂[chartMeasure (d := d) (I := I) μ i] E) ×
      ↥(E →₂[chartMeasure (d := d) (I := I) μ i] (E →L[ℝ] E)))


-- @@ L93-94 verbatim
/-- The product-of-charts target type used to define manifold `H²`. -/
abbrev h2Target (μ : Measure M) : Type _ := ∀ i : d.ι, h2TargetE (d := d) (I := I) μ i


-- @@ L96-97 verbatim
private abbrev chartMeasureE (i : d.ι) : Measure E :=
  chartMeasure (d := d) (I := I) μ i


-- @@ L99-99 verbatim
private abbrev L2ℝ (i : d.ι) : Type _ := ↥(E →₂[chartMeasureE (d := d) (I := I) (μ := μ) i] ℝ)

-- @@ L100-100 verbatim
private abbrev L2E (i : d.ι) : Type _ := ↥(E →₂[chartMeasureE (d := d) (I := I) (μ := μ) i] E)

-- @@ L101-102 verbatim
private abbrev L2EE (i : d.ι) : Type _ :=
  ↥(E →₂[chartMeasureE (d := d) (I := I) (μ := μ) i] (E →L[ℝ] E))


-- @@ L104-107 verbatim
private abbrev H2TargetE (i : d.ι) : Type _ :=
  L2ℝ (d := d) (I := I) (μ := μ) i ×
    (L2E (d := d) (I := I) (μ := μ) i ×
      L2EE (d := d) (I := I) (μ := μ) i)


-- @@ L109-109 verbatim
private abbrev H2Target : Type _ := ∀ i : d.ι, H2TargetE (d := d) (I := I) (μ := μ) i


-- @@ L111-238 verbatim
private noncomputable def localizeToC2c (i : d.ι) :
    ↥(C2 (E := E) (H := H) (M := M) (I := I)) →ₗ[ℝ]
      ↥(RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.C2c (E := E)) where
  toFun f :=
    ⟨localize (d := d) f.1 i, localize_mem_C2c (d := d) (I := I) (f := f.1) f.2 i⟩
  map_add' f g := by
    ext y
    by_cases hy : y ∈ (extChartAt I (d.center i)).target
    ·
      have hfg :
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
    ·
      have hfg : localize (d := d) (f.1 + g.1) i y = 0 := by
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
    ·
      have hcf :
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
      let φ := (extChartAt I (d.center i)).symm y
      have :
          d.ρ i φ * (c * f.1 φ) =
            c * (d.ρ i φ * f.1 φ) := by
        calc
          d.ρ i φ * (c * f.1 φ) =
              (d.ρ i φ * c) * f.1 φ := by
                simp [mul_assoc]
          _ = (c * d.ρ i φ) * f.1 φ := by
                simp [mul_comm]
          _ = c * (d.ρ i φ * f.1 φ) := by
                simp [mul_assoc]
      simpa [smul_eq_mul, Pi.smul_apply, hcf, hf] using this
    ·
      have hcf : localize (d := d) (c • f.1) i y = 0 := by
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


-- @@ L240-246 verbatim
/-- The per-chart graph map `C²(M) →ₗ h2TargetE` obtained by localization to chart `i` and the
Euclidean `H²` graph construction. -/
noncomputable def h2GraphChart (i : d.ι) :
    ↥(C2 (E := E) (H := H) (M := M) (I := I)) →ₗ[ℝ] h2TargetE (d := d) (I := I) μ i :=
  (RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.graph2
      (μ := chartMeasureE (d := d) (I := I) (μ := μ) i) (E := E)).comp
    (localizeToC2c (d := d) (I := I) i)


-- @@ L248-252 verbatim
/-- The product-of-charts graph map `C²(M) →ₗ ∀ i, h2TargetE i` used to define manifold `H²`. -/
noncomputable def h2Graph :
    ↥(C2 (E := E) (H := H) (M := M) (I := I)) →ₗ[ℝ] h2Target (d := d) (I := I) μ := by
  classical
  refine LinearMap.pi fun i => h2GraphChart (d := d) (I := I) (μ := μ) i


-- @@ L254-258 verbatim
set_option synthInstance.maxHeartbeats 200000 in
private instance instContinuousConstSMul_h2Target :
    ContinuousConstSMul ℝ (h2Target (d := d) (I := I) μ) := by
  classical
  infer_instance


-- @@ L260-262 verbatim
/-- The `H²` submodule defined by chart localizations and the Euclidean `H²` graph construction. -/
noncomputable def h2 : Submodule ℝ (h2Target (d := d) (I := I) μ) :=
  (LinearMap.range (h2Graph (d := d) (I := I) (μ := μ))).topologicalClosure


-- @@ L264-267 verbatim
omit [IsManifold I (1 : WithTop ℕ∞) M] [T2Space M] in
theorem isClosed_h2 :
    IsClosed (h2 (d := d) (I := I) (μ := μ) : Set (h2Target (d := d) (I := I) μ)) := by
  simp [h2]


-- @@ L269-272 verbatim
/-- `H²` is complete (a Hilbert space once the ambient `L²` spaces are). -/
instance instCompleteSpace_h2 : CompleteSpace (↥(h2 (d := d) (I := I) (μ := μ))) := by
  classical
  exact (isClosed_h2 (d := d) (I := I) (μ := μ)).isComplete.completeSpace_coe


-- @@ L274-278 verbatim
/-- The continuous projection `H² →` chartwise
`L² × (L²(E) × L²(E →L E))` for a fixed chart index. -/
noncomputable def h2ToChart (i : d.ι) :
    (↥(h2 (d := d) (I := I) (μ := μ))) →L[ℝ] h2TargetE (d := d) (I := I) μ i :=
  (ContinuousLinearMap.proj (R := ℝ) i).comp (Submodule.subtypeL (h2 (d := d) (I := I) (μ := μ)))


-- @@ L280-283 verbatim
/-- The continuous chartwise `L²` map extracted from `H²`. -/
noncomputable def h2ToChartL2 (i : d.ι) :
    (↥(h2 (d := d) (I := I) (μ := μ))) →L[ℝ] ↥(E →₂[chartMeasure (d := d) (I := I) μ i] ℝ) :=
  (ContinuousLinearMap.fst ℝ _ _).comp (h2ToChart (d := d) (I := I) (μ := μ) i)


-- @@ L285-289 verbatim
/-- The continuous chartwise gradient map `H² → L²(E)` extracted from `H²`. -/
noncomputable def h2ToChartL2Grad (i : d.ι) :
    (↥(h2 (d := d) (I := I) (μ := μ))) →L[ℝ] ↥(E →₂[chartMeasure (d := d) (I := I) μ i] E) :=
  (ContinuousLinearMap.fst ℝ _ _).comp
    ((ContinuousLinearMap.snd ℝ _ _).comp (h2ToChart (d := d) (I := I) (μ := μ) i))


-- @@ L291-296 verbatim
/-- The continuous chartwise Hessian map `H² → L²(E →L E)` extracted from `H²`. -/
noncomputable def h2ToChartL2Hess (i : d.ι) :
    (↥(h2 (d := d) (I := I) (μ := μ))) →L[ℝ]
      ↥(E →₂[chartMeasure (d := d) (I := I) μ i] (E →L[ℝ] E)) :=
  (ContinuousLinearMap.snd ℝ _ _).comp
    ((ContinuousLinearMap.snd ℝ _ _).comp (h2ToChart (d := d) (I := I) (μ := μ) i))


-- @@ L298-298 verbatim
end FiniteChartData


-- @@ L300-300 verbatim
end


-- @@ L302-302 verbatim
end


-- @@ L304-304 verbatim
end Sobolev

-- @@ L305-305 verbatim
end Manifold

-- @@ L306-306 verbatim
end Geometry

-- @@ L307-307 verbatim
end RellichKondrachov
