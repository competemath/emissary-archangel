import RellichKondrachov.Geometry.Manifold.Sobolev.ChartMeasure
import RellichKondrachov.Geometry.Manifold.Sobolev.Localization

/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/


-- @@ L10-26 verbatim
/-!
# `RellichKondrachov.Geometry.Manifold.Sobolev.H1`

Define a scalar `H¹` space on a compact manifold relative to finite chart data.

Given `d : FiniteChartData` and a finite measure `μ` on `M`, we:

- define the submodule `C1` of `C¹` scalar functions `M → ℝ` (in the manifold sense);
- define the per-chart graph map obtained by localizing into Euclidean `C1c` and then applying the
  Euclidean `H¹` graph `C1c →ₗ L² × L²(E)`;
- define `h1` as the topological closure of the range of the product-of-charts graph map.

## Main definitions

- `RellichKondrachov.Geometry.Manifold.Sobolev.FiniteChartData.C1`
- `RellichKondrachov.Geometry.Manifold.Sobolev.FiniteChartData.h1`
-/


-- @@ L28-28 verbatim
namespace RellichKondrachov

-- @@ L29-29 verbatim
namespace Geometry

-- @@ L30-30 verbatim
namespace Manifold

-- @@ L31-31 verbatim
namespace Sobolev


-- @@ L33-33 verbatim
open Set Topology

-- @@ L34-34 verbatim
open scoped ENNReal MeasureTheory

-- @@ L35-35 verbatim
open MeasureTheory

-- @@ L36-36 verbatim
open scoped _root_.Manifold


-- @@ L38-38 verbatim
local notation "n∞" => (⊤ : WithTop ℕ∞)


-- @@ L40-40 verbatim
noncomputable section


-- @@ L42-42 verbatim
section


-- @@ L44-44 verbatim
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

-- @@ L45-45 verbatim
variable {H : Type*} [TopologicalSpace H]

-- @@ L46-46 verbatim
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

-- @@ L47-47 verbatim
variable {I : ModelWithCorners ℝ E H}

-- @@ L48-48 verbatim
variable [IsManifold I n∞ M] [IsManifold I (1 : WithTop ℕ∞) M]

-- @@ L49-49 verbatim
variable [I.Boundaryless]

-- @@ L50-50 verbatim
variable [T2Space M] [CompactSpace M]


-- @@ L52-52 verbatim
local instance instMeasurableSpaceE_SobolevH1 : MeasurableSpace E := borel E

-- @@ L53-53 verbatim
local instance instBorelSpaceE_SobolevH1 : BorelSpace E := ⟨rfl⟩

-- @@ L54-54 verbatim
local instance instOpensMeasurableSpaceE_SobolevH1 : OpensMeasurableSpace E := by infer_instance


-- @@ L56-56 verbatim
local instance instMeasurableSpaceM_SobolevH1 : MeasurableSpace M := borel M

-- @@ L57-57 verbatim
local instance instBorelSpaceM_SobolevH1 : BorelSpace M := ⟨rfl⟩


-- @@ L59-59 verbatim
namespace FiniteChartData


-- @@ L61-78 verbatim
/-- `C¹` scalar functions `M → ℝ` (in the manifold sense), as a submodule of `M → ℝ`. -/
def C1 : Submodule ℝ (M → ℝ) where
  carrier := {f | ContMDiff I (𝓘(ℝ, ℝ)) 1 f}
  zero_mem' := by
    -- `0` is (locally) constant, hence `C¹`.
    simpa using (contMDiff_const (I := I) (I' := (𝓘(ℝ, ℝ))) (n := (1 : WithTop ℕ∞)) (c := (0 : ℝ)))
  add_mem' := by
    intro f g hf hg
    simpa using (hf.add hg)
  smul_mem' := by
    intro c f hf
    -- Scalar multiplication on `ℝ` is multiplication.
    have hc :
        ContMDiff I (𝓘(ℝ, ℝ)) 1 (fun _ : M => c) := by
      simpa using
        (contMDiff_const (I := I) (I' := (𝓘(ℝ, ℝ))) (n := (1 : WithTop ℕ∞)) (c := c))
    -- `c • f = (fun _ => c) * f`.
    simpa [Pi.mul_def, Pi.smul_def, smul_eq_mul] using (hc.mul hf)


-- @@ L80-80 verbatim
variable (d : FiniteChartData (H := H) (M := M) I)


-- @@ L82-82 verbatim
variable (μ : Measure M) [IsFiniteMeasure μ]


-- @@ L84-210 verbatim
private noncomputable def localizeToC1c (i : d.ι) :
    ↥(C1 (E := E) (H := H) (M := M) (I := I)) →ₗ[ℝ]
      ↥(RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.C1c (E := E)) where
  toFun f :=
    ⟨localize (d := d) f.1 i, localize_mem_C1c (d := d) (I := I) (f := f.1) f.2 i⟩
  map_add' f g := by
    ext y
    by_cases hy : y ∈ (extChartAt I (d.center i)).target
    · -- On the chart target, `indicator` is the identity.
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
      -- Now use distributivity in `ℝ`.
      simp [hfg, hf, hg, mul_add]
    · -- Outside the chart target, all indicator terms vanish.
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
    · have hcf :
          localize (d := d) (c • f.1) i y =
            d.ρ i ((extChartAt I (d.center i)).symm y) *
              (c • f.1) ((extChartAt I (d.center i)).symm y) := by
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
      -- Scalar multiplication is multiplication; use commutativity in `ℝ`.
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


-- @@ L212-212 verbatim
/-! ### Target types -/


-- @@ L214-216 verbatim
/-- The chartwise target type `L² × L²(E)` used to define manifold `H¹`. -/
abbrev h1TargetE (μ : Measure M) (i : d.ι) : Type _ :=
  ↥(E →₂[chartMeasure (d := d) (I := I) μ i] ℝ) × ↥(E →₂[chartMeasure (d := d) (I := I) μ i] E)


-- @@ L218-219 verbatim
/-- The product-of-charts target type used to define manifold `H¹`. -/
abbrev h1Target (μ : Measure M) : Type _ := ∀ i : d.ι, h1TargetE (d := d) (I := I) μ i


-- @@ L221-227 verbatim
/-- The per-chart graph map `C¹(M) →ₗ (L² × L²(E))` obtained by localization to chart `i` and the
Euclidean `H¹` graph construction. -/
noncomputable def h1GraphChart (i : d.ι) :
    ↥(C1 (E := E) (H := H) (M := M) (I := I)) →ₗ[ℝ] h1TargetE (d := d) (I := I) μ i :=
  (RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.graph
      (μ := chartMeasure (d := d) (I := I) μ i) (E := E)).comp
    (localizeToC1c (d := d) (I := I) i)


-- @@ L229-237 verbatim
omit [T2Space M] in
lemma h1GraphChart_mem_range_euclidean_graph (i : d.ι)
    (f : ↥(C1 (E := E) (H := H) (M := M) (I := I))) :
    h1GraphChart (d := d) (I := I) (μ := μ) i f ∈
      LinearMap.range
        (RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.graph
            (μ := chartMeasure (d := d) (I := I) μ i) (E := E)) := by
  classical
  refine ⟨localizeToC1c (d := d) (I := I) i f, rfl⟩


-- @@ L239-244 verbatim
/-!
### Unfolding lemmas

These lemmas expose the chartwise `L²` and `L²(E)` components of `h1GraphChart` in terms of the
underlying localized function `localize (d := d) f i`. They are used downstream to control supports.
-/


-- @@ L246-256 verbatim
omit [T2Space M] in
/-- The scalar `L²` component of `h1GraphChart` is the `L²` class of `localize f i`. -/
lemma h1GraphChart_fst (i : d.ι) (f : ↥(C1 (E := E) (H := H) (M := M) (I := I))) :
    (h1GraphChart (d := d) (I := I) (μ := μ) i f).1 =
      RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.toL2
        (μ := chartMeasure (d := d) (I := I) μ i)
        (E := E)
        ⟨localize (d := d) f.1 i, localize_mem_C1c (d := d) (I := I) (f := f.1) f.2 i⟩ := by
  classical
  simp [h1GraphChart, RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.graph,
    RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.toL2Linear, localizeToC1c]


-- @@ L258-269 verbatim
omit [T2Space M] in
/-- The gradient `L²(E)` component of `h1GraphChart` is the `L²(E)` class
of `grad (localize f i)`. -/
lemma h1GraphChart_snd (i : d.ι) (f : ↥(C1 (E := E) (H := H) (M := M) (I := I))) :
    (h1GraphChart (d := d) (I := I) (μ := μ) i f).2 =
      RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.toL2Grad
        (μ := chartMeasure (d := d) (I := I) μ i)
        (E := E)
        ⟨localize (d := d) f.1 i, localize_mem_C1c (d := d) (I := I) (f := f.1) f.2 i⟩ := by
  classical
  simp [h1GraphChart, RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.graph,
    RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.toL2GradLinear, localizeToC1c]


-- @@ L271-276 verbatim
/-- The product-of-charts graph map `C¹(M) →ₗ ∀ i, (L² × L²(E))` used to define manifold `H¹`. -/
noncomputable def h1Graph :
    ↥(C1 (E := E) (H := H) (M := M) (I := I)) →ₗ[ℝ] h1Target (d := d) (I := I) μ := by
  classical
  -- Assemble the per-chart graph maps into a product map.
  refine LinearMap.pi fun i => h1GraphChart (d := d) (I := I) (μ := μ) i


-- @@ L278-280 verbatim
/-- The `H¹` submodule defined by chart localizations and the Euclidean `H¹` graph construction. -/
noncomputable def h1 : Submodule ℝ (h1Target (d := d) (I := I) μ) :=
  (LinearMap.range (h1Graph (d := d) (I := I) (μ := μ))).topologicalClosure


-- @@ L282-285 verbatim
omit [T2Space M] in
theorem isClosed_h1 :
    IsClosed (h1 (d := d) (I := I) (μ := μ) : Set (h1Target (d := d) (I := I) μ)) := by
  exact Submodule.isClosed_topologicalClosure (LinearMap.range (h1Graph (d := d) (I := I) (μ := μ)))


-- @@ L287-290 verbatim
/-- `H¹` is complete (a Hilbert space once the ambient `L²` spaces are). -/
instance instCompleteSpace_h1 : CompleteSpace (↥(h1 (d := d) (I := I) (μ := μ))) := by
  classical
  exact (isClosed_h1 (d := d) (I := I) (μ := μ)).isComplete.completeSpace_coe


-- @@ L292-295 verbatim
/-- The continuous projection `H¹ →` chartwise `L² × L²(E)` for a fixed chart index. -/
noncomputable def h1ToChart (i : d.ι) :
    (↥(h1 (d := d) (I := I) (μ := μ))) →L[ℝ] h1TargetE (d := d) (I := I) μ i :=
  (ContinuousLinearMap.proj (R := ℝ) i).comp (Submodule.subtypeL (h1 (d := d) (I := I) (μ := μ)))


-- @@ L297-300 verbatim
/-- The continuous chartwise `L²` map extracted from `H¹`. -/
noncomputable def h1ToChartL2 (i : d.ι) :
    (↥(h1 (d := d) (I := I) (μ := μ))) →L[ℝ] ↥(E →₂[chartMeasure (d := d) (I := I) μ i] ℝ) :=
  (ContinuousLinearMap.fst ℝ _ _).comp (h1ToChart (d := d) (I := I) (μ := μ) i)


-- @@ L302-305 verbatim
/-- The continuous chartwise gradient map `H¹ → L²(E)` extracted from `H¹`. -/
noncomputable def h1ToChartL2Grad (i : d.ι) :
    (↥(h1 (d := d) (I := I) (μ := μ))) →L[ℝ] ↥(E →₂[chartMeasure (d := d) (I := I) μ i] E) :=
  (ContinuousLinearMap.snd ℝ _ _).comp (h1ToChart (d := d) (I := I) (μ := μ) i)


-- @@ L307-307 verbatim
end FiniteChartData


-- @@ L309-309 verbatim
end


-- @@ L311-311 verbatim
end


-- @@ L313-313 verbatim
end Sobolev

-- @@ L314-314 verbatim
end Manifold

-- @@ L315-315 verbatim
end Geometry

-- @@ L316-316 verbatim
end RellichKondrachov
