import RellichKondrachov.Geometry.Manifold.Sobolev.Localization
import RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.H2

/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/


-- @@ L10-22 verbatim
/-!
# `RellichKondrachov.Geometry.Manifold.Sobolev.LocalizationH2`

Chart-based localization of scalar functions on a compact manifold, at `C²` regularity.

This extends `RellichKondrachov.Geometry.Manifold.Sobolev.Localization` by showing that if
`f : M → ℝ` is `C²` in the manifold sense, then its chart localization belongs to Euclidean
`C²_c` (hence can be fed into the Euclidean `H²` baseline graph construction).

## Main result

- `RellichKondrachov.Geometry.Manifold.Sobolev.FiniteChartData.localize_mem_C2c`
-/


-- @@ L24-24 verbatim
namespace RellichKondrachov

-- @@ L25-25 verbatim
namespace Geometry

-- @@ L26-26 verbatim
namespace Manifold

-- @@ L27-27 verbatim
namespace Sobolev


-- @@ L29-29 verbatim
open Set Filter Topology

-- @@ L30-30 verbatim
open scoped _root_.Manifold


-- @@ L32-32 verbatim
local notation "n∞" => (⊤ : WithTop ℕ∞)


-- @@ L34-34 verbatim
noncomputable section


-- @@ L36-36 verbatim
section


-- @@ L38-38 verbatim
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

-- @@ L39-39 verbatim
variable {H : Type*} [TopologicalSpace H]

-- @@ L40-40 verbatim
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

-- @@ L41-41 verbatim
variable {I : ModelWithCorners ℝ E H}

-- @@ L42-42 verbatim
variable [IsManifold I n∞ M] [IsManifold I (1 : WithTop ℕ∞) M]

-- @@ L43-43 verbatim
variable [I.Boundaryless]

-- @@ L44-44 verbatim
variable [T2Space M] [CompactSpace M]


-- @@ L46-46 verbatim
local instance instMeasurableSpaceM_SobolevLocalizationH2 : MeasurableSpace M := borel M

-- @@ L47-47 verbatim
local instance instBorelSpaceM_SobolevLocalizationH2 : BorelSpace M := ⟨rfl⟩


-- @@ L49-49 verbatim
namespace FiniteChartData


-- @@ L51-51 verbatim
variable (d : FiniteChartData (H := H) (M := M) I)


-- @@ L53-54 verbatim
private abbrev chart (i : d.ι) : PartialEquiv M E :=
  extChartAt I (d.center i)


-- @@ L56-56 verbatim
private abbrev Iℝ : ModelWithCorners ℝ ℝ ℝ := 𝓘(ℝ, ℝ)


-- @@ L58-96 verbatim
omit [CompleteSpace E] [IsManifold I (1 : WithTop ℕ∞) M]
    [I.Boundaryless] [T2Space M] [CompactSpace M] in
private lemma contDiffOn_localize_target {f : M → ℝ}
    (hf : ContMDiff I Iℝ 2 f) (i : d.ι) :
    ContDiffOn ℝ 2 (localize (d := d) f i) (chart (d := d) i).target := by
  classical
  have hOn :
      ContDiffOn ℝ 2
        (fun y =>
          d.ρ i ((chart (d := d) i).symm y) * f ((chart (d := d) i).symm y))
        (chart (d := d) i).target := by
    have hρ : ContMDiff I Iℝ 2 fun x : M => d.ρ i x := by
      simpa using
        (d.ρ i).contMDiff.of_le
          (by
            -- `SmoothPartitionOfUnity` yields order `↑(⊤ : ℕ∞)`, so any finite order is admissible.
            exact (by decide : (2 : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞) : WithTop ℕ∞)))
    have hg : ContMDiff I Iℝ 2 fun x : M => d.ρ i x * f x :=
      hρ.mul hf
    have hs :
        ContMDiffOn 𝓘(ℝ, E) I 2 (chart (d := d) i).symm (chart (d := d) i).target := by
      simpa [chart] using
        (contMDiffOn_extChartAt_symm (I := I) (n := (2 : WithTop ℕ∞)) (x := d.center i))
    have hComp :
        ContMDiffOn 𝓘(ℝ, E) Iℝ 2
          (fun y : E => (fun x : M => d.ρ i x * f x) ((chart (d := d) i).symm y))
          (chart (d := d) i).target :=
      (hg.comp_contMDiffOn hs)
    simpa using (contMDiffOn_iff_contDiffOn (𝕜 := ℝ) (E := E) (E' := ℝ)).1 hComp
  have hEq :
      EqOn (localize (d := d) f i)
        (fun y =>
          d.ρ i ((chart (d := d) i).symm y) * f ((chart (d := d) i).symm y))
        (chart (d := d) i).target := by
    intro y hy
    simpa [FiniteChartData.localize] using
      (Set.indicator_of_mem (s := (chart (d := d) i).target) (a := y)
        (f := fun y => d.ρ i ((chart (d := d) i).symm y) * f ((chart (d := d) i).symm y)) hy)
  exact hOn.congr hEq


-- @@ L98-98 verbatim
section


-- @@ L100-100 verbatim
omit [CompleteSpace E] [IsManifold I (1 : WithTop ℕ∞) M] [T2Space M]


-- @@ L102-119 verbatim
/-- For a `C²` function on a compact manifold, the chart-localization is a Euclidean `C2c`
function. -/
lemma localize_mem_C2c {f : M → ℝ} (hf : ContMDiff I Iℝ 2 f) (i : d.ι) :
    localize (d := d) f i ∈
      RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.C2c (E := E) := by
  classical
  have hOpen : IsOpen (chart (d := d) i).target :=
    isOpen_extChartAt_target (I := I) (x := d.center i)
  have hDiffOn : ContDiffOn ℝ 2 (localize (d := d) f i) (chart (d := d) i).target :=
    contDiffOn_localize_target (d := d) (I := I) (f := f) hf i
  have hTsupport : tsupport (localize (d := d) f i) ⊆ (chart (d := d) i).target :=
    FiniteChartData.tsupport_localize_subset_target (d := d) (I := I) (f := f) i
  have hDiff : ContDiff ℝ 2 (localize (d := d) f i) :=
    RellichKondrachov.Analysis.Calculus.ContDiff.contDiff_of_contDiffOn_of_tsupport_subset
      (𝕜 := ℝ) (E := E) (F := ℝ) hOpen hDiffOn hTsupport
  have hCs : HasCompactSupport (localize (d := d) f i) :=
    FiniteChartData.hasCompactSupport_localize (d := d) (I := I) (f := f) i
  exact ⟨hDiff, hCs⟩


-- @@ L121-121 verbatim
end


-- @@ L123-123 verbatim
end FiniteChartData


-- @@ L125-125 verbatim
end


-- @@ L127-127 verbatim
end


-- @@ L129-129 verbatim
end Sobolev

-- @@ L130-130 verbatim
end Manifold

-- @@ L131-131 verbatim
end Geometry

-- @@ L132-132 verbatim
end RellichKondrachov
