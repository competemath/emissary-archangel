/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module

public import LeanPool.RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.H1
public import LeanPool.RellichKondrachov.Geometry.Manifold.Sobolev.ChartData
import LeanPool.RellichKondrachov.Analysis.Calculus.ContDiff.Support


-- @@ L12-27 verbatim
/-!
# `RellichKondrachov.Geometry.Manifold.Sobolev.Localization`

Chart-based localization of scalar functions on a compact manifold.

Given finite chart data `d : FiniteChartData` (a finite family of chart centers with a smooth
partition of unity subordinate to those charts), we define a localization operation

`localize d f i : E → ℝ`

on the model space `E`, obtained by pulling back `ρ_i • f` along the extended chart
`(extChartAt I (d.center i)).symm` and extending by `0` outside the chart target.

For compact manifolds, the resulting function has compact support and is `C^1` (hence belongs to
the Euclidean `C1c` submodule used in the Euclidean Sobolev baseline).
-/


-- @@ L29-29 verbatim
@[expose] public section


-- @@ L31-31 verbatim
namespace RellichKondrachov

-- @@ L32-32 verbatim
namespace Geometry

-- @@ L33-33 verbatim
namespace Manifold

-- @@ L34-34 verbatim
namespace Sobolev


-- @@ L36-36 verbatim
open Set Filter Topology

-- @@ L37-37 verbatim
open scoped _root_.Manifold


-- @@ L39-39 verbatim
local notation "n∞" => (⊤ : WithTop ℕ∞)


-- @@ L41-41 verbatim
noncomputable section


-- @@ L43-44 verbatim
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]

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


-- @@ L52-53 verbatim
/-- Borel σ-algebra on the model space `E`. -/
local instance instMeasurableSpaceLocalization : MeasurableSpace M := borel M

-- @@ L54-54 verbatim
local instance instBorelSpaceLocalization : BorelSpace M := ⟨rfl⟩


-- @@ L56-57 verbatim
/-- The standard model with corners on the real line. -/
abbrev Iℝ : ModelWithCorners ℝ ℝ ℝ := 𝓘(ℝ, ℝ)


-- @@ L59-59 verbatim
namespace FiniteChartData


-- @@ L61-61 verbatim
variable (d : FiniteChartData (H := H) (M := M) I)


-- @@ L63-65 verbatim
/-- The extended chart centered at the selected point of the finite chart family. -/
abbrev chart (i : d.ι) : PartialEquiv M E :=
  extChartAt I (d.center i)


-- @@ L67-70 verbatim
/-- The localization of a scalar function `f : M → ℝ` to a chart `i`, as a function on `E`. -/
noncomputable def localize (f : M → ℝ) (i : d.ι) : E → ℝ :=
  Set.indicator (chart (d := d) i).target fun y =>
    d.ρ i ((chart (d := d) i).symm y) * f ((chart (d := d) i).symm y)


-- @@ L72-74 verbatim
/-- The closed set `closure (support (ρ i))` used to control the support of localizations. -/
def rhoSupportClosure (i : d.ι) : Set M :=
  closure (Function.support (d.ρ i : M → ℝ))


-- @@ L76-80 verbatim
omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I (1 : WithTop ℕ∞) M]
    [I.Boundaryless] [T2Space M] [CompactSpace M] in
lemma rhoSupportClosure_subset_source (i : d.ι) :
    rhoSupportClosure (d := d) i ⊆ (chart (d := d) i).source := by
  simp [rhoSupportClosure, chart]


-- @@ L82-85 verbatim
omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I (1 : WithTop ℕ∞) M] [I.Boundaryless]
    [T2Space M] in
lemma isCompact_rhoSupportClosure (i : d.ι) : IsCompact (rhoSupportClosure (d := d) i) :=
  (isClosed_closure.isCompact)


-- @@ L87-89 verbatim
/-- A compact subset of the chart model space containing the supports of all localizations. -/
def rhoSupportImage (i : d.ι) : Set E :=
  (chart (d := d) i) '' rhoSupportClosure (d := d) i


-- @@ L91-99 verbatim
omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I (1 : WithTop ℕ∞) M] [I.Boundaryless]
    [T2Space M] in
lemma isCompact_rhoSupportImage (i : d.ι) : IsCompact (rhoSupportImage (d := d) i) := by
  classical
  -- `extChartAt` is continuous on its source, hence on `rhoSupportClosure`
  -- (which is contained in the source).
  refine (isCompact_rhoSupportClosure (d := d) i).image_of_continuousOn ?_
  exact (continuousOn_extChartAt (I := I) (x := d.center i)).mono
    (rhoSupportClosure_subset_source (d := d) (i := i))


-- @@ L101-143 verbatim
omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I (1 : WithTop ℕ∞) M] [I.Boundaryless]
    [T2Space M] [CompactSpace M] in
lemma support_localize_subset_rhoSupportImage (f : M → ℝ) (i : d.ι) :
    Function.support (localize (d := d) f i) ⊆ rhoSupportImage (d := d) i := by
  intro y hy
  have hyT : y ∈ (chart (d := d) i).target := by
    by_contra hyT
    have : localize (d := d) f i y = 0 := by
      -- `indicator` vanishes outside the target.
      simpa [localize] using
        (Set.indicator_of_notMem (s := (chart (d := d) i).target) (a := y)
            (f := fun y =>
              d.ρ i ((chart (d := d) i).symm y) * f ((chart (d := d) i).symm y)) hyT)
    exact hy this
  have hEq :
      localize (d := d) f i y =
        d.ρ i ((chart (d := d) i).symm y) * f ((chart (d := d) i).symm y) := by
    -- On the target, `indicator` is the identity.
    simpa [localize] using
      (Set.indicator_of_mem (s := (chart (d := d) i).target) (a := y)
        (f := fun y =>
          d.ρ i ((chart (d := d) i).symm y) * f ((chart (d := d) i).symm y)) hyT)
  have hyVal :
      d.ρ i ((chart (d := d) i).symm y) * f ((chart (d := d) i).symm y) ≠ 0 := by
    intro h0
    apply hy
    calc
      localize (d := d) f i y =
          d.ρ i ((chart (d := d) i).symm y) * f ((chart (d := d) i).symm y) := hEq
      _ = 0 := h0
  have hxRho : d.ρ i ((chart (d := d) i).symm y) ≠ 0 := by
    intro hx
    apply hyVal
    -- Avoid `simp` rewriting `mul_eq_zero` into a disjunction.
    rw [hx]
    simp
  have hx : (chart (d := d) i).symm y ∈ rhoSupportClosure (d := d) i := by
    -- A nonzero value implies membership in the (topological) support.
    refine subset_closure ?_
    exact hxRho
  refine ⟨(chart (d := d) i).symm y, hx, ?_⟩
  -- On the target, `extChartAt` and its inverse satisfy `right_inv`.
  exact (chart (d := d) i).right_inv hyT


-- @@ L145-151 verbatim
omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I (1 : WithTop ℕ∞) M] [I.Boundaryless]
    [T2Space M] in
lemma tsupport_localize_subset_rhoSupportImage (f : M → ℝ) (i : d.ι) :
    tsupport (localize (d := d) f i) ⊆ rhoSupportImage (d := d) i := by
  have hImgClosed : IsClosed (rhoSupportImage (d := d) i) :=
    (isCompact_rhoSupportImage (d := d) i).isClosed
  refine (closure_minimal (support_localize_subset_rhoSupportImage (d := d) f i) hImgClosed)


-- @@ L153-159 verbatim
omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I (1 : WithTop ℕ∞) M] [I.Boundaryless]
    [T2Space M] [CompactSpace M] in
lemma rhoSupportImage_subset_target (i : d.ι) :
    rhoSupportImage (d := d) i ⊆ (chart (d := d) i).target := by
  intro y hy
  rcases hy with ⟨x, hx, rfl⟩
  exact (chart (d := d) i).map_source (rhoSupportClosure_subset_source (d := d) (i := i) hx)


-- @@ L161-166 verbatim
omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I (1 : WithTop ℕ∞) M] [I.Boundaryless]
    [T2Space M] in
lemma tsupport_localize_subset_target (f : M → ℝ) (i : d.ι) :
    tsupport (localize (d := d) f i) ⊆ (chart (d := d) i).target :=
  (tsupport_localize_subset_rhoSupportImage (d := d) f i).trans
    (rhoSupportImage_subset_target (d := d) i)


-- @@ L168-176 verbatim
omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I (1 : WithTop ℕ∞) M] [I.Boundaryless]
    [T2Space M] in
lemma hasCompactSupport_localize (f : M → ℝ) (i : d.ι) :
    HasCompactSupport (localize (d := d) f i) := by
  -- `HasCompactSupport` is `IsCompact` of `tsupport`.
  have hClosed : IsClosed (tsupport (localize (d := d) f i)) :=
    isClosed_tsupport (f := localize (d := d) f i)
  exact (isCompact_rhoSupportImage (d := d) i).of_isClosed_subset hClosed
    (tsupport_localize_subset_rhoSupportImage (d := d) f i)


-- @@ L178-222 verbatim
omit [CompleteSpace E] [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M] [CompactSpace M] in
private lemma contDiffOn_localize_target {f : M → ℝ}
    (hf : ContMDiff I Iℝ 1 f) (i : d.ι) :
    ContDiffOn ℝ 1 (localize (d := d) f i) (chart (d := d) i).target := by
  classical
  -- On the chart target, `localize` is just composition with `extChartAt.symm`.
  have hOn :
      ContDiffOn ℝ 1
        (fun y =>
          d.ρ i ((chart (d := d) i).symm y) * f ((chart (d := d) i).symm y))
        (chart (d := d) i).target := by
    -- First show `C^1` smoothness in the manifold sense, then convert to `ContDiffOn`.
    have hρ : ContMDiff I Iℝ 1 fun x : M => d.ρ i x := by
      -- Each partition-of-unity function is `C^∞`, hence `C^1`.
      simpa using
        (d.ρ i).contMDiff.of_le
          (by
            -- `SmoothPartitionOfUnity` yields `C^∞` functions, i.e. order `↑(⊤ : ℕ∞)`.
            simp : (1 : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞) : WithTop ℕ∞))
    have hg : ContMDiff I Iℝ 1 fun x : M => d.ρ i x * f x :=
      hρ.mul hf
    have hs : ContMDiffOn 𝓘(ℝ, E) I 1 (chart (d := d) i).symm (chart (d := d) i).target := by
      -- This is `C^1` on the chart target.
      simpa [chart] using
        (contMDiffOn_extChartAt_symm (I := I) (n := (1 : WithTop ℕ∞)) (x := d.center i))
    have hComp :
        ContMDiffOn 𝓘(ℝ, E) Iℝ 1
          (fun y : E => (fun x : M => d.ρ i x * f x) ((chart (d := d) i).symm y))
          (chart (d := d) i).target :=
      (hg.comp_contMDiffOn hs)
    -- Convert `ContMDiffOn` to `ContDiffOn` for maps between vector spaces.
    simpa using (contMDiffOn_iff_contDiffOn (𝕜 := ℝ) (E := E) (E' := ℝ)).1 hComp
  -- Rewrite `localize` as an indicator and use that on the target it's equal to
  -- the underlying function.
  have hEq :
      EqOn (localize (d := d) f i)
        (fun y =>
          d.ρ i ((chart (d := d) i).symm y) * f ((chart (d := d) i).symm y))
        (chart (d := d) i).target := by
    intro y hy
    simpa [localize] using
      (Set.indicator_of_mem (s := (chart (d := d) i).target) (a := y)
        (f := fun y => d.ρ i ((chart (d := d) i).symm y) * f ((chart (d := d) i).symm y)) hy)
  -- Transfer `ContDiffOn` along the pointwise equality on the domain set.
  exact hOn.congr hEq


-- @@ L224-224 verbatim
section


-- @@ L226-226 verbatim
omit [CompleteSpace E] [FiniteDimensional ℝ E] [T2Space M]


-- @@ L228-246 verbatim
/-- For a `C^1` function on a compact manifold, the chart-localization is a Euclidean `C1c`
function. -/
lemma localize_mem_C1c {f : M → ℝ} (hf : ContMDiff I Iℝ 1 f) (i : d.ι) :
    localize (d := d) f i ∈
      RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.C1c (E := E) := by
  classical
  -- `localize` is `C^1` on the open chart target, and has support contained in it.
  have hOpen : IsOpen (chart (d := d) i).target :=
    isOpen_extChartAt_target (I := I) (x := d.center i)
  have hDiffOn : ContDiffOn ℝ 1 (localize (d := d) f i) (chart (d := d) i).target :=
    contDiffOn_localize_target (d := d) (f := f) hf i
  have hTsupport : tsupport (localize (d := d) f i) ⊆ (chart (d := d) i).target :=
    tsupport_localize_subset_target (d := d) (f := f) i
  have hDiff : ContDiff ℝ 1 (localize (d := d) f i) :=
    RellichKondrachov.Analysis.Calculus.ContDiff.contDiff_of_contDiffOn_of_tsupport_subset
      (𝕜 := ℝ) (E := E) (F := ℝ) hOpen hDiffOn hTsupport
  have hCs : HasCompactSupport (localize (d := d) f i) :=
    hasCompactSupport_localize (d := d) (f := f) i
  exact ⟨hDiff, hCs⟩


-- @@ L248-248 verbatim
end


-- @@ L250-250 verbatim
end FiniteChartData


-- @@ L252-252 verbatim
end


-- @@ L254-254 verbatim
end Sobolev

-- @@ L255-255 verbatim
end Manifold

-- @@ L256-256 verbatim
end Geometry

-- @@ L257-257 verbatim
end RellichKondrachov
