/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
module

public import Mathlib.Geometry.Manifold.IsManifold.Basic
public import Mathlib.Analysis.Complex.Basic


-- @@ L11-28 verbatim
/-!
# Charted-space kit, generalized to an arbitrary `NormedSpace ℂ` codomain

Unit: jacobian-construction (`docs/design/jacobian-construction.md` §4.2.1). Surface's
`Jacobian/Surface/ChartedSpaceKit.lean` hardcodes the chart codomain to literal `ℂ`; this file is
a **textually near-identical generalization** to an arbitrary `{E : Type*} [NormedAddCommGroup E]
[NormedSpace ℂ E]` (needed for `V := Fin n → ℂ`, the ambient space of the Jacobian torus). A
non-blocking request to generalize the upstream file instead is filed in
`docs/requests/surfaces-and-charts.md`; the two are `rfl`-compatible (identical proofs).

Namespace `RS` (Compat section, primed names to avoid clashing with Surface's originals):

* `chartedSpaceOfFamily'`: package a covering family `c : ι → OpenPartialHomeomorph Z E` as a
  `ChartedSpace E Z`;
* `isManifold_of_analyticOn_transitions'`: an atlas with `ℂ`-analytic transition maps is an
  `ω`-manifold (model `𝓘(ℂ, E)`);
* `isManifold_of_family'`: family version.
-/


-- @@ L30-30 verbatim
@[expose] public section


-- @@ L32-32 verbatim
open scoped ContDiff Manifold

-- @@ L33-33 verbatim
open Set


-- @@ L35-35 verbatim
namespace RS


-- @@ L37-37 verbatim
variable {Z : Type*} [TopologicalSpace Z] {ι : Type*}

-- @@ L38-38 verbatim
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]


-- @@ L40-46 verbatim
/-- Package a covering family of `E`-valued charts as a `ChartedSpace`. -/
@[reducible] def chartedSpaceOfFamily' (c : ι → OpenPartialHomeomorph Z E) (idx : Z → ι)
    (h : ∀ z, z ∈ (c (idx z)).source) : ChartedSpace E Z where
  atlas := Set.range c
  chartAt z := c (idx z)
  mem_chart_source := h
  chart_mem_atlas _ := Set.mem_range_self _


-- @@ L48-51 verbatim
omit [NormedSpace ℂ E] in
@[simp] theorem chartedSpaceOfFamily'_chartAt (c : ι → OpenPartialHomeomorph Z E)
    (idx : Z → ι) (h : ∀ z, z ∈ (c (idx z)).source) (z : Z) :
    @chartAt E _ Z _ (chartedSpaceOfFamily' c idx h) z = c (idx z) := rfl


-- @@ L53-56 verbatim
omit [NormedSpace ℂ E] in
@[simp] theorem chartedSpaceOfFamily'_atlas (c : ι → OpenPartialHomeomorph Z E)
    (idx : Z → ι) (h : ∀ z, z ∈ (c (idx z)).source) :
    @atlas E _ Z _ (chartedSpaceOfFamily' c idx h) = Set.range c := rfl


-- @@ L58-66 verbatim
/-- An atlas with `ℂ`-analytic transition maps is an `ω`-manifold (model `𝓘(ℂ, E)`). -/
theorem isManifold_of_analyticOn_transitions' [ChartedSpace E Z]
    (h : ∀ e ∈ atlas E Z, ∀ e' ∈ atlas E Z,
      AnalyticOnNhd ℂ (e.symm ≫ₕ e') (e.symm ≫ₕ e').source) :
    IsManifold 𝓘(ℂ, E) ω Z := by
  apply isManifold_of_contDiffOn
  intro e e' he he'
  have hs : IsOpen (e.symm ≫ₕ e').source := (e.symm ≫ₕ e').open_source
  simpa using (contDiffOn_omega_iff_analyticOn hs.uniqueDiffOn).2 ((h e he e' he').analyticOn)


-- @@ L68-76 verbatim
/-- Family version: pairwise-analytic transitions of the generating family suffice. -/
theorem isManifold_of_family' (c : ι → OpenPartialHomeomorph Z E) (idx : Z → ι)
    (h : ∀ z, z ∈ (c (idx z)).source)
    (htrans : ∀ i j, AnalyticOnNhd ℂ ((c i).symm ≫ₕ c j) ((c i).symm ≫ₕ c j).source) :
    @IsManifold ℂ _ E _ _ E _ 𝓘(ℂ, E) ω Z _ (chartedSpaceOfFamily' c idx h) := by
  let : ChartedSpace E Z := chartedSpaceOfFamily' c idx h
  refine isManifold_of_analyticOn_transitions' ?_
  rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
  exact htrans i j


-- @@ L78-78 verbatim
end RS
