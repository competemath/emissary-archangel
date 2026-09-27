/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
module

public import Mathlib.Geometry.Manifold.IsManifold.Basic
public import Mathlib.Analysis.Complex.Basic


-- @@ L11-27 verbatim
/-!
# Charted-space kit: build `ChartedSpace ℂ Z` + `IsManifold 𝓘(ℂ) ω Z` from a chart family

Unit: surfaces-and-charts (`docs/design/surfaces-and-charts.md` §3.3).

Toolkit for projective-line (CC5: two charts on `OnePoint ℂ`) and jacobian-construction
(CC9: quotient charts on `ℂ ⧸ Λ`):

* `chartedSpaceOfFamily`: package a covering family `c : ι → OpenPartialHomeomorph Z ℂ` as a
  `ChartedSpace ℂ Z` (with `@[simp]` lemmas for its `atlas`/`chartAt`);
* `isManifold_of_analyticOn_transitions`: an atlas with ℂ-analytic transition maps is an
  `ω`-manifold;
* `isManifold_of_family`: family version — pairwise-analytic transitions of the generating
  family suffice.

This file is standalone (it does not assume a pre-existing surface).
-/


-- @@ L29-29 verbatim
@[expose] public section


-- @@ L31-31 verbatim
open scoped ContDiff Manifold

-- @@ L32-32 verbatim
open Set


-- @@ L34-34 verbatim
namespace RS


-- @@ L36-36 verbatim
variable {Z : Type*} [TopologicalSpace Z] {ι : Type*}


-- @@ L38-44 verbatim
/-- Package a covering family of ℂ-charts as a `ChartedSpace`. -/
@[reducible] def chartedSpaceOfFamily (c : ι → OpenPartialHomeomorph Z ℂ) (idx : Z → ι)
    (h : ∀ z, z ∈ (c (idx z)).source) : ChartedSpace ℂ Z where
  atlas := Set.range c
  chartAt z := c (idx z)
  mem_chart_source := h
  chart_mem_atlas _ := Set.mem_range_self _


-- @@ L46-48 verbatim
@[simp] theorem chartedSpaceOfFamily_chartAt (c : ι → OpenPartialHomeomorph Z ℂ)
    (idx : Z → ι) (h : ∀ z, z ∈ (c (idx z)).source) (z : Z) :
    @chartAt ℂ _ Z _ (chartedSpaceOfFamily c idx h) z = c (idx z) := rfl


-- @@ L50-52 verbatim
@[simp] theorem chartedSpaceOfFamily_atlas (c : ι → OpenPartialHomeomorph Z ℂ)
    (idx : Z → ι) (h : ∀ z, z ∈ (c (idx z)).source) :
    @atlas ℂ _ Z _ (chartedSpaceOfFamily c idx h) = Set.range c := rfl


-- @@ L54-62 verbatim
/-- An atlas with ℂ-analytic transition maps is an `ω`-manifold. -/
theorem isManifold_of_analyticOn_transitions [ChartedSpace ℂ Z]
    (h : ∀ e ∈ atlas ℂ Z, ∀ e' ∈ atlas ℂ Z,
      AnalyticOnNhd ℂ (e.symm ≫ₕ e') (e.symm ≫ₕ e').source) :
    IsManifold 𝓘(ℂ) ω Z := by
  apply isManifold_of_contDiffOn
  intro e e' he he'
  have hs : IsOpen (e.symm ≫ₕ e').source := (e.symm ≫ₕ e').open_source
  simpa using (contDiffOn_omega_iff_analyticOn hs.uniqueDiffOn).2 ((h e he e' he').analyticOn)


-- @@ L64-72 verbatim
/-- Family version: pairwise-analytic transitions of the generating family suffice. -/
theorem isManifold_of_family (c : ι → OpenPartialHomeomorph Z ℂ) (idx : Z → ι)
    (h : ∀ z, z ∈ (c (idx z)).source)
    (htrans : ∀ i j, AnalyticOnNhd ℂ ((c i).symm ≫ₕ c j) ((c i).symm ≫ₕ c j).source) :
    @IsManifold ℂ _ ℂ _ _ ℂ _ 𝓘(ℂ) ω Z _ (chartedSpaceOfFamily c idx h) := by
  let : ChartedSpace ℂ Z := chartedSpaceOfFamily c idx h
  refine isManifold_of_analyticOn_transitions ?_
  rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
  exact htrans i j


-- @@ L74-74 verbatim
end RS
