/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Geometry.Manifold.Diffeomorph

-- @@ L10-29 verbatim
/-!
# The time manifold

In this module we define the type `TimeMan`, corresponding to the time manifold,
without any additional structures except an orientation, such as a choice of metric or origin.
I.e. it is a manifold diffeomorphic to `ℝ` with no additional structure.

If you are looking for a more standard version of time see the type `Time`.

`TimeMan` is sometimes called topological time, due to the absence of a metric, and its use in
topological field theories.

## Implementation details

The manifold `TimeMan` is defined via the type `ℝ`, and thus inherits a given choice
of map `TimeMan.val : TimeMan → ℝ`, which can be extended to a homeomorphism or a
diffeomorphism. When using `TimeMan.val`, one should be aware that using it does
constitute a choice being made.

-/


-- @@ L31-31 verbatim
@[expose] public section


-- @@ L33-38 verbatim
/-- The type `TimeMan` represents the time manifold.
  Mathematically `TimeMan` is a manifold diffeomorphic to `ℝ` with an orientation but no additional
  structure. -/
structure TimeMan where
  /-- The choice of a map from `TimeMan` to `ℝ`. -/
  val : ℝ


-- @@ L40-40 verbatim
namespace TimeMan


-- @@ L42-49 verbatim
/-!

## The topology on TimeMan.

The topology on `TimeMan` is induced from the topology on `ℝ`, via the choice
of map `TimeMan.val`.

-/


-- @@ L51-53 verbatim
/-- The instance of a topological space on `TimeMan` induced by the map `TimeMan.val`. s-/
instance : TopologicalSpace TimeMan := TopologicalSpace.induced TimeMan.val
  PseudoMetricSpace.toUniformSpace.toTopologicalSpace


-- @@ L55-57 verbatim
lemma val_surjective : Function.Surjective TimeMan.val := by
  intro t
  use { val := t }


-- @@ L59-61 verbatim
@[simp]
lemma val_range : Set.range val = Set.univ := by
  refine Set.range_eq_univ.mpr val_surjective


-- @@ L63-64 verbatim
lemma val_inducing : Topology.IsInducing TimeMan.val where
  eq_induced := rfl


-- @@ L66-70 verbatim
lemma val_injective : Function.Injective TimeMan.val := by
  intro t1 t2 h
  cases t1
  cases t2
  simp_all


-- @@ L72-76 verbatim
lemma val_isOpenEmbedding : Topology.IsOpenEmbedding TimeMan.val where
  eq_induced := rfl
  isOpen_range := by
    simp
  injective := val_injective


-- @@ L78-80 verbatim
lemma isOpen_iff {s : Set TimeMan} :
    IsOpen s ↔ IsOpen (TimeMan.val '' s) :=
  Topology.IsOpenEmbedding.isOpen_iff_image_isOpen val_isOpenEmbedding


-- @@ L82-103 verbatim
/-- The choice of map `Time.val` from `TimeMan` to `ℝ` as a homeomorphism. -/
def valHomeomorphism : TimeMan ≃ₜ ℝ where
  toFun := TimeMan.val
  invFun := fun t => { val := t }
  left_inv := by
    intro t
    cases t
    rfl
  right_inv := by
    intro t
    rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by
    refine { isOpen_preimage := ?_ }
    intro s hs
    rw [isOpen_iff] at hs
    rw [← Set.image_eq_preimage_of_inverse]
    · exact hs
    · intro t
      rfl
    · intro x
      simp


-- @@ L105-109 verbatim
/-!

## The manifold structure on TimeMan

-/


-- @@ L111-119 verbatim
/-- The structure of a charted space on `TimeMan` -/
instance : ChartedSpace ℝ TimeMan where
  atlas := { valHomeomorphism.toOpenPartialHomeomorph }
  chartAt _ := valHomeomorphism.toOpenPartialHomeomorph
  mem_chart_source := by
    simp
  chart_mem_atlas := by
    intro x
    simp


-- @@ L121-121 verbatim
open Manifold ContDiff


-- @@ L123-129 verbatim
/-- The structure of a manifold on `TimeMan` induced by the choice of map `Time.val`. -/
instance : IsManifold 𝓘(ℝ, ℝ) ω TimeMan where
  compatible := by
    intro e1 e2 h1 h2
    simp [atlas, ChartedSpace.atlas] at h1 h2
    subst h1 h2
    exact symm_trans_mem_contDiffGroupoid valHomeomorphism.toOpenPartialHomeomorph


-- @@ L131-133 verbatim
lemma val_contDiff : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ω TimeMan.val := by
  refine contMDiffOn_univ.mp ?_
  exact contMDiffOn_chart (x := (⟨0⟩ : TimeMan))


-- @@ L135-141 verbatim
/-- The choice of map `Time.val` from `TimeMan` to `ℝ` as a diffeomorphism. -/
noncomputable def valDiffeomorphism : TimeMan ≃ₘ^ω⟮𝓘(ℝ, ℝ), 𝓘(ℝ, ℝ)⟯ ℝ where
  toEquiv := valHomeomorphism.toEquiv
  contMDiff_toFun := val_contDiff
  contMDiff_invFun := by
    refine contMDiffOn_univ.mp ?_
    exact contMDiffOn_chart_symm (x := (⟨0⟩ : TimeMan))


-- @@ L143-147 verbatim
/-!

## The orientation on TimeMan

-/


-- @@ L149-151 verbatim
/-- The instance of an orientation on TimeMan. -/
instance : LE TimeMan where
  le x y := x.val ≤ y.val


-- @@ L153-153 verbatim
end TimeMan
