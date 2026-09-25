/-
Copyright (c) 2026 Rob Sneiderman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rob Sneiderman
-/
module

public import Mathlib.RepresentationTheory.Continuous.Basic
public import Physlib.SpaceAndTime.TimeAndSpace.EuclideanGroup.Action

-- @@ L10-34 verbatim
/-!

# The Euclidean group action on Schwartz maps over `TimeAndSpace`

## i. Overview

In this file we define the pullback action of the Euclidean group on Schwartz maps over
`TimeAndSpace d`. The action is
`g • η = fun tx => η (g⁻¹ • tx)`.

## ii. Key results

- `TimeAndSpace.schwartzEuclideanAction` : The Euclidean group action on Schwartz maps as a
  continuous representation (`ContRepresentation`).
- `TimeAndSpace.instMulActionSchwartzMap` : The induced `MulAction` instance on Schwartz maps.
- `TimeAndSpace.smul_schwartzMap_apply` : Pointwise formula for the action.

## iii. Table of contents

- A. The pullback action on Schwartz maps

## iv. References

* None.
-/


-- @@ L36-36 verbatim
@[expose] public section

-- @@ L37-37 verbatim
noncomputable section


-- @@ L39-39 verbatim
open SchwartzMap


-- @@ L41-41 verbatim
namespace TimeAndSpace


-- @@ L43-43 verbatim
variable {d : ℕ}


-- @@ L45-49 verbatim
/-!

## A. The pullback action on Schwartz maps

-/


-- @@ L51-51 verbatim
variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]


-- @@ L53-77 verbatim
/-- The Euclidean-group pullback action on Schwartz maps over `TimeAndSpace d`, as a continuous
representation `ContRepresentation ℝ (EuclideanGroup d) 𝓢(TimeAndSpace d, F)`.

`ContRepresentation R G V` unfolds to the monoid homomorphism `G →* V →L[R] V` into the
*continuous*-linear maps: the builder `SchwartzMap.compCLMOfAntilipschitz` already yields a
continuous-linear map for free, and the `→L` codomain lets the action compose under `∘L`. The
plain mathlib `Representation` (`G →* V →ₗ[ℝ] V`) is recovered via
`ContRepresentation.toRepresentation`. -/
noncomputable def schwartzEuclideanAction {d : ℕ} :
    ContRepresentation ℝ (EuclideanGroup d) 𝓢(TimeAndSpace d, F) where
  toMonoidHom :=
  { toFun := fun g => SchwartzMap.compCLMOfAntilipschitz (𝕜 := ℝ)
      (g := fun tx : TimeAndSpace d => g⁻¹ • tx)
      (TimeAndSpace.smul_hasTemperateGrowth g⁻¹)
      (TimeAndSpace.antilipschitz_smul g⁻¹)
    map_one' := by
      ext η tx
      simp
    map_mul' := by
      intro g h
      ext η tx
      simp only [_root_.mul_inv_rev, SchwartzMap.compCLMOfAntilipschitz_apply,
        Function.comp_apply]
      rw [mul_smul]
      rfl }


-- @@ L79-83 verbatim
/-- Pointwise formula for the monoid-homomorphism form of the Schwartz-map pullback action. -/
@[simp]
lemma schwartzEuclideanAction_apply {d : ℕ} (g : EuclideanGroup d) (η : 𝓢(TimeAndSpace d, F))
    (tx : TimeAndSpace d) :
    (schwartzEuclideanAction g η) tx = η (g⁻¹ • tx) := rfl


-- @@ L85-99 verbatim
/-- The Euclidean group acts on Schwartz maps over `TimeAndSpace d` by pullback. -/
noncomputable instance instMulActionSchwartzMap {d : ℕ} :
    MulAction (EuclideanGroup d) 𝓢(TimeAndSpace d, F) where
  smul g η := schwartzEuclideanAction g η
  one_smul η := by
    ext tx
    change (schwartzEuclideanAction (1 : EuclideanGroup d) η) tx = η tx
    rw [schwartzEuclideanAction_apply]
    simp
  mul_smul g h η := by
    ext tx
    change (schwartzEuclideanAction (g * h) η) tx =
      (schwartzEuclideanAction g (schwartzEuclideanAction h η)) tx
    simp only [schwartzEuclideanAction_apply, _root_.mul_inv_rev]
    rw [mul_smul]


-- @@ L101-105 verbatim
/-- Pointwise formula for the `MulAction` instance on Schwartz maps. -/
@[simp]
lemma smul_schwartzMap_apply {d : ℕ} (g : EuclideanGroup d) (η : 𝓢(TimeAndSpace d, F))
    (tx : TimeAndSpace d) :
    (g • η) tx = η (g⁻¹ • tx) := rfl


-- @@ L107-114 verbatim
/-- Applying `g` and then `h` to a Schwartz map is the pullback action of `h * g`. -/
lemma schwartzEuclideanAction_mul_apply {d : ℕ} (g h : EuclideanGroup d)
    (η : 𝓢(TimeAndSpace d, F)) :
    schwartzEuclideanAction h (schwartzEuclideanAction g η) =
      schwartzEuclideanAction (h * g) η := by
  ext tx
  simp only [schwartzEuclideanAction_apply, _root_.mul_inv_rev]
  rw [mul_smul]


-- @@ L116-122 verbatim
/-- Each Euclidean-group pullback action on Schwartz maps is injective. -/
lemma schwartzEuclideanAction_injective {d : ℕ} (g : EuclideanGroup d) :
    Function.Injective (schwartzEuclideanAction (F := F) g) := by
  intro η1 η2 hη
  ext tx
  have htx := congrArg (fun η : 𝓢(TimeAndSpace d, F) => η (g • tx)) hη
  simpa using htx


-- @@ L124-130 verbatim
/-- Each Euclidean-group pullback action on Schwartz maps is surjective. -/
lemma schwartzEuclideanAction_surjective {d : ℕ} (g : EuclideanGroup d) :
    Function.Surjective (schwartzEuclideanAction (F := F) g) := by
  intro η
  use schwartzEuclideanAction g⁻¹ η
  ext tx
  simp


-- @@ L132-132 verbatim
end TimeAndSpace


-- @@ L134-134 verbatim
end
