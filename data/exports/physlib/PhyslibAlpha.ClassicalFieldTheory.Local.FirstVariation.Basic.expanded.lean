/-
Copyright (c) 2026 Juan Jose Fernandez Morales. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Jose Fernandez Morales
-/
module

public import PhyslibAlpha.ClassicalFieldTheory.Local.EulerLagrange
public import Physlib.Mathematics.VariationalCalculus.Basic

-- @@ L10-32 verbatim
/-!
# First variation core objects

## i. Overview

This module contains the basic objects used throughout the local first-variation theory:
the linearized density before integration by parts and its Euler-Lagrange pairing.

## ii. Key results

- `ClassicalFieldTheory.Local.firstVariationDensityTerm`
- `ClassicalFieldTheory.Local.firstVariationDensity`
- `ClassicalFieldTheory.Local.firstVariationValue`

## iii. Table of contents

- A. First-variation values

## iv. References

* J. Cortés and A. Haupt, Lecture Notes on Mathematical Methods of Classical Physics, Chapter 5,
  Theorem 5.2. [ref: cortes_haupt_2016]
-/


-- @@ L34-34 verbatim
@[expose] public section


-- @@ L36-36 verbatim
open MeasureTheory

-- @@ L37-37 verbatim
open InnerProductSpace

-- @@ L38-38 verbatim
open Physlib

-- @@ L39-39 verbatim
open scoped BigOperators ContDiff


-- @@ L41-41 verbatim
namespace ClassicalFieldTheory

-- @@ L42-42 verbatim
namespace Local


-- @@ L44-47 verbatim
/-!
## A. First-variation values

-/


-- @@ L49-55 expanded
/-- A single term in the linearized first-variation density before integration by parts. -/
noncomputable def firstVariationDensityTerm (L : Lagrangian d m k)
    (f : Space d → EuclideanSpace ℝ (Fin m)) (η : AdmissibleVariation d (EuclideanSpace ℝ (Fin m)))
    (I : DerivativeIndex d k) (a : Fin m) : Space d → ℝ := fun x =>
  L.coordDeriv I a (jetAt k f x) * (iteratedDeriv I.1) (fun y => (η y) a) x


-- @@ L57-61 verbatim
/-- The pointwise linearized first-variation density before integration by parts. -/
noncomputable def firstVariationDensity (L : Lagrangian d m k)
    (f : Space d → EuclideanSpace ℝ (Fin m))
    (η : AdmissibleVariation d (EuclideanSpace ℝ (Fin m))) : Space d → ℝ :=
  fun x => ∑ I : DerivativeIndex d k, ∑ a : Fin m, firstVariationDensityTerm L f η I a x


-- @@ L63-67 verbatim
/-- The value predicted by the first-variation formula for an admissible variation. -/
noncomputable def firstVariationValue (L : Lagrangian d m k)
    (f : Space d → EuclideanSpace ℝ (Fin m))
    (η : AdmissibleVariation d (EuclideanSpace ℝ (Fin m))) : ℝ :=
  ∫ x, ⟪eulerLagrangeOp L f x, η x⟫_ℝ


-- @@ L69-75 expanded
@[simp]
lemma firstVariationDensityTerm_apply (L : Lagrangian d m k)
    (f : Space d → EuclideanSpace ℝ (Fin m)) (η : AdmissibleVariation d (EuclideanSpace ℝ (Fin m)))
    (I : DerivativeIndex d k) (a : Fin m) (x : Space d) :
    firstVariationDensityTerm L f η I a x =
      L.coordDeriv I a (jetAt k f x) * (iteratedDeriv I.1) (fun y => (η y) a) x :=
  rfl


-- @@ L77-82 verbatim
@[simp]
lemma firstVariationDensity_apply (L : Lagrangian d m k)
    (f : Space d → EuclideanSpace ℝ (Fin m))
    (η : AdmissibleVariation d (EuclideanSpace ℝ (Fin m))) (x : Space d) :
    firstVariationDensity L f η x =
      ∑ I : DerivativeIndex d k, ∑ a : Fin m, firstVariationDensityTerm L f η I a x := rfl


-- @@ L84-88 verbatim
@[simp]
lemma firstVariationValue_eq_integral (L : Lagrangian d m k)
    (f : Space d → EuclideanSpace ℝ (Fin m))
    (η : AdmissibleVariation d (EuclideanSpace ℝ (Fin m))) :
    firstVariationValue L f η = ∫ x, ⟪eulerLagrangeOp L f x, η x⟫_ℝ := rfl


-- @@ L90-96 verbatim
lemma firstVariationValue_eq_zero_of_eulerLagrange_zero
    (L : Lagrangian d m k) (f : Space d → EuclideanSpace ℝ (Fin m))
    (η : AdmissibleVariation d (EuclideanSpace ℝ (Fin m))) (hEuler : eulerLagrangeOp L f = 0) :
    firstVariationValue L f η = 0 := by
  unfold firstVariationValue
  rw [hEuler]
  simp


-- @@ L98-98 verbatim
end Local

-- @@ L99-99 verbatim
end ClassicalFieldTheory
