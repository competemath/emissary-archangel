/-
Copyright (c) 2026 Juan Jose Fernandez Morales. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Jose Fernandez Morales
-/
module

public import PhyslibAlpha.ClassicalFieldTheory.Local.FirstVariation.Basic

-- @@ L9-33 verbatim
/-!
# First variation support lemmas

## i. Overview

This module collects the reusable support lemmas used by the analytic part of the local
first-variation proof: basic identities for varied fields, iterated derivative regularity for
test functions, and continuity of the varied local-jet coordinate map.

## ii. Key results

- `ClassicalFieldTheory.Local.variedField_zero`
- `ClassicalFieldTheory.Local.variedField_variedField`

## iii. Table of contents

- A. Varied fields
- B. Iterated derivative support lemmas
- C. Varied local-jet coordinates

## iv. References

* J. Cortés and A. Haupt, Lecture Notes on Mathematical Methods of Classical Physics, Chapter 5,
  Theorem 5.2. [ref: cortes_haupt_2016]
-/


-- @@ L35-35 verbatim
@[expose] public section


-- @@ L37-37 verbatim
open MeasureTheory

-- @@ L38-38 verbatim
open InnerProductSpace

-- @@ L39-39 verbatim
open Physlib

-- @@ L40-40 verbatim
open scoped BigOperators ContDiff


-- @@ L42-42 verbatim
namespace ClassicalFieldTheory

-- @@ L43-43 verbatim
namespace Local


-- @@ L45-48 verbatim
/-!
## A. Varied fields

-/


-- @@ L50-55 verbatim
@[simp]
lemma variedField_zero (f : Space d → EuclideanSpace ℝ (Fin m))
    (η : AdmissibleVariation d (EuclideanSpace ℝ (Fin m))) :
    variedField f η 0 = f := by
  funext x
  simp [variedField]


-- @@ L57-63 verbatim
@[simp]
lemma variedField_variedField (f : Space d → EuclideanSpace ℝ (Fin m))
    (η : AdmissibleVariation d (EuclideanSpace ℝ (Fin m)))
    (s t : ℝ) :
    variedField (variedField f η s) η t = variedField f η (s + t) := by
  funext x
  simp [variedField, add_assoc, add_smul]


-- @@ L65-68 verbatim
/-!
## B. Iterated derivative support lemmas

-/


-- @@ L70-74 expanded
lemma contDiff_space_deriv {g : Space d → ℝ} (hg : ContDiff ℝ ∞ g) (i : Fin d) :
    ContDiff ℝ ∞ ((deriv i) g) :=
  by
  have hfamily : ContDiff ℝ ∞ (fun x : Space d => fun j : Fin d => (deriv j) g x) := by
    simpa using (Space.deriv_contDiff (n := ∞) hg)
  exact (contDiff_apply ℝ ℝ i).comp hfamily


-- @@ L76-78 expanded
lemma isTestFunction_space_deriv {g : Space d → ℝ} (hg : IsTestFunction g) (i : Fin d) :
    IsTestFunction ((deriv i) g) := by
  simpa [Space.deriv_eq_fderiv_fun] using IsTestFunction.fderiv_apply hg (Space.basis i)


-- @@ L80-88 expanded
lemma iteratedDerivList_contDiff (L : List (Fin d)) {g : Space d → ℝ} (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (L.foldr (fun i h => (deriv i) h) g) := by
  induction L generalizing g with
  | nil => simpa using hg
  | cons i L
    ih =>
    have htail : ContDiff ℝ ∞ (L.foldr (fun j h => (deriv j) h) g) := ih hg
    exact contDiff_space_deriv htail i


-- @@ L90-98 expanded
lemma iteratedDerivList_isTestFunction (L : List (Fin d)) {g : Space d → ℝ}
    (hg : IsTestFunction g) : IsTestFunction (L.foldr (fun i h => (deriv i) h) g) := by
  induction L generalizing g with
  | nil => simpa using hg
  | cons i L ih =>
    simp only [List.foldr]
    exact isTestFunction_space_deriv (ih hg) i


-- @@ L100-113 expanded
lemma iteratedDerivList_commute_deriv (L : List (Fin d)) (i : Fin d) {g : Space d → ℝ}
    (hg : ContDiff ℝ ∞ g) :
    L.foldr (fun j h => (deriv j) h) ((deriv i) g) =
      (deriv i) (L.foldr (fun j h => (deriv j) h) g) :=
  by
  induction L generalizing g with
  | nil => rfl
  | cons j L ih =>
    simp only [List.foldr]
    rw [ih hg]
    rw [Space.deriv_commute (u := j) (v := i)]
    have h2 : ContDiff ℝ (2 : ℕ∞) (L.foldr (fun j h => (deriv j) h) g) := by
      exact (iteratedDerivList_contDiff L hg).of_le (by exact WithTop.coe_le_coe.mpr le_top)
    exact h2


-- @@ L115-119 expanded
lemma iteratedDeriv_coord_isTestFunction (η : AdmissibleVariation d (EuclideanSpace ℝ (Fin m)))
    (I : DerivativeIndex d k) (a : Fin m) :
    IsTestFunction (fun x => (iteratedDeriv I.1) (fun y => (η y) a) x) := by
  simpa [Space.iteratedDeriv, Space.coord] using
    iteratedDerivList_isTestFunction I.1.toList (η.coord_euclidean a)


-- @@ L121-136 expanded
lemma firstVariationDensityTerm_integrable_of_continuous_coordDeriv (L : Lagrangian d m k)
    (f : Space d → EuclideanSpace ℝ (Fin m)) (η : AdmissibleVariation d (EuclideanSpace ℝ (Fin m)))
    (I : DerivativeIndex d k) (a : Fin m)
    (hcont : Continuous (fun x : Space d => L.coordDeriv I a (jetAt k f x))) :
    Integrable (firstVariationDensityTerm L f η I a) :=
  by
  let ψ : Space d → ℝ := fun x => (iteratedDeriv I.1) (fun y => (η y) a) x
  have hψ : IsTestFunction ψ := iteratedDeriv_coord_isTestFunction η I a
  have hψcont : Continuous ψ := hψ.contDiff.continuous
  have htermCont : Continuous (fun x => L.coordDeriv I a (jetAt k f x) * ψ x) := hcont.mul hψcont
  have hsupp : HasCompactSupport (fun x => L.coordDeriv I a (jetAt k f x) * ψ x) :=
    HasCompactSupport.mul_left hψ.supp
  exact htermCont.integrable_of_hasCompactSupport hsupp


-- @@ L138-141 verbatim
/-!
## C. Varied local-jet coordinates

-/


-- @@ L143-172 verbatim
lemma continuous_jetBaseCoordinates_variedField
    (k : ℕ) (f : Space d → EuclideanSpace ℝ (Fin m))
    (η : AdmissibleVariation d (EuclideanSpace ℝ (Fin m)))
    (hf : ContDiff ℝ ∞ f) :
    Continuous
      (fun p : ℝ × Space d => (p.2, jetCoordinatesAt k (variedField f η p.1) p.2)) := by
  have hfjet : Continuous (jetCoordinatesAt k f) :=
    (jetCoordinatesAt_contDiff k f hf).continuous
  have hηjet : Continuous (jetCoordinatesAt k η) :=
    (jetCoordinatesAt_contDiff k η η.isTestFunction.contDiff).continuous
  have hcoord :
      Continuous
        (fun p : ℝ × Space d =>
          jetCoordinatesAt k f p.2 + p.1 • jetCoordinatesAt k η p.2) := by
    exact (hfjet.comp continuous_snd).add (continuous_fst.smul (hηjet.comp continuous_snd))
  have hpair :
      Continuous
        (fun p : ℝ × Space d =>
          (p.2, jetCoordinatesAt k f p.2 + p.1 • jetCoordinatesAt k η p.2)) := by
    exact Continuous.prodMk continuous_snd hcoord
  have heq :
      (fun p : ℝ × Space d => (p.2, jetCoordinatesAt k (variedField f η p.1) p.2)) =
      (fun p : ℝ × Space d =>
        (p.2, jetCoordinatesAt k f p.2 + p.1 • jetCoordinatesAt k η p.2)) := by
    funext p
    congr 1
    exact
      (jetCoordinatesAt_add_smul k f η p.2 p.1 hf η.isTestFunction.contDiff)
  rw [heq]
  exact hpair


-- @@ L174-174 verbatim
end Local

-- @@ L175-175 verbatim
end ClassicalFieldTheory
