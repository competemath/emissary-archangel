/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.QFT.PerturbationTheory.FieldSpecification.CrAnFieldOp

-- @@ L9-13 verbatim
/-!

# Filters of lists of CrAnFieldOp

-/


-- @@ L15-15 verbatim
@[expose] public section


-- @@ L17-17 verbatim
namespace FieldSpecification

-- @@ L18-18 verbatim
variable {𝓕 : FieldSpecification}


-- @@ L20-25 verbatim
/-- Given a list of creation and annihilation states, the filtered list only containing
  the creation states. As a schematic example, for the list:
  - `[φ1c, φ1a, φ2c, φ2a]` this will return `[φ1c, φ2c]`.
-/
def createFilter (φs : List 𝓕.CrAnFieldOp) : List 𝓕.CrAnFieldOp :=
  List.filter (fun φ => 𝓕 |>ᶜ φ = CreateAnnihilate.create) φs


-- @@ L27-32 verbatim
lemma createFilter_cons_create {φ : 𝓕.CrAnFieldOp}
    (hφ : 𝓕 |>ᶜ φ = CreateAnnihilate.create) (φs : List 𝓕.CrAnFieldOp) :
    createFilter (φ :: φs) = φ :: createFilter φs := by
  simp only [createFilter]
  rw [List.filter_cons_of_pos]
  simp [hφ]


-- @@ L34-39 verbatim
lemma createFilter_cons_annihilate {φ : 𝓕.CrAnFieldOp}
    (hφ : 𝓕 |>ᶜ φ = CreateAnnihilate.annihilate) (φs : List 𝓕.CrAnFieldOp) :
    createFilter (φ :: φs) = createFilter φs := by
  simp only [createFilter]
  rw [List.filter_cons_of_neg]
  simp [hφ]


-- @@ L41-44 verbatim
lemma createFilter_append (φs φs' : List 𝓕.CrAnFieldOp) :
    createFilter (φs ++ φs') = createFilter φs ++ createFilter φs' := by
  rw [createFilter, List.filter_append]
  rfl


-- @@ L46-49 verbatim
lemma createFilter_singleton_create (φ : 𝓕.CrAnFieldOp)
    (hφ : 𝓕 |>ᶜ φ = CreateAnnihilate.create) :
    createFilter [φ] = [φ] := by
  simp [createFilter, hφ]


-- @@ L51-53 verbatim
lemma createFilter_singleton_annihilate (φ : 𝓕.CrAnFieldOp)
    (hφ : 𝓕 |>ᶜ φ = CreateAnnihilate.annihilate) : createFilter [φ] = [] := by
  simp [createFilter, hφ]


-- @@ L55-61 verbatim
/-- Given a list of creation and annihilation states, the filtered list only containing
  the annihilation states.
  As a schematic example, for the list:
  - `[φ1c, φ1a, φ2c, φ2a]` this will return `[φ1a, φ2a]`.
-/
def annihilateFilter (φs : List 𝓕.CrAnFieldOp) : List 𝓕.CrAnFieldOp :=
  List.filter (fun φ => 𝓕 |>ᶜ φ = CreateAnnihilate.annihilate) φs


-- @@ L63-68 verbatim
lemma annihilateFilter_cons_create {φ : 𝓕.CrAnFieldOp}
    (hφ : 𝓕 |>ᶜ φ = CreateAnnihilate.create) (φs : List 𝓕.CrAnFieldOp) :
    annihilateFilter (φ :: φs) = annihilateFilter φs := by
  simp only [annihilateFilter]
  rw [List.filter_cons_of_neg]
  simp [hφ]


-- @@ L70-75 verbatim
lemma annihilateFilter_cons_annihilate {φ : 𝓕.CrAnFieldOp}
    (hφ : 𝓕 |>ᶜ φ = CreateAnnihilate.annihilate) (φs : List 𝓕.CrAnFieldOp) :
    annihilateFilter (φ :: φs) = φ :: annihilateFilter φs := by
  simp only [annihilateFilter]
  rw [List.filter_cons_of_pos]
  simp [hφ]


-- @@ L77-80 verbatim
lemma annihilateFilter_append (φs φs' : List 𝓕.CrAnFieldOp) :
    annihilateFilter (φs ++ φs') = annihilateFilter φs ++ annihilateFilter φs' := by
  rw [annihilateFilter, List.filter_append]
  rfl


-- @@ L82-85 verbatim
lemma annihilateFilter_singleton_create (φ : 𝓕.CrAnFieldOp)
    (hφ : 𝓕 |>ᶜ φ = CreateAnnihilate.create) :
    annihilateFilter [φ] = [] := by
  simp [annihilateFilter, hφ]


-- @@ L87-90 verbatim
lemma annihilateFilter_singleton_annihilate (φ : 𝓕.CrAnFieldOp)
    (hφ : 𝓕 |>ᶜ φ = CreateAnnihilate.annihilate) :
    annihilateFilter [φ] = [φ] := by
  simp [annihilateFilter, hφ]


-- @@ L92-92 verbatim
end FieldSpecification
