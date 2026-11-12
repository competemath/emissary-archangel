/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import RepresentationTheory.Alignment.Attribute
import RepresentationTheory.CategoryTheory.QuiverAuxiliary
import RepresentationTheory.CategoryTheory.QuiverLinearMaps
import RepresentationTheory.Algebra.Quiver.AuxiliaryConstructions


-- @@ L12-12 verbatim
/-! # Auxiliary dependent properties for quiver-indexed objects -/


-- @@ L14-14 verbatim
namespace RepresentationTheory.CategoryTheory.QuiverAuxiliary.AuxiliaryType


-- @@ L16-16 verbatim
open RepresentationTheory.CategoryTheory.QuiverLinearDiagrams


-- @@ L18-18 verbatim
universe u v w q


-- @@ L20-20 verbatim
variable {k : Type u} {Q : Type v} [CommSemiring k] [Quiver.{w} Q]

-- @@ L21-21 verbatim
variable {ρ : AuxiliaryQuiverModuleData.{u, v, q, w} k Q}


-- @@ L23-27 verbatim
/-- Selects an element of the displayed dependent type for each quiver-dependent object. -/
noncomputable def elementAux (ρ : AuxiliaryQuiverModuleData.{u, v, q, w} k Q) :
    AuxiliaryType k Q ρ where
  carrier := fun _ => ⊥
  map_mem := by simp


-- @@ L29-33 verbatim
/-- Selects a second element of the displayed dependent type for each quiver-dependent object. -/
noncomputable def elementAux' (ρ : AuxiliaryQuiverModuleData.{u, v, q, w} k Q) :
    AuxiliaryType k Q ρ where
  carrier := fun _ => ⊤
  map_mem := by simp


-- @@ L35-37 verbatim
/-- The second auxiliary predicate on an element of the displayed dependent type. -/
def predicateAux' (S : AuxiliaryType k Q ρ) : Prop :=
  ∀ i, S.carrier i = ⊥


-- @@ L39-41 verbatim
/-- The first auxiliary predicate on an element of the displayed dependent type. -/
def predicateAux (S : AuxiliaryType k Q ρ) : Prop :=
  ∀ i, S.carrier i = ⊤


-- @@ L43-44 verbatim
/-- The first auxiliary selection satisfies the second auxiliary predicate. -/
theorem predicateAux'_elementAux : predicateAux' (elementAux ρ) := fun _ => rfl


-- @@ L46-47 verbatim
/-- The second auxiliary selection satisfies the first auxiliary predicate. -/
theorem predicateAux_elementAux' : predicateAux (elementAux' ρ) := fun _ => rfl


-- @@ L49-49 verbatim
end RepresentationTheory.CategoryTheory.QuiverAuxiliary.AuxiliaryType


-- @@ L51-51 verbatim
namespace RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData


-- @@ L53-53 verbatim
open RepresentationTheory.CategoryTheory.QuiverLinearMaps

-- @@ L54-54 verbatim
open RepresentationTheory.CategoryTheory.QuiverAuxiliary


-- @@ L56-56 verbatim
universe u v w q


-- @@ L58-58 verbatim
variable {k : Type u} {Q : Type v} [CommSemiring k] [Quiver.{w} Q]


-- @@ L60-63 verbatim
/-- The fourth auxiliary predicate on the displayed quiver-dependent object. -/
@[source_ref "Chapter2/Discussion_quiver_irreducible_indecomposable" (role := supporting)]
def predicateAux''' (ρ : AuxiliaryQuiverModuleData.{u, v, q, w} k Q) : Prop :=
  ∀ (i : Q) (x : ρ.obj i), x = 0


-- @@ L65-68 verbatim
/-- The third auxiliary predicate on the displayed quiver-dependent object. -/
@[source_ref "Chapter2/Discussion_quiver_irreducible_indecomposable" (role := supporting)]
def predicateAux'' (ρ : AuxiliaryQuiverModuleData.{u, v, q, w} k Q) : Prop :=
  ¬predicateAux''' ρ


-- @@ L70-74 verbatim
/-- The second auxiliary predicate on the displayed quiver-dependent object. -/
@[source_ref "Chapter2/Discussion_quiver_irreducible_indecomposable" (role := supporting)]
def predicateAux' (ρ : AuxiliaryQuiverModuleData.{u, v, q, w} k Q) : Prop :=
  predicateAux'' ρ ∧ ∀ S : AuxiliaryType k Q ρ,
    S.predicateAux' ∨ S.predicateAux


-- @@ L76-81 verbatim
/-- The first auxiliary predicate on the displayed quiver-dependent object. -/
@[source_ref "Chapter2/Discussion_quiver_irreducible_indecomposable" (role := supporting)]
def predicateAux (ρ : AuxiliaryQuiverModuleData.{u, v, q, w} k Q) : Prop :=
  predicateAux'' ρ ∧ ∀ (ρ₁ ρ₂ : AuxiliaryQuiverModuleData.{u, v, q, w} k Q),
    AuxiliaryQuiverEquivData k Q ρ (auxiliaryBinaryConstruction k Q ρ₁ ρ₂) →
      predicateAux''' ρ₁ ∨ predicateAux''' ρ₂


-- @@ L83-83 verbatim
end RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData
