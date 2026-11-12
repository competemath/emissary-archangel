/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import Mathlib.CategoryTheory.Abelian.Projective.Dimension
import Mathlib.Algebra.Category.ModuleCat.Abelian
import RepresentationTheory.Alignment.Attribute


-- @@ L11-11 verbatim
universe u


-- @@ L13-13 verbatim
open CategoryTheory


-- @@ L15-15 verbatim
namespace RepresentationTheory.ProjectiveDimension


-- @@ L17-21 verbatim
/-- An auxiliary extended-natural-valued invariant of a module used to characterize projective
dimension. -/
noncomputable def projectiveDimensionAux
    (R : Type u) [Ring R] (M : ModuleCat.{u} R) : WithBot ℕ∞ :=
  CategoryTheory.projectiveDimension M


-- @@ L23-26 verbatim
/-- The projective dimension of a module, valued in extended natural numbers. -/
noncomputable def projectiveDimension
    (R : Type u) [Ring R] (M : ModuleCat.{u} R) : WithBot ℕ∞ :=
  max 0 (projectiveDimensionAux R M)


-- @@ L28-28 verbatim
variable {R : Type u} [Ring R]


-- @@ L30-33 verbatim
/-- Zero is at most the projective dimension of every module. -/
lemma zero_le_projectiveDimension (M : ModuleCat.{u} R) :
    (0 : WithBot ℕ∞) ≤ projectiveDimension R M :=
  le_max_left _ _


-- @@ L35-44 verbatim
/-- For a nonzero module, zero is at most the auxiliary module invariant. -/
lemma zero_le_projectiveDimensionAux (M : ModuleCat.{u} R)
    (hM : ¬ Limits.IsZero M) : (0 : WithBot ℕ∞) ≤ projectiveDimensionAux R M := by
  have h : projectiveDimensionAux R M ≠ ⊥ := by
    rw [projectiveDimensionAux, Ne, CategoryTheory.projectiveDimension_eq_bot_iff]
    exact hM
  obtain ⟨b, hb⟩ := WithBot.ne_bot_iff_exists.1 h
  calc (0 : WithBot ℕ∞) = ((0 : ℕ∞) : WithBot ℕ∞) := by rw [WithBot.coe_zero]
    _ ≤ (b : WithBot ℕ∞) := WithBot.coe_le_coe.2 zero_le
    _ = projectiveDimensionAux R M := hb


-- @@ L46-54 verbatim
/-- The projective dimension is at most a natural number exactly when the module has projective
dimension bounded by that number. -/
lemma projectiveDimension_le_iff (M : ModuleCat.{u} R) (n : ℕ) :
    projectiveDimension R M ≤ (n : WithBot ℕ∞) ↔ HasProjectiveDimensionLE M n := by
  simp only [projectiveDimension, projectiveDimensionAux, max_le_iff]
  rw [CategoryTheory.projectiveDimension_le_iff]
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  calc (0 : WithBot ℕ∞) = ((0 : ℕ) : WithBot ℕ∞) := by rw [Nat.cast_zero]
    _ ≤ (n : WithBot ℕ∞) := by exact_mod_cast Nat.zero_le n


-- @@ L56-61 verbatim
/-- A module has projective dimension zero exactly when it is projective. -/
lemma projectiveDimension_eq_zero_iff_projective (M : ModuleCat.{u} R) :
    projectiveDimension R M = 0 ↔ Projective M := by
  rw [le_antisymm_iff, and_iff_left (zero_le_projectiveDimension M)]
  rw [show (0 : WithBot ℕ∞) = ((0 : ℕ) : WithBot ℕ∞) from by rw [Nat.cast_zero],
    projectiveDimension_le_iff, ← projective_iff_hasProjectiveDimensionLE_zero]


-- @@ L63-66 verbatim
/-- A zero module has projective dimension zero. -/
lemma projectiveDimension_eq_zero_of_isZero (M : ModuleCat.{u} R) (hM : Limits.IsZero M) :
    projectiveDimension R M = 0 :=
  (projectiveDimension_eq_zero_iff_projective M).2 hM.projective


-- @@ L68-72 verbatim
/-- For a nonzero module, the projective dimension equals the auxiliary module invariant. -/
lemma projectiveDimension_eq_projectiveDimensionAux (M : ModuleCat.{u} R)
    (hM : ¬ Limits.IsZero M) :
    projectiveDimension R M = projectiveDimensionAux R M := by
  rw [projectiveDimension, max_eq_right (zero_le_projectiveDimensionAux M hM)]


-- @@ L74-76 verbatim
end RepresentationTheory.ProjectiveDimension

-- Recovered exact-module book alignment.

-- @@ L77-77 verbatim
attribute [source_ref "Chapter9/Definition9.4.1" (role := primary)] _root_.RepresentationTheory.ProjectiveDimension.projectiveDimension

-- @@ L78-78 verbatim
attribute [source_ref "Chapter9/Definition9.4.1" (role := supporting)] _root_.RepresentationTheory.ProjectiveDimension.projectiveDimensionAux

-- @@ L79-79 verbatim
attribute [source_ref "Chapter9/Definition9.4.1" (role := supporting)] _root_.RepresentationTheory.ProjectiveDimension.projectiveDimension_eq_projectiveDimensionAux

-- @@ L80-80 verbatim
attribute [source_ref "Chapter9/Definition9.4.1" (role := supporting)] _root_.RepresentationTheory.ProjectiveDimension.projectiveDimension_eq_zero_iff_projective

-- @@ L81-81 verbatim
attribute [source_ref "Chapter9/Definition9.4.1" (role := supporting)] _root_.RepresentationTheory.ProjectiveDimension.projectiveDimension_eq_zero_of_isZero

-- @@ L82-82 verbatim
attribute [source_ref "Chapter9/Definition9.4.1" (role := supporting)] _root_.RepresentationTheory.ProjectiveDimension.projectiveDimension_le_iff

-- @@ L83-83 verbatim
attribute [source_ref "Chapter9/Definition9.4.1" (role := supporting)] _root_.RepresentationTheory.ProjectiveDimension.zero_le_projectiveDimension

-- @@ L84-84 verbatim
attribute [source_ref "Chapter9/Definition9.4.1" (role := supporting)] _root_.RepresentationTheory.ProjectiveDimension.zero_le_projectiveDimensionAux
