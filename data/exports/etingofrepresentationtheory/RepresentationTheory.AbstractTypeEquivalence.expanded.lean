/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.CategoryTheory.FintypeCat
import Mathlib.CategoryTheory.Equivalence
import RepresentationTheory.Alignment.Attribute


-- @@ L10-10 verbatim
open CategoryTheory


-- @@ L12-12 verbatim
namespace RepresentationTheory.AbstractTypeEquivalence


-- @@ L14-14 verbatim
noncomputable example : FintypeCat.Skeleton ≌ FintypeCat := FintypeCat.Skeleton.equivalence


-- @@ L16-17 verbatim
/-- The type on the left side of the categorical data. -/
def Left : Type := PUnit


-- @@ L19-20 verbatim
/-- The type on the right side of the categorical data. -/
def Right : Type := Bool


-- @@ L22-26 verbatim
/-- A category structure on the left type. -/
instance leftCategory : Category Left where
  Hom _ _ := PUnit
  id _ := ⟨⟩
  comp _ _ := ⟨⟩


-- @@ L28-32 verbatim
/-- A category structure on the right type. -/
instance rightCategory : Category Right where
  Hom _ _ := PUnit
  id _ := ⟨⟩
  comp _ _ := ⟨⟩


-- @@ L34-37 verbatim
/-- A functor from the left type to the right type. -/
def leftToRight : Left ⥤ Right where
  obj _ := true
  map _ := ⟨⟩


-- @@ L39-42 verbatim
/-- A functor from the right type to the left type. -/
def rightToLeft : Right ⥤ Left where
  obj _ := ⟨⟩
  map _ := ⟨⟩


-- @@ L44-51 verbatim
/-- An equivalence between the left and right types equipped with their category structures. -/
@[source_ref "Chapter7/Discussion_after_Definition7.4.1" (role := primary)]
def equivalence : Left ≌ Right where
  functor := leftToRight
  inverse := rightToLeft
  unitIso := NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)
  counitIso := NatIso.ofComponents (fun _ => Iso.mk ⟨⟩ ⟨⟩) (fun _ => rfl)
  functor_unitIso_comp _ := rfl


-- @@ L53-53 verbatim
end RepresentationTheory.AbstractTypeEquivalence
