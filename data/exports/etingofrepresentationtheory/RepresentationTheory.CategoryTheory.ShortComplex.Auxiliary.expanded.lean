/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import RepresentationTheory.Alignment.Attribute


-- @@ L11-16 verbatim
/-!
# Auxiliary short-complex data

This module provides auxiliary data and a characterization of short exact complexes in abelian
categories.
-/


-- @@ L18-18 verbatim
open CategoryTheory


-- @@ L20-20 verbatim
namespace RepresentationTheory.CategoryTheory.ShortComplex.Auxiliary


-- @@ L22-25 verbatim
/-- Auxiliary data in a category equipped with zero morphisms. -/
@[source_ref "Chapter7/Definition7.8.2" (role := supporting)]
def Data (C : Type*) [Category C] [Limits.HasZeroMorphisms C] :=
  {S : ShortComplex C // S.ShortExact}


-- @@ L27-36 verbatim
/-- Data in a category equipped with zero morphisms, indexed by two objects. -/
@[source_ref "Chapter7/Definition7.8.2" (role := supporting)]
structure ZeroMorphismsData (C : Type*) [Category C] [Limits.HasZeroMorphisms C]
    (Z X : C) where
  /-- Converts this data to auxiliary categorical data. -/
  toData : Data C
  /-- An isomorphism from the first endpoint of the associated short complex to `X`. -/
  leftIso : toData.1.X₁ ≅ X
  /-- An isomorphism from the third endpoint of the associated short complex to `Z`. -/
  rightIso : toData.1.X₃ ≅ Z


-- @@ L38-38 verbatim
namespace Data


-- @@ L40-46 verbatim
/-- Converts auxiliary categorical data to zero-morphism data indexed by the endpoints of a short complex. -/
@[source_ref "Chapter7/Definition7.8.2" (role := primary)]
def toZeroMorphismsData {C : Type*} [Category C] [Limits.HasZeroMorphisms C] (S : Data C) :
    ZeroMorphismsData C S.1.X₃ S.1.X₁ where
  toData := S
  leftIso := Iso.refl _
  rightIso := Iso.refl _


-- @@ L48-48 verbatim
end Data


-- @@ L50-50 verbatim
namespace ZeroMorphismsData


-- @@ L52-56 verbatim
/-- A second conversion of this data to auxiliary categorical data. -/
@[source_ref "Chapter7/Definition7.8.2" (role := supporting)]
def toData' {C : Type*} [Category C] [Limits.HasZeroMorphisms C] {Z X : C}
    (E : ZeroMorphismsData C Z X) : Data C :=
  E.toData


-- @@ L58-58 verbatim
end ZeroMorphismsData


-- @@ L60-80 verbatim
/-- A short complex in an abelian category is short exact exactly when its first map is mono, its second map is epi, and the induced cokernel morphism is an isomorphism. -/
@[source_ref "Chapter7/Definition7.8.2" (role := supporting)]
theorem shortExact_iff_mono_epi_isIso_cokernelDesc {C : Type*} [Category C]
    [Abelian C] (S : ShortComplex C) :
    S.ShortExact ↔ Mono S.f ∧ Epi S.g ∧
      IsIso (Limits.cokernel.desc S.f S.g S.zero) := by
  open CategoryTheory CategoryTheory.Limits in
  constructor
  · intro h
    haveI : Mono S.f := h.mono_f
    haveI : Epi S.g := h.epi_g
    haveI : Mono (cokernel.desc S.f S.g S.zero) := h.exact.mono_cokernelDesc
    haveI : Epi (cokernel.desc S.f S.g S.zero) :=
      epi_of_epi_fac (cokernel.π_desc S.f S.g S.zero)
    exact ⟨inferInstance, inferInstance, isIso_of_mono_of_epi _⟩
  · rintro ⟨hf, hg, hq⟩
    haveI : Mono S.f := hf
    haveI : Epi S.g := hg
    haveI : IsIso (cokernel.desc S.f S.g S.zero) := hq
    exact ShortComplex.ShortExact.mk'
      (S.exact_iff_mono_cokernel_desc.mpr inferInstance) hf hg


-- @@ L82-82 verbatim
end RepresentationTheory.CategoryTheory.ShortComplex.Auxiliary
