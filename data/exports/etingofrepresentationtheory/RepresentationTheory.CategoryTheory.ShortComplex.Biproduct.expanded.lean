/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import RepresentationTheory.Alignment.Attribute


-- @@ L11-11 verbatim
open CategoryTheory CategoryTheory.Limits


-- @@ L13-13 verbatim
namespace RepresentationTheory.CategoryTheory.ShortComplex.Biproduct


-- @@ L15-15 verbatim
variable {C : Type*} [Category C] [Preadditive C] [HasBinaryBiproducts C]


-- @@ L17-19 verbatim
/-- The short complex formed by the two canonical maps through a binary biproduct. -/
noncomputable abbrev biproductShortComplex (X Z : C) : ShortComplex C :=
  ShortComplex.mk (biprod.inl : X ⟶ X ⊞ Z) biprod.snd (by simp)


-- @@ L21-25 verbatim
/-- A splitting of the short complex associated with a binary biproduct. -/
@[source_ref "Chapter7/Example7.8.3" (role := supporting)]
noncomputable def biproductShortComplexSplitting (X Z : C) :
    (biproductShortComplex X Z).Splitting :=
  ShortComplex.Splitting.ofHasBinaryBiproduct X Z


-- @@ L27-30 verbatim
/-- The retraction component of this splitting is the first biproduct projection. -/
@[simp]
theorem biproductShortComplexSplitting_r (X Z : C) :
    (biproductShortComplexSplitting X Z).r = biprod.fst := rfl


-- @@ L32-35 verbatim
/-- The section component of this splitting is the second biproduct inclusion. -/
@[simp]
theorem biproductShortComplexSplitting_s (X Z : C) :
    (biproductShortComplexSplitting X Z).s = biprod.inr := rfl


-- @@ L37-40 verbatim
/-- The retraction in the chosen splitting is a left inverse to the first biproduct inclusion. -/
theorem biproductShortComplexSplitting_inl_comp_r (X Z : C) :
    (biprod.inl : X ⟶ X ⊞ Z) ≫ (biproductShortComplexSplitting X Z).r = 𝟙 X :=
  (biproductShortComplexSplitting X Z).f_r


-- @@ L42-45 verbatim
/-- The section in the chosen splitting is a right inverse to the second biproduct projection. -/
theorem biproductShortComplexSplitting_s_comp_snd (X Z : C) :
    (biproductShortComplexSplitting X Z).s ≫ (biprod.snd : X ⊞ Z ⟶ Z) = 𝟙 Z :=
  (biproductShortComplexSplitting X Z).s_g


-- @@ L47-52 verbatim
/-- The two summand endomorphisms determined by the splitting add to the identity of the
biproduct. -/
theorem biproductShortComplexSplitting_r_comp_inl_add_snd_comp_s (X Z : C) :
    (biproductShortComplexSplitting X Z).r ≫ (biprod.inl : X ⟶ X ⊞ Z) +
      (biprod.snd : X ⊞ Z ⟶ Z) ≫ (biproductShortComplexSplitting X Z).s = 𝟙 (X ⊞ Z) :=
  (biproductShortComplexSplitting X Z).id


-- @@ L54-57 verbatim
/-- The first inclusion into a binary biproduct is exhibited as a split monomorphism. -/
noncomputable def biprodInlSplitMono (X Z : C) :
    SplitMono (biprod.inl : X ⟶ X ⊞ Z) :=
  (biproductShortComplexSplitting X Z).splitMono_f


-- @@ L59-62 verbatim
/-- The second projection from a binary biproduct is exhibited as a split epimorphism. -/
noncomputable def biprodSndSplitEpi (X Z : C) :
    SplitEpi (biprod.snd : X ⊞ Z ⟶ Z) :=
  (biproductShortComplexSplitting X Z).splitEpi_g


-- @@ L64-68 verbatim
/-- The binary-biproduct short complex is short exact when a zero object is available. -/
@[source_ref "Chapter7/Example7.8.3" (role := supporting)]
theorem biproductShortComplex_shortExact [HasZeroObject C] (X Z : C) :
    (biproductShortComplex X Z).ShortExact :=
  (biproductShortComplexSplitting X Z).shortExact


-- @@ L70-70 verbatim
end RepresentationTheory.CategoryTheory.ShortComplex.Biproduct
