/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.LinearAlgebra.Quotient.Defs
import Mathlib.RingTheory.TwoSidedIdeal.Basic
import RepresentationTheory.Alignment.Attribute


-- @@ L10-10 verbatim
/-! # Quotient constructions -/


-- @@ L12-12 verbatim
namespace RepresentationTheory.RingTheory.Quotient.Constructions


-- @@ L14-14 verbatim
section AuxiliaryQuotient


-- @@ L16-16 verbatim
variable (k A : Type*) [CommRing k] [Ring A] [Algebra k A]


-- @@ L18-20 verbatim
/-- An auxiliary type depending on a ring and a two-sided ideal. -/
@[source_ref "Chapter2/Discussion_2.5_heading" (role := supporting)]
abbrev TwoSidedIdeal.AuxiliaryType (I : TwoSidedIdeal A) : Type _ := I.ringCon.Quotient


-- @@ L22-25 verbatim
/-- The algebra structure on the ideal-dependent auxiliary type. -/
@[source_ref "Chapter2/Discussion_2.5_well_defined" (role := supporting)]
abbrev TwoSidedIdeal.auxiliaryAlgebra (I : TwoSidedIdeal A) : Algebra k (_root_.RepresentationTheory.RingTheory.Quotient.Constructions.TwoSidedIdeal.AuxiliaryType A I) :=
  inferInstance


-- @@ L27-30 verbatim
/-- An auxiliary algebra homomorphism from a ring to the ideal-dependent auxiliary type. -/
@[source_ref "Chapter2/Discussion_2.5_heading" (role := primary)]
noncomputable def TwoSidedIdeal.auxiliaryAlgHom (I : TwoSidedIdeal A) : A →ₐ[k] _root_.RepresentationTheory.RingTheory.Quotient.Constructions.TwoSidedIdeal.AuxiliaryType A I :=
  RingCon.mkₐ k I.ringCon


-- @@ L32-37 verbatim
/-- Two images under the auxiliary algebra homomorphism are equal exactly when the difference of their representatives belongs to the ideal. -/
@[source_ref "Chapter2/Discussion_2.5_heading" (role := primary)]
theorem TwoSidedIdeal.auxiliaryAlgHom_eq_iff (I : TwoSidedIdeal A) (a b : A) :
    _root_.RepresentationTheory.RingTheory.Quotient.Constructions.TwoSidedIdeal.auxiliaryAlgHom k A I a = _root_.RepresentationTheory.RingTheory.Quotient.Constructions.TwoSidedIdeal.auxiliaryAlgHom k A I b ↔ a - b ∈ I := by
  change (a : I.ringCon.Quotient) = (b : I.ringCon.Quotient) ↔ a - b ∈ I
  rw [RingCon.eq, I.rel_iff]


-- @@ L39-43 verbatim
/-- The auxiliary algebra homomorphism preserves multiplication. -/
@[source_ref "Chapter2/Discussion_2.5_heading" (role := primary)]
theorem TwoSidedIdeal.auxiliaryAlgHom_mul (I : TwoSidedIdeal A) (a b : A) :
    _root_.RepresentationTheory.RingTheory.Quotient.Constructions.TwoSidedIdeal.auxiliaryAlgHom k A I a * _root_.RepresentationTheory.RingTheory.Quotient.Constructions.TwoSidedIdeal.auxiliaryAlgHom k A I b = _root_.RepresentationTheory.RingTheory.Quotient.Constructions.TwoSidedIdeal.auxiliaryAlgHom k A I (a * b) := by
  exact (_root_.RepresentationTheory.RingTheory.Quotient.Constructions.TwoSidedIdeal.auxiliaryAlgHom k A I).map_mul a b


-- @@ L45-51 verbatim
/-- Replacing the left factor by an ideal-congruent element leaves its image product unchanged. -/
@[source_ref "Chapter2/Discussion_2.5_well_defined" (role := primary)]
theorem TwoSidedIdeal.auxiliaryAlgHom_mul_left_congr (I : TwoSidedIdeal A) (a a' b : A)
    (h : a' - a ∈ I) :
    _root_.RepresentationTheory.RingTheory.Quotient.Constructions.TwoSidedIdeal.auxiliaryAlgHom k A I (a' * b) = _root_.RepresentationTheory.RingTheory.Quotient.Constructions.TwoSidedIdeal.auxiliaryAlgHom k A I (a * b) := by
  rw [_root_.RepresentationTheory.RingTheory.Quotient.Constructions.TwoSidedIdeal.auxiliaryAlgHom_eq_iff]
  simpa [sub_mul] using I.mul_mem_right (a' - a) b h


-- @@ L53-59 verbatim
/-- Replacing the right factor by an ideal-congruent element leaves its image product unchanged. -/
@[source_ref "Chapter2/Discussion_2.5_well_defined" (role := primary)]
theorem TwoSidedIdeal.auxiliaryAlgHom_mul_right_congr (I : TwoSidedIdeal A) (a b b' : A)
    (h : b' - b ∈ I) :
    _root_.RepresentationTheory.RingTheory.Quotient.Constructions.TwoSidedIdeal.auxiliaryAlgHom k A I (a * b') = _root_.RepresentationTheory.RingTheory.Quotient.Constructions.TwoSidedIdeal.auxiliaryAlgHom k A I (a * b) := by
  rw [_root_.RepresentationTheory.RingTheory.Quotient.Constructions.TwoSidedIdeal.auxiliaryAlgHom_eq_iff]
  simpa [mul_sub] using I.mul_mem_left a (b' - b) h


-- @@ L61-61 verbatim
end AuxiliaryQuotient


-- @@ L63-63 verbatim
section QuotientModuleConstruction


-- @@ L65-65 verbatim
variable (A V : Type*) [Ring A] [AddCommGroup V] [Module A V]


-- @@ L67-69 verbatim
/-- The module structure carried by the quotient of a module by a submodule. -/
@[source_ref "Chapter2/Discussion_2.5_well_defined" (role := primary)]
abbrev Submodule.quotientModule (W : Submodule A V) : Module A (V ⧸ W) := inferInstance


-- @@ L71-75 verbatim
/-- Scalar multiplication on a submodule quotient commutes with the quotient map. -/
@[source_ref "Chapter2/Discussion_2.5_well_defined" (role := primary)]
theorem Submodule.quotient_smul_mk (W : Submodule A V) (a : A) (v : V) :
    a • (Submodule.Quotient.mk v : V ⧸ W) = Submodule.Quotient.mk (a • v) := by
  exact (Submodule.Quotient.mk_smul W a v).symm


-- @@ L77-77 verbatim
end QuotientModuleConstruction


-- @@ L79-79 verbatim
section RegularQuotientModule


-- @@ L81-81 verbatim
variable (A : Type*) [Ring A]


-- @@ L83-85 verbatim
/-- An auxiliary type depending on a ring. -/
@[source_ref "Chapter2/Discussion_2.5_well_defined" (role := supporting)]
abbrev Ring.AuxiliaryType := Submodule A A


-- @@ L87-89 verbatim
/-- The module structure on the quotient of a ring by the auxiliary quotient data. -/
@[source_ref "Chapter2/Discussion_2.5_well_defined" (role := primary)]
abbrev Ring.quotientModule (I : _root_.RepresentationTheory.RingTheory.Quotient.Constructions.Ring.AuxiliaryType A) : Module A (A ⧸ I) := inferInstance


-- @@ L91-91 verbatim
end RegularQuotientModule


-- @@ L93-93 verbatim
end RepresentationTheory.RingTheory.Quotient.Constructions
