/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import RepresentationTheory.LinearAlgebra.ModuleAuxiliaryData
import Mathlib.RingTheory.SimpleRing.Basic
import Mathlib.RingTheory.TwoSidedIdeal.Kernel
import Mathlib.RingTheory.TwoSidedIdeal.Operations
import RepresentationTheory.Alignment.Attribute


-- @@ L12-12 verbatim
/-! # Auxiliary ring-dependent types and operations -/


-- @@ L14-14 verbatim
namespace RepresentationTheory.RingTheory.TwoSidedIdeal.Basic


-- @@ L16-16 verbatim
open scoped Pointwise


-- @@ L18-18 verbatim
variable (A : Type*) [Ring A]


-- @@ L20-22 verbatim
/-- A second auxiliary type depending on a ring. -/
@[source_ref "Chapter2/Discussion_2.4_heading" (role := supporting)]
abbrev Ring.AuxiliaryType' := Submodule A A


-- @@ L24-26 verbatim
/-- A third auxiliary type depending on a ring. -/
@[source_ref "Chapter2/Discussion_2.4_heading" (role := supporting)]
abbrev Ring.AuxiliaryType'' := Submodule Aᵐᵒᵖ Aᵐᵒᵖ


-- @@ L28-30 verbatim
/-- An auxiliary type depending on a ring. -/
@[source_ref "Chapter2/Discussion_2.4_heading" (role := supporting)]
abbrev Ring.AuxiliaryType := TwoSidedIdeal A


-- @@ L32-34 verbatim
/-- An auxiliary predicate on rings. -/
@[source_ref "Chapter2/Discussion_2.4_heading" (role := supporting)]
abbrev Ring.AuxiliaryPredicate : Prop := IsSimpleRing A


-- @@ L36-38 verbatim
/-- A second auxiliary element of the first ring-dependent type. -/
@[source_ref "Chapter2/Discussion_2.4_heading" (role := supporting)]
abbrev Ring.auxiliaryElement' : _root_.RepresentationTheory.RingTheory.TwoSidedIdeal.Basic.Ring.AuxiliaryType A := ⊥


-- @@ L40-42 verbatim
/-- An auxiliary element of the first ring-dependent type. -/
@[source_ref "Chapter2/Discussion_2.4_heading" (role := supporting)]
abbrev Ring.auxiliaryElement : _root_.RepresentationTheory.RingTheory.TwoSidedIdeal.Basic.Ring.AuxiliaryType A := ⊤


-- @@ L44-46 verbatim
/-- An auxiliary map from an element of the enclosing type to a second ring-dependent type. -/
@[source_ref "Chapter2/Discussion_2.4_heading" (role := supporting)]
abbrev Ring.AuxiliaryType.auxiliaryMap (I : _root_.RepresentationTheory.RingTheory.TwoSidedIdeal.Basic.Ring.AuxiliaryType A) : _root_.RepresentationTheory.RingTheory.TwoSidedIdeal.Basic.Ring.AuxiliaryType' A := I.asIdeal


-- @@ L48-50 verbatim
/-- An auxiliary map from an element of the enclosing type to a third ring-dependent type. -/
@[source_ref "Chapter2/Discussion_2.4_heading" (role := supporting)]
abbrev Ring.AuxiliaryType.auxiliaryMap' (I : _root_.RepresentationTheory.RingTheory.TwoSidedIdeal.Basic.Ring.AuxiliaryType A) : _root_.RepresentationTheory.RingTheory.TwoSidedIdeal.Basic.Ring.AuxiliaryType'' A := I.asIdealOpposite


-- @@ L52-53 verbatim
/-- An auxiliary construction from sets of ring elements into the second auxiliary type. -/
abbrev Ring.auxiliarySetMap' (S : Set A) : _root_.RepresentationTheory.RingTheory.TwoSidedIdeal.Basic.Ring.AuxiliaryType' A := Submodule.span A S


-- @@ L55-57 verbatim
/-- An auxiliary construction from sets of ring elements into the third auxiliary type. -/
abbrev Ring.auxiliarySetMap'' (S : Set A) : _root_.RepresentationTheory.RingTheory.TwoSidedIdeal.Basic.Ring.AuxiliaryType'' A :=
  Submodule.span Aᵐᵒᵖ (MulOpposite.op '' S)


-- @@ L59-60 verbatim
/-- An auxiliary construction from sets of ring elements into the first auxiliary type. -/
abbrev Ring.auxiliarySetMap (S : Set A) : _root_.RepresentationTheory.RingTheory.TwoSidedIdeal.Basic.Ring.AuxiliaryType A := TwoSidedIdeal.span S


-- @@ L62-65 verbatim
/-- The second auxiliary type agrees with the displayed dependent type. -/
@[source_ref "Chapter2/Discussion_2.4_heading" (role := primary)]
theorem Ring.auxiliaryType'_eq :
    _root_.RepresentationTheory.RingTheory.TwoSidedIdeal.Basic.Ring.AuxiliaryType' A = _root_.RepresentationTheory.LinearAlgebra.ModuleAuxiliaryData.ModuleAuxiliaryData A A := rfl


-- @@ L67-70 verbatim
/-- The third auxiliary type agrees with the displayed dependent type over the opposite ring. -/
@[source_ref "Chapter2/Discussion_2.4_heading" (role := primary)]
theorem Ring.auxiliaryType''_eq :
    _root_.RepresentationTheory.RingTheory.TwoSidedIdeal.Basic.Ring.AuxiliaryType'' A = _root_.RepresentationTheory.LinearAlgebra.ModuleAuxiliaryData.ModuleAuxiliaryData Aᵐᵒᵖ Aᵐᵒᵖ := rfl


-- @@ L72-75 verbatim
/-- The first auxiliary map preserves membership. -/
@[source_ref "Chapter2/Discussion_2.4_heading" (role := supporting)]
theorem Ring.mem_auxiliaryMap_iff {I : _root_.RepresentationTheory.RingTheory.TwoSidedIdeal.Basic.Ring.AuxiliaryType A} {x : A} : x ∈ I.auxiliaryMap ↔ x ∈ I :=
  TwoSidedIdeal.mem_asIdeal


-- @@ L77-80 verbatim
/-- Membership after the second auxiliary map is equivalent to membership of the unopposite element in the source. -/
@[simp, source_ref "Chapter2/Discussion_2.4_heading" (role := supporting)]
theorem Ring.mem_auxiliaryMap'_iff {I : _root_.RepresentationTheory.RingTheory.TwoSidedIdeal.Basic.Ring.AuxiliaryType A} {x : Aᵐᵒᵖ} : x ∈ I.auxiliaryMap' ↔ x.unop ∈ I :=
  TwoSidedIdeal.mem_asIdealOpposite


-- @@ L82-85 verbatim
/-- The second auxiliary set construction lies below an element exactly when the set lies below its carrier. -/
@[source_ref "Chapter2/Discussion_2.4_heading" (role := supporting)]
theorem Ring.auxiliarySetMap'_le_iff {S : Set A} {I : _root_.RepresentationTheory.RingTheory.TwoSidedIdeal.Basic.Ring.AuxiliaryType' A} :
    _root_.RepresentationTheory.RingTheory.TwoSidedIdeal.Basic.Ring.auxiliarySetMap' A S ≤ I ↔ S ⊆ I := Submodule.span_le


-- @@ L87-90 verbatim
/-- The third auxiliary set construction lies below an element exactly when the opposite image of the set lies below its carrier. -/
@[source_ref "Chapter2/Discussion_2.4_heading" (role := supporting)]
theorem Ring.auxiliarySetMap''_le_iff {S : Set A} {I : _root_.RepresentationTheory.RingTheory.TwoSidedIdeal.Basic.Ring.AuxiliaryType'' A} :
    _root_.RepresentationTheory.RingTheory.TwoSidedIdeal.Basic.Ring.auxiliarySetMap'' A S ≤ I ↔ MulOpposite.op '' S ⊆ I := Submodule.span_le


-- @@ L92-95 verbatim
/-- The auxiliary set construction lies below an element exactly when the set lies below its carrier. -/
@[source_ref "Chapter2/Discussion_2.4_heading" (role := primary)]
theorem Ring.auxiliarySetMap_le_iff {S : Set A} {I : _root_.RepresentationTheory.RingTheory.TwoSidedIdeal.Basic.Ring.AuxiliaryType A} :
    _root_.RepresentationTheory.RingTheory.TwoSidedIdeal.Basic.Ring.auxiliarySetMap A S ≤ I ↔ S ⊆ I := TwoSidedIdeal.span_le


-- @@ L97-102 verbatim
/-- Membership in the first auxiliary set construction is equivalent to membership in the additive closure of its two-sided products. -/
@[source_ref "Chapter2/Discussion_2.4_heading" (role := primary)]
theorem Ring.mem_auxiliarySetMap_iff {S : Set A} {x : A} :
    x ∈ _root_.RepresentationTheory.RingTheory.TwoSidedIdeal.Basic.Ring.auxiliarySetMap A S ↔
      x ∈ AddSubgroup.closure ((Set.univ : Set A) * S * Set.univ) :=
  TwoSidedIdeal.mem_span_iff_mem_addSubgroup_closure


-- @@ L104-107 verbatim
/-- An element belongs to the two-sided kernel of a ring homomorphism exactly when its image is zero. -/
@[source_ref "Chapter2/Discussion_2.4_heading" (role := supporting)]
theorem TwoSidedIdeal.mem_ker_iff {B : Type*} [NonAssocSemiring B] (f : A →+* B) (x : A) :
    x ∈ TwoSidedIdeal.ker f ↔ f x = 0 := TwoSidedIdeal.mem_ker f


-- @@ L109-109 verbatim
end RepresentationTheory.RingTheory.TwoSidedIdeal.Basic
