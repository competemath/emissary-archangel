/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import Mathlib.RepresentationTheory.Basic
import RepresentationTheory.Alignment.Attribute


-- @@ L10-10 verbatim
/-! # Equivalences between representation data -/


-- @@ L12-12 verbatim
namespace RepresentationTheory.Algebra.Representation.Equivalences


-- @@ L14-14 verbatim
open scoped MonoidAlgebra


-- @@ L16-17 verbatim
variable (k : Type*) [CommRing k] (G : Type*) [Group G]
    (V : Type*) [AddCommGroup V] [Module k V]


-- @@ L19-24 verbatim
/-- Equivalence from representations to algebra homomorphisms from the monoid algebra into module
endomorphisms. -/
@[source_ref "Chapter2/Example2.3.14_continued" (role := primary)]
noncomputable def representationAlgHomEquiv :
    Representation k G V ≃ (k[G] →ₐ[k] Module.End k V) :=
  MonoidAlgebra.lift k (Module.End k V) G


-- @@ L26-31 verbatim
/-- The algebra homomorphism associated with a representation sends a singleton basis element to
the corresponding action. -/
@[simp]
theorem representationAlgHomEquiv_apply_single (ρ : Representation k G V) (g : G) :
    representationAlgHomEquiv k G V ρ (MonoidAlgebra.single g 1) = ρ g := by
  simp [representationAlgHomEquiv]


-- @@ L33-38 verbatim
/-- Equivalence between homomorphisms from a group to a monoid and homomorphisms to its units. -/
def groupHomUnitsEquiv (M : Type*) [Monoid M] : (G →* M) ≃ (G →* Mˣ) where
  toFun ρ := ρ.toHomUnits
  invFun f := (Units.coeHom M).comp f
  left_inv ρ := by ext g; rfl
  right_inv f := by ext g; rfl


-- @@ L40-47 verbatim
/-- Equivalence from representations to group homomorphisms into linear automorphisms. -/
@[source_ref "Chapter2/Example2.3.14_continued" (role := primary)]
def representationLinearEquivHomEquiv :
    Representation k G V ≃ (G →* (V ≃ₗ[k] V)) :=
  Equiv.trans
    (groupHomUnitsEquiv G (Module.End k V))
    (MulEquiv.monoidHomCongrRightEquiv
      (LinearMap.GeneralLinearGroup.generalLinearEquiv k V))


-- @@ L49-53 verbatim
/-- The linear automorphism obtained from a representation acts as the original representation. -/
@[simp, source_ref "Chapter2/Example2.3.14_continued" (role := supporting)]
theorem representationLinearEquivHomEquiv_apply
    (ρ : Representation k G V) (g : G) (v : V) :
    representationLinearEquivHomEquiv k G V ρ g v = ρ g v := rfl


-- @@ L55-60 verbatim
/-- The representation recovered from a homomorphism to linear automorphisms has its specified
action. -/
@[source_ref "Chapter2/Example2.3.14_continued" (role := supporting)]
theorem representationLinearEquivHomEquiv_symm_apply
    (f : G →* (V ≃ₗ[k] V)) (g : G) (v : V) :
    (representationLinearEquivHomEquiv k G V).symm f g v = f g v := rfl


-- @@ L62-63 verbatim
attribute [nolint defsWithUnderscore]
  representationAlgHomEquiv representationLinearEquivHomEquiv groupHomUnitsEquiv


-- @@ L65-65 verbatim
end RepresentationTheory.Algebra.Representation.Equivalences
