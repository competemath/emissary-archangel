/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import Mathlib.Algebra.Module.Projective
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.Order.Lattice
import RepresentationTheory.LinearAlgebra.ModuleDecompositions
import RepresentationTheory.Alignment.Attribute


-- @@ L13-13 verbatim
namespace RepresentationTheory.RingModuleAuxiliary


-- @@ L15-36 verbatim
/-- A parameterized auxiliary object associated with a ring and one of its modules. -/
structure Auxiliary (R : Type*) [Ring R]
    (M : Type*) [AddCommGroup M] [Module R M] where
  /-- The type attached to a given auxiliary object. -/
  Carrier : Type*
  /-- The additive commutative group structure provided on the attached type. -/
  [instAddCommGroupCarrier : AddCommGroup Carrier]
  /-- The scalar action of the ambient ring on the attached type. -/
  [instModuleCarrier : Module R Carrier]
  /-- The attached type is a projective module over the ambient ring. -/
  [projective : Module.Projective R Carrier]
  /-- An opaque property asserted for the attached type over the ambient ring. -/
  auxiliaryProperty :
    RepresentationTheory.LinearAlgebra.ModuleDecompositions.AuxiliaryDecompositionPredicate R Carrier
  /-- The linear map from the attached type to the ambient module. -/
  toLinearMap : Carrier →ₗ[R] M
  /-- The associated linear map reaches every element of the ambient module. -/
  surjective_toLinearMap : Function.Surjective toLinearMap
  /-- If a submodule together with the map kernel spans the attached type, then the submodule is
  all of it. -/
  eq_top_of_sup_kernel_eq_top :
    ∀ N : Submodule R Carrier, N ⊔ LinearMap.ker toLinearMap = ⊤ → N = ⊤


-- @@ L38-40 verbatim
attribute [instance] Auxiliary.instAddCommGroupCarrier
  Auxiliary.instModuleCarrier
  Auxiliary.projective


-- @@ L42-44 verbatim
end RepresentationTheory.RingModuleAuxiliary

-- Recovered exact-module book alignment.

-- @@ L45-45 verbatim
attribute [source_ref "Chapter9/Definition9.2.2" (role := primary)] _root_.RepresentationTheory.RingModuleAuxiliary.Auxiliary

-- @@ L46-46 verbatim
attribute [source_ref "Chapter9/Definition9.2.2" (role := supporting)] _root_.RepresentationTheory.RingModuleAuxiliary.Auxiliary.Carrier

-- @@ L47-47 verbatim
attribute [source_ref "Chapter9/Definition9.2.2" (role := supporting)] _root_.RepresentationTheory.RingModuleAuxiliary.Auxiliary.auxiliaryProperty

-- @@ L48-48 verbatim
attribute [source_ref "Chapter9/Definition9.2.2" (role := supporting)] _root_.RepresentationTheory.RingModuleAuxiliary.Auxiliary.eq_top_of_sup_kernel_eq_top

-- @@ L49-49 verbatim
attribute [source_ref "Chapter9/Definition9.2.2" (role := supporting)] _root_.RepresentationTheory.RingModuleAuxiliary.Auxiliary.instAddCommGroupCarrier

-- @@ L50-50 verbatim
attribute [source_ref "Chapter9/Definition9.2.2" (role := supporting)] _root_.RepresentationTheory.RingModuleAuxiliary.Auxiliary.instModuleCarrier

-- @@ L51-51 verbatim
attribute [source_ref "Chapter9/Definition9.2.2" (role := supporting)] _root_.RepresentationTheory.RingModuleAuxiliary.Auxiliary.projective

-- @@ L52-52 verbatim
attribute [source_ref "Chapter9/Definition9.2.2" (role := supporting)] _root_.RepresentationTheory.RingModuleAuxiliary.Auxiliary.surjective_toLinearMap

-- @@ L53-53 verbatim
attribute [source_ref "Chapter9/Definition9.2.2" (role := supporting)] _root_.RepresentationTheory.RingModuleAuxiliary.Auxiliary.toLinearMap
