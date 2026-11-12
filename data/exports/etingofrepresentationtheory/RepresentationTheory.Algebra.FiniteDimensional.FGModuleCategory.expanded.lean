/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.FGModuleCat.Abelian
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Finiteness.Basic
import RepresentationTheory.Alignment.Attribute


-- @@ L14-14 verbatim
/-! # Finitely generated module categories -/


-- @@ L16-16 verbatim
open CategoryTheory


-- @@ L18-18 verbatim
namespace RepresentationTheory.Algebra.FiniteDimensional.FGModuleCategory


-- @@ L20-20 verbatim
example (A : Type*) [Ring A] : Abelian (ModuleCat A) := inferInstance


-- @@ L22-22 verbatim
section FiniteDimensionalAlgebra


-- @@ L24-24 verbatim
variable (k A : Type*) [Field k] [Ring A] [Algebra k A]


-- @@ L26-29 verbatim
/-- A finite-dimensional algebra over a field is a Noetherian ring. -/
theorem isNoetherianRing_of_finiteDimensional [FiniteDimensional k A] :
    IsNoetherianRing A :=
  IsNoetherianRing.of_finite k A


-- @@ L31-36 verbatim
/-- A module over a finite-dimensional algebra is finitely generated exactly when it is finite-dimensional over the base field. -/
@[source_ref "Chapter7/Example7.7.2" (role := supporting)]
theorem moduleFinite_iff_finiteDimensional [FiniteDimensional k A]
    (M : Type*) [AddCommGroup M] [Module A M] [Module k M] [IsScalarTower k A M] :
    Module.Finite A M ↔ FiniteDimensional k M :=
  ⟨fun _ => Module.Finite.trans A M, fun _ => Module.Finite.of_restrictScalars_finite k A M⟩


-- @@ L38-43 verbatim
/-- Finitely generated modules over a finite-dimensional algebra form an abelian category. -/
@[reducible, source_ref "Chapter7/Example7.7.2" (role := supporting)]
noncomputable def FGModuleCat.instAbelian_of_finiteDimensional
    [FiniteDimensional k A] : Abelian (FGModuleCat A) :=
  haveI : IsNoetherianRing A := isNoetherianRing_of_finiteDimensional k A
  inferInstance


-- @@ L45-45 verbatim
end FiniteDimensionalAlgebra


-- @@ L47-48 verbatim
noncomputable example (k : Type*) [Field k] : Abelian (FGModuleCat k) :=
  FGModuleCat.instAbelian_of_finiteDimensional k k


-- @@ L50-50 verbatim
end RepresentationTheory.Algebra.FiniteDimensional.FGModuleCategory
