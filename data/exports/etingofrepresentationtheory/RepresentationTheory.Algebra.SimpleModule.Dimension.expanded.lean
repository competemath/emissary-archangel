/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.RepresentationTheory.AlgebraRepresentation.Basic
import RepresentationTheory.Alignment.Attribute


-- @@ L9-13 verbatim
/-!
# Dimensions of simple modules

Dimension results for finite-dimensional simple modules.
-/


-- @@ L15-15 verbatim
set_option linter.style.whitespace false


-- @@ L17-17 verbatim
namespace RepresentationTheory.Algebra.SimpleModule.Dimension


-- @@ L19-32 verbatim
/-- A finite-dimensional simple module over a commutative algebra over an algebraically closed
field has dimension one. -/
@[source_ref "Chapter2/Corollary2.3.12" (role := primary),
  source_ref "Chapter2/Discussion_proof_Corollary2.3.12" (role := supporting),
  source_ref "Chapter2/Discussion_proof_Corollary2.3.12/Derived2" (role := supporting),
  source_ref "Chapter2/Discussion_proof_Corollary2.3.12/Derived3" (role := supporting)]
theorem finrank_eq_one
    {k : Type*} [Field k] [IsAlgClosed k]
    {A : Type*} [CommRing A] [Algebra k A]
    {V : Type*} [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
    [IsSimpleModule A V] [FiniteDimensional k V] :
    Module.finrank k V = 1 := by
  have : IsMulCommutative A := ⟨⟨mul_comm⟩⟩
  exact IsSimpleModule.finrank_eq_one_of_isMulCommutative (k := k) (A := A) (V := V)


-- @@ L34-34 verbatim
end RepresentationTheory.Algebra.SimpleModule.Dimension
