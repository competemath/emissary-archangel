/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import Mathlib.RingTheory.Artinian.Module
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import RepresentationTheory.RingTheory.SimpleModuleAnnihilator
import RepresentationTheory.Alignment.Attribute


-- @@ L12-12 verbatim
/-! # Finite-dimensional algebra semisimplicity -/


-- @@ L14-14 verbatim
namespace RepresentationTheory.Algebra.FiniteDimensionalSemisimplicity


-- @@ L16-19 verbatim
/-- A module-theoretic semisimplicity condition for a finite-dimensional algebra over a field. -/
abbrev FiniteAlgebraModuleSemisimple (k A : Type*) [Field k] [Ring A] [Algebra k A]
    [FiniteDimensional k A] :=
  RepresentationTheory.RingTheory.SimpleModuleAnnihilator.simpleModuleAnnihilator A = ⊥


-- @@ L21-28 verbatim
/-- A finite-dimensional algebra whose underlying ring is semisimple satisfies the module semisimplicity condition. -/
theorem finiteAlgebraModuleSemisimple_of_isSemisimpleRing (k A : Type*) [Field k] [Ring A]
    [Algebra k A] [FiniteDimensional k A] (h : IsSemisimpleRing A) :
    FiniteAlgebraModuleSemisimple k A := by
  rw [FiniteAlgebraModuleSemisimple,
    RepresentationTheory.RingTheory.SimpleModuleAnnihilator.simpleModuleAnnihilator,
    Ideal.jacobson_bot]
  exact h.jacobson_eq_bot


-- @@ L30-38 verbatim
/-- An algebra satisfying the finite-dimensional module semisimplicity condition is a semisimple ring. -/
theorem FiniteAlgebraModuleSemisimple.isSemisimpleRing {k A : Type*} [Field k] [Ring A]
    [Algebra k A] [FiniteDimensional k A] (h : FiniteAlgebraModuleSemisimple k A) :
    IsSemisimpleRing A := by
  letI : IsArtinianRing A := IsArtinianRing.of_finite k A
  rw [FiniteAlgebraModuleSemisimple,
    RepresentationTheory.RingTheory.SimpleModuleAnnihilator.simpleModuleAnnihilator,
    Ideal.jacobson_bot, ← IsArtinianRing.isSemisimpleRing_iff_jacobson] at h
  exact h


-- @@ L40-45 verbatim
/-- For a finite-dimensional algebra over a field, the module semisimplicity condition is equivalent to semisimplicity of the underlying ring. -/
theorem finiteAlgebraModuleSemisimple_iff (k A : Type*) [Field k] [Ring A]
    [Algebra k A] [FiniteDimensional k A] :
    FiniteAlgebraModuleSemisimple k A ↔ IsSemisimpleRing A :=
  ⟨FiniteAlgebraModuleSemisimple.isSemisimpleRing,
    finiteAlgebraModuleSemisimple_of_isSemisimpleRing k A⟩


-- @@ L47-47 verbatim
end RepresentationTheory.Algebra.FiniteDimensionalSemisimplicity


-- @@ L49-50 verbatim
/-- A semisimplicity condition for a finite-dimensional algebra over a field. -/
alias _root_.RepresentationTheory.Algebra.FiniteDimensionalSemisimplicity.FiniteAlgebraSemisimpleCondition := _root_.RepresentationTheory.Algebra.FiniteDimensionalSemisimplicity.FiniteAlgebraModuleSemisimple


-- @@ L52-56 verbatim
/--
For a finite-dimensional algebra over a field, the displayed condition is equivalent to
semisimplicity of the underlying ring.
-/
alias _root_.RepresentationTheory.Algebra.FiniteDimensionalSemisimplicity.finiteAlgebraSemisimpleCondition_iff := _root_.RepresentationTheory.Algebra.FiniteDimensionalSemisimplicity.finiteAlgebraModuleSemisimple_iff


-- @@ L58-62 verbatim
/--
A finite-dimensional algebra whose underlying ring is semisimple satisfies the displayed
condition.
-/
alias _root_.RepresentationTheory.Algebra.FiniteDimensionalSemisimplicity.finiteAlgebraSemisimpleCondition_of_isSemisimpleRing := _root_.RepresentationTheory.Algebra.FiniteDimensionalSemisimplicity.finiteAlgebraModuleSemisimple_of_isSemisimpleRing


-- @@ L64-65 verbatim
/-- An algebra satisfying the finite-dimensional semisimplicity condition is a semisimple ring. -/
alias _root_.RepresentationTheory.Algebra.FiniteDimensionalSemisimplicity.FiniteAlgebraSemisimpleCondition.isSemisimpleRing := _root_.RepresentationTheory.Algebra.FiniteDimensionalSemisimplicity.FiniteAlgebraModuleSemisimple.isSemisimpleRing


-- @@ L67-67 verbatim
attribute [source_ref "Chapter3/Definition3.5.7" (role := supporting)] _root_.RepresentationTheory.Algebra.FiniteDimensionalSemisimplicity.FiniteAlgebraSemisimpleCondition


-- @@ L69-69 verbatim
attribute [source_ref "Chapter3/Definition3.5.7" (role := supporting)] _root_.RepresentationTheory.Algebra.FiniteDimensionalSemisimplicity.finiteAlgebraSemisimpleCondition_iff
