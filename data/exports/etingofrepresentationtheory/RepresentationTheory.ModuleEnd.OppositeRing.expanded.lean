/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import Mathlib.Algebra.Module.LinearMap.End
import RepresentationTheory.Alignment.Attribute


-- @@ L10-10 verbatim
/-! # Endomorphisms of regular modules and opposite rings -/


-- @@ L12-12 verbatim
namespace RepresentationTheory.ModuleEnd.OppositeRing


-- @@ L14-18 verbatim
/-- The ring equivalence from endomorphisms of the regular module to the opposite ring. -/
@[source_ref "Chapter2/Problem2.3.17" (role := primary)]
noncomputable def regularEndRingEquivOpposite (A : Type*) [Ring A] :
    Module.End A A ≃+* Aᵐᵒᵖ :=
  (RingEquiv.moduleEndSelf A).symm


-- @@ L20-24 verbatim
/-- Evaluating the equivalence on an endomorphism gives the opposite of its value at one. -/
@[simp, source_ref "Chapter2/Problem2.3.17" (role := supporting)]
theorem regularEndRingEquivOpposite_apply (A : Type*) [Ring A] (f : Module.End A A) :
    regularEndRingEquivOpposite A f = MulOpposite.op (f 1) :=
  rfl


-- @@ L26-31 verbatim
/-- The inverse equivalence sends an opposite element to right multiplication by that element. -/
@[source_ref "Chapter2/Problem2.3.17" (role := supporting)]
theorem regularEndRingEquivOpposite_symm_apply (A : Type*) [Ring A] (a x : A) :
    (regularEndRingEquivOpposite A).symm (MulOpposite.op a) x = x * a := by
  simp only [regularEndRingEquivOpposite, RingEquiv.symm_symm]
  rfl


-- @@ L33-33 verbatim
end RepresentationTheory.ModuleEnd.OppositeRing
