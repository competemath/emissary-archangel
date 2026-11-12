/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import Mathlib.RingTheory.SimpleModule.Rank
import RepresentationTheory.Alignment.Attribute


-- @@ L10-10 verbatim
/-! # Simple modules of finrank one -/


-- @@ L12-12 verbatim
namespace RepresentationTheory.Module.FinrankOneSimple


-- @@ L14-27 verbatim
/-- A module of dimension one over the base field is simple for the given algebra action. -/
@[source_ref "Chapter2/Remark2.3.13" (role := primary)]
theorem isSimpleModule_of_finrank_eq_one
    {k : Type*} [Field k]
    {A : Type*} [Ring A] [Algebra k A]
    {V : Type*} [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
    (h : Module.finrank k V = 1) :
    IsSimpleModule A V := by
  haveI hk : IsSimpleModule k V := isSimpleModule_iff_finrank_eq_one.mpr h
  haveI : Nontrivial V := IsSimpleModule.nontrivial k V
  refine { eq_bot_or_eq_top := fun W => ?_ }
  rcases eq_bot_or_eq_top (W.restrictScalars k) with hW | hW
  · exact Or.inl (by simpa using hW)
  · exact Or.inr (by simpa using hW)


-- @@ L29-29 verbatim
end RepresentationTheory.Module.FinrankOneSimple
