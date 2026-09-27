/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import LeanPool.InfinitaryLogic.Descriptive.LopezEscobarEasy
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Data.EReal.Inv
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

-- @@ L13-18 verbatim
/-!
# Complement closure for isomorphism-invariant classes

The complement of an isomorphism-invariant class of coded structures is again invariant. This
elementary lemma is the only closure property needed by the retained López–Escobar branch.
-/


-- @@ L20-20 verbatim
@[expose] public section


-- @@ L22-22 verbatim
namespace FirstOrder.Language


-- @@ L24-24 verbatim
variable {L : Language.{0, 0}}


-- @@ L26-26 verbatim
variable [L.IsRelational]


-- @@ L28-31 verbatim
/-- Isomorphism invariance is closed under complement. -/
theorem IsomorphismInvariant.compl {B : Set (StructureSpace L)} (h : IsomorphismInvariant B) :
    IsomorphismInvariant Bᶜ := fun c d hcd => by
  simp only [Set.mem_compl_iff]; rw [h c d hcd]


-- @@ L33-33 verbatim
end FirstOrder.Language
