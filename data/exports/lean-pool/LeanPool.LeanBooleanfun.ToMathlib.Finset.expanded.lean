/-
Copyright (c) 2024 Joris Roos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris Roos
-/
module

public import Mathlib.Data.Finset.BooleanAlgebra
import Mathlib.Tactic.Bound.Init


-- @@ L11-15 verbatim
/-!
# Auxiliary `Finset` lemmas

Small helper lemmas about `Finset` that are not specific to Boolean functions.
-/


-- @@ L17-17 verbatim
@[expose] public section


-- @@ L19-19 verbatim
namespace Finset


-- @@ L21-21 verbatim
variable {α : Type*}


-- @@ L23-23 verbatim
section ToDataFintypeBasic


-- @@ L25-25 verbatim
variable [Fintype α] [DecidableEq α]


-- @@ L27-29 verbatim
@[simp]
lemma filter_univ_not_mem (s : Finset α) : univ.filter (· ∉ s) = sᶜ := by
  ext; simp only [mem_filter, mem_univ, true_and, mem_compl]


-- @@ L31-31 verbatim
end ToDataFintypeBasic


-- @@ L33-33 verbatim
end Finset
