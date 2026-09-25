/-
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
module

public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic


-- @@ L10-14 verbatim
/-!
# Basic

Material destined for Mathlib.
-/


-- @@ L16-18 verbatim
@[expose] public section

-- TODO upstream

-- @@ L19-19 verbatim
namespace Rat


-- @@ L21-21 verbatim
open NumberField


-- @@ L23-24 verbatim
lemma infinitePlace_isReal (v : InfinitePlace ℚ) : v.IsReal :=
  Subsingleton.elim v infinitePlace ▸ isReal_infinitePlace


-- @@ L26-26 verbatim
end Rat
