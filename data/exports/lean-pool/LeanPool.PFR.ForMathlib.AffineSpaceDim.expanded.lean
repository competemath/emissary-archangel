/-
Copyright (c) 2026 PFR contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PFR contributors
-/

module

public import LeanPool.PFR.Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs
public import Mathlib.LinearAlgebra.InvariantBasisNumber
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions


-- @@ L15-17 verbatim
/-!
# Dimensions of affine spaces
-/


-- @@ L19-19 verbatim
open scoped Pointwise


-- @@ L21-21 verbatim
namespace AffineSpace

-- @@ L22-23 verbatim
variable {k V P : Type*} [Ring k] [AddCommGroup V] [Module k V] [AddTorsor V P] {s : Set P}
  {S : Submodule k V}


-- @@ L25-30 verbatim
variable (k) in
open scoped Classical in
/-- The dimension of the affine span over `ℤ` of a subset of an additive group. -/
@[expose]
public
noncomputable def finrank (s : Set P) : ℕ := (vectorSpan k s).finrank


-- @@ L32-36 verbatim
variable (k) in
@[simp]
public
lemma finrank_vadd_set (s : Set P) (v : V) : finrank k (v +ᵥ s) = AffineSpace.finrank k s := by
  simp [finrank]




-- @@ L40-40 verbatim
variable [StrongRankCondition k]




-- @@ L44-46 verbatim
public
lemma finrank_le_moduleFinrank [Module.Finite k V] : finrank k s ≤ Module.finrank k V :=
  (vectorSpan k s).finrank_le


-- @@ L48-48 verbatim
end AffineSpace
