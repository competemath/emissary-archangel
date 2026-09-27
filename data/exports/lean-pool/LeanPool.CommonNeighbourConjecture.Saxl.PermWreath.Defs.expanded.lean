/-
Copyright (c) 2026 Aluna Rizzoli and Adam R. Thomas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aluna Rizzoli, Adam R. Thomas
-/
module

public import Mathlib.GroupTheory.SemidirectProduct


-- @@ L10-20 verbatim
/-!
# Permutation wreath products

This file defines the wreath product attached to an arbitrary action of a top
group on an index type.  The top group acts on the base group by contravariant
reindexing, so that

`(reindexAut X Q ι q f) i = f (q⁻¹ • i)`.

Unlike `RegularWreathProduct`, the action of `Q` on `ι` need not be regular.
-/


-- @@ L22-22 verbatim
@[expose] public section


-- @@ L24-24 verbatim
namespace Saxl


-- @@ L26-26 verbatim
variable (X Q ι : Type*) [Group X] [Group Q] [MulAction Q ι]


-- @@ L28-37 verbatim
/-- The action of `Q` on the base group `ι → X` by contravariant
reindexing. -/
def reindexAut : Q →* MulAut (ι → X) where
  toFun q := MulEquiv.arrowCongr (MulAction.toPerm q) (MulEquiv.refl X)
  map_one' := by
    ext f i
    simp
  map_mul' q r := by
    ext f i
    simp [mul_smul]


-- @@ L39-41 verbatim
@[simp]
theorem reindexAut_apply (q : Q) (f : ι → X) (i : ι) :
    reindexAut X Q ι q f i = f (q⁻¹ • i) := rfl


-- @@ L43-45 verbatim
/-- The permutation wreath product `X wr_ι Q`, with base group `ι → X`
and the specified action of `Q` on `ι`. -/
abbrev PermWreath := (ι → X) ⋊[reindexAut X Q ι] Q


-- @@ L47-47 verbatim
namespace PermWreath


-- @@ L49-52 verbatim
/-- The canonical inclusion of the base group into the permutation wreath
product. -/
def base : (ι → X) →* PermWreath X Q ι :=
  SemidirectProduct.inl


-- @@ L54-57 verbatim
/-- The canonical inclusion of the top group into the permutation wreath
product. -/
def top : Q →* PermWreath X Q ι :=
  SemidirectProduct.inr


-- @@ L59-60 verbatim
@[simp]
theorem base_left (f : ι → X) : (base X Q ι f).left = f := rfl


-- @@ L62-63 verbatim
@[simp]
theorem base_right (f : ι → X) : (base X Q ι f).right = 1 := rfl


-- @@ L65-66 verbatim
@[simp]
theorem top_left (q : Q) : (top X Q ι q).left = 1 := rfl


-- @@ L68-69 verbatim
@[simp]
theorem top_right (q : Q) : (top X Q ι q).right = q := rfl


-- @@ L71-74 verbatim
/-- Extensionality in the base and top coordinates. -/
theorem ext {g h : PermWreath X Q ι} (hbase : g.left = h.left)
    (htop : g.right = h.right) : g = h :=
  SemidirectProduct.ext hbase htop


-- @@ L76-76 verbatim
end PermWreath


-- @@ L78-78 verbatim
end Saxl
