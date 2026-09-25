/-
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace


-- @@ L11-15 verbatim
/-!
# Restricted Product

Material destined for Mathlib.
-/


-- @@ L17-26 verbatim
@[expose] public section

/-

If a restricted product of measurable spaces is made into a measurable space in e.g. mathlib
then the measurable space instance below should be removed, and the Borel space instance
should be replaced by the appropriate theorem (which will presumably need second countability
assumptions everywhere) saying that a restricted product of Borel spaces is a Borel space.

-/


-- @@ L28-29 verbatim
variable {ι : Type*} (R : ι → Type*) (A : (i : ι) → Set (R i)) (𝓕 : Filter ι)
  [(i : ι) → TopologicalSpace (R i)]


-- @@ L31-31 verbatim
open scoped RestrictedProduct


-- @@ L33-33 verbatim
instance : MeasurableSpace Πʳ (i : ι), [R i, A i]_[𝓕] := borel _


-- @@ L35-35 verbatim
instance : BorelSpace Πʳ (i : ι), [R i, A i]_[𝓕] := ⟨rfl⟩
