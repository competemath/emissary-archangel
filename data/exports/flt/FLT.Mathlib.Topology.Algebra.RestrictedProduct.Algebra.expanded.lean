/-
Copyright (c) 2026 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import FLT.Mathlib.Topology.Algebra.RestrictedProduct.Basic
public import FLT.Mathlib.Topology.Algebra.RestrictedProduct.Module


-- @@ L11-11 verbatim
/-! # Lemmas about restricted products of algebras -/


-- @@ L13-13 verbatim
@[expose] public section


-- @@ L15-15 verbatim
namespace RestrictedProduct


-- @@ L17-19 verbatim
variable {ι : Type*} (M : ι → Type*) [(i : ι) → CommRing (M i)]
    {S : ι → Type*} [∀ i, SetLike (S i) (M i)] [∀ i, SubringClass (S i) (M i)] (A : Π i, S i)
    (𝓕 : Filter ι)


-- @@ L21-23 verbatim
instance piAlgebra :
    Algebra (Π i, A i) (Πʳ i, [M i, Subring.ofClass (A i)]_[𝓕]) :=
  .compHom _ (structureMapRingHom M A 𝓕)


-- @@ L25-27 verbatim
@[simp]
lemma piSmul_apply (r : Π i, A i) (s : Πʳ i, [M i, Subring.ofClass (A i)]_[𝓕]) (i) :
    (r • s) i = r i • s i := rfl


-- @@ L29-31 verbatim
@[simp]
lemma algebraMap_pi_apply (r : Π i, A i) (i) :
    algebraMap _ (Πʳ i, [M i, Subring.ofClass (A i)]_[𝓕]) r i = r i := rfl


-- @@ L33-33 verbatim
end RestrictedProduct
