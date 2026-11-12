/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import Mathlib.CategoryTheory.Yoneda
import RepresentationTheory.Alignment.Attribute


-- @@ L10-14 verbatim
/-!
# Yoneda isomorphisms

Uniqueness of represented objects under isomorphisms of their Yoneda functors.
-/


-- @@ L16-16 verbatim
open CategoryTheory


-- @@ L18-18 verbatim
namespace RepresentationTheory.CategoryTheory.Yoneda


-- @@ L20-31 verbatim
/-- Every isomorphism between representable Yoneda functors is induced by a unique isomorphism of
the represented objects. -/
@[source_ref "Chapter7/Lemma7.5.1" (role := primary)]
theorem yonedaIsoLiftUnique {C : Type*} [Category C]
    (X Y : C) (φ : yoneda.obj X ≅ yoneda.obj Y) :
    ∃! (a : X ≅ Y), yoneda.map a.hom = φ.hom := by
  refine ⟨Yoneda.fullyFaithful.preimageIso φ, ?_, ?_⟩
  · exact Yoneda.fullyFaithful.map_preimage φ.hom
  · intro b hb
    apply Yoneda.fullyFaithful.isoEquiv.injective
    ext1
    exact hb.trans (Yoneda.fullyFaithful.map_preimage φ.hom).symm


-- @@ L33-33 verbatim
end RepresentationTheory.CategoryTheory.Yoneda
