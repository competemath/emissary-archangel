/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/
import Mathlib.CategoryTheory.Abelian.Ext
import Mathlib.Algebra.Category.ModuleCat.Algebra
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Projective
import RepresentationTheory.Alignment.Attribute


-- @@ L12-12 verbatim
open CategoryTheory Limits


-- @@ L14-14 verbatim
namespace RepresentationTheory.Algebra.Homology.LinearYoneda


-- @@ L16-16 verbatim
universe u


-- @@ L18-18 verbatim
variable (k : Type u) [Field k]

-- @@ L19-19 verbatim
variable (A : Type u) [Ring A] [Algebra k A]


-- @@ L21-24 verbatim
/-- The degree-n k-module represented by linear Yoneda homology for two A-module objects. -/
noncomputable def ModuleCat.linearYonedaHomology (M N : ModuleCat.{u} A) (n : ℕ) :
    ModuleCat.{u} k :=
  ((_root_.Ext k (ModuleCat.{u} A) n).obj (Opposite.op M)).obj N


-- @@ L26-34 verbatim
/-- An isomorphism from the degree-n linear Yoneda homology object to the homology of the linear
Yoneda complex obtained from a projective resolution of the first A-module and the second
A-module. -/
@[source_ref "Chapter8/Definition8.2.4" (role := primary)]
noncomputable def ModuleCat.linearYonedaHomologyIsoOfProjectiveResolution
    (M N : ModuleCat.{u} A) (P : ProjectiveResolution M) (n : ℕ) :
    ModuleCat.linearYonedaHomology k A M N n ≅
      (P.complex.linearYonedaObj k N).homology n :=
  P.isoExt n N


-- @@ L36-36 verbatim
end RepresentationTheory.Algebra.Homology.LinearYoneda
