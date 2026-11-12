/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/
import Mathlib
import RepresentationTheory.Alignment.Attribute


-- @@ L9-9 verbatim
open CategoryTheory


-- @@ L11-11 verbatim
namespace RepresentationTheory.InductionCoinduction.FiniteIndex


-- @@ L13-21 verbatim
/-- The isomorphism from induction to coinduction for a finite-index subgroup. -/
@[source_ref "Chapter5/Remark5.8.2" (role := supporting)]
noncomputable def indCoindIsoOfFiniteIndex
    {k : Type*} [CommRing k]
    {G : Type*} [Group G] (H : Subgroup G)
    [DecidableRel (QuotientGroup.rightRel H)] [H.FiniteIndex]
    (A : Rep k H) :
    Rep.ind H.subtype A ≅ Rep.coind' H.subtype A :=
  Rep.indCoindIso A ≪≫ Rep.coindIso H.subtype A


-- @@ L23-30 verbatim
/-- The natural isomorphism between induction and coinduction functors for a finite-index subgroup. -/
@[simps!, source_ref "Chapter5/Remark5.8.2" (role := supporting)]
noncomputable def indFunctorIsoCoindFunctorOfFiniteIndex
    {k : Type*} [CommRing k]
    {G : Type*} [Group G] (H : Subgroup G)
    [DecidableRel (QuotientGroup.rightRel H)] [H.FiniteIndex] :
    Rep.indFunctor k H.subtype ≅ Rep.coindFunctor' k H.subtype :=
  Rep.indCoindNatIso k H ≪≫ Rep.coindFunctorIso H.subtype


-- @@ L32-40 verbatim
/-- The component of the induction--coinduction functor isomorphism is the representation isomorphism. -/
@[source_ref "Chapter5/Remark5.8.2" (role := supporting)]
theorem indFunctorIsoCoindFunctorOfFiniteIndex_app
    {k : Type*} [CommRing k]
    {G : Type*} [Group G] (H : Subgroup G)
    [DecidableRel (QuotientGroup.rightRel H)] [H.FiniteIndex]
    (A : Rep k H) :
    (indFunctorIsoCoindFunctorOfFiniteIndex H).app A = indCoindIsoOfFiniteIndex H A :=
  rfl


-- @@ L42-44 verbatim
/-- Evaluating the forward component on a regular-representation vector is a linear combination. -/
alias indFunctorIsoCoindFunctorOfFiniteIndex_hom_apply :=
  indFunctorIsoCoindFunctorOfFiniteIndex_hom_app_hom_toFun_hom_toFun


-- @@ L46-48 verbatim
/-- The inverse component agrees with the inverse representation isomorphism after the coinduction comparison. -/
alias indFunctorIsoCoindFunctorOfFiniteIndex_inv_apply :=
  indFunctorIsoCoindFunctorOfFiniteIndex_inv_app_hom_toFun


-- @@ L50-50 verbatim
end RepresentationTheory.InductionCoinduction.FiniteIndex
