/-
Copyright (c) 2026 Jeremy Parker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy P Parker
-/
import Formalisation.HansenCograph.HansenPortalFlagIntervals


-- @@ L8-14 verbatim
/-!
# Join intervals at Hansen portals

The interval below a neutral join face is the product of the corresponding
factor intervals.  This is the geometric input for the lower-chain shuffle
in the full-flag recurrence.
-/


-- @@ L16-16 verbatim
open Set SimpleGraph


-- @@ L18-18 verbatim
namespace HansenCograph

-- @@ L19-19 verbatim
namespace HansenCombinatorialFace


-- @@ L21-21 verbatim
universe u v


-- @@ L23-23 verbatim
variable {V : Type u} {W : Type v}

-- @@ L24-24 verbatim
variable [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]


-- @@ L26-34 verbatim
/-- Every face below a neutral-or-empty face is neutral-or-empty. -/
theorem IsNeutralOrEmpty.lower {G : SimpleGraph V}
    {E X : HansenCombinatorialFace G} (hE : E.IsNeutralOrEmpty)
    (hXE : X ≤ E) : X.IsNeutralOrEmpty := by
  constructor
  · intro hX
    exact hE.1 (hX.mono hXE)
  · intro hX
    exact hE.2 (hX.mono hXE)


-- @@ L36-45 verbatim
/-- The lower interval of a neutral face of a Hansen graph join is the
componentwise product of the two factor lower intervals. -/
private def prodIicOrderIso {P : Type*} {Q : Type*}
    [Preorder P] [Preorder Q] (a : P) (b : Q) :
    Set.Iic a × Set.Iic b ≃o Set.Iic (a, b) where
  toFun x := ⟨(x.1.1, x.2.1), ⟨x.1.2, x.2.2⟩⟩
  invFun x := (⟨x.1.1, x.2.1⟩, ⟨x.1.2, x.2.2⟩)
  left_inv _x := rfl
  right_inv _x := rfl
  map_rel_iff' := Iff.rfl


-- @@ L47-53 verbatim
private def prodOrderIso {P P' Q Q' : Type*}
    [Preorder P] [Preorder P'] [Preorder Q] [Preorder Q']
    (e : P ≃o P') (f : Q ≃o Q') : P × Q ≃o P' × Q' where
  toEquiv := Equiv.prodCongr e.toEquiv f.toEquiv
  map_rel_iff' := by
    intro x y
    exact and_congr (map_le_map_iff e) (map_le_map_iff f)


-- @@ L55-64 verbatim
/-- Restrict an order isomorphism to the lower intervals at corresponding
points.  Unlike `OrderIso.Iic`, this needs only preorders, not lattices. -/
private def OrderIso.restrictIic {P : Type*} {Q : Type*}
    [Preorder P] [Preorder Q] (e : P ≃o Q) (a : P) :
    Set.Iic a ≃o Set.Iic (e a) where
  toFun x := ⟨e x.1, (map_le_map_iff e).mpr x.2⟩
  invFun x := ⟨e.symm x.1, e.symm_apply_le.mpr x.2⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x.1)
  right_inv x := Subtype.ext (e.apply_symm_apply x.1)
  map_rel_iff' := map_le_map_iff e


-- @@ L66-75 verbatim
/-- A lower interval below a neutral-or-empty face consists entirely of
neutral-or-empty faces, so taking the neutral subtype loses nothing. -/
private noncomputable def neutralLowerIntervalOrderIso
    (G : SimpleGraph V) (E : NeutralOrEmpty G) :
    Set.Iic E.1 ≃o Set.Iic E where
  toFun X := ⟨⟨X.1, E.2.lower X.2⟩, X.2⟩
  invFun X := ⟨X.1.1, X.2⟩
  left_inv _X := rfl
  right_inv _X := rfl
  map_rel_iff' := Iff.rfl


-- @@ L77-86 expanded
/-- The neutral stratum of a Hansen join, including the empty face, is an
order product rather than merely an equivalent type. -/
noncomputable def joinNeutralOrderIso (A : SimpleGraph V) (B : SimpleGraph W) :
    NeutralOrEmpty A × NeutralOrEmpty B ≃o NeutralOrEmpty (graphJoin A B)
    where
  toEquiv := joinNeutralEquiv A B
  map_rel_iff' := by
    intro x y
    exact joinNeutral_le_iff A B x.1 y.1 x.2 y.2


-- @@ L88-101 expanded
noncomputable def joinNeutralLowerIntervalOrderIso (A : SimpleGraph V) (B : SimpleGraph W)
    (E : NeutralOrEmpty A) (L : NeutralOrEmpty B) :
    Set.Iic E.1 × Set.Iic L.1 ≃o Set.Iic (joinNeutral A B E L) :=
  by
  change Set.Iic E.1 × Set.Iic L.1 ≃o Set.Iic (joinNeutralOrderIso A B (E, L)).1
  exact
    (prodOrderIso (neutralLowerIntervalOrderIso A E) (neutralLowerIntervalOrderIso B L)).trans
      ((prodIicOrderIso E L).trans
        ((OrderIso.restrictIic (joinNeutralOrderIso A B) (E, L)).trans
          (neutralLowerIntervalOrderIso (graphJoin A B) (joinNeutralOrderIso A B (E, L))).symm))


-- @@ L103-110 verbatim
/-- Consequently, lower-interval full flags at a join portal are maximal
chains of the corresponding product interval. -/
noncomputable def joinNeutralLowerIntervalFlagEquiv
    (A : SimpleGraph V) (B : SimpleGraph W)
    (E : NeutralOrEmpty A) (L : NeutralOrEmpty B) :
    Flag (Set.Iic E.1 × Set.Iic L.1) ≃
      Flag (Set.Iic (joinNeutral A B E L)) :=
  Flag.map (joinNeutralLowerIntervalOrderIso A B E L)


-- @@ L112-112 verbatim
end HansenCombinatorialFace

-- @@ L113-113 verbatim
end HansenCograph
