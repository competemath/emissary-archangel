/-
Copyright (c) 2026 Jeremy Parker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy P Parker
-/
import Formalisation.HansenCograph.HansenJoinPortalIntervals
import Formalisation.HansenCograph.FlagWithTop
import Mathlib.Order.Hom.WithTopBot


-- @@ L10-17 verbatim
/-!
# Upper intervals at Hansen join portals

Above a positive-rooted join face, all proper faces remain positive-rooted.
The proper part is a product of the two factor rooted intervals, while the
whole Hansen polytope supplies one new common top.  Thus the full upper
interval is the product interval with a single top adjoined.
-/


-- @@ L19-19 verbatim
open Set SimpleGraph


-- @@ L21-21 verbatim
namespace HansenCograph

-- @@ L22-22 verbatim
namespace HansenCombinatorialFace


-- @@ L24-24 verbatim
universe u v


-- @@ L26-26 verbatim
variable {V : Type u} {W : Type v}

-- @@ L27-27 verbatim
variable [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]


-- @@ L29-37 verbatim
/-- A face above a positive-rooted face is positive-rooted unless it is the
global top face. -/
theorem IsRootedPos.upper_of_ne_top {G : SimpleGraph V}
    {F X : HansenCombinatorialFace G} (hF : F.IsRootedPos)
    (hFX : F ≤ X) (hX : X ≠ top G) : X.IsRootedPos := by
  have hpos := hF.1.mono hFX
  refine ⟨hpos, ?_⟩
  intro hneg
  exact hX ((eq_top_iff_contains_both G X).mpr ⟨hpos, hneg⟩)


-- @@ L39-45 verbatim
/-- Forget the adjoined top from the upper interval of a rooted face. -/
private noncomputable def rootedUpperWithTopMap
    (G : SimpleGraph V) (F : RootedPos G) :
    WithTop (Set.Ici F) → Set.Ici F.1 :=
  WithTop.recTopCoe
    ⟨top G, (show F.1 ≤ top G from le_top)⟩
    (fun X ↦ ⟨X.1.1, X.2⟩)


-- @@ L47-50 verbatim
@[simp] private theorem rootedUpperWithTopMap_top
    (G : SimpleGraph V) (F : RootedPos G) :
    rootedUpperWithTopMap G F ⊤ =
      ⟨top G, (show F.1 ≤ top G from le_top)⟩ := rfl


-- @@ L52-55 verbatim
@[simp] private theorem rootedUpperWithTopMap_coe
    (G : SimpleGraph V) (F : RootedPos G) (X : Set.Ici F) :
    rootedUpperWithTopMap G F (X : WithTop (Set.Ici F)) =
      ⟨X.1.1, X.2⟩ := rfl


-- @@ L57-99 verbatim
private theorem rootedUpperWithTopMap_bijective
    (G : SimpleGraph V) (F : RootedPos G) :
    Function.Bijective (rootedUpperWithTopMap G F) := by
  constructor
  · intro X Y hXY
    induction X using WithTop.recTopCoe with
    | top =>
        induction Y using WithTop.recTopCoe with
        | top => rfl
        | coe Y =>
            exfalso
            have hface := congrArg Subtype.val hXY
            rw [rootedUpperWithTopMap_top,
              rootedUpperWithTopMap_coe] at hface
            exact Y.1.2.ne_top hface.symm
    | coe X =>
        induction Y using WithTop.recTopCoe with
        | top =>
            exfalso
            have hface := congrArg Subtype.val hXY
            rw [rootedUpperWithTopMap_coe,
              rootedUpperWithTopMap_top] at hface
            exact X.1.2.ne_top hface
        | coe Y =>
            apply congrArg ((↑) : Set.Ici F → WithTop (Set.Ici F))
            apply Subtype.ext
            apply Subtype.ext
            have hface := congrArg Subtype.val hXY
            rw [rootedUpperWithTopMap_coe,
              rootedUpperWithTopMap_coe] at hface
            exact hface
  · intro X
    by_cases hX : X.1 = top G
    · refine ⟨⊤, ?_⟩
      apply Subtype.ext
      rw [rootedUpperWithTopMap_top]
      exact hX.symm
    · let Xr : RootedPos G :=
        ⟨X.1, F.2.upper_of_ne_top X.2 hX⟩
      let Xi : Set.Ici F := ⟨Xr, X.2⟩
      refine ⟨(Xi : WithTop (Set.Ici F)), ?_⟩
      apply Subtype.ext
      rw [rootedUpperWithTopMap_coe]


-- @@ L101-133 verbatim
/-- The upper interval of a positive-rooted face is its rooted-stratum upper
interval with one common global top adjoined. -/
noncomputable def rootedUpperWithTopOrderIso
    (G : SimpleGraph V) (F : RootedPos G) :
    WithTop (Set.Ici F) ≃o Set.Ici F.1 where
  toEquiv := Equiv.ofBijective (rootedUpperWithTopMap G F)
    (rootedUpperWithTopMap_bijective G F)
  map_rel_iff' := by
    intro X Y
    change rootedUpperWithTopMap G F X ≤ rootedUpperWithTopMap G F Y ↔ X ≤ Y
    induction X using WithTop.recTopCoe with
    | top =>
        induction Y using WithTop.recTopCoe with
        | top => simp
        | coe Y =>
            have hnot : ¬(top G ≤ Y.1.1) := by
              intro h
              exact Y.1.2.ne_top (top_unique h)
            rw [rootedUpperWithTopMap_top, rootedUpperWithTopMap_coe]
            change top G ≤ Y.1.1 ↔
              (⊤ : WithTop (Set.Ici F)) ≤ (Y : WithTop (Set.Ici F))
            simp [hnot]
    | coe X =>
        induction Y using WithTop.recTopCoe with
        | top =>
            rw [rootedUpperWithTopMap_coe, rootedUpperWithTopMap_top]
            constructor <;> intro _
            · exact le_top
            · exact le_top
        | coe Y =>
            rw [rootedUpperWithTopMap_coe, rootedUpperWithTopMap_coe]
            simp only [WithTop.coe_le_coe]
            rfl


-- @@ L135-142 verbatim
private def prodIciOrderIso {P : Type*} {Q : Type*}
    [Preorder P] [Preorder Q] (a : P) (b : Q) :
    Set.Ici a × Set.Ici b ≃o Set.Ici (a, b) where
  toFun x := ⟨(x.1.1, x.2.1), ⟨x.1.2, x.2.2⟩⟩
  invFun x := (⟨x.1.1, x.2.1⟩, ⟨x.1.2, x.2.2⟩)
  left_inv _x := rfl
  right_inv _x := rfl
  map_rel_iff' := Iff.rfl


-- @@ L144-153 verbatim
/-- Restrict an order isomorphism to upper intervals at corresponding
points. -/
private def OrderIso.restrictIci {P : Type*} {Q : Type*}
    [Preorder P] [Preorder Q] (e : P ≃o Q) (a : P) :
    Set.Ici a ≃o Set.Ici (e a) where
  toFun x := ⟨e x.1, (map_le_map_iff e).mpr x.2⟩
  invFun x := ⟨e.symm x.1, e.le_symm_apply.mpr x.2⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x.1)
  right_inv x := Subtype.ext (e.apply_symm_apply x.1)
  map_rel_iff' := map_le_map_iff e


-- @@ L155-162 expanded
/-- The positive-rooted stratum of a Hansen join is an order product. -/
noncomputable def joinRootedPosOrderIso (A : SimpleGraph V) (B : SimpleGraph W) :
    RootedPos A × RootedPos B ≃o RootedPos (graphJoin A B)
    where
  toEquiv := joinRootedPosEquiv A B
  map_rel_iff' := by
    intro x y
    exact joinRootedPos_le_iff A B x.1 y.1 x.2 y.2


-- @@ L164-178 expanded
/-- The full upper interval of a positive-rooted join face is the product of
the factor rooted upper intervals with one common top adjoined. -/
noncomputable def joinRootedUpperIntervalOrderIso (A : SimpleGraph V) (B : SimpleGraph W)
    (F : RootedPos A) (K : RootedPos B) :
    Set.Ici (joinRootedPos A B F K) ≃o WithTop (Set.Ici F × Set.Ici K) :=
  by
  change Set.Ici (joinRootedPosOrderIso A B (F, K)).1 ≃o WithTop (Set.Ici F × Set.Ici K)
  exact
    (rootedUpperWithTopOrderIso (graphJoin A B) (joinRootedPosOrderIso A B (F, K))).symm |>.trans
        ((OrderIso.restrictIci (joinRootedPosOrderIso A B) (F, K)).symm |>.withTopCongr) |>.trans
      ((prodIciOrderIso F K).symm.withTopCongr)


-- @@ L180-188 verbatim
/-- Consequently, an upper-interval full flag at a rooted join face is a
maximal chain of the product of the two factor rooted upper intervals. -/
noncomputable def joinRootedUpperIntervalFlagEquiv
    (A : SimpleGraph V) (B : SimpleGraph W)
    (F : RootedPos A) (K : RootedPos B) :
    Flag (Set.Ici (joinRootedPos A B F K)) ≃
      Flag (Set.Ici F × Set.Ici K) :=
  (Flag.map (joinRootedUpperIntervalOrderIso A B F K)).trans
    Flag.withTopEquiv


-- @@ L190-190 verbatim
end HansenCombinatorialFace

-- @@ L191-191 verbatim
end HansenCograph
