/-
Copyright (c) 2026 Sven Manthe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sven Manthe
-/
module

public import Mathlib.Order.Category.PartOrd
public import LeanPool.AFormalizationOfBorelDeterminacyInLean.Tree.Trees
public import Mathlib.Tactic.Continuity
import LeanPool.AFormalizationOfBorelDeterminacyInLean.Basic.General
import LeanPool.AFormalizationOfBorelDeterminacyInLean.Basic.Meta
import LeanPool.AFormalizationOfBorelDeterminacyInLean.Basic.MiscCat
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Order.Lattice.Nat
import Mathlib.Tactic.ApplyFun
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow


-- @@ L22-26 verbatim
/-!
# LeanPool.AFormalizationOfBorelDeterminacyInLean.Tree.LenTreeHom

Auxiliary declarations for the Borel determinacy formalization.
-/


-- @@ L28-28 verbatim
@[expose] public section



-- @@ L31-31 verbatim
open CategoryTheory


-- @@ L33-33 verbatim
namespace Descriptive.Tree

-- @@ L34-34 verbatim
noncomputable section «Section1»


-- @@ L36-37 verbatim
/-- The objects of the category of trees -/
def Trees := Σ A, tree A

-- @@ L38-39 verbatim
instance : CoeSort Trees (Type _) where
  coe S := S.2

-- @@ L40-40 verbatim
variable {S T U : Trees}

-- @@ L41-43 verbatim
/-- The morphisms in the category of trees, length-preserving order-preserving maps -/
@[ext] structure LenHom (S T : Trees) extends OrderHom S.2 T.2 where
  h_length : ∀ x : S.2, (toFun x).val.length = x.val.length


-- @@ L45-52 verbatim
/-- The category of trees has as objects trees in some set of nodes and as morphisms
  length-preserving order-preserving maps. It is a topos (although this fact is not
  proved here). Namely, the map to Presheaves on ℕ such that evaluation becomes resEq
  and the transition maps are given by `List.take` induces an equivalence -/
instance : Category Trees where
  Hom := LenHom
  id S := ⟨OrderHom.id, fun _ ↦ rfl⟩
  comp f g := ⟨g.toOrderHom.comp f.toOrderHom, fun h ↦ by erw [g.h_length, f.h_length]⟩

-- @@ L53-56 verbatim
/-- Auxiliary declaration for the Borel determinacy formalization. -/
def forgetPO : Trees ⥤ PartOrd where
  obj T := { carrier := T.2 }
  map f := PartOrd.ofHom f.toOrderHom

-- @@ L57-58 verbatim
instance : forgetPO.Faithful where
  map_injective {_ _} _ _ h := LenHom.ext (congr_arg (OrderHom.toFun ∘ PartOrd.Hom.hom) h)

-- @@ L59-61 verbatim
instance : FunLike (S ⟶ T) S T where
  coe f := f.toFun
  coe_injective _ _ h := LenHom.ext h

-- @@ L62-63 verbatim
instance : OrderHomClass (S ⟶ T) S.2 T.2 where
  map_rel f _ _ h := f.toOrderHom.monotone' h

-- @@ L64-70 verbatim
instance : ConcreteCategory Trees (fun S T ↦ S ⟶ T) (CC := fun S ↦ S.2) where
  hom f := f
  ofHom f := f
  hom_ofHom _ := rfl
  ofHom_hom _ := rfl
  id_apply _ := rfl
  comp_apply _ _ _ := rfl


-- @@ L72-72 verbatim
@[simp] lemma rem_lenHom : LenHom S T = (S ⟶ T) := rfl

-- @@ L73-73 verbatim
@[ext] lemma tree_ext {x y : S} (h : x.val = y.val) : x = y := Subtype.ext h

-- @@ L74-74 verbatim
instance instPartialOrderTreeElement : PartialOrder S := inferInstance

-- @@ L75-75 verbatim
@[simp] lemma le_def_trees (x y : T) : x ≤ y ↔ x.val <+: y.val := Iff.rfl

-- @@ L76-77 verbatim
@[simp] lemma rem_toOrderHom (f : S ⟶ T) :
  DFunLike.coe (F := S →o T) f.toOrderHom = f := rfl

-- @@ L78-78 verbatim
lemma rem_toFun (f : S ⟶ T) (x : S) : f.toFun x = f x := rfl

-- @@ L79-79 verbatim
@[simp] lemma forget_map (f : S ⟶ T) : (forget Trees).map f = TypeCat.ofHom f := rfl


-- @@ L81-81 verbatim
namespace LenHom

-- @@ L82-82 verbatim
lemma id_toFun (S : Trees) : (𝟙 S : S ⟶ S).toFun = _root_.id := rfl

-- @@ L83-84 verbatim
lemma comp_toFun (f : S ⟶ T) (g : T ⟶ U) :
  (f ≫ g).toFun = g.toFun ∘ f.toFun := rfl

-- @@ L85-86 verbatim
instance {S T : Trees} (f : S ⟶ T) [IsIso f] : IsIso (TypeCat.ofHom f.toFun) := by
  simpa [forget_map] using inferInstanceAs (IsIso ((forget Trees).map f))

-- @@ L87-90 verbatim
lemma inv_toFun {S T : Trees} (f : S ⟶ T) [IsIso f] :
  (inv f).toFun = inv (TypeCat.ofHom f.toFun) :=
  congrArg TypeCat.Fun.toFun <|
    congrArg TypeCat.Hom.hom (IsIso.Iso.inv_hom ((forget Trees).mapIso (asIso f))).symm


-- @@ L92-93 verbatim
@[simp, simp_lengths] lemma h_length_simp (f : S ⟶ T) (x : S) :
  (f x).val.length (α := no_index _) = x.val.length (α := no_index _) := f.h_length x

-- @@ L94-103 verbatim
lemma h_length_inv (f : S ⟶ T) [IsIso (TypeCat.ofHom f.toFun)] (x : T) :
  (inv (TypeCat.ofHom f.toFun) x).val.length = x.val.length := by
  have hlen :
      ((TypeCat.ofHom f.toFun) (inv (TypeCat.ofHom f.toFun) x)).val.length =
        (inv (TypeCat.ofHom f.toFun) x).val.length :=
    h_length_simp f (inv (TypeCat.ofHom f.toFun) x)
  have hcancel :
      ((TypeCat.ofHom f.toFun) (inv (TypeCat.ofHom f.toFun) x)).val.length = x.val.length :=
    congrArg (fun y : T ↦ y.val.length) (cancel_inv_right_types (TypeCat.ofHom f.toFun) x)
  exact hlen.symm.trans hcancel

-- @@ L104-105 verbatim
@[simp] lemma map_nil (f : S ⟶ T) (h : [] ∈ S.2) : (f ⟨[], h⟩).val = [] := by
  apply List.eq_nil_of_length_eq_zero; simp

-- @@ L106-108 verbatim
lemma map_ne_nil (f : S ⟶ T) {x : S} (h : x.val ≠ []) : (f x).val ≠ [] := by
  intro h'; apply_fun List.length at h'
  exact h <| List.length_eq_zero_iff.mp <| by simpa using h'


-- @@ L110-111 verbatim
lemma mk_eval (S T : Trees) (f : S → T) hf1 hf2 (x : S) :
  DFunLike.coe (F := S ⟶ T) (no_index ⟨⟨f, hf1⟩, hf2⟩) x = f x := rfl

-- @@ L112-112 verbatim
end LenHom


-- @@ L114-118 verbatim
lemma take_apply (f : S ⟶ T) (n : ℕ) (x : S) :
  f (take n x) = take n (f x) := by
  ext1; apply List.IsPrefix.eq_of_length
  · simpa [List.prefix_take_iff] using f.monotone' (List.take_prefix n x.val)
  · simp only [LenHom.h_length_simp, take_coe, List.length_take]

-- @@ L119-121 verbatim
lemma take_apply_val (f : S ⟶ T) (n : ℕ) (x : S) :
  (f (take n x)).val = (f x).val.take n :=
  congr_arg Subtype.val (take_apply f n x)

-- @@ L122-127 verbatim
lemma prefix_iff (f : S ⟶ T) x y (hf : Function.Injective f) :
  f x ≤ f y ↔ x ≤ y := by
  constructor <;> intro h
  · conv at h => simp [List.prefix_iff_eq_take, ← take_apply_val, Subtype.val_inj]
    exact List.prefix_iff_eq_take.mpr <| congr_arg Subtype.val (hf h)
  · exact f.monotone' h


-- @@ L129-158 verbatim
instance : (forget Trees).ReflectsIsomorphisms where
  reflects := by
    intro S T f _
    constructor
    have hIso : IsIso (TypeCat.ofHom f.toFun) := by
      simpa [forget_map] using inferInstanceAs (IsIso ((forget Trees).map f))
    have := hIso
    have hinj : Function.Injective f := by
      intro x y h
      exact ((isIso_iff_bijective (TypeCat.ofHom f.toFun)).mp inferInstance).1 h
    let g : T ⟶ S := {
      toFun := inv (TypeCat.ofHom f.toFun)
      monotone' := by
        intro x y h
        apply (prefix_iff f _ _ hinj).mp
        have hx : f (inv (TypeCat.ofHom f.toFun) x) = x :=
          cancel_inv_right_types (TypeCat.ofHom f.toFun) x
        have hy : f (inv (TypeCat.ofHom f.toFun) y) = y :=
          cancel_inv_right_types (TypeCat.ofHom f.toFun) y
        simpa [hx, hy] using h
      h_length := LenHom.h_length_inv _
    }
    use g
    constructor
    · apply LenHom.ext
      funext x
      exact cancel_inv_left_types (TypeCat.ofHom f.toFun) x
    · apply LenHom.ext
      funext x
      exact cancel_inv_right_types (TypeCat.ofHom f.toFun) x


-- @@ L160-160 verbatim
end «Section1»


-- @@ L162-162 verbatim
end Descriptive.Tree
